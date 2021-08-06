{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}

module Cardano.Wallet.Primitive.CoinSelection.CollateralSpec where

import Prelude

import Cardano.Wallet.Primitive.CoinSelection.Collateral
    ( AddrNotSuitableForCollateral (..)
    , asCollateral
    , classifyCollateralAddress
    )
import Cardano.Wallet.Primitive.Types.Address
    ( Address (..) )
import Cardano.Wallet.Primitive.Types.Hash
    ( Hash (..) )
import Cardano.Wallet.Primitive.Types.TokenBundle
    ( TokenBundle )
import Cardano.Wallet.Primitive.Types.TokenBundle.Gen
    ( genTokenBundleSmallRangePositive, shrinkTokenBundleSmallRangePositive )
import Cardano.Wallet.Primitive.Types.Tx
    ( TxIn (..), TxOut (..) )
import Cardano.Wallet.Unsafe
    ( unsafeBech32Decode )
import Control.Monad
    ( replicateM_ )
import Data.Bits
    ( (.&.) )
import Data.ByteString
    ( ByteString )
import Data.ByteString.Base58
    ( bitcoinAlphabet, decodeBase58 )
import Data.Function
    ( (&) )
import Data.Maybe
    ( fromJust, isJust, isNothing )
import Numeric
    ( showHex )
import Test.Hspec
    ( Expectation, Spec, describe, it, parallel, shouldBe )
import Test.QuickCheck
    ( Arbitrary (..)
    , Gen
    , Property
    , allProperties
    , checkCoverage
    , counterexample
    , cover
    , coverTable
    , disjoin
    , forAll
    , forAllShrink
    , frequency
    , oneof
    , property
    , scale
    , tabulate
    , vector
    , withMaxSuccess
    , (=/=)
    , (===)
    )
import Test.QuickCheck.Hedgehog
    ( hedgehog )

import qualified Cardano.Ledger.Address as L
import qualified Cardano.Ledger.Credential as L
import qualified Cardano.Ledger.Crypto as CC
import qualified Cardano.Ledger.Hashes as L
import qualified Cardano.Wallet.Primitive.Types.TokenBundle as TokenBundle
import qualified Data.Binary.Get as B
import qualified Data.Binary.Put as B
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Lazy as BSL
import qualified Test.Cardano.Chain.Common.Gen as Byron
import qualified Test.Shelley.Spec.Ledger.Serialisation.EraIndepGenerators as L
import qualified Test.Shelley.Spec.Ledger.Serialisation.Generators.Genesis as L
    ( genRewardAcnt )

-- In the realm of cardano-ledger-specs, we recognize the following types of
-- addresses:
--   (see https://hydra.iohk.io/build/6752483/download/1/ledger-spec.pdf):
--
-- | Address type       | Payment Credential | Stake Credential | Header, first nibble |
-- |--------------------+--------------------+------------------+----------------------|
-- | Base address       | keyhash            | keyhash          |                 0000 |
-- |                    | scripthash         | keyhash          |                 0001 |
-- |                    | keyhash            | scripthash       |                 0010 |
-- |                    | scripthash         | scripthash       |                 0011 |
-- | Pointer address    | keyhash            | ptr              |                 0100 |
-- |                    | scripthash         | ptr              |                 0101 |
-- | Enterprise address | keyhash            | -                |                 0110 |
-- |                    | scripthash         | 0                |                 0111 |
-- | Bootstrap address  | keyhash            | -                |                 1000 |
-- | Stake address      | -                  | keyhash          |                 1110 |
-- |                    | -                  | scripthash       |                 1111 |
-- | Future formats     | ?                  | ?                |            1001-1101 |
--
-- We represent these types of addresses with the following data types:

-- | The type of the address
data AddressType
    = BaseAddress Credential Credential
    | PointerAddress Credential
    | EnterpriseAddress Credential
    | StakeAddress Credential
    | BootstrapAddress
    -- ^ A Bootstrap (a.k.a. Byron) address
    deriving (Eq, Show)

-- | Represents the type of the credential
data Credential
    = CredentialKeyHash
    | CredentialScriptHash
    deriving (Eq, Show)

-- To parse the address type, we can inspect the first four bits (nibble) of the
-- address:

-- | Get an AddressType from a binary stream.
getHeader :: B.Get AddressType
getHeader = do
    headerAndNetwork <- B.getWord8
    let
        header =
            -- Mask for just the address type nibble
            headerAndNetwork .&. 0b11110000
    case header of
        0b00000000 -> pure $ BaseAddress CredentialKeyHash CredentialKeyHash
        0b00010000 -> pure $ BaseAddress CredentialScriptHash CredentialKeyHash
        0b00100000 -> pure $ BaseAddress CredentialKeyHash CredentialScriptHash
        0b00110000 -> pure $ BaseAddress CredentialScriptHash CredentialScriptHash
        0b01000000 -> pure $ PointerAddress CredentialKeyHash
        0b01010000 -> pure $ PointerAddress CredentialScriptHash
        0b01100000 -> pure $ EnterpriseAddress CredentialKeyHash
        0b01110000 -> pure $ EnterpriseAddress CredentialScriptHash
        0b10000000 -> pure BootstrapAddress
        0b11100000 -> pure $ StakeAddress CredentialKeyHash
        0b11110000 -> pure $ StakeAddress CredentialScriptHash
        _          -> fail "Unknown address type."

-- For testing purposes, it is also helpful to have a way of writing the
-- AddressType back to a binary stream.

-- | Write an AddressType to a binary stream.
putHeader :: AddressType -> B.Put
putHeader (BaseAddress CredentialKeyHash CredentialKeyHash) =
    B.putWord8 0b00000000
putHeader (BaseAddress CredentialScriptHash CredentialKeyHash) =
    B.putWord8 0b00010000
putHeader (BaseAddress CredentialKeyHash CredentialScriptHash) =
    B.putWord8 0b00100000
putHeader (BaseAddress CredentialScriptHash CredentialScriptHash) =
    B.putWord8 0b00110000
putHeader (PointerAddress CredentialKeyHash) =
    B.putWord8 0b01000000
putHeader (PointerAddress CredentialScriptHash) =
    B.putWord8 0b01010000
putHeader (EnterpriseAddress CredentialKeyHash) =
    B.putWord8 0b01100000
putHeader (EnterpriseAddress CredentialScriptHash) =
    B.putWord8 0b01110000
putHeader BootstrapAddress =
    B.putWord8 0b10000000
putHeader (StakeAddress CredentialKeyHash) =
    B.putWord8 0b11100000
putHeader (StakeAddress CredentialScriptHash) =
    B.putWord8 0b11110000

-- We want to test that these functions work, so we write a set of properties to
-- test:

-- First we write our generator, which customizes it's frequency so that every
-- branch of the AddressType type is evenly covered.

-- | Generate an AddressType.
genAddressType :: Gen AddressType
genAddressType =
    frequency
        [ (4, BaseAddress <$> genCredential <*> genCredential)
        , (2, PointerAddress <$> genCredential)
        , (2, EnterpriseAddress <$> genCredential)
        , (2, StakeAddress <$> genCredential)
        , (1, pure BootstrapAddress)
        ]

-- | Generate a credential.
genCredential :: Gen Credential
genCredential =
    oneof [ pure CredentialKeyHash
          , pure CredentialScriptHash
          ]

-- | Test that our generator covers every type of address, so we know our
-- property tests are sensible.
prop_genAddressType_coverage :: Property
prop_genAddressType_coverage =
    withMaxSuccess 1000 $
    forAll genAddressType $ \addrType ->
    coverTable "Address types"
        [ ("BaseAddress CredentialKeyHash CredentialKeyHash"       , 5)
        , ("BaseAddress CredentialKeyHash CredentialScriptHash"    , 5)
        , ("BaseAddress CredentialScriptHash CredentialKeyHash"    , 5)
        , ("BaseAddress CredentialScriptHash CredentialScriptHash" , 5)
        , ("PointerAddress CredentialKeyHash"                      , 5)
        , ("PointerAddress CredentialScriptHash"                   , 5)
        , ("EnterpriseAddress CredentialKeyHash"                   , 5)
        , ("EnterpriseAddress CredentialScriptHash"                , 5)
        , ("StakeAddress CredentialKeyHash"                        , 5)
        , ("StakeAddress CredentialScriptHash"                     , 5)
        , ("BootstrapAddress"                                      , 5)
        ] $
        tabulate "Address types" [show addrType] $ True === True

-- | Test that putting then getting an AddressType results in the original
-- AddressType (we can roundtrip successfully).
prop_header_roundtrips :: Property
prop_header_roundtrips =
    forAll genAddressType $ \addrType ->
        B.runGet getHeader (B.runPut $ putHeader addrType) === addrType

-- We an also write properties for the general types of addresses, and ensure
-- that we are classifying them correctly.

-- | Test that for any Byron address, we classify it as a Byron (a.k.a.
-- bootstrap) address.
prop_addressType_byron :: Property
prop_addressType_byron =
    forAll genByronAddr $ \byronAddr -> do
        let (Address addrBytes) = asAddress byronAddr
        B.runGet getHeader (BSL.fromStrict addrBytes) === BootstrapAddress

-- | Test that for any stake address, we classify it as a stake address
-- (although not necessarily the correct one, as it's a bit difficult to assert
-- that the credential type is correct).
prop_addressType_stake :: Property
prop_addressType_stake =
    forAll genStakeAddr $ \stakeAddr -> do
        let
            (Address addrBytes) = asStakeAddress stakeAddr
            addrType = B.runGet getHeader (BSL.fromStrict addrBytes)
        disjoin
          [ addrType === StakeAddress CredentialKeyHash
          , addrType === StakeAddress CredentialScriptHash
          ]

-- | Test that for any shelley keyhash address, we classify it as a shelley
-- keyhash address (although not necessarily the correct one, as it's a bit
-- difficult to assert that the exact type is correct).
prop_addressType_shelleyKeyHash :: Property
prop_addressType_shelleyKeyHash =
    forAll genShelleyKeyHashAddr $ \shelleyKeyHashAddr -> do
        let
            (Address addrBytes) = asAddress shelleyKeyHashAddr
            addrType = B.runGet getHeader (BSL.fromStrict addrBytes)
        disjoin
          [ addrType === BaseAddress CredentialKeyHash CredentialKeyHash
          , addrType === BaseAddress CredentialKeyHash CredentialScriptHash
          , addrType === PointerAddress CredentialKeyHash
          , addrType === EnterpriseAddress CredentialKeyHash
          ]

-- | Test that for any shelley scripthash address, we classify it as a shelley
-- scripthash address (although not necessarily the correct one, as it's a bit
-- difficult to assert that the exact type is correct).
prop_addressType_shelleyScriptHash :: Property
prop_addressType_shelleyScriptHash =
    forAll genShelleyScriptHashAddr $ \shelleyScriptHashAddr -> do
        let
            (Address addrBytes) = asAddress shelleyScriptHashAddr
            addrType = B.runGet getHeader (BSL.fromStrict addrBytes)
        disjoin
          [ addrType === BaseAddress CredentialScriptHash CredentialKeyHash
          , addrType === BaseAddress CredentialScriptHash CredentialScriptHash
          , addrType === PointerAddress CredentialScriptHash
          , addrType === EnterpriseAddress CredentialScriptHash
          ]

-- To be extra sure, we also test our code with some golden addresses we
-- generated with "cardano-addresses":

unit_addressType_byronGolden :: Expectation
unit_addressType_byronGolden =
    B.runGet getHeader byronAddrGolden `shouldBe` BootstrapAddress

unit_addressType_shelleyEnterprisePaymentGolden :: Expectation
unit_addressType_shelleyEnterprisePaymentGolden =
    B.runGet getHeader shelleyEnterprisePaymentAddrGolden
        `shouldBe` EnterpriseAddress CredentialKeyHash

unit_addressType_stakeAddrGolden :: Expectation
unit_addressType_stakeAddrGolden =
    B.runGet getHeader stakeAddrGolden
        `shouldBe` StakeAddress CredentialKeyHash

unit_addressType_pointerAddrGolden :: Expectation
unit_addressType_pointerAddrGolden =
    B.runGet getHeader pointerAddrGolden
        `shouldBe` PointerAddress CredentialKeyHash

unit_addressType_delegationAddrGolden :: Expectation
unit_addressType_delegationAddrGolden =
    B.runGet getHeader delegationAddrGolden
        `shouldBe` BaseAddress CredentialKeyHash CredentialKeyHash

-- TODO generate more unit tests for each type of address.

-- The funds associated with an address are considered suitable for use as
-- collateral iff the payment credential column of that address is "key hash".
--
-- So, there are a few properties we would like to assert about our
-- "classifyCollateralAddress" function:
--
-- 1. That our classification function always considers addresses with a keyhash
--    payment credential as suitable for collateral.
-- 2. That our classification function always considers addresses without a
--    keyhash payment credential as unsuitable for collateral.
-- 3. That future format addresses are always rejected.
--
-- That's it really. We also want to assert that our generators cover the full
-- range of possible address types, including future and unknown formats. So we
-- start by creating a generator that customizes it's frequency to ensure that
-- every type of address is evenly covered ("genByronAddr" only generates one
-- type of address so is given lower frequency than "genShelleyAddr", which must
-- generate eight types of addresses). We also include Addresses that are just
-- an arbitrary set of bytes (very likely to be invalid).

-- | Generate an Address, covers the full range of address types plus invalid
-- addresses.
genAnyAddress :: Gen Address
genAnyAddress =
    frequency [ (10, asAddress <$> genShelleyAddr)
              , (1, asAddress <$> genByronAddr)
              , (2, asStakeAddress <$> genStakeAddr)
              , (3, Address <$> arbitrary)
              ]

-- | Check that @genAnyAddress@ has sufficient coverage.
prop_genAddress_coverage :: Property
prop_genAddress_coverage =
    withMaxSuccess 1000 $
    forAll genAnyAddress $ \addr@(Address addrBytes) -> do
        let addrType = runGetMaybe getHeader $ BSL.fromStrict addrBytes
        coverTable "Address types"
            [ ("Just (BaseAddress CredentialKeyHash CredentialKeyHash)"       , 5)
            , ("Just (BaseAddress CredentialKeyHash CredentialScriptHash)"    , 5)
            , ("Just (BaseAddress CredentialScriptHash CredentialKeyHash)"    , 5)
            , ("Just (BaseAddress CredentialScriptHash CredentialScriptHash)" , 5)
            , ("Just (PointerAddress CredentialKeyHash)"                      , 5)
            , ("Just (PointerAddress CredentialScriptHash)"                   , 5)
            , ("Just (EnterpriseAddress CredentialKeyHash)"                   , 5)
            , ("Just (EnterpriseAddress CredentialScriptHash)"                , 5)
            , ("Just (StakeAddress CredentialKeyHash)"                        , 5)
            , ("Just (StakeAddress CredentialScriptHash)"                     , 5)
            , ("Just BootstrapAddress"                                        , 5)
            , ("Nothing"                                                      , 5)
            ] $
            tabulate "Address types" [show addrType] $ True === True

-- Using real addresses for the generators is an important idea, as the domain
-- of the classification function is the set of all addresses (really all
-- ByteStrings, thanks to our loose representation of Addresses, but we account
-- for that in our generator already). However, real addresses make for awful
-- counterexamples, so after generating an address, we try to determine what
-- kind of address it is by inspecting the first four bits: If it is an address
-- format we recognize, we shrink towards an address that has the same first
-- four bits, but 0 bits everywhere else. This forms a valid address that is
-- easier on the eyes, except in two cases: stake addresses and bootstrap
-- addresses. We can offer no shrinkage for those two kinds of addresses, but
-- try to provide a good explanation using `counterExample`. This is a helpful
-- strategy because at this current point in time collateral suitability can be
-- determined simply by inspecting the first four bits, so that is the most
-- important piece of information for debugging.
--
-- Here is an example of test output without shrinking:
-- Address "p\r\148\225ts.\249\170\231?9Z\180E\a\191\169\131\214P#\193\SUB\149\US\f2\228\204u\NUL\SOH"
-- Address hex: 71d94e174732ef9aae73f395ab4457bfa983d65023c11a951fc32e4cc7501
-- AddressType: Just (EnterpriseAddress CredentialScriptHash)
--
-- And here is an example of test output with shrinking:
-- Address "p\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"
-- Address hex: 700000000000000000000000000000
-- AddressType: Just (EnterpriseAddress CredentialScriptHash)

-- | Attempt to simplify an address. Only shelley addresses can be simplified
-- and are simplified towards a binary encoding of addrType:(set of null bytes).
simplifiedAddress :: Address -> Maybe Address
simplifiedAddress (Address addrBytes) = do
    -- Don't try to simplify malformed addresses or stake addresses
    _ <- L.deserialiseAddr addrBytes :: Maybe (L.Addr CC.StandardCrypto)

    bytes <- case runGetMaybe getHeader (BSL.fromStrict addrBytes) of
        Just BootstrapAddress ->
            Nothing
        Just (StakeAddress _) ->
            Nothing
        Just addr@(BaseAddress _ _) -> do
            Just $ B.runPut $ do
                putHeader addr
                -- payload for base addr is two 28-byte bytestrings
                putNullBytes 28
                putNullBytes 28
        Just addr@(PointerAddress _) ->
            Just $ B.runPut $ do
                putHeader addr
                -- payload for pointer addr is one 28-byte bytestring followed
                -- by three unsigned ints of variable size (in this case two
                -- bytes each).
                putNullBytes 28
                putNullBytes 2
                putNullBytes 2
                putNullBytes 2
        Just addr@(EnterpriseAddress _) ->
            Just $ B.runPut $ do
                putHeader addr
                -- payload for enterprise addr is one 28-byte bytestring
                putNullBytes 28
        Nothing ->
            Nothing

    pure $ Address $ BSL.toStrict bytes

    where
        -- Put n bytes worth of null bytes
        putNullBytes :: Int -> B.Put
        putNullBytes n = replicateM_ n putNullByte

        -- Put a byte of unset bits
        putNullByte :: B.Put
        putNullByte = B.putWord8 0b00000000

-- Of course, there are some properties we want to assert about this function.
-- When we simplify an address:
--
--   Given the address can be simplified,
--   - the simplified address is still a valid address
--   - the type of the simplified address matches the type of the original
--     address (address type is preserved)

-- | Assert that if an address can be simplified, the simplified address is
-- still a valid address.
prop_simplifiedAddress_validAddress :: Property
prop_simplifiedAddress_validAddress =
    forAll genAnyAddress $ \addr@(Address addrBytes) ->
        checkCoverage $
            cover 30 (isNothing $ simplifiedAddress addr)
                "couldn't simplify address"  $
            cover 30 (isJust $ simplifiedAddress addr)
                "could simplify address"  $
            case simplifiedAddress addr of
                Nothing ->
                    True === True
                Just simplified@(Address simplifiedBytes) ->
                    let
                        originalAddress :: Maybe (L.Addr CC.StandardCrypto)
                        originalAddress = L.deserialiseAddr addrBytes

                        simplifiedAddress :: Maybe (L.Addr CC.StandardCrypto)
                        simplifiedAddress = L.deserialiseAddr simplifiedBytes
                    in
                        isJust originalAddress === isJust simplifiedAddress
                        & counterexample
                            ("Simplified: " <> show simplifiedAddress <>
                             ", bytes (hex): " <>
                                BS.foldr showHex "" simplifiedBytes
                            )
                        & counterexample
                            ("Original: " <> show originalAddress <>
                             ", bytes (hex): " <>
                                BS.foldr showHex "" addrBytes
                            )

-- | Assert that if an address can be simplified, the type of the simplified
-- address matches the type of the original address.
prop_simplifiedAddress_typeMaintained :: Property
prop_simplifiedAddress_typeMaintained =
    forAll genAnyAddress $ \addr@(Address addrBytes) ->
        checkCoverage $
            cover 30 (isNothing $ simplifiedAddress addr)
                "couldn't simplify address"  $
            cover 30 (isJust $ simplifiedAddress addr)
                "could simplify address"  $
            case simplifiedAddress addr of
                Nothing ->
                    True === True
                Just simplified@(Address simplifiedBytes) ->
                    let
                        originalAddressType =
                            B.runGet getHeader (BSL.fromStrict addrBytes)

                        simplifiedAddressType =
                            B.runGet getHeader (BSL.fromStrict simplifiedBytes)
                    in
                        originalAddressType === simplifiedAddressType

-- From this function we can generator a QuickCheck shrinker:

-- | Try to shrink an address by simplifying it.
shrinkAddress :: Address -> [Address]
shrinkAddress addr =
    case simplifiedAddress addr of
        Nothing ->
            -- There are some address types we can't meaningfully shrink.
            []
        Just simplified ->
            -- Otherwise we can shrink to the simplified address, so long as we
            -- actually changed the address
            [simplified | simplified /= addr]

-- With that out the way we can write our property test to ensure that
-- classifyCollateral address behaves as expected:

-- | Assert that, for any valid address, we only classify addresses with a key
-- hash payment credential as being suitable for collateral.
prop_classifyCollateralAddress :: Property
prop_classifyCollateralAddress =
    withMaxSuccess 2000 $
    forAllShrink genAnyAddress shrinkAddress $ \addr@(Address addrBytes) -> do
        let
            addrType = runGetMaybe getHeader $ BSL.fromStrict addrBytes
            validAddress = isValidAddress addr

        checkCoverage $
            cover 30 validAddress "valid address"  $
            cover 10 (not validAddress) "invalid address"  $
            if not validAddress
            then
                -- It will always fail invalid addresses
                classifyCollateralAddress addr
                    === Left IsAMalformedOrUnknownAddr
            else
                case addrType of
                    -- Only unrecognized addresses are classified as malformed
                    -- or unknown (i.e. we otherwise classify any known address
                    -- according to it's type)
                    Nothing ->
                        classifyCollateralAddress addr
                            === Left IsAMalformedOrUnknownAddr

                    -- Stake addresses are not suitable for collateral
                    Just (StakeAddress _) ->
                        classifyCollateralAddress addr
                            === Left IsAStakeAddr

                    -- Script addresses are not suitable for collateral
                    Just (BaseAddress CredentialScriptHash _) ->
                        classifyCollateralAddress addr
                            === Left IsAScriptAddr
                    Just (PointerAddress CredentialScriptHash) ->
                        classifyCollateralAddress addr
                            === Left IsAScriptAddr
                    Just (EnterpriseAddress CredentialScriptHash) ->
                        classifyCollateralAddress addr
                            === Left IsAScriptAddr

                    -- The following addresses all have a key hash payment
                    -- credential and are thus suitable for collateral
                    Just (BaseAddress CredentialKeyHash _) ->
                        classifyCollateralAddress addr
                            === Right addr
                    Just (PointerAddress CredentialKeyHash) ->
                        classifyCollateralAddress addr
                            === Right addr
                    Just (EnterpriseAddress CredentialKeyHash) ->
                        classifyCollateralAddress addr
                            === Right addr
                    Just BootstrapAddress ->
                        classifyCollateralAddress addr
                            === Right addr

                & counterexample ("AddressType: " <> show addrType)
                & counterexample ("Address hex: " <> asHex addrBytes)

-- | Returns True if the given address parses as a known address.
isValidAddress :: Address -> Bool
isValidAddress (Address addrBytes) =
  isJust (L.deserialiseAddr addrBytes
          :: Maybe (L.Addr CC.StandardCrypto))
  ||
  isJust (L.deserialiseRewardAcnt addrBytes
          :: Maybe (L.RewardAcnt CC.StandardCrypto))

-- To be extra sure, we also test classifyCollateralAddress with some golden
-- addresses:

unit_classifyCollateralAddress_byronGolden :: Expectation
unit_classifyCollateralAddress_byronGolden =
    let
        addr =
            Address . fromJust . decodeBase58 bitcoinAlphabet . BSL.toStrict
            $ byronAddrGolden
    in
        classifyCollateralAddress addr `shouldBe` Right addr

unit_classifyCollateralAddress_shelleyEnterprisePaymentGolden :: Expectation
unit_classifyCollateralAddress_shelleyEnterprisePaymentGolden =
    let
        addr = Address . BSL.toStrict . unsafeBech32Decode
               $ _ $ shelleyEnterprisePaymentAddrGolden
    in
        classifyCollateralAddress addr `shouldBe` Right addr

unit_classifyCollateralAddress_stakeAddrGolden :: Expectation
unit_classifyCollateralAddress_stakeAddrGolden =
    let
        addr = Address . BSL.toStrict . unsafeBech32Decode
               $ _ $ stakeAddrGolden
    in
        classifyCollateralAddress addr `shouldBe` Left IsAStakeAddr

unit_classifyCollateralAddress_pointerAddrGolden :: Expectation
unit_classifyCollateralAddress_pointerAddrGolden =
    let
        addr = Address . BSL.toStrict . unsafeBech32Decode
               $ _ $ pointerAddrGolden
    in
        classifyCollateralAddress addr `shouldBe` Right addr

unit_classifyCollateralAddress_delegationAddrGolden :: Expectation
unit_classifyCollateralAddress_delegationAddrGolden =
    let
        addr = Address . BSL.toStrict . unsafeBech32Decode
               $ _ $ delegationAddrGolden
    in
        classifyCollateralAddress addr `shouldBe` Right addr

-- We want to assert many of the same properties about "asCollateral" as we did
-- "classifyCollateralAddress". Rather than testing these properties twice, we
-- use the following logic:
--
--   - Given that the implementation of "classifyCollateralAddress" is correct,
--   - Given that the implementation of "TokenBundle.toCoin" is correct,
--   - and that "asCollateral" is equivalent to a simple composition of
--     "classifyCollateralAddress" and "TokenBundle.toCoin",
--   - we can say that the implementation of "asCollateral" is also correct, so
--     long as the composition operator is guranteed not to change the
--     properties we are interested in.
--
-- The composition operator we are using here is the Maybe instance of (>>).
-- Initially, the Either is demoted to a Maybe, which we know maintains the
-- falsity of the value (Left = Nothing = False, Right = Just = True). From
-- here, the composition operator discards the value inside the Maybe, and so
-- the next argument can only depend on the falsity of the Maybe (indeed, it
-- must). Thus the falsity of the properties is maintained (i.e. "asCollateral"
-- will accept/reject an UTxO correctly, so long as "classifyCollateralAddress"
-- classifies an address correctly). "asCollateral" will return the correct coin
-- value so long as "TokenBundle.toCoin" is working correctly (tested
-- elsewhere).
--
-- I wish I knew how to formally prove things using category theory concepts
-- like monadic composition...

-- | Assert that the "asCollateral" function is equivalent to the "composition"
-- of "classifyCollateralAddress" and "TokenBundle.toCoin".
prop_equivalence :: (TxIn, TxOut) -> Property
prop_equivalence (txIn, txOut@(TxOut addr toks)) =
    asCollateral (txIn, txOut)
    ===
    (either (const Nothing) Just (classifyCollateralAddress addr)
     >> TokenBundle.toCoin toks)

instance Arbitrary TokenBundle where
    arbitrary = genTokenBundleSmallRangePositive
    shrink = shrinkTokenBundleSmallRangePositive

instance Arbitrary TxIn where
    arbitrary = TxIn
        <$> (Hash . B8.pack <$> vector 32)
        <*> scale (`mod` 3) arbitrary

instance Arbitrary TxOut where
    arbitrary = TxOut <$> genAnyAddress <*> arbitrary

-- Finally we group the tests for easy execution

spec :: Spec
spec = do
    parallel $ do
        describe "address types" $ do
            describe "generators" $
              it "generates values with sufficient coverage" $
                  property prop_genAddressType_coverage
            it "serialise/deserialise roundtrips" $
                property prop_header_roundtrips
            it "classifies byron address type correctly" $
                property prop_addressType_byron
            it "classifies stake address type correctly" $
                property prop_addressType_stake
            it "classifies shelley key hash type correctly" $
                property prop_addressType_shelleyKeyHash
            it "classifies shelley script hash type correctly" $
                property prop_addressType_shelleyScriptHash
            it "golden" $ do
                unit_addressType_byronGolden
                unit_addressType_shelleyEnterprisePaymentGolden
                unit_addressType_stakeAddrGolden
                unit_addressType_pointerAddrGolden
                unit_addressType_delegationAddrGolden
        describe "collateral suitability" $ do
            describe "generators and shrinkers" $ do
              it "generates values with sufficient coverage" $
                  property prop_genAddress_coverage
              it "shrink maintains validity" $
                  property prop_simplifiedAddress_validAddress
              it "shrink maintains type" $
                  property prop_simplifiedAddress_typeMaintained
            describe "classifyCollateralAddress" $
                it "classifies any address correctly" $
                    property prop_classifyCollateralAddress
                it "golden" $ do
                    unit_classifyCollateralAddress_byronGolden
                    unit_classifyCollateralAddress_shelleyEnterprisePaymentGolden
                    unit_classifyCollateralAddress_stakeAddrGolden
                    unit_classifyCollateralAddress_pointerAddrGolden
                    unit_classifyCollateralAddress_delegationAddrGolden

-- The following golden keys were generated from the recovery phrase:
-- [change twin tired knee syrup cover dog glare canvas canvas jump egg]

-- cat recovery-phrase.txt | cardano-address key from-recovery-phrase Byron > root.prv
-- cat root.prv | cardano-address key child 14H/42H | tee addr.prv | cardano-address key public --with-chain-code | cardano-address address bootstrap --root $(cat root.prv | cardano-address key public --with-chain-code) --network-tag testnet 14H/42H
byronAddrGolden :: BSL.ByteString
byronAddrGolden = BSL.fromStrict . fromJust . decodeBase58 bitcoinAlphabet $ "37btjrVyb4KFsMoVwPRZ5aJko48uBFFUnJ46eV3vC3uBCC65mj5BfbGP6jYDfhojm8MAayHo4RPvWH4x852FcJq8SHazCx31FJM2TfDpV9Azrc8UKD"

-- cat recovery-phrase.txt | cardano-address key from-recovery-phrase Shelley > root.prv
-- cat root.prv | cardano-address key child 1852H/1815H/0H/2/0 > stake.prv
-- cat stake.prv | cardano-address key public --with-chain-code | cardano-address address stake --network-tag testnet
stakeAddrGolden :: BSL.ByteString
stakeAddrGolden = unsafeBech32Decode
    "stake_test1uztjkmlcknuv29pwuwd8wsk54q5eus56flqs4xy730yvnust8pvfj"

-- cat recovery-phrase.txt | cardano-address key from-recovery-phrase Shelley > root.prv
-- cat root.prv | cardano-address key child 1852H/1815H/0H/0/0 > addr.prv
-- cat addr.prv | cardano-address key public --with-chain-code | cardano-address address payment --network-tag 0 | cardano-address address pointer 42 14 0
pointerAddrGolden :: BSL.ByteString
pointerAddrGolden  = unsafeBech32Decode
    "addr_test1gpdylg53ekxh2404mfgw4pt4gfm7dc9dkc74ck0gtrld8up2pcqqefucl2"

-- cat recovery-phrase.txt | cardano-address key from-recovery-phrase Shelley > root.prv
-- cat root.prv | cardano-address key child 1852H/1815H/0H/2/0 > stake.prv
-- cat root.prv | cardano-address key child 1852H/1815H/0H/0/0 > addr.prv
-- cat addr.prv | cardano-address key public --with-chain-code | cardano-address address payment --network-tag testnet | cardano-address address delegation $(cat stake.prv | cardano-address key public --with-chain-code)
delegationAddrGolden :: BSL.ByteString
delegationAddrGolden = unsafeBech32Decode "addr_test1qpdylg53ekxh2404mfgw4pt4gfm7dc9dkc74ck0gtrld8uyh9dhl3d8cc52zacu6wapdf2pfnepf5n7pp2vfaz7ge8eqd4nn9s"

-- cat recovery-phrase.txt | cardano-address key from-recovery-phrase Shelley > root.prv
-- cat root.prv | cardano-address key child 1852H/1815H/0H/0/0 > addr.prv
-- cat addr.prv | cardano-address key public --with-chain-code | cardano-address address payment --network-tag testnet
shelleyEnterprisePaymentAddrGolden :: BSL.ByteString
shelleyEnterprisePaymentAddrGolden = unsafeBech32Decode
    "addr_test1vpdylg53ekxh2404mfgw4pt4gfm7dc9dkc74ck0gtrld8uqewynck"

-- To define these generators, we rely on explicit generators (and implicit
-- Arbitrary instance generators) provided by
-- "Test.Shelley.Spec.Ledger.Serialisation.EraIndepGenerators". Do not try to
-- move the generators below to any of our "*.Gen" modules. Unfortunately
-- "EraIndepGenerators" exports Arbitrary instances that will conflict with the
-- Arbitrary instances we define in our Specs.

genShelleyAddr :: Gen (L.Addr CC.StandardCrypto)
genShelleyAddr =
    L.Addr <$> arbitrary <*> arbitrary <*> arbitrary

genShelleyScriptHashAddr :: Gen (L.Addr CC.StandardCrypto)
genShelleyScriptHashAddr =
    L.Addr <$> arbitrary
           <*> (L.ScriptHashObj . L.ScriptHash <$> L.genHash)
           <*> arbitrary

genShelleyKeyHashAddr :: Gen (L.Addr CC.StandardCrypto)
genShelleyKeyHashAddr =
    L.Addr <$> arbitrary
           <*> (L.KeyHashObj <$> arbitrary)
           <*> arbitrary

genByronAddr :: Gen (L.Addr CC.StandardCrypto)
genByronAddr =
    L.AddrBootstrap . L.BootstrapAddress <$> hedgehog Byron.genAddress

genStakeAddr :: Gen (L.RewardAcnt CC.StandardCrypto)
genStakeAddr = hedgehog L.genRewardAcnt

-- Some helper functions

asAddress :: L.Addr CC.StandardCrypto -> Address
asAddress = Address . L.serialiseAddr

asStakeAddress :: L.RewardAcnt crypto -> Address
asStakeAddress = Address . L.serialiseRewardAcnt

runGetMaybe :: B.Get a -> BSL.ByteString -> Maybe a
runGetMaybe parser x =
    either (const Nothing) (\(_, _, a) -> Just a) $ B.runGetOrFail parser x

asHex :: ByteString -> String
asHex = BS.foldr showHex ""
