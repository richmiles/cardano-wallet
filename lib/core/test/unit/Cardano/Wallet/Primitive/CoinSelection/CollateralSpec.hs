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
import Cardano.Wallet.Primitive.Types.Address.Gen
    ( genAddressSmallRange, shrinkAddressSmallRange )
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
import Cardano.Wallet.Unsafe
    ( unsafeFromHex )
import Data.ByteString
    ( ByteString )
import Data.ByteString.Base58
    ( bitcoinAlphabet, decodeBase58 )
import Data.Maybe
    ( fromJust, isJust, isNothing )
import Test.Hspec
    ( Expectation, Spec, describe, it, shouldBe )
import Test.Hspec.Extra
    ( parallel )
import Test.QuickCheck
    ( Arbitrary (..)
    , Gen
    , Property
    , checkCoverage
    , counterexample
    , cover
    , coverTable
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

import qualified Cardano.Binary as Binary
import qualified Cardano.Ledger.Address as L
import qualified Cardano.Ledger.Credential as L
import qualified Cardano.Ledger.Crypto as CC
import qualified Cardano.Ledger.Hashes as L
import qualified Cardano.Wallet.Primitive.Types.TokenBundle as TokenBundle
import Control.Monad
    ( replicateM_ )
import qualified Data.Binary.Get as B
import qualified Data.Binary.Put as B
import Data.Bits
    ( (.&.) )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Lazy as BSL
import qualified Data.ByteString.Lazy.Char8 as BSLC8
import Data.Function
    ( (&) )
import Data.Int
    ( Int64 )
import Data.String
    ( fromString )
import Numeric
    ( showHex )
import qualified Test.Cardano.Chain.Common.Gen as Byron
import qualified Test.Shelley.Spec.Ledger.Serialisation.EraIndepGenerators as L

-- | In the realm of cardano-ledger-specs, we recognize the following types of
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
-- The funds associated with an address are considered suitable for use as
-- collateral iff the payment credential of that address is a "key hash".
--
-- So, there are a few properties we would like to assert:
--
-- 1. That our classification function always considers addresses with a keyhash
--    payment credential as suitable for collateral.
-- 2. That our classification function always considers addresses without a
--    keyhash payment credential as unsuitable for collateral.
-- 3. That future format addresses are always rejected.
--
-- That's it really. We also want to assert that our generators cover the full
-- range of possible address types, including future formats and unknown
-- formats.
--
-- Using real addresses for the generators is an important idea, as the domain
-- of the classification function is the set of all addresses (really all
-- ByteStrings, thanks to our loose representation of Addresses, but because
-- most of the set of all ByteStrings is not helpful to us, we will test the
-- classification function with only a small percentage of unstructured
-- ByteStrings). However, real addresses make for awful counterexamples, so
-- after generating an address, we try to determine what kind of address it is
-- by inspecting the first four bits: If it is an address format we recognize,
-- we shrink towards an address that has the same first four bits, but 0 bits
-- everywhere else. This forms a valid address that is easier on the eyes,
-- except in two cases: stake addresses and bootstrap addresses. We can offer no
-- shrinkage for those two kinds of addresses, but try to provide a good
-- explanation using `counterExample`. This is a helpful strategy because at
-- this current point in time collateral suitability can be determined simply by
-- inspecting the first four bits, so that is the most important piece of
-- information for debugging.

runGetMaybe :: B.Get a -> BSL.ByteString -> Maybe a
runGetMaybe parser x =
    either (const Nothing) (\(_, _, a) -> Just a) $ B.runGetOrFail parser x

x :: Property
x =
    withMaxSuccess 1000 $
    forAllShrink genAnyAddress shrinkAddress $ \addr@(Address addrBytes) -> do
        let addrType = runGetMaybe getHeader $ BSL.fromStrict addrBytes
        coverTable "Address types"
            [ ("Just (BaseAddress CredentialKeyHash CredentialKeyHash)"       , 1)
            , ("Just (BaseAddress CredentialKeyHash CredentialScriptHash)"    , 1)
            , ("Just (BaseAddress CredentialScriptHash CredentialKeyHash)"    , 1)
            , ("Just (BaseAddress CredentialScriptHash CredentialScriptHash)" , 1)
            , ("Just (PointerAddress CredentialKeyHash)"                      , 1)
            , ("Just (PointerAddress CredentialScriptHash)"                   , 1)
            , ("Just (EnterpriseAddress CredentialKeyHash)"                   , 1)
            , ("Just (EnterpriseAddress CredentialScriptHash)"                , 1)
            , ("Just (StakeAddress CredentialKeyHash)"                        , 1)
            , ("Just (StakeAddress CredentialScriptHash)"                     , 1)
            , ("Just BootstrapAddress"                                        , 1)
            ] $
            tabulate "Address types" [show addrType] $
                case addrType of
                    Nothing ->
                        classifyCollateralAddress addr
                            === Left IsAMalformedOrUnknownAddr
                    Just typ | hasScriptHashPayCred typ ->
                            === Left IsAScriptAddr
                    Just typ | hasKeyHashPayCred typ ->
                        classifyCollateralAddress addr
                            === Right addr
                    Just other ->
                        fail ""

shrinkAddress :: Address -> [Address]
shrinkAddress addr =
    case simplifiedAddress addr of
        Nothing ->
            -- There are some address types we can't meaningfully shrink.
            []
        Just simplified ->
            -- Otherwise we can shrink to the simplified address.
            [simplified]

simplifiedAddress :: Address -> Maybe Address
simplifiedAddress (Address addrBytes) = do
    -- Don't try to simplify malformed addresses
    _ <- L.deserialiseAddr addrBytes :: Maybe (L.Addr CC.StandardCrypto)

    bytes <- case B.runGetOrFail getHeader (BSL.fromStrict addrBytes) of
        Right (_, _, BootstrapAddress) ->
            Nothing
        Right (_, _, StakeAddress _) ->
            Nothing
        Right (_, _, addr@(BaseAddress _ _)) -> do
            Just $ B.runPut $ do
                putHeader addr
                -- payload for base addr is two 28-byte bytestrings
                putNullBytes 28
                putNullBytes 28
        Right (_, _, addr@(PointerAddress _)) ->
            Just $ B.runPut $ do
                putHeader addr
                -- payload for pointer addr is one 28-byte bytestring followed
                -- by three unsigned ints of variable size (in this case two 
                -- bytes each).
                putNullBytes 28
                putNullBytes 2
                putNullBytes 2
                putNullBytes 2
        Right (_, _, addr@(EnterpriseAddress _)) ->
            Just $ B.runPut $ do
                putHeader addr
                -- payload for enterprise addr is one 28-byte bytestring
                putNullBytes 28
        Left _ ->
            Nothing

    pure $ Address $ BSL.toStrict bytes

    where
        -- Put n bytes worth of null bytes
        putNullBytes :: Int -> B.Put
        putNullBytes n = replicateM_ n putNullByte

        -- Put a byte of unset bits
        putNullByte :: B.Put
        putNullByte = B.putWord8 0b00000000

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

prop_header_roundtrips :: Property
prop_header_roundtrips =
    forAll genAddressType $ \addrType ->
        B.runGet getHeader (B.runPut $ putHeader addrType) === addrType

-- | We want to assert that when we simplify an address:
--
--   - the simplified address is still a valid address
--   - the type of the simplified address matches the type of the original
--     address (address type is preserved)

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

spec :: Spec
spec = do
    parallel $ describe "collateral suitability" $ do
        describe "classifyCollateralAddress" $ do
          it "classifies Byron/bootstrap addresses correctly" $
              property prop_bootstrapAddresses
          it "classifies script addresses correctly" $
              property prop_scriptAddresses
          it "classifies key hash (VK input) addresses correctly" $
              property prop_keyHashAddresses
          it "classifies malformed addresses correctly" $
              property prop_malformedAddresses
          describe "golden" $ do
              it "classifies byron address" unit_byronGolden
              it "classifies good address" unit_shelleyPaymentGolden
              it "classifies script address" unit_scriptGolden
        describe "asCollateral" $ do
          it "is equivalent to the composition of classifyCollateralAddress and pureAdaValue" $
              property prop_equivalence

prop_bootstrapAddresses :: Property
prop_bootstrapAddresses =
    forAll genBootstrapAddress $ \addr ->
        classifyCollateralAddress addr === Left IsABootstrapAddr

prop_scriptAddresses :: Property
prop_scriptAddresses =
    forAll genScriptAddress $ \addr ->
        classifyCollateralAddress addr === Left IsAScriptAddr

prop_keyHashAddresses :: Property
prop_keyHashAddresses =
    forAll genKeyHashAddress $ \addr ->
        classifyCollateralAddress addr === Right addr

prop_malformedAddresses :: Property
prop_malformedAddresses =
    forAllShrink genAddressSmallRange shrinkAddressSmallRange $ \addr ->
        classifyCollateralAddress addr === Left IsAMalformedOrUnknownAddr

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

-- The following golden keys were generated from the recovery phrase:
-- [change twin tired knee syrup cover dog glare canvas canvas jump egg]

-- cardano-address key child 14H/42H
unit_byronGolden :: Expectation
unit_byronGolden =
    let
        byronAddr =
            Address . fromJust . decodeBase58 bitcoinAlphabet
            $ "37btjrVyb4KFsMoVwPRZ5aJko48uBFFUnJ46eV3vC3uBCC65mj5BfbGP6jYDfhojm8MAayHo4RPvWH4x852FcJq8SHazCx31FJM2TfDpV9Azrc8UKD"
    in
        classifyCollateralAddress byronAddr `shouldBe` Left IsABootstrapAddr

-- cardano-address key child 1852H/1815H/0H/0/0
unit_shelleyPaymentGolden :: Expectation
unit_shelleyPaymentGolden =
    let
        shelleyAddr =
            Address . BSL.toStrict . unsafeBech32Decode
            $ "addr_test1vpdylg53ekxh2404mfgw4pt4gfm7dc9dkc74ck0gtrld8uqewynck"
    in
        classifyCollateralAddress shelleyAddr `shouldBe` Right shelleyAddr

shelleyAddr = Address . BSL.toStrict . unsafeBech32Decode $ "addr_test1vpdylg53ekxh2404mfgw4pt4gfm7dc9dkc74ck0gtrld8uqewynck"

unit_scriptGolden :: Expectation
unit_scriptGolden =
    let
        scriptAddr =
            Address . BSL.toStrict . unsafeBech32Decode
            $ "addr_test1ypdylg53ekxh2404mfgw4pt4gfm7dc9dkc74ck0gtrld8u9wau4cw97kuzqhsk5phx3jdc0s8vcnzdpl0ek6sykkyxtsentrpt"
    in
        classifyCollateralAddress scriptAddr `shouldBe` Left IsAScriptAddr

-- To define these generators, we rely on explicit generators (and implicit
-- Arbitrary instance generators) provided by
-- "Test.Shelley.Spec.Ledger.Serialisation.EraIndepGenerators". Do not try to
-- move the generators below to any of our "*.Gen" modules. Unfortunately
-- "EraIndepGenerators" exports Arbitrary instances that will conflict with the
-- Arbitrary instances we define in our Specs.

genAnyAddress :: Gen Address
genAnyAddress =
    frequency [ (8, asAddress <$> genShelleyAddr)
              , (1, asAddress <$> genByronAddr)
              , (2, Address <$> arbitrary)
              ]
    where
        asAddress :: L.Addr CC.StandardCrypto -> Address
        asAddress = Address . L.serialiseAddr

        genShelleyAddr :: Gen (L.Addr CC.StandardCrypto)
        genShelleyAddr =
            L.Addr <$> arbitrary <*> arbitrary <*> arbitrary
    
        genByronAddr :: Gen (L.Addr CC.StandardCrypto)
        genByronAddr =
            L.AddrBootstrap . L.BootstrapAddress <$> hedgehog Byron.genAddress

genScriptAddress :: Gen Address
genScriptAddress = (Address . L.serialiseAddr) <$> genScriptAddr

genKeyHashAddress :: Gen Address
genKeyHashAddress = (Address . L.serialiseAddr) <$> genKeyHashAddr

genScriptAddr :: Gen (L.Addr CC.StandardCrypto)
genScriptAddr =
    L.Addr <$> arbitrary
           <*> (L.ScriptHashObj . L.ScriptHash <$> L.genHash)
           <*> arbitrary

genKeyHashAddr :: Gen (L.Addr CC.StandardCrypto)
genKeyHashAddr =
    L.Addr <$> arbitrary
           <*> (L.KeyHashObj <$> arbitrary)
           <*> arbitrary

genBootstrapAddress :: Gen Address
genBootstrapAddress = do
    addr <- hedgehog Byron.genAddress
    -- Do not use any encoding (e.g. Base58) when serializing, Address presumes
    -- no encoding.
    pure $ Address $ Binary.serialize' addr

-- generateKeyHashAddress' :: Gen Address
-- generateKeyHashAddress' =
--     oneof [ genBootstrapAddress -- Byron addresses always have a keyhash
--           , Address <$> (header $ BaseAddress CredentialKeyHash <$> arbitrary)

data Credential
    = CredentialKeyHash
    | CredentialScriptHash
    deriving (Eq, Show)

data AddressType
    = BaseAddress Credential Credential
    | PointerAddress Credential
    | EnterpriseAddress Credential
    | StakeAddress Credential
    | BootstrapAddress
    deriving (Eq, Show)

genAddressType :: Gen AddressType
genAddressType =
    oneof [ BaseAddress <$> genCredential <*> genCredential
          , PointerAddress <$> genCredential
          , EnterpriseAddress <$> genCredential
          , StakeAddress <$> genCredential
          , pure BootstrapAddress
          ]

genCredential :: Gen Credential
genCredential =
    oneof [ pure CredentialKeyHash
          , pure CredentialScriptHash
          ]
