{-# OPTIONS_GHC -fno-warn-orphans #-}
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
    , pureAdaValue
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
import Data.ByteString.Base58
    ( bitcoinAlphabet, decodeBase58 )
import Data.Maybe
    ( fromJust )
import Test.Hspec
    ( Spec, describe, it )
import Test.Hspec.Extra
    ( parallel )
import Test.QuickCheck
    ( Arbitrary (..)
    , Gen
    , Property
    , checkCoverage
    , cover
    , forAll
    , forAllShrink
    , oneof
    , property
    , scale
    , vector
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
import qualified Data.ByteString.Char8 as B8
import qualified Test.Cardano.Chain.Common.Gen as Byron
import qualified Test.Shelley.Spec.Ledger.Serialisation.EraIndepGenerators as L

spec :: Spec
spec = do
    parallel $ describe "collateral suitability" $ do
        describe "pureAdaValue" $ do
            it "only returns when token bundle has only ADA" $
                property prop_pureAdaValue
        describe "classifyCollateralAddress" $ do
          it "classifies Byron/bootstrap addresses correctly" $
              property prop_bootstrapAddresses
          it "classifies script addresses correctly" $
              property prop_scriptAddresses
          it "classifies key hash (VK input) addresses correctly" $
              property prop_keyHashAddresses
          it "classifies malformed addresses correctly" $
              property prop_malformedAddresses
        describe "asCollateral" $ do
          it "is equivalent to the composition of classifyCollateralAddress and pureAdaValue" $
              property prop_equivalence

test =
    let
        byronAddr =
            Address . fromJust . decodeBase58 bitcoinAlphabet $ "37btjrVyb4KFsMoVwPRZ5aJko48uBFFUnJ46eV3vC3uBCC65mj5BfbGP6jYDfhojm8MAayHo4RPvWH4x852FcJq8SHazCx31FJM2TfDpV9Azrc8UKD"
    in
        classifyCollateralAddress byronAddr === Left IsABootstrapAddr

prop_pureAdaValue :: TokenBundle -> Property
prop_pureAdaValue bundle =
    let
        result = pureAdaValue bundle
    in
        checkCoverage $
        cover 30 (not (TokenBundle.isCoin bundle))
            "Token bundle has at least 1 non-ada asset" $
        cover 30 (TokenBundle.isCoin bundle)
            "Token bundle has no non-ada assets" $
        if TokenBundle.isCoin bundle
        then result === Just (TokenBundle.coin bundle)
        else result === Nothing

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
     >> pureAdaValue toks)

instance Arbitrary TokenBundle where
    arbitrary = genTokenBundleSmallRangePositive
    shrink = shrinkTokenBundleSmallRangePositive

instance Arbitrary TxIn where
    arbitrary = TxIn
        <$> (Hash . B8.pack <$> vector 32)
        <*> scale (`mod` 3) arbitrary

instance Arbitrary TxOut where
    arbitrary = TxOut <$> genAnyAddress <*> arbitrary

-- To define these generators, we rely on explicit generators (and implicit
-- Arbitrary instance generators) provided by
-- "Test.Shelley.Spec.Ledger.Serialisation.EraIndepGenerators". Do not try to
-- move the generators below to any of our "*.Gen" modules. Unfortunately
-- "EraIndepGenerators" exports Arbitrary instances that will conflict with the
-- Arbitrary instances we define in our Specs.

genAnyAddress :: Gen Address
genAnyAddress =
    oneof [ genBootstrapAddress
          , genScriptAddress
          , genKeyHashAddress
          , genAddressSmallRange -- Essentially, malformed addresses
          , Address . L.serialiseAddr
            <$> (L.genByronAddress :: Gen (L.Addr CC.StandardCrypto))
          , Address . L.serialiseAddr
            <$> (L.genShelleyAddress :: Gen (L.Addr CC.StandardCrypto))
          ]

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
