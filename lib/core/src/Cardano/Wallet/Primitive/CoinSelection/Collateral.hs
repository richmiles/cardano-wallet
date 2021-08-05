{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- For a UTxO to be considered a suitable collateral input, it must:
--    - Be a pure ADA UTxO (no tokens)
--    - Require a verification key witness to be spent
--    - Have an output address that is not any of:
--      - a native script address
--      - a bootstrap address
--      - a plutus script address
--
-- UTxOs of this kind are sometimes referred to as "VK" inputs.

module Cardano.Wallet.Primitive.CoinSelection.Collateral
    ( classifyCollateralAddress
    , asCollateral
    , AddrNotSuitableForCollateral(..)
    ) where

import Prelude

import Cardano.Wallet.Primitive.Types.Address
    ( Address (..) )
import Cardano.Wallet.Primitive.Types.Coin
    ( Coin )
import Cardano.Wallet.Primitive.Types.Tx
    ( TxIn (..), TxOut (..) )

import qualified Cardano.Ledger.Address as L
import qualified Cardano.Ledger.Credential as L
import qualified Cardano.Ledger.Crypto as L
import qualified Cardano.Ledger.Keys as L
import qualified Cardano.Wallet.Primitive.Types.TokenBundle as TokenBundle

-- | If the given @(TxIn, TxOut)@ represents a UTxO that is suitable for use as
-- a collateral input, returns @Just@ along with the total ADA value of the
-- UTxO. Otherwise returns @Nothing@ if it is not a suitable collateral value.
--
-- For a UTxO to be considered a suitable collateral input, it must:
--    - Be a pure ADA UTxO (no tokens)
--    - Require a verification key witness to be spent
--    - Have an output address that is not any of:
--      - a native script address
--      - a bootstrap address
--      - a plutus script address
--
-- UTxOs of this kind are sometimes referred to as "VK" inputs.
asCollateral
    :: (TxIn, TxOut)
    -- ^ TxIn, TxOut representing the value of a UTxO
    -> Maybe Coin
    -- ^ The total ADA value of that UTxO if it is suitable for collateral,
    -- otherwise Nothing.
asCollateral (_txIn, txOut) = do
   coin <- TokenBundle.toCoin $ tokens txOut

   case classifyCollateralAddress (address txOut) of
     Left IsABootstrapAddr ->
         Nothing
     Left IsAScriptAddr ->
         Nothing
     Left IsAMalformedOrUnknownAddr ->
         Nothing
     Right _addr ->
         Just coin

-- | Reasons why an address might be considered unsuitable for a collateral
-- input.
data AddrNotSuitableForCollateral
    = IsABootstrapAddr
    -- ^ The address is a bootstrap address
    | IsAScriptAddr
    -- ^ The address is some form of script address
    | IsAMalformedOrUnknownAddr
    -- ^ The address could not be parsed
    deriving (Eq, Show)

-- | Analyze an address to determine if it's funds are suitable for use as a
-- collateral input.
--
-- This function returns an Either instead of a Maybe because I think it's
-- important these functions return why they failed. It is extremely useful for
-- debugging programs.
classifyCollateralAddress
    :: Address
    -> Either AddrNotSuitableForCollateral Address
classifyCollateralAddress addr =
    case L.deserialiseAddr addrBytes of
        -- If we couldn't deserialise the address, it's either a malformed
        -- address or an address the Ledger doesn't know about.
        Nothing ->
            Left IsAMalformedOrUnknownAddr

        -- This is a bootstrap address, therefore not a suitable collateral
        -- input.
        Just (L.AddrBootstrap _bootstrapAddr) ->
            Left IsABootstrapAddr

        -- Otherwise, we further analyze the address.
        Just (L.Addr _network payCred _stakeRef) ->
            case (payCred :: L.Credential 'L.Payment L.StandardCrypto) of
                -- Check if this is a script address.
                L.ScriptHashObj _scriptHash ->
                    -- This is a native script address or a Plutus script
                    -- address, therefore not a suitable collateral input.
                    Left IsAScriptAddr

                -- Otherwise, this is an address that corresponds with a
                -- suitable collateral input
                L.KeyHashObj (_keyHash :: L.KeyHash 'L.Payment L.StandardCrypto) ->
                    Right addr

    where
        addrBytes = unAddress addr
