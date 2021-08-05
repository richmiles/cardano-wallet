{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Small module for writing text-based golden tests.
--
-- In contrast to `hspec-golden-aeson` this module works with manually provided
-- values instead of QuickCheck, and with text instead of JSON.
module Test.Hspec.Goldens
    ( Settings (..)
    , textGolden
    )
    where

import Prelude

import Control.Exception
    ( try )
import Data.Maybe
    ( isJust )
import Data.Text
    ( Text )
import System.Environment
    ( lookupEnv )
import System.FilePath
    ( (</>) )
import Test.Hspec

import qualified Data.Text.IO as TIO

newtype Settings = Settings
    { goldenDirectory :: FilePath
    }

textGolden
    :: Settings
    -> String -- ^ Filename for the test
    -> Text  -- ^ Value to compare with the golden file
    -> Expectation
textGolden settings title value = do
    let f = goldenDirectory settings </> title
    overwrite <- isJust <$> lookupEnv "OVERWRITE_GOLDENS"
    readGolden f >>= \case
        Right expected | not overwrite -> value `shouldBe` expected
                       | otherwise     -> writeGoldenAndFail f value "Overwriting goldens"
        Left _ -> do
            writeGoldenAndFail f value "No existing golden file found"

  where
    readGolden :: FilePath -> IO (Either IOError Text)
    readGolden f = try (TIO.readFile f)

    -- NOTE: Not the most elegant error handling, but using e.g. ExceptT seemed
    -- to get unnecessarily complicated and not interplay with the IO `shouldBe`
    -- expectation.
    writeGoldenAndFail
        :: FilePath
        -> Text
        -> String -- ^ Error message prefix on failure
        -> IO ()
    writeGoldenAndFail f v errMsg = do
        try @IOError (TIO.writeFile f v) >>= \case
            Right () -> expectationFailure $ mconcat
                [ errMsg
                , "... "
                , "Now written to disk. Please check for correctness and "
                , "commit."
                ]
            Left writeError -> expectationFailure $ mconcat
                [ errMsg
                , "... "
                , "Unable to write the new value to disk because of:\n"
                , show writeError
                ]
