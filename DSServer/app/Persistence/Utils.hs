{-# LANGUAGE OverloadedStrings #-}

module Persistence.Utils where

import qualified Data.Text as T
import System.Random (randomRs, getStdGen)

genKey :: IO T.Text
genKey = do
  stdGen <- getStdGen
  return $ T.pack $ take 10 $ randomRs ('a','z') stdGen

