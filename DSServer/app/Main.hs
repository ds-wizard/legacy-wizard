{-# LANGUAGE OverloadedStrings #-}

module Main where

import Web.Scotty (scotty)
import qualified Database.PostgreSQL.Simple as PG
import Data.Pool (createPool, destroyAllResources)

import Config.Server.Config (port, pgCreds)
import Routes (routes)

main :: IO ()
main = do
  pool <- createPool (PG.connect pgCreds) PG.close 1 300 5
  scotty port (routes pool)
  destroyAllResources pool

