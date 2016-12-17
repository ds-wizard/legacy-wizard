{-# LANGUAGE OverloadedStrings #-}

import System.IO
import System.Environment
import Data.Aeson (decode)
import Data.Maybe
import qualified Data.ByteString.Lazy as BS
import qualified Database.PostgreSQL.Simple as PG

import KModel
import KMTransform (transformQuestionnaire, distillQuestionnaire)
import qualified Config.Server.Config as Config

main :: IO ()
main = do
  args <- getArgs  
  handle <- openFile (head args) ReadMode
  contentsJSON <- BS.hGetContents handle
  let contents = decode contentsJSON :: Maybe [Chapter]
  case contents of
    Nothing -> putStrLn "Invalid JSON..."
    _ -> do
      pgConn <- PG.connect Config.pgCreds
      _ <- PG.execute_ pgConn "DELETE FROM \"Questions\""
      distillQuestionnaire pgConn (fromJust contents)
      print $ transformQuestionnaire (fromJust contents)
      PG.close pgConn
