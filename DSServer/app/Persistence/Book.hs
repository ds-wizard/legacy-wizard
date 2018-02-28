{-# LANGUAGE OverloadedStrings #-}

module Persistence.Book where

import           Data.Text (Text, unpack)
import qualified Database.PostgreSQL.Simple as PG

import Model.Book

getBookByShortUID :: Text -> PG.Connection -> IO (Maybe Book)
getBookByShortUID shortuid conn = do
  results <- PG.query conn
               "SELECT \
                \    id, \
                \    chapter, \
                \    contents, \
                \    shortuid \
                \FROM \"Book\" WHERE \
                \    shortuid = ?"
                (PG.Only shortuid)
  let r = results :: [Book]
  if null r
    then return Nothing
    else return $ Just $ head r
