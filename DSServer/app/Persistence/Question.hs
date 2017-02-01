{-# LANGUAGE OverloadedStrings #-}

module Persistence.Question where

import           Data.Text (Text, pack)
import           Data.Maybe (fromMaybe)
import           Control.Monad.Trans
import qualified Database.PostgreSQL.Simple as PG
import           Database.PostgreSQL.Simple.FromRow

import Model.Question

instance FromRow Question where
  fromRow = Question <$> field <*> field <*> field <*> field

getQuestion :: Int -> Int -> PG.Connection -> IO (Maybe Question)
getQuestion chid qid conn = do
  results <- PG.query conn
               "SELECT \
                \    chapterId, \
                \    questionId, \
                \    bookRef, \
                \    otherInfo \
                \FROM \"Questions\" WHERE \
                \    chapterId = ? AND questionID = ?"
               (chid, qid)
  let r = results :: [Question]
  if null r
    then return Nothing
    else return $ Just $ head r

getBookContents :: Int -> Int -> PG.Connection -> IO (Maybe Text)
getBookContents chid qid conn = do
  results <- PG.query conn
               "SELECT contents FROM \"Book\" WHERE \
                \    chapter = (SELECT bookRef from \"Questions\" WHERE \
                \        chapterId = ? AND questionID = ?)"
               (chid, qid)
  let r = results :: [PG.Only Text]
  if null r
    then return Nothing
    else return $ Just $ PG.fromOnly $ head r


