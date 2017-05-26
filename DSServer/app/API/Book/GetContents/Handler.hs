{-# LANGUAGE OverloadedStrings #-}

module API.Book.GetContents.Handler
  ( url
  , handler
  ) where

import Data.Text.Lazy (toStrict)
import Control.Monad (join)
import qualified Data.Text.Lazy as TL
import Data.Maybe (fromMaybe)
import Web.Scotty (params, text)
--import qualified Database.PostgreSQL.Simple as PG

import App (Action, PGPool, runQuery)
import API.Utils (readInt)
import Persistence.Question (getBookContents)

url :: String
url = "/api/getBookContents"

handler :: PGPool -> Action
handler pool = do
  ps <- params
  case join $ readInt . toStrict <$> lookup "chid" ps of
    Nothing -> text "Missing chid"
    Just chid ->
      case join $ readInt . toStrict <$> lookup "qid" ps of
        Nothing -> text "Missing qid"
        Just qid -> do
          maybeText <- runQuery pool $ getBookContents chid qid
          --maybeText <- liftIO $ withResource pool $ getBookContents chid qid
          text $ TL.fromStrict $ fromMaybe "" maybeText

