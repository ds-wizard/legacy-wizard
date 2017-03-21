{-# LANGUAGE OverloadedStrings #-}

module API.Question.GetQuestion.Handler
  ( url
  , handler
  ) where

import qualified Data.Text.Lazy as TL
import Control.Monad (join)
import Data.Maybe (fromMaybe)
import Web.Scotty (ActionM, params, text)

import App (PGPool, runQuery)
import API.Utils (readInt)
import Persistence.Question (getQuestion)

url :: String
url = "api/getQuestion"

handler :: PGPool -> ActionM ()
handler pool = do
  ps <- params
  case join $ (readInt . TL.toStrict) <$> lookup "chid" ps of
    Nothing -> text "Missing chid"
    Just chid ->
      case join $ (readInt . TL.toStrict) <$> lookup "qid" ps of
        Nothing -> text "Missing qid"
        Just qid -> do
          maybeQuestion <- runQuery pool $ getQuestion chid qid
          text $ fromMaybe "" $ (TL.pack . show) <$> maybeQuestion

