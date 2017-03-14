{-# LANGUAGE OverloadedStrings, DataKinds #-}

module API.Question.GetQuestion
  ( url
  , handler
  ) where

import Control.Monad (join)
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import Web.Spock (Path)
import qualified Web.Spock as W
import Web.Routing.Combinators (PathState(..))

import App (WizardAction)
import API.Utils (readInt)
import Persistence.Question (getQuestion)

url :: Path '[] 'Open
url = "api/getQuestion"

handler :: WizardAction ctx b a
handler = do
  ps <- W.params
  case join $ readInt <$> lookup "chid" ps of
    Nothing -> W.text "Missing chid"
    Just chid ->
      case join $ readInt <$> lookup "qid" ps of
        Nothing -> W.text "Missing qid"
        Just qid -> do
          maybeQuestion <- W.runQuery $ getQuestion chid qid
          W.text $ fromMaybe "" $ (T.pack . show) <$> maybeQuestion

