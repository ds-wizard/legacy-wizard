{-# LANGUAGE OverloadedStrings, DataKinds #-}

module API.Book.GetContents
  ( url
  , handler
  ) where

import Control.Monad (join)
import Data.Maybe (fromMaybe)
import Web.Spock (Path)
import qualified Web.Spock as W
import Web.Routing.Combinators (PathState(..))

import App (WizardAction)
import API.Utils (readInt)
import Persistence.Question (getBookContents)

url :: Path '[] 'Open
url = "api/getBookContents"

handler :: WizardAction ctx b a
handler = do
  ps <- W.params
  case join $ readInt <$> lookup "chid" ps of
    Nothing -> W.text "Missing chid"
    Just chid ->
      case join $ readInt <$> lookup "qid" ps of
        Nothing -> W.text "Missing qid"
        Just qid -> do
          maybeText <- W.runQuery $ getBookContents chid qid
          W.text $ fromMaybe "" maybeText

