{-# LANGUAGE OverloadedStrings #-}

module API.Plan.GetData.Handler
  ( url
  , handler
  ) where

import qualified Data.Text.Lazy as TL
import Control.Monad (join)
import Data.Maybe (fromMaybe)
import Web.Scotty (params, text)

import App (Action, PGPool, runQuery)
import API.Utils (readInt)
import Persistence.Question (getQuestion)

url :: String
url = "api/plan/getData"

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLoggedAPI pool cookies (\user -> do
  let maybeRespondentKey = lookup respondentKeyFieldName ps
  case maybeRespondentKey of
    Nothing -> W.text ""
    Just respondentKey -> do
      formData <- runQuery $ getResultsForRespondent respondentKey
      W.text $ toStrict $ pack $ show $ values2Data formData


