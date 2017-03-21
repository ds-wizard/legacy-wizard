{-# LANGUAGE OverloadedStrings #-}

module Actions.Save.Handler
  ( url
  , handler
  ) where

import Web.Scotty (params)

import App (Action, PGPool, Cookies, runQuery)
import Auth (checkLogged)
import Actions.Responses (infoResponse, errorResponse)

import Model.Plan
import Persistence.Plan (getPlanByUser)
import Persistence.Result (getResultId, insertResult, updateResult)
import Questionnaire (formItems)
import FormEngine.FormData (FieldValue, getFieldInfos)

url :: String
url = "/save"

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLogged pool cookies (\user -> do
  ps <- params
  let fieldValues = map (getValue ps) (getFieldInfos formItems)
  mPlan <- runQuery pool $ getPlanByUser user
  case mPlan of
    Nothing -> errorResponse "Failed getting plan of a user. Please contact an administrator."
    Just plan -> do
      mapM_ (storeValue plan) fieldValues
      infoResponse "Data has been saved.")
  where
    getValue ps (name1, text1) = (name1, text1, lookup name1 ps)
    storeValue :: Plan -> FieldValue -> Action
    storeValue plan (name1, text1, value1) = do
      resId <- runQuery pool $ getResultId plan name1
      _ <- if resId == 0 then
        runQuery pool $ insertResult plan name1 text1 value1
      else
        runQuery pool $ updateResult plan name1 value1
      return ()

