{-# LANGUAGE OverloadedStrings #-}

module Actions.Save.Handler
  ( url
  , handler
  ) where

import qualified Control.Monad as M
import Web.Scotty (Param, params)

import App (Action, PGPool, Cookies, runQuery)
import Auth (checkLogged)
import Actions.Responses (infoResponse, errorResponse)

import Model.Plan
import Persistence.Plan (getPlanByUser)
import Persistence.Result (getResultId, insertResult, updateResult)
import Questionnaire (formItems)
import FormEngine.FormData (FieldInfo, getFieldInfos, baseName)

url :: String
url = "/save"

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLogged pool cookies (\user -> do
  let fieldInfos = getFieldInfos formItems
  mPlan <- runQuery pool $ getPlanByUser user
  case mPlan of
    Nothing -> errorResponse "Failed getting plan of a user. Please contact an administrator."
    Just plan -> do
      ps <- params
      mapM_ (storeValue plan fieldInfos) ps
      infoResponse "Data has been saved.")
  where
    storeValue :: Plan -> [FieldInfo] -> Param -> Action
    storeValue plan fieldInfos (name, value) = do
      let mText = M.join $ lookup (baseName name) fieldInfos
      resId <- runQuery pool $ getResultId plan name
      _ <- if resId == 0 then
        runQuery pool $ insertResult plan name mText (Just value)
      else
        runQuery pool $ updateResult plan name (Just value)
      return ()
      --where


