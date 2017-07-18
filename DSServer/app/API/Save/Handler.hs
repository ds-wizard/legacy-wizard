{-# LANGUAGE OverloadedStrings #-}

module API.Save.Handler (handler) where

import Web.Scotty (Param, params, text)

import App (Action, PGPool, Cookies, runQuery)
import Auth (checkLogged)

import Model.Plan
import Persistence.Plan (getPlanByUser)
import Persistence.Result (getResultId, insertResult, updateResult)

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLogged pool cookies (\user -> do
  mPlan <- runQuery pool $ getPlanByUser user
  case mPlan of
    Nothing -> text "No opened plan"
    Just plan -> do
      ps <- params
      mapM_ (storeValue plan) ps
      text "Data has been saved.")
  where
    storeValue :: Plan -> Param -> Action
    storeValue plan (key, value) = do
      resId <- runQuery pool $ getResultId plan key
      _ <- if resId == 0 then
        runQuery pool $ insertResult plan (key, Just value)
      else
        runQuery pool $ updateResult plan (key, Just value)
      return ()


