{-# LANGUAGE OverloadedStrings #-}

module Actions.Save.Handler (handler) where

import Web.Scotty (Param, params)

import App (Action, PGPool, Cookies, runQuery)
import Auth (checkLogged)
import Actions.Responses (infoResponse, errorResponse)

import Model.Plan
import Persistence.Plan (getPlanByUser)
import Persistence.Result (getResultId, insertResult, updateResult)

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLogged pool cookies (\user -> do
  mPlan <- runQuery pool $ getPlanByUser user
  case mPlan of
    Nothing -> errorResponse "Failed getting plan of a user. Please contact an administrator."
    Just plan -> do
      ps <- params
      mapM_ (storeValue plan) ps
      infoResponse "Data has been saved.")
  where
    storeValue :: Plan -> Param -> Action
    storeValue plan (key, value) = do
      resId <- runQuery pool $ getResultId plan key
      _ <- if resId == 0 then
        runQuery pool $ insertResult plan (key, Just value)
      else
        runQuery pool $ updateResult plan (key, Just value)
      return ()
      --where


