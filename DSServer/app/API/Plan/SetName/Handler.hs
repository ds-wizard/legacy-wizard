{-# LANGUAGE OverloadedStrings #-}

module API.Plan.SetName.Handler (handler) where

import qualified Data.Text.Lazy as TL
import Web.Scotty (params, text)

import App (Action, PGPool, Cookies, runQuery)
import Auth (checkLogged)
import Persistence.Plan (setPlanName)

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLogged pool cookies (\_ -> do
  ps <- params
  case lookup "planId" ps of
    Nothing -> text "Plan name save failed: invalid planId"
    Just planId -> case lookup "newValue" ps of
      Nothing -> text "Plan name save failed: invalid newName"
      Just planName -> do
        _ <- runQuery pool $ setPlanName (read $ TL.unpack planId) planName
        text "Plan name saved"
  )
