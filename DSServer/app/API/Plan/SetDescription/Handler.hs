{-# LANGUAGE OverloadedStrings #-}

module API.Plan.SetDescription.Handler (handler) where

import qualified Data.Text.Lazy as TL
import Web.Scotty (params, text)

import App (Action, PGPool, Cookies, runQuery)
import Auth (checkLogged)
import Persistence.Plan (setPlanDescription)

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLogged pool cookies (\_ -> do
  ps <- params
  case lookup "planId" ps of
    Nothing -> text "Plan description save failed: invalid planId"
    Just planId -> case lookup "newValue" ps of
      Nothing -> text "Plan description save failed: invalid newName"
      Just planDescription -> do
        _ <- runQuery pool $ setPlanDescription (read $ TL.unpack planId) planDescription
        text "Plan description saved"
  )
