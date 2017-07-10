{-# LANGUAGE OverloadedStrings #-}

module API.Plan.GetData.Handler (handler) where

import qualified Data.Text.Lazy as TL
import Web.Scotty (text)

import App (Action, PGPool, Cookies, runQuery)
import Auth (checkLogged)
import Persistence.Plan (getPlanByUser)
import Persistence.Result (getResultsForPlan)
import FormEngine.FormData (values2Data)

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLogged pool cookies (\user -> do
  mPlan <- runQuery pool $ getPlanByUser user
  case mPlan of
    Nothing -> text ""
    Just plan -> do
      formData <- runQuery pool $ getResultsForPlan plan
      text $ TL.pack $ show $ values2Data formData
  )
