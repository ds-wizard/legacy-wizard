{-# LANGUAGE OverloadedStrings #-}

module Actions.ManagePlans.Add.Handler (handler) where

import qualified Data.Text.Lazy as TL
import Web.Scotty (redirect)

import App (Action, PGPool, runQuery, Cookies)
import Auth (checkLogged)

import Persistence.Plan (addPlan)

import Actions.ManagePlans.Url (url)

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLogged pool cookies (\user -> do
    _ <- runQuery pool $ addPlan user "New plan" Nothing
    redirect $ TL.pack url
    )
