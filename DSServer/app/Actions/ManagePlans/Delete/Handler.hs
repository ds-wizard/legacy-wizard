{-# LANGUAGE OverloadedStrings #-}

module Actions.ManagePlans.Delete.Handler (handler) where

import qualified Data.Text.Lazy as TL
import Web.Scotty (params, redirect)

import App (Action, PGPool, Cookies, runQuery)
import Auth (checkLogged)

import Persistence.Plan (deletePlan)

import Actions.Responses (errorResponse)
import Actions.ManagePlans.Url (url)

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLogged pool cookies (\_ -> do
    ps <- params
    case lookup "planId" ps of
      Nothing -> errorResponse "planId parametre missing -- probably a system error, please contact the administrator."
      Just planIdStr -> do
        let planId = read $ TL.unpack planIdStr :: Int
        _ <- runQuery pool $ deletePlan planId
        redirect $ TL.pack url
    )
