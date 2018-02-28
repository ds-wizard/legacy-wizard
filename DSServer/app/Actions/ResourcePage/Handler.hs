{-# LANGUAGE OverloadedStrings #-}

module Actions.ResourcePage.Handler (handler) where

import qualified Data.Text.Lazy as TL
import Web.Scotty (param, params, redirect)

import qualified Persistence.User as U
import qualified Model.ActionKey as AC
import qualified Persistence.ActionKey as AC
import Text.Blaze.Html5 (Html, (!))
import qualified Text.Blaze.Html5 as H

import App (Action, PGPool, runQuery)
import qualified Page

showResourcePage :: String -> Html
showResourcePage x = do
  H.h2 "Resource page"
  H.p (H.string x)


handler :: PGPool -> Action
handler pool = do
  shortuid <- param "shortuid"
  Page.render (showResourcePage shortuid) Page.defaultPageConfig
