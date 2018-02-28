{-# LANGUAGE OverloadedStrings #-}

module Actions.ResourcePage.Handler (handler) where

import Data.Text (Text)
import qualified Data.Text.Lazy as TL
import Web.Scotty (param, params, redirect)

import qualified Model.Book as B
import qualified Persistence.Book as B
import Text.Blaze.Html5 (Html, (!))
import qualified Text.Blaze.Html5 as H

import App (Action, PGPool, runQuery)
import Actions.Responses (errorResponse)
import qualified Page

showResourcePage :: B.Book -> Html
showResourcePage book = H.preEscapedText . B.b_contents $ book


handler :: PGPool -> Action
handler pool = do
  shortuid <- param "shortuid"
  result <- runQuery pool $ B.getBookByShortUID shortuid
  case result of
    Nothing -> errorResponse "Resource not found!"
    Just book -> Page.render (showResourcePage book) Page.defaultPageConfig
