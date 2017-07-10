{-# LANGUAGE OverloadedStrings #-}

module Actions.Logout.Handler (handler) where

import qualified Data.Text.Lazy as TL
import Web.Scotty (redirect)

import App (Action, PGPool, Cookies, deleteSession)

import qualified Actions.Main.Url as Actions.Main

handler :: PGPool -> Cookies -> Action
handler pool cookies = do
  deleteSession pool cookies
  redirect $ TL.pack Actions.Main.url

