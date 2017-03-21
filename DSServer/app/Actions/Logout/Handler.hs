{-# LANGUAGE OverloadedStrings #-}

module Actions.Logout.Handler
  ( url
  , handler
  ) where

--import qualified Data.Text.Lazy as TL
import Web.Scotty (redirect)

import App (Action, PGPool, Cookies, deleteSession)

url :: String
url = "/logout"

handler :: PGPool -> Cookies -> Action
handler pool cookies = do
  deleteSession pool cookies
  redirect "/"

