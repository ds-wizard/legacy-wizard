{-# LANGUAGE OverloadedStrings #-}

module Views.Logout
  ( url
  , handler
  ) where

--import qualified Data.Text.Lazy as TL
import Web.Scotty (ActionM, redirect)

import App (PGPool, Cookies, deleteSession)

url :: String
url = "/logout"

handler :: PGPool -> Cookies -> ActionM ()
handler pool cookies = do
  deleteSession pool cookies
  redirect "/"

