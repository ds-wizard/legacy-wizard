{-# LANGUAGE OverloadedStrings #-}

module Actions.Save.Handler
  ( url
  , handler
  ) where

--import Web.Scotty (redirect)

import App (Action, PGPool, Cookies)
import Auth (checkLogged)
import Actions.Responses (infoResponse)

url :: String
url = "/save"

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLogged pool cookies $ (\_ -> infoResponse "Data has been saved.")

