{-# LANGUAGE OverloadedStrings #-}

module Actions.Main.Handler
  ( url
  , handler
  ) where

--import qualified Data.Text.Lazy as TL
import Text.Blaze.Html5 (Html, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

import App (Action, PGPool, Cookies, getSession, runQuery)
import Persistence.Session (getUserFromSession)
import qualified Page

url :: String
url = "/"

view :: Html
view = H.form ! A.id "form" ! A.method "post" $ mempty

handler :: PGPool -> Cookies -> Action
handler pool cookies =
  case getSession cookies of
    Nothing -> Page.render True view Nothing Page.NoMessage
    Just sessionId -> do
      mUser <- runQuery pool $ getUserFromSession sessionId
      Page.render True view mUser Page.NoMessage

