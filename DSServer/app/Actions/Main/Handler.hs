{-# LANGUAGE OverloadedStrings #-}

module Actions.Main.Handler (handler) where

import qualified Data.Text as T
import Text.Blaze.Internal (textValue)
import Text.Blaze.Html5 (Html, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

import App (Action, PGPool, Cookies, getSession, runQuery)
import Persistence.Session (getUserFromSession)
import qualified Page
import qualified Actions.Save.Url as Actions.Save

view :: Html
view = H.form ! A.id "form" ! A.method "post" ! A.action (textValue $ T.pack Actions.Save.url) $ mempty

handler :: PGPool -> Cookies -> Action
handler pool cookies =
  case getSession cookies of
    Nothing -> Page.render True view Nothing Page.NoMessage
    Just sessionId -> do
      mUser <- runQuery pool $ getUserFromSession sessionId
      Page.render True view mUser Page.NoMessage


