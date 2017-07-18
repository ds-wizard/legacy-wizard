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
import Persistence.User (getOpenPlan)
import qualified API.Save.Url as API.Save

view :: Html
view = H.form ! A.id "form" ! A.method "post" ! A.action (textValue $ T.pack API.Save.url) $ mempty

handler :: PGPool -> Cookies -> Action
handler pool cookies =
  case getSession cookies of
    Nothing -> Page.render view $ Page.defaultPageConfig { Page.pc_isMain = True }
    Just sessionId -> do
      mUser <- runQuery pool $ getUserFromSession sessionId
      case mUser of
        Nothing -> Page.render view $ Page.defaultPageConfig { Page.pc_isMain = True, Page.pc_mUser = Nothing }
        Just user -> do
          mPlan <- runQuery pool $ getOpenPlan user
          Page.render view $ Page.defaultPageConfig { Page.pc_isMain = True, Page.pc_mUser = mUser, Page.pc_mPlan = mPlan }


