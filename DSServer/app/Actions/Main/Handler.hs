{-# LANGUAGE OverloadedStrings #-}

module Actions.Main.Handler (handler) where

import qualified Data.Text as T
import Text.Blaze.Internal (textValue)
import Text.Blaze.Html5 (Html, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

import App (Action, PGPool, Cookies, getSession, runQuery)
import Persistence.Session (getUserFromSession)
import Persistence.Plan (getPlanByUser)
import Page (render, PageConfig(..), defaultPageConfig)
import qualified Actions.Save.Url as Actions.Save

view :: Html
view = H.form ! A.id "form" ! A.method "post" ! A.action (textValue $ T.pack Actions.Save.url) $ mempty

handler :: PGPool -> Cookies -> Action
handler pool cookies = let config = defaultPageConfig { pc_isMain = True } in
  case getSession cookies of
    Nothing -> render view config
    Just sessionId -> do
      mUser <- runQuery pool $ getUserFromSession sessionId
      mPlan <- case mUser of
        Nothing -> return Nothing
        Just user -> runQuery pool $ getPlanByUser user
      render view $ config { pc_mUser = mUser, pc_mPlan = mPlan }


