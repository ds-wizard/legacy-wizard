{-# LANGUAGE OverloadedStrings #-}

module Actions.LoginScreen.Login.Handler (handler) where

import qualified Data.Text.Lazy as TL
import qualified Text.Digestive as D
import Web.Scotty (redirect)
import Text.Digestive.Scotty (runForm)

import App (Action, PGPool, runQuery)
import Auth (doLoginAction)
import qualified Model.User as U
import qualified Persistence.User as U
import qualified Page
import Actions.FormUtils (addError, emailFormlet, passwordFormlet)
import Actions.LoginScreen.LoginScreen (LoginForm, LoginRequest(..), formView)
import qualified Actions.Main.Url as Main

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

form :: Monad m => LoginForm m
form = LoginRequest <$> "email" D..: emailFormlet Nothing
                    <*> "password" D..: passwordFormlet Nothing

handler :: PGPool -> Action
handler pool = do
  f <- runForm "loginForm" form
  case f of
    (v, Nothing) -> Page.render (formView v) Page.defaultPageConfig
    (v, Just loginReq) -> do
      mUser <- runQuery pool $ U.getUserByEmail (U.Email $ TL.fromStrict $ lr_email loginReq)
      case mUser of
        Nothing -> do
          let v2 = addError v "email" "Email not registered"
          Page.render (formView v2) Page.defaultPageConfig
        Just user ->
          if not (U.u_registration_confirmed user) then do
            let v2 = addError v "email" "Email registration has not been confirmed."
            Page.render (formView v2) Page.defaultPageConfig
          else
            if not $ U.authUser (U.Password $ TL.fromStrict $ lr_password loginReq) user then do
              let v2 = addError v "password" "Incorrect password."
              Page.render (formView v2) Page.defaultPageConfig
            else
              doLoginAction pool user $ redirect $ TL.pack Main.url
