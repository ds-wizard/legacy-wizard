{-# LANGUAGE OverloadedStrings #-}

module Actions.LoginScreen.ForgottenPassword.Handler (handler) where

import qualified Data.Text.Lazy as TL
import Data.Monoid ((<>))
import Control.Monad.Trans (liftIO)
import Text.Blaze.Html5 (toHtml)
import qualified Text.Digestive as D
import Text.Digestive.Scotty (runForm)

import App (Action, PGPool, runQuery)
import qualified Model.User as U
import qualified Persistence.User as U
import qualified Model.ActionKey as AC
import qualified Persistence.ActionKey as AC
import Mailing
import Actions.FormUtils (addError, emailFormlet)
import qualified Page
import qualified Actions.ResetPassword.Url as ResetPassword
import Actions.LoginScreen.LoginScreen (LoginForm, formView, LoginRequest(..))
import Actions.Responses (infoResponse)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

form :: Monad m => LoginForm m
form = LoginRequest <$> "email" D..: emailFormlet Nothing
                    <*> "password" D..: D.text Nothing

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
        Just user -> do
          if not (U.u_registration_confirmed user) then do
            let v2 = addError v "email" "Email registration has not been confirmed."
            Page.render (formView v2) Page.defaultPageConfig
          else do
            actionKeyKey <- runQuery pool $ AC.createActionKey user AC.ResetPassword
            liftIO $ mailResetPasswordLink user ResetPassword.url actionKeyKey
            infoResponse $ toHtml $ "The reset password link has been sent to " <> U.runEmail (U.u_email user) <> "."
