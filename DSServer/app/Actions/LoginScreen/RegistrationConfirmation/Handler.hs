{-# LANGUAGE OverloadedStrings #-}

module Actions.LoginScreen.RegistrationConfirmation.Handler (handler) where

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
import qualified Page
import Actions.FormUtils (addError, emailFormlet)
import Actions.LoginScreen.LoginScreen (LoginForm, formView, LoginRequest(..))
import Actions.ConfirmRegistration.Url as ConfirmRegistration
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
          actionKeyKey <- runQuery pool $ AC.createActionKey user AC.ConfirmRegistration
          liftIO $ mailRegistrationConfirmation user ConfirmRegistration.url actionKeyKey
          infoResponse $ toHtml $ "Registration confirmation e-mail has been sent to " <> U.runEmail (U.u_email user) <> "."

