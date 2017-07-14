{-# LANGUAGE OverloadedStrings #-}

module Actions.ForgottenPassword.Handler (handler) where

import Data.Monoid ((<>))
import Control.Monad.Trans (liftIO)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Text.Blaze.Html5 (Html, (!), toHtml)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Text.Digestive ((.:))
import qualified Text.Digestive as D
import qualified Text.Digestive.Blaze.Html5 as DH
import Text.Digestive.Scotty (runForm)

import App (Action, PGPool, runQuery)
import qualified Model.User as U
import qualified Persistence.User as U
import qualified Model.ActionKey as AC
import qualified Persistence.ActionKey as AC
import Actions.FormUtils (emailFormlet, addError, errorTr)
import Actions.Responses (infoResponse)
import Actions.ForgottenPassword.Url (url)
import qualified Actions.ResetPassword.Url as Actions.ResetPassword
import qualified Actions.Login.Url as Actions.Login
import qualified Page
import Mailing

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

data LoginRequest = LoginRequest
  { lr_email :: Text
  , lr_password :: Text
  } deriving (Show)

loginForm :: Monad m => D.Form Html m LoginRequest
loginForm =
  LoginRequest <$> "email" .: emailFormlet Nothing
                  <*> "password" .: D.text Nothing

formView :: D.View Html -> Html
formView v = do
 -- errorList "mail" view
  H.h2 "Forgotten Password"
  DH.form v (T.pack url) $ do
    H.table ! A.class_ "form-table" $
      H.tbody $ do
        H.tr $ do
          H.td $ DH.label     "email" v "Email: "
          H.td $ DH.inputText "email" v
        errorTr "email" v
        H.tr $ do
          H.td $ DH.label         "password" v "Password: "
          H.td $ do
            DH.inputPassword "password" v
            H.button ! A.type_ "submit" $ "Forgotten password"
            --H.a ! A.href (H.textValue $ T.pack Actions.ForgottenPassword.url) $ "Forgotten password"
        errorTr "password" v
        H.tr $ do
          H.td mempty
          H.td $ H.button ! A.type_ "submit" ! A.formaction (H.textValue $ T.pack Actions.Login.url) $ "Login"


handler :: PGPool -> Action
handler pool = do
  f <- runForm "loginForm" loginForm
  case f of
    (v, Nothing) -> Page.render False (formView v) Nothing Page.NoMessage
    (v, Just loginReq) -> do
      mUser <- runQuery pool $ U.getUserByEmail (U.Email $ TL.fromStrict $ lr_email loginReq)
      case mUser of
        Nothing -> do
          let v2 = addError v "email" "Email not registered."
          Page.render False (formView v2) Nothing Page.NoMessage
        Just user -> do
          if not (U.u_registration_confirmed user) then do
            let v2 = addError v "email" "Email registration has not been confirmed."
            Page.render False (formView v2) Nothing Page.NoMessage
          else do
            actionKeyKey <- runQuery pool $ AC.createActionKey user AC.ResetPassword
            liftIO $ mailResetPasswordLink user Actions.ResetPassword.url actionKeyKey
            infoResponse $ toHtml $ "The reset password link has been sent to " <> U.runEmail (U.u_email user) <> "."
