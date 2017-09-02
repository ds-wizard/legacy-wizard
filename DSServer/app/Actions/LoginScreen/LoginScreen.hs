{-# LANGUAGE OverloadedStrings #-}

module Actions.LoginScreen.LoginScreen where

import Data.Text (Text)
import qualified Data.Text as T
import Text.Blaze.Html5 (Html, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import qualified Text.Digestive as D
import qualified Text.Digestive.Blaze.Html5 as DH

import Actions.FormUtils (MyView, errorTr)
import qualified Actions.LoginScreen.Login.Url as Login
import qualified Actions.LoginScreen.RegistrationConfirmation.Url as RegistrationConfirmation
import qualified Actions.LoginScreen.ForgottenPassword.Url as ForgottenPassword

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

type LoginForm m = D.Form Html m LoginRequest

data LoginRequest = LoginRequest
  { lr_email :: Text
  , lr_password :: Text
  } deriving (Show)

formView :: MyView -> Html
formView v = do
  H.h2 "User Login"
  DH.form v "" $ do
    H.table ! A.class_ "form-table" $
      H.tbody $ do
        H.tr $ do
          H.td $ DH.label     "email" v "Email: "
          H.td $ DH.inputText "email" v
        errorTr "email" v
        H.tr $ do
          H.td $ DH.label         "password" v "Password: "
          H.td $ DH.inputPassword "password" v
        errorTr "password" v
        H.tr $ do
          H.td mempty
          H.td $ do
            H.button ! A.type_ "submit" ! A.formaction (H.textValue $ T.pack Login.url) $ "Login"
            H.button ! A.type_ "submit" ! A.style "margin-left: 10px;" ! A.formaction (H.textValue $ T.pack ForgottenPassword.url) $ "Forgotten password"
            H.button ! A.type_ "submit" ! A.style "margin-left: 10px;" ! A.formaction (H.textValue $ T.pack RegistrationConfirmation.url) $ "Resend the confirmation e-mail"



