{-# LANGUAGE OverloadedStrings #-}

module Views.Forms.Login where

import qualified Data.Text as T
import Text.Blaze.Html5 (Html, toHtml, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import qualified Text.Digestive as D
import qualified Text.Digestive.Blaze.Html5 as DH

import Views.Forms.Common (emailFormlet, passwordFormlet)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

data LoginRequest = LoginRequest
  { lr_password :: T.Text
  , lr_passwordConfirm :: T.Text
  } deriving (Show)

registerForm :: Monad m => D.Form H.Html m LoginRequest
registerForm =
  LoginRequest <$> "email" D..: emailFormlet Nothing
                  <*> "password" D..: passwordFormlet Nothing

url :: T.Text
url = "/login"

view :: D.View H.Html -> H.Html
view v = do
 -- errorList "mail" view
  H.h2 "User Login"
  DH.form v "/loginSent" $ do
    H.table ! A.class_ "form-table" $
      H.tbody $ do
        H.tr $ do
          H.td $ DH.label     "email" v "Email: "
          H.td $ DH.inputText "email" v
        H.tr $ do
          H.td $ DH.label     "password1" v "Password: "
          H.td $ DH.inputPassword "password1" v
        H.tr $ do
          H.td mempty
          H.td $ H.button ! A.type_ "submit" $ "Login"
