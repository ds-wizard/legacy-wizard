{-# LANGUAGE OverloadedStrings #-}

module Views.Forms.Registration where

import qualified Data.Text as T
import Text.Blaze.Html5 (Html, toHtml, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import qualified Text.Digestive as D
import qualified Text.Digestive.Blaze.Html5 as DH

import Views.Forms.Common (emailFormlet, passwordFormlet)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

data RegistrationRequest = RegistrationRequest
  { rr_password :: T.Text
  , rr_passwordConfirm :: T.Text
  , rr_email :: T.Text
  , rr_name :: T.Text
  , rr_affiliation :: T.Text
  } deriving (Show)

registrationForm :: Monad m => D.Form H.Html m RegistrationRequest
registrationForm =
  RegistrationRequest <$> "email" D..: emailFormlet Nothing
                  <*> "password1" D..: passwordFormlet Nothing
                  <*> "password2" D..: passwordFormlet Nothing
                  <*> "name" D..: D.text Nothing
                  <*> "affiliation" D..: D.text Nothing

url :: T.Text
url = "/registration"

view :: D.View H.Html -> H.Html
view v = do
 -- errorList "mail" view
  H.h2 "New User Registration"
  DH.form v "/registrationSent" $ do
    H.table ! A.class_ "form-table" $
      H.tbody $ do
        H.tr $ do
          H.td $ DH.label     "email" v "Email: "
          H.td $ DH.inputText "email" v
        H.tr $ do
          H.td $ DH.label     "password1" v "Password: "
          H.td $ DH.inputPassword "password1" v
        H.tr $ do
          H.td $ DH.label     "password2" v "Repeat: "
          H.td $ DH.inputPassword "password2" v
        H.tr $ do
          H.td $ DH.label     "name" v "Name: "
          H.td $ DH.inputText "name" v
        H.tr $ do
          H.td $ DH.label     "affiliation" v "Affiliation: "
          H.td $ DH.inputText "affiliation" v
        H.tr $ do
          H.td mempty
          H.td $ H.button ! A.type_ "submit" $ "Register"
