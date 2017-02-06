{-# LANGUAGE OverloadedStrings #-}

module Views.Forms.Registration where

import qualified Data.Text as T
import Text.Blaze.Html5 (Html, toHtml, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Text.Digestive ((.:))
import qualified Text.Digestive as D
import qualified Text.Digestive.Blaze.Html5 as DH

import Views.Forms.Common (notEmpty, emailFormlet, passwordFormlet, errorTr)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

data RegistrationRequest = RegistrationRequest
  { rr_email :: T.Text
  , rr_password :: T.Text
  ---, rr_password2 :: T.Text
  , rr_name :: T.Text
  , rr_affiliation :: T.Text
  } deriving (Show)

registrationForm :: Monad m => D.Form H.Html m RegistrationRequest
registrationForm =
  RegistrationRequest <$> "email" .: emailFormlet Nothing
  --                <*> "password1" .: passwordFormlet Nothing
  --                <*> "password2" .: passwordFormlet Nothing
                  <*> "password" .: passwordConfirmer
                  <*> "name" .: D.validate notEmpty (D.text Nothing)
                  <*> "affiliation" .: D.validate notEmpty (D.text Nothing)
    where
    passwordConfirmer =
      D.validate fst' $ (,) <$> ("p1" .: passwordFormlet Nothing)
                          <*> ("p2" .: passwordFormlet Nothing)
    fst' (p1, p2) | p1 == p2  = D.Success p1
                  | otherwise = D.Error "Passwords do not match"

url :: T.Text
url = "/registration"

view :: D.View H.Html -> H.Html
view v = do
  H.h2 "New User Registration"
  DH.form v url $ do
    H.table ! A.class_ "form-table" $
      H.tbody $ do
        H.tr $ do
          H.td $ DH.label     "email" v "Email: "
          H.td $ DH.inputText "email" v
        errorTr "email" v
        H.tr $ do
          H.td $ DH.label     "password.p1" v "Password: "
          H.td $ DH.inputPassword "password.p1" v
        errorTr "password.p1" v
        H.tr $ do
          H.td $ DH.label     "password.p2" v "Repeat: "
          H.td $ DH.inputPassword "password.p2" v
        errorTr "password.p2" v
        errorTr "password" v
        H.tr $ do
          H.td $ DH.label     "name" v "Name: "
          H.td $ DH.inputText "name" v
        errorTr "name" v
        H.tr $ do
          H.td $ DH.label     "affiliation" v "Affiliation: "
          H.td $ DH.inputText "affiliation" v
        errorTr "affiliation" v
        H.tr $ do
          H.td mempty
          H.td $ H.button ! A.type_ "submit" $ "Register"
