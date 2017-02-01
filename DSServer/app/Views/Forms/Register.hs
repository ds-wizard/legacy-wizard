{-# LANGUAGE OverloadedStrings #-}

module Views.Forms.Register where

import Views.Forms.Common

import qualified Data.Text as T
import qualified Text.Blaze.Html5 as H
import Text.Digestive
import Text.Digestive.Blaze.Html5

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

data RegisterRequest = RegisterRequest
  { rr_password :: T.Text
  , rr_passwordConfirm :: T.Text
  , rr_email :: T.Text
  , rr_name :: T.Text
  , rr_affiliation :: T.Text
  } deriving (Show)

registerForm :: Monad m => Form H.Html m RegisterRequest
registerForm =
  RegisterRequest <$> "email" .: emailFormlet Nothing
                  <*> "password1" .: passwordFormlet Nothing
                  <*> "password2" .: passwordFormlet Nothing
                  <*> "name" .: text Nothing
                  <*> "affiliation" .: text Nothing

registerView :: View H.Html -> H.Html
registerView view = do
 -- errorList "mail" view
  label     "email" view "Email: "
  inputText "email" view
  H.br

