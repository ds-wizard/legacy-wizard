{-# LANGUAGE OverloadedStrings #-}
{-# ANN module "HLint: ignore Use camelCase" #-}

module Web.Forms.Register where

import Web.Forms.Common

import qualified Data.Text as T
import qualified Text.Blaze.Html
import Text.Digestive
import Text.Digestive.Bootstrap

data RegisterRequest = RegisterRequest
  { rr_username :: T.Text
  , rr_password :: T.Text
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
  H.label "email" view "Email: "
  H.inputText "email" view
  H.br
  H.label "name" view "Name: "
  H.inputText "name" view
  H.br
