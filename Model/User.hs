{-# LANGUAGE OverloadedStrings #-}
{-# ANN module "HLint: ignore Use camelCase" #-}

module Model.User where

type UserId = Int
newtype Email = Email T.Text
newtype Password = Password T.Text
type PasswordSalt = PasswordSalt BS.ByteString
newtype PasswordHash = PasswordHash BS.ByteString

data User = User
  { u_user_id :: UserId
  , u_email :: Email
  , u_password_hash :: PasswordHash
  , u_salt :: PasswordSalt
  , u_name :: T.Text
  , u_affiliation :: T.Text
  } deriving (Show)

