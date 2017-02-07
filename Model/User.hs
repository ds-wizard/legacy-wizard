{-# LANGUAGE OverloadedStrings #-}

module Model.User where

import qualified Data.Text as T
import qualified Data.ByteString as BS

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

type UserId = Int
newtype Email = Email T.Text
newtype Password = Password T.Text
newtype PasswordHash = PasswordHash BS.ByteString

data User = User
  { u_user_id :: UserId
  , u_email :: Email
  , u_password_hash :: PasswordHash
  , u_name :: T.Text
  , u_affiliation :: T.Text
  }

