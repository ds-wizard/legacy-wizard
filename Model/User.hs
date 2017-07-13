{-# LANGUAGE OverloadedStrings #-}

module Model.User where

import qualified Data.Text.Lazy as T
import qualified Data.ByteString as BS
import Database.PostgreSQL.Simple.FromRow
import Database.PostgreSQL.Simple.FromField (FromField (fromField))
import Database.PostgreSQL.Simple.ToField (ToField (toField))

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

type UserId = Int
newtype Email = Email T.Text deriving (Show, Eq)
newtype Password = Password T.Text deriving (Show, Eq)
newtype PasswordHash = PasswordHash BS.ByteString deriving (Show, Eq)

runEmail :: Email -> T.Text
runEmail (Email email) = email

data User = User
  { u_user_id :: UserId
  , u_email :: Email
  , u_password_hash :: PasswordHash
  , u_name :: T.Text
  , u_affiliation :: T.Text
  , u_registration_confirmed :: Bool
  } deriving (Show, Eq)

instance FromField Email where
  fromField f mdata = Email <$> fromField f mdata

instance ToField Email where
  toField (Email e) = toField e

instance FromField PasswordHash where
  fromField f mdata = PasswordHash <$> fromField f mdata

instance ToField PasswordHash where
  toField (PasswordHash ph) = toField ph

instance FromRow User where
  fromRow = User <$> field <*> field <*> field <*> field <*> field <*> field


