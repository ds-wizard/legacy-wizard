{-# LANGUAGE OverloadedStrings #-}

module Persistence.User
  ( createUser
  , getUserById
  , getUserByEmail
  , confirmRegistration
  , authUser
  ) where

import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Encoding as T
import Crypto.PasswordStore (makePassword, verifyPassword)
import qualified Database.PostgreSQL.Simple as PG
import Database.PostgreSQL.Simple.FromRow
import Database.PostgreSQL.Simple.FromField (FromField (fromField))
import Database.PostgreSQL.Simple.ToField (ToField (toField))

import Model.User
import Persistence.Utils (genKey)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}

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

createUser :: Email -> Password -> T.Text -> T.Text -> PG.Connection -> IO Int
createUser (Email email) (Password password) name affiliation conn = do
  passwordHash <- makePassword (T.encodeUtf8 $ TL.toStrict password) 18
  registrationKey <- genKey
  r <- PG.query conn "INSERT INTO \"User\" (email, password_hash, name, affiliation, registration_key) VALUES (?, ?, ?, ?, ?) RETURNING user_id"
         (email, passwordHash, name, affiliation, registrationKey) :: IO [PG.Only Int]
  let x =
        case r of
          (f:_) -> f
          []    -> PG.Only 0
  let (PG.Only i) = x
  return i

getUserById :: Int -> PG.Connection -> IO (Maybe User)
getUserById userId conn = do
  results <- PG.query conn "SELECT * FROM \"User\" WHERE user_id = ?" (PG.Only userId)
  let r = results :: [User]
  if null r
    then return Nothing
    else do
      let user = head r
      return $ Just user

getUserByEmail :: Email -> PG.Connection -> IO (Maybe User)
getUserByEmail (Email email) conn = do
  results <- PG.query conn "SELECT * FROM \"User\" WHERE email = ?" (PG.Only email)
  let r = results :: [User]
  if null r
    then return Nothing
    else do
      let user = head r
      return $ Just user

confirmRegistration :: T.Text -> PG.Connection -> IO Bool
confirmRegistration key conn = do
  r <- PG.query conn "UPDATE \"User\" SET registration_key = NULL WHERE registration_key = ? RETURNING user_id" (PG.Only key) :: IO [PG.Only Int]
  let x =
        case r of
          (f:_) -> f
          []    -> PG.Only 0
  let (PG.Only i) = x
  return $ i == 1

authUser :: Password -> User -> Bool
authUser (Password password) user = let PasswordHash ph = u_password_hash user in
  verifyPassword (T.encodeUtf8 $ TL.toStrict password) ph
