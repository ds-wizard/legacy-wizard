{-# LANGUAGE OverloadedStrings #-}

module Persistence.User
  ( UserResult(..)
  , createUser
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

import Model.User
import Persistence.Utils (genKey)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}

data UserResult = UserOK | InvalidRegistrationKey | UserAlreadyConfirmed

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
  r <- PG.query conn "SELECT * FROM \"User\" WHERE user_id = ?" (PG.Only userId) :: IO [User]
  if null r
    then return Nothing
    else do
      let user = head r
      return $ Just user

getUserByEmail :: Email -> PG.Connection -> IO (Maybe User)
getUserByEmail (Email email) conn = do
  r <- PG.query conn "SELECT * FROM \"User\" WHERE email = ?" (PG.Only email) :: IO [User]
  if null r
    then return Nothing
    else do
      let user = head r
      return $ Just user

confirmRegistration :: T.Text -> PG.Connection -> IO UserResult
confirmRegistration key conn = do
  users <- PG.query conn "SELECT * FROM \"User\" WHERE registration_key = ?" (PG.Only key) :: IO [User]
  if null users
    then return InvalidRegistrationKey
    else do
      let user = head users
      if u_registration_confirmed user then return UserAlreadyConfirmed
      else do
        _ <- PG.execute conn "UPDATE \"User\" SET registration_confirmed = 't' WHERE user_id = ?" (PG.Only $ u_user_id user)
        return UserOK

authUser :: Password -> User -> Bool
authUser (Password password) user = let PasswordHash ph = u_password_hash user in
  verifyPassword (T.encodeUtf8 $ TL.toStrict password) ph
