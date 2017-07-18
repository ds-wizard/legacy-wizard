{-# LANGUAGE OverloadedStrings #-}

module Persistence.User
  ( UserResult(..)
  , createUser
  , isExistingEmail
  , updateUser
  , changePassword
  , getUserById
  , getUserByEmail
  , confirmRegistration
  , authUser
  , getOpenPlan
  , openPlan
  ) where

import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Encoding as T
import Crypto.PasswordStore (makePassword, verifyPassword)
import qualified Database.PostgreSQL.Simple as PG

import Model.User
import Model.Plan

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}

data UserResult = UserOK | InvalidRegistrationKey | UserAlreadyConfirmed

createUser :: Email -> Password -> T.Text -> T.Text -> PG.Connection -> IO Int
createUser (Email email) (Password password) name affiliation conn = do
  passwordHash <- makePassword (T.encodeUtf8 $ TL.toStrict password) 18
  r <- PG.query conn "INSERT INTO \"User\" (email, password_hash, name, affiliation) VALUES (?, ?, ?, ?) RETURNING user_id"
         (email, passwordHash, name, affiliation) :: IO [PG.Only Int]
  let x =
        case r of
          (f:_) -> f
          []    -> PG.Only 0
  let (PG.Only i) = x
  return i

isExistingEmail :: User -> Email -> PG.Connection -> IO Bool
isExistingEmail user (Email email) conn = do
  r <- PG.query conn "SELECT * FROM \"User\" WHERE email = ?" (PG.Only email) :: IO [User]
  if null r || head r == user then return False else return True

updateUser :: User -> Email -> T.Text -> T.Text -> PG.Connection -> IO Int
updateUser user (Email email) name affiliation conn = do
  r <- PG.execute conn "UPDATE \"User\" set email = ?, name = ?, affiliation = ? WHERE user_id = ?"
         (email, name, affiliation, u_user_id user)
  return (fromIntegral r)

changePassword :: User -> Password -> PG.Connection -> IO Int
changePassword user (Password password) conn = do
  passwordHash <- makePassword (T.encodeUtf8 $ TL.toStrict password) 18
  r <- PG.execute conn "UPDATE \"User\" set password_hash = ? WHERE user_id = ?"
         (passwordHash, u_user_id user)
  return (fromIntegral r)

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
    else return $ Just $ head r

confirmRegistration :: UserId -> PG.Connection -> IO ()
confirmRegistration userId conn = do
  _ <- PG.execute conn "UPDATE \"User\" SET registration_confirmed = 't' WHERE user_id = ?" (PG.Only userId)
  return ()

authUser :: Password -> User -> Bool
authUser (Password password) user = let PasswordHash ph = u_password_hash user in
  verifyPassword (T.encodeUtf8 $ TL.toStrict password) ph

getOpenPlan :: User -> PG.Connection -> IO (Maybe Plan)
getOpenPlan user conn = case u_open_plan_id user of
  Nothing -> return Nothing
  Just planId -> do
    r <- PG.query conn "SELECT * FROM \"Plan\" WHERE id = ?" (PG.Only planId) :: IO [Plan]
    if null r
      then return Nothing
      else return $ Just $ head r

openPlan :: User -> Int -> PG.Connection -> IO ()
openPlan user planId conn = do
  _ <- PG.execute conn "UPDATE \"User\" SET open_plan_id = ? WHERE user_id = ?" (planId, u_user_id user)
  return ()
