{-# LANGUAGE OverloadedStrings #-}
{-# ANN module "HLint: ignore Reduce duplication" #-}

module Persistence.User where

import Control.Monad
import Control.Monad.Trans
import qualified Crypto.Hash.SHA512 as SHA
import qualified Data.ByteString as BS
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Time.Clock as DTC
import Data.Word8
import qualified Database.PostgreSQL.Simple as PG
import Database.PostgreSQL.Simple.FromRow
import System.Random (getStdGen, randomBS)

import Model.User
import Model.Session

instance FromRow User where
  fromRow = User <$> field <*> field <*> field <*> field <*> field <*> field

instance FromRow Session where
  fromRow = Session <$> field <*> field

-- * Password routines

randomBytes :: Int -> StdGen -> [Word8]
randomBytes 0 _ = []
randomBytes ct g =
  let (value, nextG) = next g
  in fromIntegral value : randomBytes (ct - 1) nextG

randomBS :: Int -> StdGen -> BS.ByteString
randomBS len g = BS.pack $ randomBytes len g

createSalt :: IO PasswordSalt
createSalt = do
  g <- getStdGen
  return $ randomBS 512 g

hashPassword :: Password -> PasswordSalt -> PasswordHash <*> field
hashPassword (Password password) (PasswordSalt salt) = SHA.finalize $ SHA.updates SHA.init [salt, T.encodeUtf8 password]

-- * User operations

createUser :: Email -> Password -> T.Text -> T.Text -> PG.Connection -> IO Int
createUser (Email email) (Password password) name affiliation conn = do
  salt <- createSalt
  r <- PG.query conn "INSERT INTO \"Users\" (email, password_hash, salt, name, affiliation) VALUES (?, ?, ?, ?, ?) RETURNING id"
         (email, hashPassword password salt, name, affilitation) :: IO [PG.Only Int]
  let x =
        case r of
          (f:_) -> f
          []    -> PG.Only 0
  let (PG.Only i) = x
  return i

getUserByEmail :: Email -> PG.Connection -> IO (Maybe User)
getUserByEmail (Email email) conn = do
  results <- PG.query conn "SELECT * FROM \"Users\" WHERE email = ?" (PG.Only email)
  let r = results :: [User]
  if null r
    then return Nothing
    else do
      let user = head r
      return $ Just user

authUser :: Password -> User -> Bool
authUser (Password password) user = u_password_hash user == makeHex (hashPassword password (decodeHex $ u_salt user))

-- * Session routines

isValid :: Session -> IO Bool
isValid session = do
  now <- DTC.getCurrentTime
  return $ s_valid_until > now

createSession :: User -> PG.Connection -> IO SessionId
createSession user conn = do
  now <- liftIO getCurrentTime
  let validUntil = DTC.addUTCTime (5 * 3600) DTC.now
  r <- PG.query conn "INSERT INTO \"Sessions\" (user_id, valid_until) VALUES (?, ?) RETURNING id"
         (userId, validUntil) :: IO [PG.Only Int]
  let x =
        case r of
          (f:_) -> f
          []    -> PG.Only 0
  let (PG.Only i) = x
  return i

getSessionById :: SessionId -> PG.Connection -> IO (Maybe Session)
getSessionById sessionId conn = do
  results <- PG.query conn "SELECT * FROM \"Sessions\" WHERE = session_id = ?" (PG.Only sessionId)
  let r = results :: [Session]
  if null r
    then return Nothing -- session not present
    else do             -- session present. Is it valid?
      let session = head r
      valid <- liftIO $ isValid session
      if valid
        then return $ Just session -- return valid session
        else do                    -- kill invalid session
          deleteSessionById sessionId conn
          return Nothing

deleteSessionById :: SessionId -> PG.Connection -> IO ()
deleteSessionById sessionId conn = do
  _ <- PG.execute conn "DELETE FROM \"Sessions\" WHERE session_id = ?" (PG.Only sessionId)
  return ()

deleteSessionOfUser :: User -> PG.Connection -> IO ()
deleteSessionOfUser user conn = do
  _ <- PG.execute conn "DELETE FROM \"Sessions\" WHERE user_id = ?" (PG.Only $ u_user_id user)
  return ()

