{-# LANGUAGE OverloadedStrings #-}

module Persistence.Session
  ( createSession
  , getSessionById
  , sessionIsValid
  , deleteSessionById
  , deleteSessionOfUser
  ) where

import Control.Monad.Trans (liftIO)
import qualified Data.Time.Clock as DTC
import qualified Database.PostgreSQL.Simple as PG

import Model.User (User(..))
import Model.Session
import Persistence.Utils (genKey)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}

createSession :: User -> PG.Connection -> IO (Maybe SessionId)
createSession user conn = do
  now <- liftIO DTC.getCurrentTime
  sessionId <- genKey
  let validUntil = DTC.addUTCTime (5 * 3600) now
  r <- PG.query conn "INSERT INTO \"Session\" (session_id, user_id, valid_until) VALUES (?, ?) RETURNING session_id"
         (sessionId, u_user_id user, validUntil) :: IO [PG.Only SessionId]
  let x =
        case r of
          (f:_) -> Just f
          []    -> Nothing
  case x of
    Just (PG.Only sid) -> return $ Just sid
    Nothing -> return Nothing

getSessionById :: SessionId -> PG.Connection -> IO (Maybe Session)
getSessionById sessionId conn = do
  results <- PG.query conn "SELECT * FROM \"Session\" WHERE = session_id = ?" (PG.Only sessionId)
  let r = results :: [Session]
  if null r
    then return Nothing -- session not present
    else do             -- session present. Is it valid?
      let session = head r
      valid <- liftIO $ sessionIsValid session
      if valid
        then return $ Just session -- return valid session
        else do                    -- kill invalid session
          deleteSessionById sessionId conn
          return Nothing

sessionIsValid :: Session -> IO Bool
sessionIsValid session = do
  now <- DTC.getCurrentTime
  return $ s_valid_until session > now

deleteSessionById :: SessionId -> PG.Connection -> IO ()
deleteSessionById sessionId conn = do
  _ <- PG.execute conn "DELETE FROM \"Session\" WHERE session_id = ?" (PG.Only sessionId)
  return ()

deleteSessionOfUser :: User -> PG.Connection -> IO ()
deleteSessionOfUser user conn = do
  _ <- PG.execute conn "DELETE FROM \"Session\" WHERE user_id = ?" (PG.Only $ u_user_id user)
  return ()

