{-# LANGUAGE OverloadedStrings #-}

module Persistence.ActionKey
  ( createActionKey
  , useActionKey
  ) where

import Control.Monad.Trans (liftIO)
import qualified Database.PostgreSQL.Simple as PG
import qualified Data.Time.Clock as DTC

import Persistence.Utils (genKey)
import Model.ActionKey
import Model.User

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}

createActionKey :: User -> Action -> PG.Connection -> IO ActionKeyKey
createActionKey user action conn = do
  actionKey <- genKey
  ts <- liftIO DTC.getCurrentTime
  _ <- PG.execute conn "INSERT INTO \"ActionKey\" (user_id, action, action_key, created) VALUES (?, ?, ?, ?)"
         (u_user_id user, action, actionKey, ts)
  return actionKey

useActionKey :: ActionKeyKey -> Action -> PG.Connection -> IO (Maybe ActionKey)
useActionKey key action conn = do
  actionKeys <- PG.query conn "SELECT * FROM \"ActionKey\" WHERE action = ? AND action_key = ?" (action, key) :: IO [ActionKey]
  if null actionKeys
    then return Nothing
    else do
      _ <- PG.execute conn "DELETE FROM \"ActionKey\" WHERE action_key = ?" (PG.Only key)
      return $ Just $ head actionKeys
