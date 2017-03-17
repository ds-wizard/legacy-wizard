{-# LANGUAGE OverloadedStrings #-}

module Model.Session  where

import Data.Text (Text)
import qualified Data.Time.Clock as DTC
import Database.PostgreSQL.Simple.FromRow

import Model.User (UserId)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

type SessionId = Text

data Session = Session
  { s_session_id :: SessionId
  , s_user_id :: UserId
  , s_valid_until :: DTC.UTCTime
  } deriving (Show)

instance FromRow Session where
  fromRow = Session <$> field <*> field <*> field
