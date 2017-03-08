{-# LANGUAGE OverloadedStrings #-}

module Model.Session  where

import qualified Data.Text.Lazy as T
import qualified Data.Time.Clock as DTC
import Model.User (UserId)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

type SessionId = T.Text

data Session = Session
  { s_session_id :: SessionId
  , s_user_id :: UserId
  , s_valid_until :: DTC.UTCTime
  } deriving (Show)

