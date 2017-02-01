{-# LANGUAGE OverloadedStrings #-}
{-# ANN module "HLint: ignore Use camelCase" #-}

module Model.Session  where

type SessionId = BS.ByteString

data Session = Session
  { s_session_id :: SessionId
  , s_user_id :: UserId
  , s_valid_until :: DTC.UTCTime
  } deriving (Show)

