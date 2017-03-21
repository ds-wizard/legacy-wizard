{-# LANGUAGE OverloadedStrings, CPP #-}

module Model.Result where

import Database.PostgreSQL.Simple.FromRow

#ifdef __HASTE__
type Text = String
#else
import Data.Text (Text)
#endif

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

data Result = Result
  { r_id :: Int
  , r_plan_id :: Int
  , r_name :: Text
  , r_rid :: Maybe Text
  , r_text :: Maybe Text
  , r_value :: Maybe Text
  } deriving (Show, Read)

instance FromRow Result where
  fromRow = Result <$> field <*> field <*> field <*> field <*> field <*> field

