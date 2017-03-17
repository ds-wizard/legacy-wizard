{-# LANGUAGE OverloadedStrings, CPP #-}

module Model.Question where

import Database.PostgreSQL.Simple.FromRow

#ifdef __HASTE__
type Text = String
#else
import Data.Text (Text)
#endif

data Question = Question
  { chapterId :: Int
  , questionId :: Int
  , bookRef :: Maybe Text
  , otherInfo :: Maybe Text
  } deriving (Show, Read)

instance FromRow Question where
  fromRow = Question <$> field <*> field <*> field <*> field

