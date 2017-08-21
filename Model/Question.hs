{-# LANGUAGE CPP #-}

module Model.Question where

#ifdef __HASTE__
type Text = String
#else
import Data.Text (Text)
import Database.PostgreSQL.Simple.FromRow (FromRow, fromRow, field)
#endif

data Question = Question
  { chapterId :: Int
  , questionId :: Int
  , bookRef :: Maybe Text
  , otherInfo :: Maybe Text
  } deriving (Show, Read)

#ifndef __HASTE__
instance FromRow Question where
  fromRow = Question <$> field <*> field <*> field <*> field
#endif
