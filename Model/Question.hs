{-# LANGUAGE OverloadedStrings, CPP #-}

module Model.Question where

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
