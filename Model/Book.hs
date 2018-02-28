{-# LANGUAGE OverloadedStrings, CPP #-}

module Model.Book where

import Database.PostgreSQL.Simple.FromRow

#ifdef __HASTE__
type Text = String
#else
import Data.Text (Text)
#endif

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

data Book = Book
  { b_id :: Int
  , b_chapter :: Text
  , b_contents :: Text
  , b_shortuid :: Maybe Text
  } deriving (Show, Read)

instance FromRow Book where
  fromRow = Book <$> field <*> field <*> field <*> field
