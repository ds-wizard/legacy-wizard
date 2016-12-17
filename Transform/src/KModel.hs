{-# LANGUAGE OverloadedStrings #-}

module KModel where

import Data.Aeson
import Data.Aeson.Types
import Data.Text

data Reference = Reference
  { refType :: !Text
  , dmpChapter :: Maybe Text
  , urlrefLink :: Maybe Text
  , urlrefText :: Maybe Text
  , xrefQID :: Maybe Int
  , xrefChID :: Maybe Int
  , xrefNS :: Maybe Text
  } deriving (Show)

data Expert = Expert
  { expertName :: !Text
  , expertEmail :: Maybe Text
  , expertIndiv :: Maybe Text
  } deriving (Show)

data Answer = Answer
  { answerID :: Int
  , answerLabel :: !Text
  , answerAdvice :: Maybe Text
  , answerFollow :: Maybe [Question]
  } deriving (Show)

data Question = Question
  { questID :: Int
  , questType :: !Text
  , questTitle :: !Text
  , questText :: Maybe Text
  , questRefs :: Maybe [Reference]
  , questExps :: Maybe [Expert]
  , questAnswers :: Maybe [Answer]
  , questFollow :: Maybe [Question]
  } deriving (Show)

data Chapter = Chapter
  { chapTitle :: !Text
  , chapText :: Maybe Text
  , chapID :: Int
  , chapQuests :: [Question]
  } deriving (Show)

{- JSON parsing ------------------------------------------------}
instance FromJSON Reference where
  parseJSON (Object v) =
    Reference <$> v .: "type" <*> v .:? "chapter" <*> v .:? "weblink" <*> v .:? "anchor" <*> v .:? "chapterid" <*>
    v .:? "questionid" <*>
    v .:? "namespace"
  parseJSON x = typeMismatch "Reference" x

instance FromJSON Expert where
  parseJSON (Object v) = Expert <$> v .: "name" <*> v .:? "email" <*> v .:? "class"
  parseJSON x = typeMismatch "Expert" x

instance FromJSON Answer where
  parseJSON (Object v) = Answer <$> v .: "id" <*> v .: "label" <*> v .:? "advice" <*> v .:? "followups"
  parseJSON x = typeMismatch "Answer" x

instance FromJSON Question where
  parseJSON (Object v) =
    Question <$> v .: "questionid" <*> v .: "type" <*> v .: "title" <*> v .:? "text" <*> v .:? "references" <*>
    v .:? "experts" <*>
    v .:? "answers" <*>
    v .:? "followups"
  parseJSON x = typeMismatch "Question" x

instance FromJSON Chapter where
  parseJSON (Object v) = Chapter <$> v .: "title" <*> v .:? "text" <*> v .: "chapterid" <*> v .: "questions"
  parseJSON x = typeMismatch "Chapter" x
