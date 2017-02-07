{-# LANGUAGE OverloadedStrings, CPP #-}

module Config.Config where

import  Data.Monoid ((<>))

#ifdef __HASTE__
type Text = String
#else
import           Data.Text (Text)
#endif

domainURL :: Text
domainURL = "dmp.fairdata.solutions"

baseURL :: Text
baseURL = "/"

staticURL :: Text
staticURL = baseURL <> "static/"

