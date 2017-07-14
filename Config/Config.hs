{-# LANGUAGE OverloadedStrings, CPP #-}

module Config.Config where

import  Data.Monoid ((<>))

domainURL :: String
domainURL = "dmp.fairdata.solutions"

rootURL :: String
rootURL = "http://" <> domainURL

baseURL :: String
baseURL = "/"

staticURL :: String
staticURL = baseURL <> "static/"

