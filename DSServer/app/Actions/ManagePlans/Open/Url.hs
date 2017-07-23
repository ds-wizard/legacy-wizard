{-# LANGUAGE CPP #-}

module Actions.ManagePlans.Open.Url (url) where

import qualified Actions.ManagePlans.Url as Parent

url :: String
url = Parent.url ++ "/open"

