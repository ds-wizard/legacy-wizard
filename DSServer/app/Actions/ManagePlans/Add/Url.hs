{-# LANGUAGE CPP #-}

module Actions.ManagePlans.Add.Url (url) where

import qualified Actions.ManagePlans.Url as Parent

url :: String
url = Parent.url ++ "/add"

