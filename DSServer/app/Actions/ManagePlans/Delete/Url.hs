{-# LANGUAGE CPP #-}

module Actions.ManagePlans.Delete.Url (url) where

import qualified Actions.ManagePlans.Url as Parent

url :: String
url = Parent.url ++ "/delete"

