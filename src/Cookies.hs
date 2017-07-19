{-# LANGUAGE OverloadedStrings #-}

module Cookies
  ( getCookie
  ) where

import Prelude
import Haste
import Haste.Foreign

getCookie :: String -> IO (Maybe String)
getCookie cName = let cNameJS = toJSString cName in do
  res <- doFFI cNameJS
  if res == "undefined" then return Nothing else return $ Just res
  where
    doFFI :: JSString -> IO String
    doFFI = ffi "(function (cName) { return Cookies.get(cName); })"


