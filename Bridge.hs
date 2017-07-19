{-# LANGUAGE CPP, OverloadedStrings #-}

module Bridge where

import Data.Char (toLower)
import Data.Monoid ((<>))

#ifndef __HASTE__
type JSString = String
toJSString :: String -> JSString
toJSString = id
#else
import Haste
#endif

data ClientAction
  = SavePlan
  | ManagePlans
  | ShowMessage
  deriving (Show)

infoBar :: String
infoBar = "info-bar"

warningBar :: String
warningBar = "warning-bar"

errorBar :: String
errorBar = "error-bar"

toFnName :: ClientAction -> String
toFnName action = let s = show action in
  [toLower (head s)] <> tail s

call0 :: ClientAction -> JSString
call0 action = toJSString $ "Haste['" ++ toFnName action ++ "']()"

call1 :: ClientAction -> String -> JSString
call1 action param = toJSString $ "Haste['" ++ toFnName action ++ "'](" ++ param ++ ")"
