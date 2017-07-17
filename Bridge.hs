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
  deriving (Show)

toFnName :: ClientAction -> String
toFnName action = let s = show action in
  [toLower (head s)] <> tail s

call0 :: ClientAction -> JSString
call0 action = toJSString $ "Haste['" ++ toFnName action ++ "']()"
