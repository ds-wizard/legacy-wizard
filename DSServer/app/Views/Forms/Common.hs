{-# LANGUAGE OverloadedStrings #-}

module Views.Forms.Common
  ( emailFormlet
  , passwordFormlet
  ) where

import Data.Maybe
import qualified Data.Text as T
import qualified Text.Blaze.Html as H
import Text.Digestive

minMaxLen :: (Int, Int) -> T.Text -> Result H.Html T.Text
minMaxLen (minLen, maxLen) t =
  if len >= minLen && len <= maxLen
    then Success stripped
    else Error $
         H.toHtml $ "Must be longer than " ++ show minLen ++ " and shorter than " ++ show maxLen ++ " characters"
  where
    stripped = T.strip t
    len = T.length stripped

emailFormlet
  :: Monad m
  => Maybe T.Text -> Form H.Html m T.Text
emailFormlet mTxt =
  check "Not a valid email address" (isJust . T.find (== '@')) $ validate (minMaxLen (4, 50)) (text mTxt)

passwordFormlet
  :: Monad m
  => Maybe T.Text -> Form H.Html m T.Text
passwordFormlet mTxt = validate (minMaxLen (6, 40)) (text mTxt)
