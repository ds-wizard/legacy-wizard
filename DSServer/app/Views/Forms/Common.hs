{-# LANGUAGE OverloadedStrings #-}

module Views.Forms.Common
  ( emailFormlet
  , passwordFormlet
  ) where

import Data.Maybe
import qualified Data.Text as T
import qualified Text.Blaze.Html as H
import qualified Text.Digestive as D

minMaxLen :: (Int, Int) -> T.Text -> D.Result H.Html T.Text
minMaxLen (minLen, maxLen) t =
  if len >= minLen && len <= maxLen
    then D.Success stripped
    else D.Error $
         H.toHtml $ "Must be longer than " ++ show minLen ++ " and shorter than " ++ show maxLen ++ " characters"
  where
    stripped = T.strip t
    len = T.length stripped

emailFormlet
  :: Monad m
  => Maybe T.Text -> D.Form H.Html m T.Text
emailFormlet mTxt =
  D.check "Not a valid email address" (isJust . T.find (== '@')) $ D.validate (minMaxLen (4, 50)) (D.text mTxt)

passwordFormlet
  :: Monad m
  => Maybe T.Text -> D.Form H.Html m T.Text
passwordFormlet mTxt = D.validate (minMaxLen (6, 40)) (D.text mTxt)
