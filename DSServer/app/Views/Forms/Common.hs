{-# LANGUAGE OverloadedStrings #-}

module Views.Forms.Common
  ( notEmpty
  , emailFormlet
  , passwordFormlet
  , errorTr
  ) where

import Data.Maybe
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import qualified Text.Digestive as D
import Text.Blaze.Html5 ((!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import qualified Text.Digestive.Blaze.Html5 as DH
import qualified Text.Email.Validate as V

notEmpty :: T.Text -> D.Result H.Html T.Text
notEmpty t
  | T.length t == 0 = D.Error "Must not be empty"
  | otherwise = D.Success t

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
  D.check "Not a valid email address" (V.isValid . encodeUtf8) (D.text mTxt)

passwordFormlet
  :: Monad m
  => Maybe T.Text -> D.Form H.Html m T.Text
passwordFormlet mTxt = D.validate (minMaxLen (6, 40)) (D.text mTxt)

errorTr :: T.Text -> D.View H.Html -> H.Html
errorTr ref v =
  H.tr $
    H.td ! A.colspan "2" $
      DH.errorList ref v
