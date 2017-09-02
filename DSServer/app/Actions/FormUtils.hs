{-# LANGUAGE OverloadedStrings #-}

module Actions.FormUtils
  ( MyView
  , notEmpty
  , emailFormlet
  , passwordFormlet
  , passwordConfirmer
  , addError
  , errorTr
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import qualified Text.Digestive as D
import Text.Blaze.Html5 ((!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Text.Digestive ((.:))
import qualified Text.Digestive.Blaze.Html5 as DH
import qualified Text.Email.Validate as V

type MyForm m = D.Form H.Html m Text
type MyView = D.View H.Html

notEmpty :: Text -> D.Result H.Html Text
notEmpty t
  | T.length t == 0 = D.Error "Must not be empty"
  | otherwise = D.Success t

minMaxLen :: (Int, Int) -> Text -> D.Result H.Html Text
minMaxLen (minLen, maxLen) t =
  if len >= minLen && len <= maxLen
    then D.Success stripped
    else D.Error $
         H.toHtml $ "Must be longer than " ++ show minLen ++ " and shorter than " ++ show maxLen ++ " characters"
  where
    stripped = T.strip t
    len = T.length stripped

emailFormlet :: Monad m => Maybe Text -> MyForm m
emailFormlet mTxt =
  D.check "Not a valid email address" (V.isValid . encodeUtf8) (D.text mTxt)

passwordFormlet :: Monad m => Maybe Text -> MyForm m
passwordFormlet mTxt = D.validate (minMaxLen (6, 40)) (D.text mTxt)

passwordConfirmer :: Monad m => MyForm m
passwordConfirmer  =
  D.validate fst' $ (,) <$> ("p1" .: passwordFormlet Nothing)
                      <*> ("p2" .: passwordFormlet Nothing)
  where
    fst' (p1, p2) | p1 == p2  = D.Success p1
                  | otherwise = D.Error "Passwords do not match"

addError :: MyView -> Text -> H.Html -> MyView
addError view ref err = view { D.viewErrors = viewErrors2}
  where
  viewErrors2 = D.viewErrors view ++ [(D.toPath ref, err)]

errorTr :: Text -> MyView -> H.Html
errorTr ref v =
  H.tr $
    H.td ! A.colspan "2" $
      DH.errorList ref v
