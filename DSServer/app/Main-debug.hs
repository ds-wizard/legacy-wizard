{-# LANGUAGE OverloadedStrings #-}

module Main where

--import FormEngine.FormItem
import FormEngine.FormData
import qualified Questionnaire
import qualified FormEngine.FormElement.FormElement as Element

--import Debug.Hood.Observe
import Debug.Trace

maybeFormData :: Maybe FormData
maybeFormData = Just [("0_1_0","Yes"),("0_1_0_1_0_0_0","Yes"),("0_1_0_1_0_0_0_1_0_0_0_0_G0","item1"),("0_1_0_1_0_0_0_1_0_0_0_3_0_0_0_0_0_G0",""),("0_1_0_1_0_0_0_1_0_1_0_0_G0",""),("0_1_0_1_0_0_0_1_0_2_0_0_0_1_0",""),("0_1_0_1_0_0_0_1_0_2_0_0_0_3_0",""),("0_1_0_1_0_0_0_1_0_2_0_0_0_5_0",""),("0_2_0_0_0_0_0",""),("0_2_0_0_0_1_0",""),("0_2_0_0_0_2_0",""),("1_2_0_0_0_2_0",""),("1_7_0_1_0_0_0_0_0_0_0","")]

tabMaybes = map (Element.makeChapter maybeFormData) Questionnaire.formItems

main :: IO ()
main = case (tabMaybes !! 0) of
  Nothing ->
    print $ "Nothing"
  Just chapterElem ->
    print chapterElem




