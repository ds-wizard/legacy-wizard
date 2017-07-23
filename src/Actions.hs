{-# LANGUAGE OverloadedStrings #-}

module Actions
  ( doExports
  , showInfo
  , showWarning
  , showError
  ) where

import Prelude
import Control.Monad (when)
import Data.Maybe (fromMaybe)
import Haste
import Haste.Foreign
import Haste.Ajax (ajaxRequest, Method(POST))
import FormEngine.JQuery

import qualified Bridge as B

doExports :: IO ()
doExports = do
  doExport B.SavePlan savePlan
  doExport B.ShowMessage showMessage
  doExport B.PlanNameEdit planNameEdit
  doExport B.PlanDescriptionEdit planDescriptionEdit

doExport :: (ToAny a, FFI a) => B.ClientAction -> a -> IO ()
doExport action = export (toJSString  $ B.toFnName action)

savePlan :: JQuery -> IO ()
savePlan jq = do
  form <- selectById "form"
  ajaxSubmitForm form (showInfo jq . fromMaybe "")

showInfo :: JQuery -> String -> IO ()
showInfo _ msg = selectById B.infoBar >>= showMessage msg

showWarning :: JQuery -> String -> IO ()
showWarning _ msg = selectById B.warningBar >>= showMessage msg

showError :: JQuery -> String -> IO ()
showError _ msg = selectById B.errorBar >>= showMessage msg

showMessage :: String -> JQuery -> IO ()
showMessage msg barJq = do
  _ <- appearJq barJq >>= setHtml msg
  _ <- setTimer (Once 3000) (do
    _ <- disappearJq barJq >>= setHtml ""
    return ()
    )
  return ()

fieldEdit :: JQuery -> Int -> String -> String -> (String -> JQuery -> IO JQuery) -> String -> IO ()
fieldEdit jq planId editor editorHtml setValueFn url = do
  inp <- findSelector editor jq
  len <- jqLength inp
  when (len == 0) $ do
    val <- getText jq
    _ <- removeClass "editable" jq >>= addClass "editing"
    _ <- setHtml editorHtml jq
      >>= inside
        >>= setValueFn val
        >>= onKeypress (\ev -> do
          key <- getEvKeyCode ev
          when (key == "13") save
          )
        >>= onBlur (\_ -> cancel val)
      >>= parent
    return ()
    where
    save :: IO ()
    save = do
      val <- findSelector editor jq >>= getVal
      ajaxRequest POST url
        [("planId" :: JSString, show planId), ("newValue", val)]
        (\mRes -> case mRes of
          Nothing -> showError documentJq "Save failed"
          Just res -> do
            showInfo documentJq res
            _ <- setText val jq
            _ <- removeClass "editing" jq >>= addClass "editable"
            return ()
        )
    cancel :: String -> IO ()
    cancel origVal = do
      _ <- setText origVal jq
      return ()

planNameEdit :: JQuery -> Int-> IO ()
planNameEdit jq planId = fieldEdit jq planId "input" "<input type='text'></input>" setVal "api/plan/setName"

planDescriptionEdit :: JQuery -> Int-> IO ()
planDescriptionEdit jq planId = fieldEdit jq planId "textarea" "<textarea></textarea>" setHtml "api/plan/setDescription"
