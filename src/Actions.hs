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

planNameEdit :: JQuery -> Int-> IO ()
planNameEdit jq planId = do
  inp <- findSelector "input" jq
  len <- jqLength inp
  when (len == 0) $ do
    val <- getText jq
    _ <- removeClass "editable" jq >>= addClass "editing"
    _ <- setHtml "<input type='text'></input>" jq
      >>= inside
        >>= setVal val
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
      val <- findSelector "input" jq >>= getVal
      ajaxRequest POST "api/plan/setName"
        [("planId" :: JSString, show planId), ("newName", val)]
        (\mRes -> case mRes of
          Nothing -> showError documentJq "Saving the name failed"
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
