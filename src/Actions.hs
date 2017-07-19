{-# LANGUAGE OverloadedStrings #-}

module Actions
  ( doExports
  , showInfo
  , showWarning
  , showError
  ) where

import Prelude
import Data.Maybe (fromMaybe)
import Haste
import Haste.Foreign
--import Haste.Ajax (ajaxRequest, Method(POST))
import FormEngine.JQuery

import qualified Bridge as B

doExports :: IO ()
doExports = do
  doExport B.SavePlan savePlan
  doExport B.ShowMessage showMessage

doExport :: (ToAny a, FFI a) => B.ClientAction -> a -> IO ()
doExport action = export (toJSString  $ B.toFnName action)

savePlan :: IO ()
savePlan = do
  form <- selectById "form"
  ajaxSubmitForm form (showInfo . fromMaybe "")

showInfo :: String -> IO ()
showInfo msg = selectById B.infoBar >>= showMessage msg

showWarning :: String -> IO ()
showWarning msg = selectById B.warningBar >>= showMessage msg

showError :: String -> IO ()
showError msg = selectById B.errorBar >>= showMessage msg

showMessage :: String -> JQuery -> IO ()
showMessage msg barJq = do
  _ <- appearJq barJq >>= setHtml msg
  _ <- setTimer (Once 3000) (do
    _ <- disappearJq barJq >>= setHtml ""
    return ()
    )
  return ()

