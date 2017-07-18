{-# LANGUAGE OverloadedStrings #-}

module Actions
  ( doExports
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
  ajaxSubmitForm form (showMessage . fromMaybe "")

showMessage :: String -> IO ()
showMessage msg = do
  _ <- selectById "info-bar" >>= appearJq >>= setHtml msg
  _ <- setTimer (Once 3000) (do
    _ <- selectById "info-bar" >>= disappearJq >>= setHtml ""
    return ()
    )
  return ()

