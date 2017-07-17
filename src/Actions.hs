{-# LANGUAGE OverloadedStrings #-}

module Actions
  ( doExports
  ) where

import Prelude
import Haste
import Haste.Foreign
--import Haste.Ajax (ajaxRequest, Method(POST))

import qualified Bridge as B

doExports :: IO ()
doExports = doExport B.SavePlan savePlan

doExport :: (ToAny a, FFI a) => B.ClientAction -> a -> IO ()
doExport action = export (toJSString  $ B.toFnName action)

savePlan :: IO ()
savePlan = alert "Saved"
