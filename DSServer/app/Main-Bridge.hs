module Main where

import FormEngine.Types
import Language.PureScript.Bridge (writePSTypes, buildBridge, defaultBridge, mkSumType)
import Language.PureScript.Bridge.TypeInfo (mkTypeInfo)
import Data.Proxy (Proxy(..))

main :: IO ()
main = writePSTypes "../PureScript/src" (buildBridge defaultBridge) myTypes
  where
    myTypes =
      [ mkSumType (Proxy :: Proxy Numbering)
      , mkTypeInfo (Proxy :: Proxy ItemIdentity)
      , mkSumType (Proxy :: Proxy Unit)
      , mkSumType (Proxy :: Proxy Tag)
      , mkSumType (Proxy :: Proxy Param)
      , mkSumType (Proxy :: Proxy FormRule)
      , mkSumType (Proxy :: Proxy FIDescriptor)
      , mkSumType (Proxy :: Proxy Option)
      , mkSumType (Proxy :: Proxy FormItem)
      ]