{-# LANGUAGE OverloadedStrings #-}

module API.Utils where

import Data.Text (Text)
import qualified Data.Text as T

readInt :: Text -> Maybe Int
readInt str
  | Prelude.length readChid /= 1 = Nothing
  | otherwise = if not $ Prelude.null $ snd $ Prelude.head readChid
     then Nothing
     else Just $ fst $ Prelude.head readChid
  where
    readChid = reads (T.unpack str) :: [(Int, String)]

