{-# LANGUAGE OverloadedStrings #-}

module Persistence.Result
  ( getResultId
  , updateResult
  , insertResult
  , getResultsForPlan
  ) where

import Data.Text.Lazy (Text)
import qualified Control.Monad as M
import qualified Database.PostgreSQL.Simple as PG

import Model.Plan
import Persistence.Plan (updateModified)
import qualified Questionnaire as Q
import FormEngine.FormData (FieldValue, getFieldInfos, getName)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}

getResultId :: Plan -> Text -> PG.Connection -> IO Int
getResultId plan key conn = do
  r <- PG.query conn
        "SELECT id FROM \"Result\" WHERE plan_id = ? AND name = ?"
        (p_id plan, key) :: IO [PG.Only Int]
  let x =
        case r of
          (f:_) -> f
          []    -> PG.Only 0
  let (PG.Only i) = x
  return i

updateResult :: Plan -> (Text, Maybe Text) -> PG.Connection -> IO Int
updateResult plan (key, value) conn = do
  r <- PG.execute conn "UPDATE \"Result\" SET value = ?\
    \ WHERE plan_id = ? AND name = ?" (value, p_id plan, key)
  _ <- updateModified plan conn
  return (fromIntegral r)

insertResult :: Plan -> (Text, Maybe Text) -> PG.Connection -> IO Int
insertResult plan (key, value) conn = do
  let fieldInfos = getFieldInfos Q.formItems
      mText = M.join $ lookup (getName key) fieldInfos
  r <- PG.query conn "INSERT INTO \"Result\" (plan_id, name, text, value) VALUES (?, ?, ?, ?) RETURNING id"
         (p_id plan, key, mText, value) :: IO [PG.Only Int]
  _ <- updateModified plan conn
  let x =
        case r of
          (f:_) -> f
          []    -> PG.Only 0
  let (PG.Only i) = x
  return i

getResultsForPlan :: Plan -> PG.Connection -> IO [FieldValue]
getResultsForPlan plan conn = PG.query conn
                                          "SELECT name, text, value FROM \"Result\" WHERE plan_id = ?"
                                          (PG.Only $ p_id plan)

