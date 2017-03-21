{-# LANGUAGE OverloadedStrings #-}

module Persistence.Result
  (
  ) where

import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Encoding as T
import qualified Database.PostgreSQL.Simple as PG

import Model.Result
import Model.Plan

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}

resultId :: Plan -> Text -> PG.Connection -> IO Int
resultId plan name1 conn = do
  r <- PG.query conn
        "SELECT id FROM \"Result\" WHERE plan_id = ? AND name = ?"
        (R.id plan, name1) :: IO [PG.Only Int]
  let x =
        case r of
          (f:_) -> f
          []    -> PG.Only 0
  let (PG.Only i) = x
  return i

updateResult :: Plan -> Text -> Maybe Text -> PG.Connection -> IO Int
updateResult plan name1 value1 conn = do
  r <- PG.execute conn "UPDATE \"Result\" SET value = ?\
                     \ WHERE name = ? AND plan_id = ?" (value1, name1, r_plan_id plan)
  return (fromIntegral r)

insertResult :: Plan -> Text -> Maybe Text -> Maybe Text -> PG.Connection -> IO Int
insertResult plan name1 text1 value1 conn = do
  r <- PG.query conn "INSERT INTO \"Result\" (plan_id, name, text, value) VALUES (?, ?, ?, ?) RETURNING id"
         (r_plan_id plan, name1, text1, value1) :: IO [PG.Only Int]
  let x =
        case r of
          (f:_) -> f
          []    -> PG.Only 0
  let (PG.Only i) = x
  return i

getResultForPlan :: Text -> PG.Connection -> IO [FieldValue]
getResultForPlan planKey conn = PG.query conn
                                          "SELECT name, text, value FROM \"Result\" WHERE plan_id = (SELECT id from \"Plan\" WHERE =?)"
                                          (PG.Only planKey)

