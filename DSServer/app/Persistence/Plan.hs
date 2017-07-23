{-# LANGUAGE OverloadedStrings #-}

module Persistence.Plan
  ( addPlan
  , getOpenPlanOfUser
  , getPlansOfUser
  , setPlanName
  , setPlanDescription
  , deletePlan
  ) where

import Data.Text.Lazy (Text)
import qualified Database.PostgreSQL.Simple as PG

import Model.User
import Model.Plan

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}

addPlan :: User -> Text -> Maybe Text -> PG.Connection -> IO Int
addPlan user name mDescription conn = do
  r <- PG.query conn "INSERT INTO \"Plan\" (user_id, name, description) VALUES (?, ?, ?) RETURNING id"
      (u_user_id user, name, mDescription) :: IO [PG.Only Int]
  let x =
        case r of
          (f:_) -> f
          []    -> PG.Only 0
  let (PG.Only i) = x
  return i

getOpenPlanOfUser :: User -> PG.Connection -> IO (Maybe Plan)
getOpenPlanOfUser user conn = do
  r <- PG.query conn "SELECT * FROM \"Plan\" WHERE id = ?" (PG.Only $ u_open_plan_id user) :: IO [Plan]
  if null r
    then return Nothing
    else do
      let plan = head r
      return $ Just plan

getPlansOfUser :: User -> PG.Connection -> IO [Plan]
getPlansOfUser user conn = PG.query conn "SELECT * FROM \"Plan\" WHERE user_id = ? ORDER BY id" (PG.Only $ u_user_id user)

setPlanName :: Int -> Text -> PG.Connection -> IO Int
setPlanName planId newVal conn = do
  r <- PG.execute conn "UPDATE \"Plan\" SET name = ? WHERE id = ?" (newVal, planId)
  return (fromIntegral r)

setPlanDescription :: Int -> Text -> PG.Connection -> IO Int
setPlanDescription planId newVal conn = do
  r <- PG.execute conn "UPDATE \"Plan\" SET description = ? WHERE id = ?" (newVal, planId)
  return (fromIntegral r)

deletePlan :: Int -> PG.Connection -> IO Int
deletePlan planId conn = do
  r <- PG.execute conn "DELETE FROM \"Plan\" WHERE id = ?" (PG.Only planId)
  return (fromIntegral r)

