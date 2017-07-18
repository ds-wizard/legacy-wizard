{-# LANGUAGE OverloadedStrings #-}

module Persistence.Plan
  ( createPlan
  , getPlanByUser
  ) where

import Data.Text.Lazy (Text)
import qualified Database.PostgreSQL.Simple as PG

import Model.User
import Model.Plan

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}

createPlan :: User -> Text -> Maybe Text -> PG.Connection -> IO Int
createPlan user name mDescription conn = do
  r <- PG.query conn "INSERT INTO \"Plan\" (user_id, name, description) VALUES (?, ?, ?) RETURNING id"
      (u_user_id user, name, mDescription) :: IO [PG.Only Int]
  let x =
        case r of
          (f:_) -> f
          []    -> PG.Only 0
  let (PG.Only i) = x
  return i

getPlanByUser :: User -> PG.Connection -> IO (Maybe Plan)
getPlanByUser user conn = do
  r <- PG.query conn "SELECT * FROM \"Plan\" WHERE id = ?" (PG.Only (u_open_plan_id user)) :: IO [Plan]
  if null r
    then return Nothing
    else do
      let plan = head r
      return $ Just plan
