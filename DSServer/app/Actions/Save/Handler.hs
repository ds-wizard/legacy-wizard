{-# LANGUAGE OverloadedStrings #-}

module Actions.Save.Handler
  ( url
  , handler
  , baseName
  ) where


import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as TL
import qualified Control.Monad as M
import Web.Scotty (Param, params)

import App (Action, PGPool, Cookies, runQuery)
import Auth (checkLogged)
import Actions.Responses (infoResponse, errorResponse)

import Model.Plan
import Persistence.Plan (getPlanByUser)
import Persistence.Result (getResultId, insertResult, updateResult)
import Questionnaire (formItems)
import FormEngine.FormData (FieldInfo, getFieldInfos)

baseName :: Text -> Text -- strip the multiple group "_Gx" suffix
baseName fullName = if null br then fullName else TL.dropEnd 1 n2
  where
  br = TL.breakOnAll "G" fullName
  (n2, _) = head br

url :: String
url = "/save"

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLogged pool cookies (\user -> do
  let fieldInfos = getFieldInfos formItems
  mPlan <- runQuery pool $ getPlanByUser user
  case mPlan of
    Nothing -> errorResponse "Failed getting plan of a user. Please contact an administrator."
    Just plan -> do
      ps <- params
      mapM_ (storeValue plan fieldInfos) ps
      infoResponse "Data has been saved.")
  where
    storeValue :: Plan -> [FieldInfo] -> Param -> Action
    storeValue plan fieldInfos (name, value) = do
      let mText = M.join $ lookup (baseName name) fieldInfos
      resId <- runQuery pool $ getResultId plan name
      _ <- if resId == 0 then
        runQuery pool $ insertResult plan name mText (Just value)
      else
        runQuery pool $ updateResult plan name (Just value)
      return ()
      --where


