{-# LANGUAGE OverloadedStrings #-}

module Auth
  ( checkLogged
  ) where

import App (Action, PGPool, Cookies, getSession, runQuery)
import Model.User
import Persistence.Session (getUserFromSession)
import Actions.Responses (logInResponse)

checkLogged :: PGPool -> Cookies -> (User -> Action) -> Action
checkLogged pool cookies action =
  case getSession cookies of
    Nothing -> logInResponse
    Just sessionId -> do
      mUser <- runQuery pool $ getUserFromSession sessionId
      case mUser of
        Nothing  -> logInResponse
        Just user -> action user
