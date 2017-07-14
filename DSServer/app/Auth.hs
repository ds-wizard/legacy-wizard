{-# LANGUAGE OverloadedStrings #-}

module Auth
  ( checkLogged
  , doLoginAction
  ) where

import App (Action, PGPool, Cookies, getSession, setSession, runQuery)
import Model.User
import Model.Session
import Persistence.Session (getUserFromSession, getSessionByUser)
import Actions.Responses (logInResponse, errorResponse)

checkLogged :: PGPool -> Cookies -> (User -> Action) -> Action
checkLogged pool cookies action =
  case getSession cookies of
    Nothing -> logInResponse
    Just sessionId -> do
      mUser <- runQuery pool $ getUserFromSession sessionId
      case mUser of
        Nothing  -> logInResponse
        Just user -> action user

doLoginAction :: PGPool -> User -> Action -> Action
doLoginAction pool user action = do
  mSession <- runQuery pool $ getSessionByUser user
  case mSession of
    Nothing -> errorResponse "We are sorry, internal error happened. Please contact the administrator."
    Just session -> do
      setSession $ s_session_id session
      action
