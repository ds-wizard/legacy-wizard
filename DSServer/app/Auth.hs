{-# LANGUAGE OverloadedStrings #-}

module Auth
  ( checkLogged
  , checkAdmin
  , checkLoggedAPI
  , checkAdminAPI
  , doLoginAction
  ) where

import Data.Text (Text)
import Data.Text.Lazy (toStrict, fromStrict)
import Web.Scotty (Param, text)
import Text.Blaze.Html5 (toHtml)
import App (Action, PGPool, Cookies, getSession, setSession, runQuery)
import Model.User
import Model.Session
import Persistence.Session (getUserFromSession, getSessionByUser)
import Actions.Responses (logInResponse, errorResponse)

generalCheckLogged :: Action -> PGPool -> [Param] -> (User -> Action) -> Action
generalCheckLogged errorAction pool ps okActionWithUser = do
  let mSessionId = lookup "sessionid" ps
  case mSessionId of
    Nothing -> errorAction
    Just sessionId -> do
      mUser <- runQuery pool $ getUserFromSession (toStrict sessionId)
      case mUser of
        Nothing  -> errorAction
        Just user -> okActionWithUser user

checkLogged :: PGPool -> Cookies -> (User -> Action) -> Action
checkLogged pool cookies action =
  case getSession cookies of
    Nothing -> logInResponse
    Just sessionId -> generalCheckLogged logInResponse pool [("sessionid", fromStrict sessionId)] action

checkLoggedAPI :: PGPool -> [Param] -> (User -> Action) -> Action
checkLoggedAPI = generalCheckLogged (text "Logged user required.")

generalCheckAdmin :: Action -> PGPool -> [Param] -> (User -> Action) -> Action
generalCheckAdmin errorAction pool ps okActionWithUser =
  generalCheckLogged errorAction pool ps (\user ->
    if u_isAdmin user then
      okActionWithUser user
    else
      errorAction
    )

adminErr :: Text
adminErr = "This action requires administrator priviledges."

checkAdmin :: PGPool -> Cookies -> (User -> Action) -> Action
checkAdmin pool cookies action =
  case getSession cookies of
    Nothing -> logInResponse
    Just sessionId -> generalCheckAdmin (errorResponse $ toHtml adminErr) pool [("sessionid", fromStrict sessionId)] action

checkAdminAPI :: PGPool -> [Param] -> (User -> Action) -> Action
checkAdminAPI = generalCheckAdmin (text $ fromStrict adminErr)

doLoginAction :: PGPool -> User -> Action -> Action
doLoginAction pool user action = do
  mSession <- runQuery pool $ getSessionByUser user
  case mSession of
    Nothing -> errorResponse "We are sorry, internal error happened. Please contact the administrator."
    Just session -> do
      setSession $ s_session_id session
      action
