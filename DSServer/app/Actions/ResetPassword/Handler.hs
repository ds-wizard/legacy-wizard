{-# LANGUAGE OverloadedStrings #-}

module Actions.ResetPassword.Handler (handler) where

import qualified Data.Text.Lazy as TL
import Web.Scotty (params, redirect)

import qualified Persistence.User as U
import qualified Model.ActionKey as AC
import qualified Persistence.ActionKey as AC

import App (Action, PGPool, runQuery)
import Auth (doLoginAction)
import Actions.Responses (errorResponse)
import qualified Actions.ChangePassword.Url as Actions.ChangePassword

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

handler :: PGPool -> Action
handler pool = do
  ps <- params
  case lookup "key" ps of
    Nothing -> errorResponse "Password reset failed: incorrect key in the URL."
    Just key -> do
        mActionKey <- runQuery pool $ AC.useActionKey (TL.toStrict key) AC.ResetPassword
        case mActionKey of
          Nothing -> errorResponse "Invalid password reset key or the key has been already used."
          Just actionKey -> do
            mUser <- runQuery pool $ U.getUserById $ AC.ac_user_id actionKey
            case mUser of
              Nothing -> errorResponse "We are sorry, an internal error occured, please contact the administrator."
              Just user -> do
                doLoginAction pool user $ redirect $ TL.pack Actions.ChangePassword.url
