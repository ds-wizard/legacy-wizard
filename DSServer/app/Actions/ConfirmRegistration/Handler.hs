{-# LANGUAGE OverloadedStrings #-}

module Actions.ConfirmRegistration.Handler (handler) where

import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Data.Monoid ((<>))
import Text.Blaze.Html5 ((!), textValue)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Web.Scotty (params)

import qualified Persistence.User as U
import qualified Model.ActionKey as AC
import qualified Persistence.ActionKey as AC

import App (Action, PGPool, runQuery)
import qualified Actions.LoginScreen.Login.Url as Login
import Actions.Responses (infoResponse, errorResponse)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

handler :: PGPool -> Action
handler pool = do
  ps <- params
  case lookup "key" ps of
    Nothing -> errorResponse "Registration confirmation failed: incorrect key in the URL."
    Just key -> do
        mActionKey <- runQuery pool $ AC.useActionKey (TL.toStrict key) AC.ConfirmRegistration
        case mActionKey of
          Nothing -> errorResponse "Invalid registration key or the registration has been already confirmed."
          Just actionKey -> do
            runQuery pool $ U.confirmRegistration (AC.ac_user_id actionKey)
            infoResponse $ "Registration has been successfuly completed. You may now " <> (H.a ! A.href (textValue $ T.pack Login.url) $ "log in") <> "."
