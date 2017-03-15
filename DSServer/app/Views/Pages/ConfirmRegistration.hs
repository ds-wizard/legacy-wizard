{-# LANGUAGE OverloadedStrings, DataKinds #-}

module Views.Pages.ConfirmRegistration where

import Data.Monoid ((<>))
import Text.Blaze.Html5 ((!), textValue)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Web.Spock (Path)
import qualified Web.Spock as W
import Web.Routing.Combinators (PathState(..))

import qualified Persistence.User as U

import App (WizardAction)
import Views.Info (infoResponse, errorResponse)
import qualified Views.Forms.Login

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

url :: Path '[] 'Open
url = "/confirmRegistration"

handler :: WizardAction ctx b a
handler = do
  ps <- W.params
  case lookup "key" ps of
    Nothing -> errorResponse "Registration confirmation failed: incorrect URL parameter."
    Just key -> do
        res <- W.runQuery $ U.confirmRegistration key
        case res of
          U.InvalidRegistrationKey ->
            errorResponse "Registration confirmation failed: invalid registration key."
          U.UserAlreadyConfirmed ->
            infoResponse $ "Registration was already confirmed. You may " <> (H.a ! A.href (textValue $ W.renderRoute Views.Forms.Login.url) $ "log in") <> "."
          U.UserOK ->
            infoResponse $ "Registration has been successfuly completed. You may now " <> (H.a ! A.href "/login" $ "log in") <> "."

