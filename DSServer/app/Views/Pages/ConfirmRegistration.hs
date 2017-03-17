{-# LANGUAGE OverloadedStrings #-}

module Views.Pages.ConfirmRegistration where

import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Data.Monoid ((<>))
import Text.Blaze.Html5 ((!), textValue)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Web.Scotty (ActionM, params)

import qualified Persistence.User as U

import App (PGPool, runQuery)
import Views.Info (infoResponse, errorResponse)
import qualified Views.Forms.Login

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

url :: String
url = "/confirmRegistration"

handler :: PGPool -> ActionM ()
handler pool = do
  ps <- params
  case lookup "key" ps of
    Nothing -> errorResponse "Registration confirmation failed: incorrect URL parameter."
    Just key -> do
        res <- runQuery pool $ U.confirmRegistration $ TL.toStrict key
        case res of
          U.InvalidRegistrationKey ->
            errorResponse "Registration confirmation failed: invalid registration key."
          U.UserAlreadyConfirmed ->
            infoResponse $ "Registration was already confirmed. You may " <> (H.a ! A.href (textValue $ T.pack Views.Forms.Login.url) $ "log in") <> "."
          U.UserOK ->
            infoResponse $ "Registration has been successfuly completed. You may now " <> (H.a ! A.href "/login" $ "log in") <> "."

