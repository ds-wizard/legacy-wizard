{-# LANGUAGE OverloadedStrings #-}

module Views.Forms.Login
  ( url
  , handler
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Text.Blaze.Html5 (Html, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Text.Digestive ((.:))
import qualified Text.Digestive as D
import qualified Text.Digestive.Blaze.Html5 as DH
import Text.Digestive.Scotty (runForm)
import Web.Scotty (ActionM)

import App (PGPool, runQuery)
import qualified Model.User as U
import qualified Persistence.User as U
import Persistence.Session (getSessionByUser)
import Views.Forms.Common (emailFormlet, passwordFormlet, addError, errorTr)
import Views.Info (infoResponse, errorResponse)
import qualified Views.Page as Page

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

url :: String
url = "/login"

data LoginRequest = LoginRequest
  { lr_email :: Text
  , lr_password :: Text
  } deriving (Show)

loginForm :: Monad m => D.Form Html m LoginRequest
loginForm =
  LoginRequest <$> "email" .: emailFormlet Nothing
                  <*> "password" .: passwordFormlet Nothing

formView :: D.View Html -> Html
formView v = do
 -- errorList "mail" view
  H.h2 "User Login"
  DH.form v (T.pack url) $ do
    H.table ! A.class_ "form-table" $
      H.tbody $ do
        H.tr $ do
          H.td $ DH.label     "email" v "Email: "
          H.td $ DH.inputText "email" v
        errorTr "email" v
        H.tr $ do
          H.td $ DH.label         "password" v "Password: "
          H.td $ DH.inputPassword "password" v
        errorTr "password" v
        H.tr $ do
          H.td mempty
          H.td $ H.button ! A.type_ "submit" $ "Login"


-- loginHandler :: (ListContains n IsGuest xs, NotInList (UserId, User) xs ~ 'True) => WizardAction (HVect xs) a
handler :: PGPool -> ActionM ()
handler pool = do
  f <- runForm "loginForm" loginForm
  case f of
    (v, Nothing) -> Page.render False (formView v) Page.NoMessage
    (v, Just loginReq) -> do
      mUser <- runQuery pool $ U.getUserByEmail (U.Email $ TL.fromStrict $ lr_email loginReq)
      case mUser of
        Nothing -> do
          let v2 = addError v "email" "Email not registered."
          Page.render False (formView v2) Page.NoMessage
        Just user -> do
          if not (U.u_registration_confirmed user) then do
            let v2 = addError v "email" "Email registration has not been confirmed."
            Page.render False (formView v2) Page.NoMessage
        -- todo
          else
            if not $ U.authUser (U.Password $ TL.fromStrict $ lr_password loginReq) user then do
              let v2 = addError v "password" "Incorrect password."
              Page.render False (formView v2) Page.NoMessage
            else do
              mSession <- runQuery pool $ getSessionByUser user
              case mSession of
                Nothing -> errorResponse "Session management failed. Please contact the administrator."
                Just session -> infoResponse "You are logged in."
