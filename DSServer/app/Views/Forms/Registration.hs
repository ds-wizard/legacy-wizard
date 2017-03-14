{-# LANGUAGE OverloadedStrings, DataKinds #-}

module Views.Forms.Registration where

import Data.Monoid ((<>))
import Control.Monad.Trans (liftIO)
import Data.Text (Text)
import qualified Data.Text.Lazy as TL
import Text.Blaze.Html5 (Html, toHtml, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Text.Digestive ((.:))
import qualified Text.Digestive as D
import qualified Text.Digestive.Blaze.Html5 as DH
import Web.Spock (Path)
import qualified Web.Spock as W
import Web.Routing.Combinators (PathState(..))
import Web.Spock.Digestive (runForm)

import qualified Model.User as U
import qualified Persistence.User as U
import Mailing
import App (WizardAction)
import Views.Forms.Common (notEmpty, emailFormlet, passwordFormlet, addError, errorTr)
import qualified Views.Page as Page
import Views.Info (infoResponse, errorResponse)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

url :: Path '[] 'Open
url = "/registration"

data RegistrationRequest = RegistrationRequest
  { rr_email :: Text
  , rr_password :: Text
  ---, rr_password2 :: T.Text
  , rr_name :: Text
  , rr_affiliation :: Text
  } deriving (Show)

registrationForm :: Monad m => D.Form Html m RegistrationRequest
registrationForm =
  RegistrationRequest <$> "email" .: emailFormlet Nothing
  --                <*> "password1" .: passwordFormlet Nothing
  --                <*> "password2" .: passwordFormlet Nothing
                  <*> "password" .: passwordConfirmer
                  <*> "name" .: D.validate notEmpty (D.text Nothing)
                  <*> "affiliation" .: D.validate notEmpty (D.text Nothing)
    where
    passwordConfirmer =
      D.validate fst' $ (,) <$> ("p1" .: passwordFormlet Nothing)
                          <*> ("p2" .: passwordFormlet Nothing)
    fst' (p1, p2) | p1 == p2  = D.Success p1
                  | otherwise = D.Error "Passwords do not match"

formView :: D.View Html -> Html
formView v = do
  H.h2 "New User Registration"
  DH.form v (W.renderRoute url) $ do
    H.table ! A.class_ "form-table" $
      H.tbody $ do
        H.tr $ do
          H.td $ DH.label     "email" v "Email: "
          H.td $ DH.inputText "email" v
        errorTr "email" v
        H.tr $ do
          H.td $ DH.label     "password.p1" v "Password: "
          H.td $ DH.inputPassword "password.p1" v
        errorTr "password.p1" v
        H.tr $ do
          H.td $ DH.label     "password.p2" v "Repeat: "
          H.td $ DH.inputPassword "password.p2" v
        errorTr "password.p2" v
        errorTr "password" v
        H.tr $ do
          H.td $ DH.label     "name" v "Name: "
          H.td $ DH.inputText "name" v
        errorTr "name" v
        H.tr $ do
          H.td $ DH.label     "affiliation" v "Affiliation: "
          H.td $ DH.inputText "affiliation" v
        errorTr "affiliation" v
        H.tr $ do
          H.td mempty
          H.td $ H.button ! A.type_ "submit" $ "Register"


-- registerHandler :: (ListContains n IsGuest xs, NotInList (UserId, User) xs ~ 'True) => WizardAction (HVect xs) a
handler :: WizardAction ctx b a
handler = do
  res <- runForm "registrationForm" registrationForm
  case res of
    (v, Nothing) -> Page.render False (formView v) Page.NoMessage
    (v, Just regReq) -> do
      mExisting <- W.runQuery $ U.getUserByEmail $ U.Email $ TL.fromStrict $ rr_email regReq
      case mExisting of
        Just _ -> do
          let v2 = addError v "email" "Email already registered"
          Page.render False (formView v2) Page.NoMessage
        Nothing -> do
          let email = U.Email $ TL.fromStrict $ rr_email regReq
          userId <- W.runQuery $ U.createUser email (U.Password $ TL.fromStrict $ rr_password regReq) (rr_name regReq) (rr_affiliation regReq)
          mUser <- W.runQuery $ U.getUserById userId
          case mUser of
            Nothing -> errorResponse "Registration failed. Please contact the administrator."
            Just user -> do
              liftIO $ mailRegistrationConfirmation user
              infoResponse $ toHtml $ "Registration successful. A confirmation email has been sent to " <> rr_email regReq <> "."

