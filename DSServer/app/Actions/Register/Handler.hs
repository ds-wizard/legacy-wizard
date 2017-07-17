{-# LANGUAGE OverloadedStrings #-}

module Actions.Register.Handler (handler) where

import Data.Monoid ((<>))
import Control.Monad.Trans (liftIO)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Text.Blaze.Html5 (Html, toHtml, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Text.Digestive ((.:))
import qualified Text.Digestive as D
import qualified Text.Digestive.Blaze.Html5 as DH
import Text.Digestive.Scotty (runForm)

import App (Action, PGPool, runQuery)
import qualified Model.User as U
import qualified Persistence.User as U
import qualified Model.ActionKey as AC
import qualified Persistence.ActionKey as AC
import Persistence.Plan (createPlan)
import Mailing
import Actions.FormUtils (notEmpty, emailFormlet, passwordConfirmer, addError, errorTr)
import qualified Page
import Actions.Register.Url (url)
import qualified Actions.ConfirmRegistration.Url as Actions.ConfirmRegistration
import Actions.Responses (infoResponse, errorResponse)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

data RegistrationRequest = RegistrationRequest
  { rr_email :: Text
  , rr_password :: Text
  , rr_name :: Text
  , rr_affiliation :: Text
  } deriving (Show)

registrationForm :: Monad m => D.Form Html m RegistrationRequest
registrationForm =
  RegistrationRequest <$> "email" .: emailFormlet Nothing
                      <*> "password" .: passwordConfirmer
                      <*> "name" .: D.validate notEmpty (D.text Nothing)
                      <*> "affiliation" .: D.validate notEmpty (D.text Nothing)

formView :: D.View Html -> Html
formView v = do
  H.h2 "New User Registration"
  DH.form v (T.pack url) $ do
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
handler :: PGPool -> Action
handler pool = do
  f <- runForm "registrationForm" registrationForm
  case f of
    (v, Nothing) -> Page.render (formView v) Page.defaultPageConfig
    (v, Just regReq) -> do
      mExisting <- runQuery pool $ U.getUserByEmail $ U.Email $ TL.fromStrict $ rr_email regReq
      case mExisting of
        Just _ -> do
          let v2 = addError v "email" "Email already registered"
          Page.render (formView v2) Page.defaultPageConfig
        Nothing -> do
          let email = U.Email $ TL.fromStrict $ rr_email regReq
          userId <- runQuery pool $ U.createUser email (U.Password $ TL.fromStrict $ rr_password regReq) (rr_name regReq) (rr_affiliation regReq)
          mUser <- runQuery pool $ U.getUserById userId
          case mUser of
            Nothing -> errorResponse "Registration failed. Please contact the administrator."
            Just user -> do
              actionKeyKey <- runQuery pool $ AC.createActionKey user AC.ConfirmRegistration
              _ <- runQuery pool $ createPlan user "Default" (Just "Automatically created plan")
              liftIO $ mailRegistrationConfirmation user Actions.ConfirmRegistration.url actionKeyKey
              infoResponse $ toHtml $ "Registration successful. A confirmation email has been sent to " <> rr_email regReq <> "."

