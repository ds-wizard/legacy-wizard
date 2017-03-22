{-# LANGUAGE OverloadedStrings #-}

module Actions.ave.Handler
  ( url
  , handler
  ) where

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
import Persistence.Plan (createPlan)
import Mailing
import Actions.FormUtils (notEmpty, emailFormlet, passwordFormlet, addError, errorTr)
import qualified Page
import Actions.Responses (infoResponse, errorResponse)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

url :: String
url = "/profile"

data ProfileData = ProfileData
  { pd_email :: Text
  , pd_name :: Text
  , pd_affiliation :: Text
  } deriving (Show)

registrationForm :: Monad m => D.Form Html m ProfileData
registrationForm =
  ProfileData <$> "email" .: emailFormlet Nothing
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
          H.td $ DH.label     "name" v "Name: "
          H.td $ DH.inputText "name" v
        errorTr "name" v
        H.tr $ do
          H.td $ DH.label     "affiliation" v "Affiliation: "
          H.td $ DH.inputText "affiliation" v
        errorTr "affiliation" v
        H.tr $ do
          H.td mempty
          H.td $ H.button ! A.type_ "submit" $ "ave"

-- registerHandler :: (ListContains n IsGuest xs, NotInList (UserId, User) xs ~ 'True) => WizardAction (HVect xs) a
handler :: PGPool -> Action
handler pool = do
  f <- runForm "registrationForm" registrationForm
  case f of
    (v, Nothing) -> Page.render False (formView v) Nothing Page.NoMessage
    (v, Just regReq) -> do
      mExisting <- runQuery pool $ U.getUserByEmail $ U.Email $ TL.fromStrict $ pd_email regReq
      case mExisting of
        Just _ -> do
          let v2 = addError v "email" "Email already registered"
          Page.render False (formView v2) Nothing Page.NoMessage
        Nothing -> do
          let email = U.Email $ TL.fromStrict $ pd_email regReq
          userId <- runQuery pool $ U.createUser email (U.Password $ TL.fromStrict $ pd_password regReq) (pd_name regReq) (pd_affiliation regReq)
          mUser <- runQuery pool $ U.getUserById userId
          case mUser of
            Nothing -> errorResponse "Registration failed. Please contact the administrator."
            Just user -> do
              _ <- runQuery pool $ createPlan user "Default" (Just "Automatically created plan")
              liftIO $ mailRegistrationConfirmation user
              infoResponse $ toHtml $ "Registration successful. A confirmation email has been sent to " <> pd_email regReq <> "."

