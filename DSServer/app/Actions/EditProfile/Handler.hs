{-# LANGUAGE OverloadedStrings #-}

module Actions.EditProfile.Handler
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

import App (Action, PGPool, Cookies, runQuery)
import Auth (checkLogged)
import Model.User
import qualified Persistence.User as U
import Actions.FormUtils (notEmpty, emailFormlet, addError, errorTr)
import qualified Page
import Actions.Responses (infoResponse)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

url :: String
url = "/editProfile"

data ProfileData = ProfileData
  { pd_email :: Text
  , pd_name :: Text
  , pd_affiliation :: Text
  } deriving (Show)

profileForm :: Monad m => User -> D.Form Html m ProfileData
profileForm user =
  ProfileData <$> "email" .: emailFormlet (Just $ TL.toStrict $ runEmail $ u_email user)
              <*> "name" .: D.validate notEmpty (D.text $ Just $ TL.toStrict $ u_name user)
              <*> "affiliation" .: D.validate notEmpty (D.text $ Just $ TL.toStrict $ u_affiliation user)

formView :: D.View Html -> Html
formView v = do
  H.h2 "Profile update"
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
          H.td $ do
            H.button ! A.type_ "submit" ! A.style "margin-right: 15px;" $ "Save"
            H.button ! A.type_ "button" ! A.onclick "window.location.href='/'" $ "Cancel"

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLogged pool cookies (\user -> do
  f <- runForm "profileForm" $ profileForm user
  case f of
    (v, Nothing) -> Page.render False (formView v) (Just user) Page.NoMessage
    (v, Just profileData) -> do
      let email = Email $ TL.fromStrict $ pd_email profileData
      isExisting <- runQuery pool $ U.isExistingEmail user email
      if isExisting then do
        let v2 = addError v "email" "Email already taken"
        Page.render False (formView v2) (Just user) Page.NoMessage
      else do
        _ <- runQuery pool $ U.updateUser user email (pd_name profileData) (pd_affiliation profileData)
        infoResponse "Your profile has been updated."
  )

