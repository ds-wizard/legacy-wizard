{-# LANGUAGE OverloadedStrings #-}

module Actions.ChangePassword.Handler (handler) where

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
import Actions.FormUtils (passwordConfirmer, errorTr)
import qualified Page
import Actions.ChangePassword.Url (url)
import Actions.Responses (infoResponse)

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}
{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

newtype ChangePasswordRequest = ChangePasswordRequest { chp_password :: Text } deriving (Show)

changePasswordForm :: Monad m => D.Form Html m ChangePasswordRequest
changePasswordForm = ChangePasswordRequest <$> "password" .: passwordConfirmer

formView :: D.View Html -> Html
formView v = do
  H.h2 "Password change"
  DH.form v (T.pack url) $ do
    H.table ! A.class_ "form-table" $
      H.tbody $ do
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
          H.td mempty
          H.td $ do
            H.button ! A.type_ "submit" ! A.style "margin-right: 15px;" $ "Change password"
            H.button ! A.type_ "button" ! A.onclick "window.location.href='/'" $ "Cancel"

handler :: PGPool -> Cookies -> Action
handler pool cookies = checkLogged pool cookies (\user -> do
  f <- runForm "changePasswordForm" changePasswordForm
  case f of
    (v, Nothing) -> Page.render (formView v) Page.defaultPageConfig { Page.pc_mUser = Just user }
    (_, Just changePasswordReq) -> do
      _ <- runQuery pool $ U.changePassword user (Password $ TL.fromStrict $ chp_password changePasswordReq)
      infoResponse "Your password has been changed."
  )

