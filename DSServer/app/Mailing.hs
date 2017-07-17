{-# LANGUAGE OverloadedStrings, NamedFieldPuns, RecordWildCards #-}

module Mailing where

import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Data.Monoid ((<>))
import Network.Mail.SMTP
import Text.Blaze.Html5 (Html, (!), toHtml)
import Text.Blaze.Internal (textValue)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Text.Blaze.Html.Renderer.Text (renderHtml)

import Config.Config (domainURL)
import Model.User
import Model.ActionKey

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

fromAddr :: Address
fromAddr = Address (Just "DS Wizard") "info@dmp.fairdata.solutions"

fullUrl :: String -> T.Text -> T.Text
fullUrl actionUrl actionKey = "http://" <> T.pack domainURL <> T.pack actionUrl <> "?key=" <> actionKey

mailRegistrationConfirmation :: User -> String -> ActionKeyKey -> IO ()
mailRegistrationConfirmation User{ u_email, u_name, .. } actionUrl actionKey = let
  body = htmlPart $ renderHtml message
  mail = simpleMail fromAddr [Address Nothing (TL.toStrict $ runEmail u_email)] [] [] "Registration confirmation" [body]
  in renderSendMail mail
  where
    message :: Html
    message = H.docTypeHtml $ do
      H.head $ do
        H.meta ! A.charset "utf-8"
        H.title "DS Wizard registration confirmation"
      H.body $ do
        H.p $ toHtml $ "Dear " <> u_name <> ","
        H.p $ do
          _ <- "you have registered in "
          H.a ! A.href (textValue $ T.pack $ "http://" <> domainURL) $ "Data Stewardship Wizard."
        H.p "Please confirm your registration by clicking the link: "
        H.p $ H.a ! A.href (textValue $ fullUrl actionUrl actionKey) $ toHtml $ fullUrl actionUrl actionKey

mailResetPasswordLink :: User -> String -> ActionKeyKey -> IO ()
mailResetPasswordLink User{ u_email, u_name, .. } actionUrl actionKey = let
  body = htmlPart $ renderHtml message
  mail = simpleMail fromAddr [Address Nothing (TL.toStrict $ runEmail u_email)] [] [] "Password reset" [body]
  in renderSendMail mail
  where
    message :: Html
    message = H.docTypeHtml $ do
      H.head $ do
        H.meta ! A.charset "utf-8"
        H.title "DS Wizard account password reset"
      H.body $ do
        H.p $ toHtml $ "Dear " <> u_name <> ","
        H.p $ do
          _ <- "you have requested to reset your password in the "
          H.a ! A.href (textValue $ T.pack $ "http://" <> domainURL) $ "Data Stewardship Wizard."
        H.p "You may do so by following this link: "
        H.p $ H.a ! A.href (textValue $ fullUrl actionUrl actionKey) $ toHtml $ fullUrl actionUrl actionKey
        H.p "Please note that this link expires in 24 hours."
