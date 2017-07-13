{-# LANGUAGE OverloadedStrings, NamedFieldPuns, RecordWildCards #-}

module Mailing where

import qualified Data.Text.Lazy as T
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

mailRegistrationConfirmation :: User -> ActionKeyKey -> IO ()
mailRegistrationConfirmation User{ u_email, u_name, .. } key =
  let
    from = Address (Just "DS Wizard") "info@dmp.fairdata.solutions"
    body = htmlPart $ renderHtml $ message u_name (T.pack $ show key)
    mail = simpleMail from [Address Nothing (T.toStrict $ runEmail u_email)] [] [] "Registration confirmation" [body]
  in
    renderSendMail mail

message :: T.Text -> T.Text -> Html
message name registrationKey = H.docTypeHtml $ do
  H.head $ do
    H.meta ! A.charset "utf-8"
    H.title "DS Wizard registration confirmation"
  H.body $ do
    H.p $ "Dear " <> toHtml name <> ","
    H.p $ do
      _ <- "you have registered in "
      H.a ! A.href ("http://" <>  textValue domainURL) $ "Data Stewardship Wizard."
    H.p "Please confirm your registration by clicking the link: "
    H.p $ H.a ! A.href ("http://" <> textValue domainURL <> "/confirmRegistration?key=" <> textValue (T.toStrict registrationKey)) $
      "http://" <> toHtml domainURL <> "/confirmRegistration?key="<> toHtml (T.toStrict registrationKey)
