{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.Monoid ((<>))
import Data.Maybe (fromMaybe)
--import Data.HVect
import Control.Monad (join)
import Control.Monad.Trans (liftIO)
--import Control.Monad.IO.Class (MonadIO)
import Data.Text (Text, unpack)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Text.Blaze.Html.Renderer.Text (renderHtml)
import Text.Blaze.Html5 (Html, (!), toHtml)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import qualified Web.Spock as W
import qualified Web.Spock.Config as WC
import Text.Digestive.Types (toPath)
import Text.Digestive.View (View(..))
import Web.Spock.Digestive (runForm)
import qualified Network.Wai.Middleware.Static as M
import Network.Wai.Middleware.RequestLogger (logStdoutDev)
--import Data.Pool
import qualified Database.PostgreSQL.Simple as PG

--import Config.Config (baseURL)
import Config.Server.Config (port, pgCreds)

import Persistence.Question (getQuestion, getBookContents)
import qualified Model.User as U
import qualified Persistence.User as U
import qualified Model.Session as S
import qualified Persistence.Session as S
import qualified Views.Base as V
import qualified Views.Pages.Info as V
import Views.Forms.Registration (registrationForm, RegistrationRequest(..))
import Mailing

type SessionVal = Maybe W.SessionId
type WizardAction ctx b a = W.ActionCtxT ctx (W.WebStateM PG.Connection b ()) a

poolCfg :: WC.PoolCfg
poolCfg = WC.PoolCfg 50 50 60

pcconn :: WC.ConnBuilder PG.Connection
pcconn = WC.ConnBuilder (PG.connect pgCreds) PG.close poolCfg

dbConn :: WC.PoolOrConn PG.Connection
dbConn = WC.PCConn pcconn

main :: IO ()
main = do
  cfg <- WC.defaultSpockCfg WC.defaultSessionCfg dbConn ()
  W.runSpock port $ W.spock cfg $ do
    W.middleware M.static
    W.middleware logStdoutDev
    W.get W.root $ W.html $ TL.toStrict $ renderHtml $ V.makePage V.Main V.NoMessage
    W.getpost "api/getQuestion" getQuestionHandler
    W.getpost "api/getBookContents" getBookContentsHandler
  --  prehook guestOnlyHook $ do
    W.getpost "/registration" registrationHandler
    W.getpost "/confirmRegistration" confirmRegistrationHandler
    --  getpost "/login" loginHandler
   -- prehook authHook $
   --  get "/logout" logoutHandler

-- * Utils

readInt :: Text -> Maybe Int
readInt str
  | Prelude.length readChid /= 1 = Nothing
  | otherwise = if not $ Prelude.null $ snd $ Prelude.head readChid
     then Nothing
     else Just $ fst $ Prelude.head readChid
  where
    readChid = reads (unpack str) :: [(Int, String)]

infoResponse :: Html ->  WizardAction ctx b a
infoResponse msg = W.html $ TL.toStrict $ renderHtml $ V.makePage (V.InfoPage V.OKInfo msg) V.NoMessage

errorResponse :: Html ->  WizardAction ctx b a
errorResponse msg = W.html $ TL.toStrict $ renderHtml $ V.makePage (V.InfoPage V.ErrorInfo msg) V.NoMessage

-- * Authentication

-- authHook :: WizardAction (HVect xs) (HVect ((UserId, User) ': xs))
-- authHook =
--     maybeUser $ \mUser ->
--     do oldCtx <- getContext
--        case mUser of
--          Nothing ->
--              noAccessPage "Unknown user. Login first!"
--          Just val ->
--              return (val :&: oldCtx)

-- * Handlers

getQuestionHandler :: WizardAction ctx b a
getQuestionHandler = do
  ps <- W.params
  case join $ readInt <$> lookup "chid" ps of
    Nothing -> W.text "Missing chid"
    Just chid ->
      case join $ readInt <$> lookup "qid" ps of
        Nothing -> W.text "Missing qid"
        Just qid -> do
          maybeQuestion <- W.runQuery $ getQuestion chid qid
          W.text $ fromMaybe "" $ (T.pack . show) <$> maybeQuestion

getBookContentsHandler :: WizardAction ctx b a
getBookContentsHandler = do
  ps <- W.params
  case join $ readInt <$> lookup "chid" ps of
    Nothing -> W.text "Missing chid"
    Just chid ->
      case join $ readInt <$> lookup "qid" ps of
        Nothing -> W.text "Missing qid"
        Just qid -> do
          maybeText <- W.runQuery $ getBookContents chid qid
          W.text $ fromMaybe "" maybeText

-- ** User management

addError :: View v -> Text -> v -> View v
addError view ref err = view { viewErrors = viewErrors2}
  where
  viewErrors2 = viewErrors view ++ [(toPath ref, err)]

-- registerHandler :: (ListContains n IsGuest xs, NotInList (UserId, User) xs ~ 'True) => WizardAction (HVect xs) a
registrationHandler :: WizardAction ctx b a
registrationHandler = do
  res <- runForm "registrationForm" registrationForm
  case res of
    (view, Nothing) ->
      W.html $ TL.toStrict $ renderHtml $ V.makePage (V.Registration (toHtml <$> view)) V.NoMessage
    (view, Just regReq) -> do
      mExisting <- W.runQuery $ U.getUserByEmail $ U.Email $ TL.fromStrict $ rr_email regReq
      case mExisting of
        Just _ -> do
          let view2 = addError view "email" "Email already registered"
          W.html $ TL.toStrict $ renderHtml $ V.makePage (V.Registration (toHtml <$> view2)) V.NoMessage
        Nothing -> do
          let email = U.Email $ TL.fromStrict $ rr_email regReq
          userId <- W.runQuery $ U.createUser email (U.Password $ TL.fromStrict $ rr_password regReq) (rr_name regReq) (rr_affiliation regReq)
          mUser <- W.runQuery $ U.getUserById userId
          case mUser of
            Nothing -> errorResponse "Registration failed. Please contact the administrator."
            Just user -> do
              liftIO $ mailRegistrationConfirmation user
              infoResponse $ toHtml $ "Registration successful. A confirmation email has been sent to " <> rr_email regReq <> "."

confirmRegistrationHandler :: WizardAction ctx b a
confirmRegistrationHandler = do
  ps <- W.params
  case lookup "key" ps of
    Nothing -> errorResponse "Registration confirmation failed: incorrect URL parameter."
    Just key -> do
        res <- W.runQuery $ U.confirmRegistration key
        case res of
          U.InvalidRegistrationKey ->
            errorResponse "Registration confirmation failed: invalid registration key."
          U.UserAlreadyConfirmed ->
            infoResponse $ "Registration was already confirmed. You may " <> (H.a ! A.href "/login" $ "log in") <> "."
          U.UserOK ->
            infoResponse $ "Registration has been successfuly completed. You may now " <> (H.a ! A.href "/login" $ "log in") <> "."


-- loginHandler :: (ListContains n IsGuest xs, NotInList (UserId, User) xs ~ 'True) => WizardAction (HVect xs) a
-- loginHandler =
--     do f <- runForm "loginForm" loginForm
--        let formView mErr view =
--                panelWithErrorView "Login" mErr $ renderForm loginFormSpec view
--        case f of -- (View, Maybe LoginRequest)
--          (view, Nothing) ->
--              mkSite' (formView Nothing view)
--          (view, Just loginReq) ->
--              do loginRes <-
--                     runQuery $ loginUser (lr_user loginReq) (lr_password loginReq)
--                 case loginRes of
--                   Just userId ->
--                       do sid <- runQuery $ createSession userId
--                          writeSession (Just sid)
--                          redirect "/"
--                   Nothing ->
--                       mkSite' (formView (Just "Invalid login credentials!") view)

