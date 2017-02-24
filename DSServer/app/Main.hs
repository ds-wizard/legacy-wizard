{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.Maybe (fromMaybe)
--import Data.HVect
import Control.Monad (join)
--import Control.Monad.IO.Class (MonadIO)
import Data.Text (Text, unpack)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Text.Blaze.Html.Renderer.Text (renderHtml)
import qualified Text.Blaze.Html5 as H
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
import Views.Forms.Registration (registrationForm, RegistrationRequest(..))

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
    W.get W.root $ W.html $ TL.toStrict $ renderHtml $ V.makePage V.Main
    W.getpost "api/getQuestion" getQuestionHandler
    W.getpost "api/getBookContents" getBookContentsHandler
  --  prehook guestOnlyHook $ do
    W.getpost "/registration" registrationHandler
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
      W.html $ TL.toStrict $ renderHtml $ V.makePage $ V.Registration (H.toHtml <$> view)
    (view, Just registrationReq) -> do
      mExisting <- W.runQuery $ U.getUserByEmail $ U.Email (rr_email registrationReq)
      case mExisting of
        Just _ -> do
          let view2 = addError view "email" "Email already registered"
          W.html $ TL.toStrict $ renderHtml $ V.makePage $ V.Registration (H.toHtml <$> view2)
          -- signalise the error
        Nothing -> do
          _ <- W.runQuery $ U.createUser (U.Email (rr_email registrationReq)) (U.Password (rr_password registrationReq)) (rr_name registrationReq) (rr_affiliation registrationReq)
          -- TODO: send confirmation email
          W.html $ TL.toStrict $ renderHtml $ V.makePage V.RegistrationSucc

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

