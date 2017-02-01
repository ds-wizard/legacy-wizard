{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.Monoid ((<>))
import Data.Maybe (fromMaybe)
import Data.HVect
import Control.Monad (join)
import Control.Monad.IO.Class (MonadIO)
import Data.Text (Text, unpack)
import qualified Data.Text.Lazy as T
import Text.Blaze.Html.Renderer.Text (renderHtml)
import qualified Text.Blaze.Html5 as H
import Web.Spock as W
import Web.Spock.Config as WC
import DigestiveForm (runForm)
import Network.Wai.Middleware.Static as M
import Network.Wai.Middleware.RequestLogger
import Data.Pool
import qualified Database.PostgreSQL.Simple as PG

import Config.Config (baseURL)
import Config.Server.Config (port, pgCreds)

import PageGenerator (renderPage)
import Model.Question
import Persistence.Question (getQuestion, getBookContents)
import Views.Forms.Register (registerForm, registerView, RegisterRequest(..))

type SessionVal = Maybe SessionId
type WizardAction ctx b a = ActionCtxT ctx (WebStateM PG.Connection b ()) a

poolCfg :: WC.PoolCfg
poolCfg = WC.PoolCfg 50 50 60

pcconn :: WC.ConnBuilder PG.Connection
pcconn = WC.ConnBuilder (PG.connect pgCreds) PG.close poolCfg

dbConn :: WC.PoolOrConn PG.Connection
dbConn = WC.PCConn pcconn

main :: IO ()
main = do
  cfg <- WC.defaultSpockCfg WC.defaultSessionCfg dbConn ()
  runSpock port $ spock cfg $
    subcomponent "/" $ do
      middleware M.static
      middleware logStdoutDev
      get root rootHandler
      getpost "api/getQuestion" getQuestionHandler
      getpost "api/getBookContents" getBookContentsHandler
    --  prehook guestOnlyHook $ do
      getpost "/register" registerHandler
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

rootHandler :: WizardAction ctx b a
rootHandler = W.html $ T.toStrict $ renderHtml renderPage

getQuestionHandler :: WizardAction ctx b a
getQuestionHandler = do
  ps <- params
  case join $ readInt <$> lookup "chid" ps of
    Nothing -> W.text "Missing chid"
    Just chid ->
      case join $ readInt <$> lookup "qid" ps of
        Nothing -> W.text "Missing qid"
        Just qid -> do
          maybeQuestion <- runQuery $ getQuestion chid qid
          W.text $ T.toStrict $ fromMaybe "" $ (T.pack . show) <$> maybeQuestion

getBookContentsHandler :: WizardAction ctx b a
getBookContentsHandler = do
  ps <- params
  case join $ readInt <$> lookup "chid" ps of
    Nothing -> W.text "Missing chid"
    Just chid ->
      case join $ readInt <$> lookup "qid" ps of
        Nothing -> W.text "Missing qid"
        Just qid -> do
          maybeText <- runQuery $ getBookContents chid qid
          W.text $ fromMaybe "" maybeText

-- ** User management

-- registerHandler :: (ListContains n IsGuest xs, NotInList (UserId, User) xs ~ 'True) => WizardAction (HVect xs) a
registerHandler :: WizardAction ctx b a
registerHandler = do
  res <- runForm "registerForm" registerForm
  case res of
    (view, Nothing) -> do
      let view' = fmap H.toHtml view
      W.html $ T.toStrict $ renderHtml (registerView view')
    (view, Just registerReq) ->
        if rr_password registerReq /= rr_passwordConfirm registerReq
        then W.text "passwords do not match"
        else W.text "registering"
        --else do registerRes <-
        --          runQuery $ createUser (rr_email registerReq) (rr_password registerReq) (rr_name registerReq) (rr_affiliation registerReq)

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

