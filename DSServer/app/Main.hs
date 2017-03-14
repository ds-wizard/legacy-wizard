{-# LANGUAGE OverloadedStrings #-}

module Main where

--import Data.HVect
import qualified Web.Spock as W
import qualified Web.Spock.Config as WC
import qualified Network.Wai.Middleware.Static as M
import Network.Wai.Middleware.RequestLogger (logStdoutDev)
--import Data.Pool
import qualified Database.PostgreSQL.Simple as PG

--import Config.Config (baseURL)
import Config.Server.Config (port, pgCreds)

import qualified Views.Pages.Main
import qualified Views.Forms.Registration
import qualified Views.Pages.ConfirmRegistration
import qualified API.Question.GetQuestion
import qualified API.Book.GetContents

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
    W.get Views.Pages.Main.url Views.Pages.Main.handler
    W.getpost API.Question.GetQuestion.url API.Question.GetQuestion.handler
    W.getpost API.Book.GetContents.url API.Book.GetContents.handler
  --  prehook guestOnlyHook $ do
    W.getpost Views.Forms.Registration.url Views.Forms.Registration.handler
    W.getpost Views.Pages.ConfirmRegistration.url Views.Pages.ConfirmRegistration.handler
   -- prehook authHook $
   --  get "/logout" logoutHandler

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



