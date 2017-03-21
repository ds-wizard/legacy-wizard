{-# LANGUAGE OverloadedStrings #-}

module Routes (routes) where

--import Data.HVect
import Web.Scotty (ScottyM, capture, middleware, get, post)
import Web.Scotty.Cookie (getCookies)
import qualified Network.Wai.Middleware.Static as M
import Network.Wai.Middleware.RequestLogger (logStdoutDev)

import App (PGPool)

import qualified Actions.Main.Handler
import qualified Actions.Registration.Handler
import qualified Actions.ConfirmRegistration.Handler
import qualified Actions.Login.Handler
import qualified Actions.Logout.Handler
import qualified API.Question.GetQuestion.Handler
import qualified API.Book.GetContents.Handler

routes :: PGPool -> ScottyM ()
routes pool = do
  middleware M.static
  middleware logStdoutDev
  get  (capture Actions.Main.Handler.url) (getCookies >>= Actions.Main.Handler.handler pool)
  post (capture API.Question.GetQuestion.Handler.url) (API.Question.GetQuestion.Handler.handler pool)
  post (capture API.Book.GetContents.Handler.url) (API.Book.GetContents.Handler.handler pool)
  get  (capture Actions.Registration.Handler.url) (Actions.Registration.Handler.handler pool)
  post (capture Actions.Registration.Handler.url) (Actions.Registration.Handler.handler pool)
  get  (capture Actions.ConfirmRegistration.Handler.url) (Actions.ConfirmRegistration.Handler.handler pool)
  post (capture Actions.ConfirmRegistration.Handler.url) (Actions.ConfirmRegistration.Handler.handler pool)
  get  (capture Actions.Login.Handler.url) (Actions.Login.Handler.handler pool)
  post (capture Actions.Login.Handler.url) (Actions.Login.Handler.handler pool)
  get  (capture Actions.Logout.Handler.url) (getCookies >>= Actions.Logout.Handler.handler pool)
