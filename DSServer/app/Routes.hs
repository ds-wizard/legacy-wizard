{-# LANGUAGE OverloadedStrings #-}

module Routes (routes) where

--import Data.HVect
import Web.Scotty (ScottyM, capture, middleware, get, post)
import qualified Network.Wai.Middleware.Static as M
import Network.Wai.Middleware.RequestLogger (logStdoutDev)

import App (PGPool)

import qualified Views.Pages.Main
import qualified Views.Forms.Registration
import qualified Views.Pages.ConfirmRegistration
import qualified Views.Forms.Login
import qualified API.Question.GetQuestion
import qualified API.Book.GetContents

routes :: PGPool -> ScottyM ()
routes pool = do
  middleware M.static
  middleware logStdoutDev
  get  (capture Views.Pages.Main.url) (Views.Pages.Main.handler pool)
  post (capture API.Question.GetQuestion.url) (API.Question.GetQuestion.handler pool)
  post (capture API.Book.GetContents.url) (API.Book.GetContents.handler pool)
  get  (capture Views.Forms.Registration.url) (Views.Forms.Registration.handler pool)
  post (capture Views.Forms.Registration.url) (Views.Forms.Registration.handler pool)
  get  (capture Views.Pages.ConfirmRegistration.url) (Views.Pages.ConfirmRegistration.handler pool)
  post (capture Views.Pages.ConfirmRegistration.url) (Views.Pages.ConfirmRegistration.handler pool)
  get  (capture Views.Forms.Login.url) (Views.Forms.Login.handler pool)
  post (capture Views.Forms.Login.url) (Views.Forms.Login.handler pool)
