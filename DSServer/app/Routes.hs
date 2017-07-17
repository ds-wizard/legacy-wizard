module Routes (routes) where

--import Data.HVect
import Web.Scotty (ScottyM, capture, middleware, get, post)
import Web.Scotty.Cookie (getCookies)
import qualified Network.Wai.Middleware.Static as M
import Network.Wai.Middleware.RequestLogger (logStdoutDev)

import App (PGPool)

import qualified Actions.Main.Url
import qualified Actions.Main.Handler
import qualified Actions.Register.Url
import qualified Actions.Register.Handler
import qualified Actions.ConfirmRegistration.Url
import qualified Actions.ConfirmRegistration.Handler
import qualified Actions.Login.Url
import qualified Actions.Login.Handler
import qualified Actions.ForgottenPassword.Url
import qualified Actions.ForgottenPassword.Handler
import qualified Actions.ResetPassword.Url
import qualified Actions.ResetPassword.Handler
import qualified Actions.Logout.Url
import qualified Actions.Logout.Handler
import qualified Actions.Save.Url
import qualified Actions.Save.Handler
import qualified Actions.ManagePlans.Url
import qualified Actions.ManagePlans.Handler
import qualified Actions.EditProfile.Url
import qualified Actions.EditProfile.Handler
import qualified Actions.ChangePassword.Url
import qualified Actions.ChangePassword.Handler
import qualified API.Question.GetQuestion.Url
import qualified API.Question.GetQuestion.Handler
import qualified API.Book.GetContents.Url
import qualified API.Book.GetContents.Handler
import qualified API.Plan.GetData.Url
import qualified API.Plan.GetData.Handler

routes :: PGPool -> ScottyM ()
routes pool = do
  middleware M.static
  middleware logStdoutDev
  get  (capture Actions.Main.Url.url) (getCookies >>= Actions.Main.Handler.handler pool)
  get  (capture API.Question.GetQuestion.Url.url) (API.Question.GetQuestion.Handler.handler pool)
  post (capture API.Question.GetQuestion.Url.url) (API.Question.GetQuestion.Handler.handler pool)
  get  (capture API.Book.GetContents.Url.url) (API.Book.GetContents.Handler.handler pool)
  post (capture API.Book.GetContents.Url.url) (API.Book.GetContents.Handler.handler pool)
  post (capture API.Plan.GetData.Url.url) (getCookies >>= API.Plan.GetData.Handler.handler pool)
  get  (capture Actions.Register.Url.url) (Actions.Register.Handler.handler pool)
  post (capture Actions.Register.Url.url) (Actions.Register.Handler.handler pool)
  get  (capture Actions.ConfirmRegistration.Url.url) (Actions.ConfirmRegistration.Handler.handler pool)
  post (capture Actions.ConfirmRegistration.Url.url) (Actions.ConfirmRegistration.Handler.handler pool)
  get  (capture Actions.Login.Url.url) (Actions.Login.Handler.handler pool)
  post (capture Actions.Login.Url.url) (Actions.Login.Handler.handler pool)
  get  (capture Actions.ForgottenPassword.Url.url) (Actions.ForgottenPassword.Handler.handler pool)
  post (capture Actions.ForgottenPassword.Url.url) (Actions.ForgottenPassword.Handler.handler pool)
  get  (capture Actions.ResetPassword.Url.url) (Actions.ResetPassword.Handler.handler pool)
  post (capture Actions.ResetPassword.Url.url) (Actions.ResetPassword.Handler.handler pool)
  get  (capture Actions.Logout.Url.url) (getCookies >>= Actions.Logout.Handler.handler pool)
  post (capture Actions.Save.Url.url) (getCookies >>= Actions.Save.Handler.handler pool)
  get  (capture Actions.ManagePlans.Url.url) (getCookies >>= Actions.ManagePlans.Handler.handler pool)
  get  (capture Actions.EditProfile.Url.url) (getCookies >>= Actions.EditProfile.Handler.handler pool)
  post (capture Actions.EditProfile.Url.url) (getCookies >>= Actions.EditProfile.Handler.handler pool)
  get  (capture Actions.ChangePassword.Url.url) (getCookies >>= Actions.ChangePassword.Handler.handler pool)
  post (capture Actions.ChangePassword.Url.url) (getCookies >>= Actions.ChangePassword.Handler.handler pool)
