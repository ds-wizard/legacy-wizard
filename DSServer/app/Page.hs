{-# LANGUAGE OverloadedStrings #-}

module Page
  ( Message(..)
  , render
  ) where

--import Control.Monad.Trans (liftIO)
import Data.Monoid ((<>))
import qualified Data.Text as T
import Text.Blaze.Internal (textValue)
import Text.Blaze.Html5 (Html, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Text.Blaze.Html.Renderer.Text (renderHtml)
import qualified Web.Scotty as W
import App (Action)

import Config.Config (staticURL)
import Model.User (User(..))

import qualified Actions.Register.Url as Actions.Register
import qualified Actions.Login.Url as Actions.Login
import qualified Actions.Logout.Url as Actions.Logout
import qualified Actions.EditProfile.Url as Actions.EditProfile

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

data Message = InfoMessage Html | ErrorMessage Html | NoMessage

render :: Bool -> Html -> Maybe User -> Message -> Action
render isMain page mUser message = W.html $ renderHtml $
  H.docTypeHtml ! A.class_ "no-js" ! A.lang "" $ do
    renderHead
    H.body $
      H.div ! A.id "container" $ do
        renderLogin mUser
        H.div ! A.class_ "banner-bar" $ do
          renderBanner
          renderControlPanel mUser
        renderMessage message
        H.div ! A.class_ "inside" $
          page
        H.div ! A.id "overlay" ! A.class_ "overlay" $ H.div "overlay"
        renderFooter
        renderAcknowledgement
        if isMain then
          H.script ! A.src (textValue $ staticURL <> "js/main.js") $ mempty
        else
          mempty

renderHead :: Html
renderHead = H.head $ do
    H.meta ! A.charset "utf-8"
    H.meta ! A.httpEquiv "X-UA-Compatible" ! A.content "IE=edge"
    H.title "DS Wizard"
    H.meta ! A.name "viewport" ! A.content "width=device-width, initial-scale=1"
    H.link ! A.rel "stylesheet" ! A.href (textValue $ staticURL <> "css/normalize.min.css")
    H.link ! A.rel "stylesheet" ! A.href ( textValue $ staticURL <> "css/main.css")
    H.script ! A.src (textValue $ staticURL <> "js/vendor/jquery-3.1.1.min.js") $ mempty

renderLogin :: Maybe User -> Html
renderLogin mUser = H.div ! A.class_ "login-box" $ do
  case mUser of
    Just user -> do
      H.span $ H.a ! A.href (textValue $ T.pack Actions.EditProfile.url) $ H.toHtml $ u_name user
      _ <- " | "
      H.a ! A.href (textValue $ T.pack Actions.Logout.url) $ "Logout"
    Nothing -> do
      H.a ! A.href (textValue $ T.pack Actions.Login.url) $ "Login"
      _ <- " | "
      H.a ! A.href (textValue $ T.pack Actions.Register.url) $ "Register"

renderBanner :: Html
renderBanner = H.div ! A.id "banner" ! A.class_ "banner" $ do
  H.a ! A.href "https://www.elixir-europe.org/" $
    H.img ! A.src (textValue $ staticURL <> "img/logo.png") ! A.id "logo" ! A.alt "Elixir logo"
  H.h1 ! A.class_ "title" $ do
    _ <- "Data Stewardship Wizard"
    H.span ! A.class_ "version" $ " v0.5, "
    H.span ! A.class_ "version" $ " KM: Jan 19, 2017"

renderControlPanel :: Maybe User -> Html
renderControlPanel mUser =  H.div ! A.class_ "control-panel" $ do
  case mUser of
    Nothing -> mempty
    Just _ -> do
      H.button ! A.class_ "action-button" ! A.onclick "document.getElementById('form').submit();" $ "Save the plan"

renderMessage :: Message -> Html
renderMessage NoMessage = mempty
renderMessage (InfoMessage msg) = H.div ! A.class_ "bar message" $ msg
renderMessage (ErrorMessage msg) = H.div ! A.class_ "bar error" $ msg

renderFooter :: Html
renderFooter = H.div ! A.id "footer" ! A.class_ "stripe" $
  H.table ! A.class_ "footer-table" $ H.tbody $
    H.tr $ do
      H.td $ do
        H.h3 "Technical contacts"
        H.a ! A.href "mailto:robert.pergl@fit.cvut.cz" $ "Robert Pergl"
        H.br
        H.a ! A.href "mailto:suchama4@fit.cvut.cz" $ "Marek Suchánek"
      H.td ! A.style "text-align: center; " $ do
        H.h3 "Data stewardship action team"
        H.a ! A.href "http://elixir-czech.cz" $ H.img ! A.src (textValue $ staticURL <> "img/logo-elixir-cz.jpg") ! A.class_ "logo" ! A.alt "ELIXIR-CZ logo"
        H.a ! A.href "https://www.uochb.cz" $ H.img ! A.src (textValue $ staticURL <> "img/logo-uochb.png") ! A.class_ "logo" ! A.alt "FIT logo"
        H.a ! A.href "http://ccmi.fit.cvut.cz/en" $ H.img ! A.src (textValue $ staticURL <> "img/logo-ccmi.png") ! A.class_ "logo" ! A.alt "CCMi logo"
        H.a ! A.href "http://fit.cvut.cz/en" $ H.img ! A.src (textValue $ staticURL <> "img/logo-fit.png") ! A.class_ "logo" ! A.alt "FIT logo"
        H.a ! A.href "http://www.dtls.nl/elixir-nl/elixir-nl-2/" $ H.img ! A.src (textValue $ staticURL <> "img/logo-elixir-nl.png") ! A.class_ "logo" ! A.alt "ELIXIR-NL logo"
        H.a ! A.href "http://www.dtls.nl/" $ H.img ! A.src (textValue $ staticURL <> "img/logo-dtl.png") ! A.class_ "logo" ! A.alt "DTL logo"
      H.td $ do
        H.h3 "Links"
        H.a ! A.href "http://www.elixir-europe.org/" $ "ELIXIR Europe"
        H.br
        H.a ! A.href "http://www.elixir-europe.org/about/elixir-nodes" $ "ELIXIR Nodes"

renderAcknowledgement :: Html
renderAcknowledgement =
  H.div ! A.class_ "colophon-box" $ do
    H.p ! A.class_ "colophon-line" $ do
      H.span ! A.class_ "colophon-text" $ "Crafted with "
      H.a ! A.href "https://www.haskell.org/ghc/" ! A.class_ "colophon-text" $ "GHC"
      H.span ! A.class_ "colophon-text" $ " & "
      H.a ! A.href "http://haste-lang.org/" ! A.class_ "colophon-text" $ "Haste"
      H.span ! A.class_ "colophon-text" $ ", powered by "
      H.a ! A.href "http://hackage.haskell.org/package/scotty" ! A.class_ "colophon-text" $ "Scotty"
      H.img ! A.src (textValue $ staticURL <> "img/haskell.png") ! A.alt "Haskell logo" ! A.class_ "logo"


