{-# LANGUAGE OverloadedStrings #-}

module Page
  ( Message(..)
  , PageConfig(..)
  , defaultPageConfig
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
import Model.Plan (Plan(..))

import qualified Actions.Main.Url as Actions.Main
import qualified Actions.Register.Url as Actions.Register
import qualified Actions.Login.Url as Actions.Login
import qualified Actions.Logout.Url as Actions.Logout
import qualified Actions.EditProfile.Url as Actions.EditProfile
import qualified Actions.ManagePlans.Url as Actions.ManagePlans

import qualified Bridge as B

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}
{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

data Message = InfoMessage Html | ErrorMessage Html | NoMessage

data PageConfig = PageConfig
  { pc_isMain :: Bool
  , pc_mUser :: Maybe User
  , pc_mPlan :: Maybe Plan
  }

defaultPageConfig :: PageConfig
defaultPageConfig = PageConfig { pc_isMain = False, pc_mUser = Nothing, pc_mPlan = Nothing }

render :: Html -> PageConfig -> Action
render page pConfig = W.html $ renderHtml $
  H.docTypeHtml ! A.class_ "no-js" ! A.lang "" $ do
    renderHead
    H.body $
      H.div ! A.id "container" $ do
        renderLogin (pc_mUser pConfig)
        H.div ! A.class_ "banner-bar" $ do
          renderBanner
        if pc_isMain pConfig then renderControlPanel pConfig else mempty
        renderMessageBars
        H.div ! A.class_ "inside" $
          page
        H.div ! A.id "overlay" ! A.class_ "overlay" $ H.div "overlay"
        renderFooter
        renderAcknowledgement
        --if pc_isMain pConfig then
        H.script ! A.src (textValue $ T.pack staticURL <> "js/main.js") $ mempty
        --else
        --  mempty
        H.script ! A.src (textValue $ T.pack staticURL <> "js/analytics.js") $ mempty

renderHead :: Html
renderHead = H.head $ do
    H.meta ! A.charset "utf-8"
    H.meta ! A.httpEquiv "X-UA-Compatible" ! A.content "IE=edge"
    H.title "DS Wizard"
    H.meta ! A.name "viewport" ! A.content "width=device-width, initial-scale=1"
    H.link ! A.rel "stylesheet" ! A.href (textValue $ T.pack staticURL <> "css/normalize.min.css")
    H.link ! A.rel "stylesheet" ! A.href ( textValue $ T.pack staticURL <> "css/main.css")
    H.script ! A.src (textValue $ T.pack staticURL <> "js/vendor/jquery-3.1.1.min.js") $ mempty
    H.script ! A.src (textValue $ T.pack staticURL <> "js/vendor/js.cookie-2.1.4.min.js") $ mempty

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
  H.div ! A.class_ "banner-element" $
    H.a ! A.href (textValue $ T.pack Actions.Main.url) $
      H.img ! A.class_ "dsplogo" ! A.src (textValue $ T.pack staticURL <> "img/DSP-logo.png") ! A.alt "DSP logo"
  H.div ! A.class_ "banner-element" $ do
    H.h1 ! A.class_ "title" $ do
      _ <- "Data Stewardship Wizard"
      H.span ! A.class_ "version" $ " v0.9, "
      H.span ! A.class_ "version" $ " KM: Jan 19, 2017"
    H.div ! A.class_ "subtitle" $ "Data Management Plans for FAIR Open Science"

renderControlPanel :: PageConfig -> Html
renderControlPanel pConfig = case pc_mUser pConfig of
    Nothing -> mempty
    Just _ -> do
      H.div ! A.class_ "control-panel" $ do
        case pc_mPlan pConfig of
          Just plan -> do
            H.div ! A.class_ "control-panel-label" $ do
              _ <- "Plan: "
              H.a ! A.href (textValue $ T.pack Actions.ManagePlans.url) $ H.toHtml $ p_name plan
            H.button ! A.class_ "action-button" ! A.onclick (textValue $ T.pack $ B.call0 B.SavePlan) $
              H.img ! A.class_ "action-icon" ! A.src (textValue $ T.pack staticURL <> "img/save.png") ! A.alt "Save the plan"
          Nothing -> do
            H.div ! A.class_ "control-panel-label no-plan" $ "No plan opened"
            H.button ! A.class_ "action-button action-button-disabled" $
              H.img ! A.class_ "action-icon action-icon-disabled" ! A.src (textValue $ T.pack staticURL <> "img/save.png") ! A.alt "Save the plan"
        H.a ! A.class_ "action-button" ! A.href (textValue $ T.pack Actions.ManagePlans.url) $
          H.img ! A.class_ "action-icon" ! A.src (textValue $ T.pack staticURL <> "img/manage.png") ! A.alt "Manage plans"

renderMessageBars :: Html
renderMessageBars = do
  H.div ! A.id (textValue $ T.pack B.infoBar)    ! A.class_ "bar-fixed info"    $ mempty
  H.div ! A.id (textValue $ T.pack B.warningBar) ! A.class_ "bar-fixed warning" $ mempty
  H.div ! A.id (textValue $ T.pack B.errorBar)   ! A.class_ "bar-fixed error"   $ mempty

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
        H.a ! A.href "http://elixir-czech.cz" $ H.img ! A.src (textValue $ T.pack staticURL <> "img/logo-elixir-cz.jpg") ! A.class_ "logo" ! A.alt "ELIXIR-CZ logo"
        H.a ! A.href "https://www.uochb.cz" $ H.img ! A.src (textValue $ T.pack staticURL <> "img/logo-uochb.png") ! A.class_ "logo" ! A.alt "FIT logo"
        H.a ! A.href "http://ccmi.fit.cvut.cz/en" $ H.img ! A.src (textValue $ T.pack staticURL <> "img/logo-ccmi.png") ! A.class_ "logo" ! A.alt "CCMi logo"
        H.a ! A.href "http://fit.cvut.cz/en" $ H.img ! A.src (textValue $ T.pack staticURL <> "img/logo-fit.png") ! A.class_ "logo" ! A.alt "FIT logo"
        H.a ! A.href "http://www.dtls.nl/elixir-nl/elixir-nl-2/" $ H.img ! A.src (textValue $ T.pack staticURL <> "img/logo-elixir-nl.png") ! A.class_ "logo" ! A.alt "ELIXIR-NL logo"
        H.a ! A.href "http://www.dtls.nl/" $ H.img ! A.src (textValue $ T.pack staticURL <> "img/logo-dtl.png") ! A.class_ "logo" ! A.alt "DTL logo"
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
      H.img ! A.src (textValue $ T.pack staticURL <> "img/haskell.png") ! A.alt "Haskell logo" ! A.class_ "logo"


