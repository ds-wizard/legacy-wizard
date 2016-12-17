{-# LANGUAGE OverloadedStrings #-}
module PageGenerator (renderPage) where

import           Data.Monoid ((<>))
import qualified Data.Text as T

import           Text.Blaze.Internal (textValue)
import           Text.Blaze.Html5 (Html, toHtml, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

import           Config.Config (staticURL)

import           Model.Question as Q

renderHead :: Html
renderHead = H.head $ do
    H.meta ! A.charset "utf-8"
    H.meta ! A.httpEquiv "X-UA-Compatible" ! A.content "IE=edge"
    H.title "DS Wizard"
    H.meta ! A.name "viewport" ! A.content "width=device-width, initial-scale=1"
    H.link ! A.rel "stylesheet" ! A.href (textValue $ staticURL <> "css/normalize.min.css")
    H.link ! A.rel "stylesheet" ! A.href ( textValue $ staticURL <> "css/main.css")
    H.script ! A.src (textValue $ staticURL <> "js/vendor/jquery-3.1.1.min.js") $ mempty

renderBanner :: Html
renderBanner = H.div ! A.id "banner" $ do
  H.p ! A.class_ "title" $ "Data Stewardship Wizard" 
  H.a ! A.href "https://www.elixir-europe.org/" $ 
    H.img ! A.src (textValue $ staticURL <> "img/logo.png") ! A.id "logo" ! A.alt "Elixir logo"

renderFooter :: Html
renderFooter = H.div ! A.id "footer" ! A.class_ "stripe" $ 
  H.table ! A.class_ "footer-table" $ H.tbody $ 
    H.tr $ do
      H.td $ do
        H.h3 "Contact"
        _ <- "Phone: +420 220 183 267"
        H.br
        _ <- "E-mail : elixir@uochb.cas.cz"
        H.br
        H.a ! A.href "http://www.elixir-czech.cz" $ "http://www.elixir-czech.cz"
      H.td $ do
        H.h3 "Address"
        _ <- "ELIXIR CZ"
        H.br
        _ <- "Flemingovo nám. 542/2"
        H.br
        _ <- "166 10 Praha 6 - Dejvice"
        H.br
        "Czech Republic"
      H.td ! A.style "text-align: center; " $ do
        H.h3 "Data stewardship action team"
        H.a ! A.href "http://ccmi.fit.cvut.cz/en" $ H.img ! A.src (textValue $ staticURL <> "img/CCMi-logo.png") ! A.class_ "logo" ! A.alt "CCMi logo"
        H.a ! A.href "http://fit.cvut.cz/en" $ H.img ! A.src (textValue $ staticURL <> "img/FITlogo-small.png") ! A.class_ "logo" ! A.alt "FIT logo"
        H.br
        H.span "Contact: "
        H.a ! A.href "mailto:robert.pergl@fit.cvut.cz" $ "robert.pergl@fit.cvut.cz"
      H.td $ do
        H.h3 "Links"
        H.a ! A.href "http://www.elixir-europe.org/" $ "ELIXIR Europe"
        H.br
        H.a ! A.href "http://www.elixir-europe.org/about/elixir-nodes" $ "ELIXIR Nodes"
        H.br
        H.a ! A.href "http://www.elixir-czech.org/" $ "ELIXIR Czech"
        H.br
        H.a ! A.href "http://www.elixir-czech.cz/" $ "ELIXIR Czech local"
        H.br
        H.a ! A.href "https://www.elixir-czech.cz/login" $ "Members area"

renderAcknowledgement :: Html
renderAcknowledgement = 
  H.div ! A.class_ "colophon-box" $ do
    H.span ! A.class_ "colophon-text" $ "Crafted with "
    H.a ! A.href "https://www.haskell.org/ghc/" ! A.class_ "colophon-text" $ "GHC"
    H.span ! A.class_ "colophon-text" $ " & "
    H.a ! A.href "http://haste-lang.org/" ! A.class_ "colophon-text" $ "Haste"
    H.span ! A.class_ "colophon-text" $ ", powered by "
    H.a ! A.href "https://www.spock.li/" ! A.class_ "colophon-text" $ "Spock"
    H.img ! A.src (textValue $ staticURL <> "img/haskell.png") ! A.alt "Haskell logo" 

-- Pages

renderPage :: Html
renderPage = 
  H.docTypeHtml ! A.class_ "no-js" ! A.lang "" $ do
    renderHead
    H.body $ 
      H.div ! A.id "container" $ do
        renderBanner
        H.div ! A.class_ "inside" $ 
          H.form ! A.id "form" ! A.method "post" $ mempty
        H.div ! A.id "overlay" ! A.class_ "overlay" $ H.div "overlay"
        renderFooter
        renderAcknowledgement
        H.script ! A.src (textValue $ staticURL <> "js/main.js") $ mempty

