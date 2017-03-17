{-# LANGUAGE OverloadedStrings #-}

module Views.Pages.Main
  ( url
  , view
  , handler
  ) where

import Text.Blaze.Html5 (Html, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Web.Scotty (ActionM)

import App (PGPool)
import qualified Views.Page as Page

url :: String
url = "/"

view :: Html
view = H.form ! A.id "form" ! A.method "post" $ mempty

handler :: PGPool -> ActionM ()
handler _ = Page.render True view Page.NoMessage

