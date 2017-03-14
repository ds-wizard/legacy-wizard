{-# LANGUAGE OverloadedStrings, DataKinds #-}

module Views.Pages.Main
  ( url
  , view
  , handler
  ) where

import Text.Blaze.Html5 (Html, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Web.Spock (Path, root)
import Web.Routing.Combinators (PathState(..))

import App (WizardAction)
import qualified Views.Page as Page

url :: Path '[] 'Open
url = root

view :: Html
view = H.form ! A.id "form" ! A.method "post" $ mempty

handler :: WizardAction ctx b a
handler = Page.render True view Page.NoMessage

