{-# LANGUAGE OverloadedStrings #-}

module Views.Info
  ( url
  , infoResponse
  , errorResponse
  ) where

import Text.Blaze.Html5 (Html,(!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Web.Scotty (RoutePattern, ActionM)

import qualified Views.Page as Page

url :: RoutePattern
url = "/info"

data InfoType = OKInfo | ErrorInfo

view :: InfoType -> Html -> Html
view infoType message = do
  H.div !
    (case infoType of
      OKInfo -> A.class_ "bar message"
      ErrorInfo -> A.class_ "bar error") $ message
  H.a ! A.href "/" $ H.button ! A.class_ "info" $ "OK"

infoResponse :: Html ->  ActionM ()
infoResponse msg = Page.render False (view OKInfo msg) Page.NoMessage

errorResponse :: Html ->  ActionM ()
errorResponse msg = Page.render False (view ErrorInfo msg) Page.NoMessage

