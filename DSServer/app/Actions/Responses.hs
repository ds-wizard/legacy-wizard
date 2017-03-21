{-# LANGUAGE OverloadedStrings #-}

module Actions.Responses
  ( url
  , infoResponse
  , errorResponse
  , logInResponse
  ) where

import Text.Blaze.Html5 (Html,(!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Web.Scotty (RoutePattern)

import App (Action)
import qualified Page

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

infoResponse :: Html ->  Action
infoResponse msg = Page.render False (view OKInfo msg) Nothing Page.NoMessage

errorResponse :: Html ->  Action
errorResponse msg = Page.render False (view ErrorInfo msg) Nothing Page.NoMessage

logInResponse :: Action
logInResponse = errorResponse "Please log in first."
