{-# LANGUAGE OverloadedStrings #-}

module Views.Pages.Info
  ( InfoType(..)
  , view
  , url
  ) where

--import Data.Monoid ((<>))
import Data.Text as T

--import Text.Blaze.Internal (textValue)
import Text.Blaze.Html5 (Html,(!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

--import Config.Config (staticURL)

url :: T.Text
url = "/info"

data InfoType = OKInfo | ErrorInfo

view :: InfoType -> Html -> Html
view infoType message = do
  H.div !
    (case infoType of
      OKInfo -> A.class_ "bar message"
      ErrorInfo -> A.class_ "bar error") $ message
  H.a ! A.href "/" $ H.button ! A.class_ "info" $ "OK"

