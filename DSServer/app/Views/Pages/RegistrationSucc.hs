{-# LANGUAGE OverloadedStrings #-}

module Views.Pages.RegistrationSucc
  ( view
  ) where

--import Data.Monoid ((<>))
import Data.Text as T

--import Text.Blaze.Internal (textValue)
import Text.Blaze.Html5 (Html, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

--import Config.Config (staticURL)

url :: T.Text
url = "/"

view :: Html
view = H.p "Registration Successful"

