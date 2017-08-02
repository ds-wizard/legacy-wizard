{-# LANGUAGE OverloadedStrings #-}

module Texts where

import Prelude
import Data.Monoid ((<>))

import Config.Config (staticURL)

bookLabelTxt :: String -> String
bookLabelTxt ref =
  "<div class='book-banner'>\
  \  <img class='book-clipart' src='" <> staticURL <> "img/book.png' alt='book clipart'/>\
  \  <div class='book-title'>\
  \    <a href='https://www.crcpress.com/Data-Stewardship-for-Discovery-A-Practical-Guide-for-Data-Experts/Mons/p/book/9781498753173' target='_blank'>\
  \      Data Stewardship for Discovery\
  \    </a>\
  \    : Chapter " <> ref <> "\
  \  </div>\
  \  <div class='book-acknowledgement'>\
  \    <div class='book-permission'>\
  \      With kind permission of\
  \    </div>\
  \    <div class='crc-log'>\
  \      <a href='http://taylorandfrancis.com/' target='_blank'><img src='" <> staticURL <> "img/crc-logo.png' alt='CRC logo'/></a>\
  \    </div>\
  \  </div>\
  \</div>"


