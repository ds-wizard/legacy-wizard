{-# LANGUAGE OverloadedStrings #-}

module Texts where

import Prelude
import Data.Monoid ((<>))

import Config.Config (staticURL)
       
bookLabelTxt :: String -> String
bookLabelTxt ref = 
  "<h1> \
  \  <a href='https://www.crcpress.com/Data-Stewardship-for-Discovery-A-Practical-Guide-for-Data-Experts/Mons/p/book/9781498753173' target='_blank'>Book</a> \
  \  (*) chapter " <> ref <> ": \
  \</h1>"

bookAckTxt :: String
bookAckTxt = 
  "<hr/> \
  \  <p> \
  \    (*) With kind permission of \
  \    <a href='http://taylorandfrancis.com/' target='_blank'> \
  \      <img src='" <> staticURL <> "img/crc-logo.png' alt='CRC logo'/>  \
  \    </a> \
  \  </p>"
