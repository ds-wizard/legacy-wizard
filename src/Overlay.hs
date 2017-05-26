{-# LANGUAGE OverloadedStrings #-}

module Overlay (initOverlay, overlayOn, overlayOff) where

import Prelude

import FormEngine.JQuery

overlayId :: String
overlayId = "overlay"

getBox :: JQuery -> IO JQuery
getBox = findSelector "div"

setBoxTopMargin :: JQuery -> IO JQuery
setBoxTopMargin jq = do
  box <- getBox jq
  top <- select "body" >>= getScrollTop
  _ <- setCss "margin-top" (show $ top + 25) box
  return jq

setOverlaySize :: JQuery -> IO JQuery
setOverlaySize jq = do
  h <- select "body" >>= getHeight
  _ <- setHeight h jq
  return jq

initOverlay :: IO JQuery
initOverlay = selectById overlayId >>= onClick (\_ -> do _ <- overlayOff; return ())

setContents :: String -> JQuery -> IO JQuery
setContents html jq = do
  box <- getBox jq
  _ <- if null html then
    setText "No details available" box
  else
    setHtml html box
  return jq

overlayOn :: String -> IO JQuery
overlayOn txt = selectById overlayId >>= setContents txt >>= setOverlaySize >>= setBoxTopMargin >>= showJq

overlayOff :: IO JQuery
overlayOff = selectById overlayId >>= hideJq

