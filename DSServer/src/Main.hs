{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.Monoid ((<>))
import Data.Maybe (fromMaybe)
import Control.Monad (join)
import Control.Monad.IO.Class (MonadIO)
import Data.Text (Text, unpack)
import Data.Text.Lazy (toStrict, pack)
import Text.Blaze.Html.Renderer.Text
import Web.Spock.Safe as W
import Network.Wai.Middleware.Static as M
import Network.Wai.Middleware.RequestLogger
import Data.Pool
import qualified Database.PostgreSQL.Simple as PG

import Config.Config (baseURL)
import Config.Server.Config (port, pgCreds)

import PageGenerator (renderPage)
import Model.Question
import Persistence.Question (getQuestion, getBookContents)

poolCfg :: PoolCfg
poolCfg = PoolCfg 50 50 60

pcconn :: ConnBuilder PG.Connection
pcconn = ConnBuilder (PG.connect pgCreds) PG.close poolCfg

dbConn :: PoolOrConn PG.Connection
dbConn = PCConn pcconn

main :: IO ()
main =
  runSpock port $
  spock (defaultSpockCfg Nothing dbConn ()) $
  subcomponent "/" $
  do middleware M.static
     middleware logStdoutDev
     get root rootHandler
     post "api/getQuestion" getQuestionHandler
     post "api/getBookContents" getBookContentsHandler

rootHandler :: ActionCtxT ctx (WebStateM PG.Connection b ()) a
rootHandler = html $ toStrict $ renderHtml renderPage

getQuestionHandler :: ActionCtxT ctx (WebStateM PG.Connection b ()) a
getQuestionHandler = do
  ps <- params
  case join $ readInt <$> lookup "chid" ps of
    Nothing -> W.text "Missing chid"
    Just chid ->
      case join $ readInt <$> lookup "qid" ps of
        Nothing -> W.text "Missing qid"
        Just qid -> do
          maybeQuestion <- runQuery $ getQuestion chid qid
          W.text $ toStrict $ fromMaybe "" $ (pack . show) <$> maybeQuestion

getBookContentsHandler :: ActionCtxT ctx (WebStateM PG.Connection b ()) a
getBookContentsHandler = do
  ps <- params
  case join $ readInt <$> lookup "chid" ps of
    Nothing -> W.text "Missing chid"
    Just chid ->
      case join $ readInt <$> lookup "qid" ps of
        Nothing -> W.text "Missing qid"
        Just qid -> do
          maybeText <- runQuery $ getBookContents chid qid
          W.text $ fromMaybe "" maybeText

readInt :: Text -> Maybe Int
readInt str
  | length readChid /= 1 = Nothing
  | otherwise = if not $ null $ snd $ Prelude.head readChid
     then Nothing
     else Just $ fst $ Prelude.head readChid
  where
    readChid = reads (unpack str) :: [(Int, String)]
