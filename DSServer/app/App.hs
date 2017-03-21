{-# LANGUAGE OverloadedStrings #-}

module App
  ( Action
  , PGPool
  , Cookies
  , setSession
  , getSession
  , deleteSession
  , runQuery
  ) where

--import qualified Data.Text.Lazy as TL
--import qualified Data.Text.Lazy.Encoding as T
import Data.Text (Text)

import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans (liftIO)
--import           Control.Monad.Reader
--import           Web.Scotty.Trans (ReaderT, ScottyT, ActionT)
import Data.Map.Lazy (Map, member, (!))
import Data.Pool (Pool, withResource)
import Database.PostgreSQL.Simple (Connection)
import Web.Scotty (ActionM)
import Web.Scotty.Cookie (setSimpleCookie, deleteCookie)

import Model.Session (SessionId)
import Persistence.Session (deleteSessionById)

type Action = ActionM ()

type PGPool = Pool Connection

type Cookies = Map Text Text

sessionCookie = "sessionId"

paramVal :: Text -> Cookies -> Maybe Text
paramVal key cookies =
  if member key cookies
    then Just $ cookies ! key
    else Nothing

setSession :: SessionId -> Action
setSession = setSimpleCookie sessionCookie

getSession :: Cookies -> Maybe SessionId
getSession = paramVal sessionCookie

deleteSession :: PGPool -> Cookies -> Action
deleteSession pool cookies =
  case getSession cookies of
    Nothing -> return ()
    Just sessionId -> do
      _ <- runQuery pool $ deleteSessionById sessionId
      deleteCookie sessionCookie

--tl2t :: TL.Text -> Data.Text.Internal.Lazy.Text
--t2t t = Data.Text.Lazy.pack $ tifName tif
--tif2t :: TransactionInputField -> Data.Text.Text
--tif2t tif = Data.Text.pack $ tifName tif

runQuery
  :: MonadIO m
  => Pool Connection -> (Connection -> IO a) -> m a
runQuery pool query = liftIO $ withResource pool query
