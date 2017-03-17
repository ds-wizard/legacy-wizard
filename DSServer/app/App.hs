{-# LANGUAGE OverloadedStrings #-}

module App
  ( PGPool
  , runQuery
  ) where

--import qualified Data.Text.Lazy as T
--import qualified Data.Text.Lazy.Encoding as T
--import           Data.Text.Lazy (Text)
--import           Control.Monad.Reader
--import           Web.Scotty.Trans (ReaderT, ScottyT, ActionT)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans (liftIO)
import           Data.Pool (Pool, withResource)
import Database.PostgreSQL.Simple (Connection)

type PGPool = Pool Connection

runQuery :: MonadIO m => Pool Connection -> (Connection -> IO a) -> m a
runQuery pool query = liftIO $ withResource pool query
