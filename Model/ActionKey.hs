{-# LANGUAGE OverloadedStrings, CPP #-}

module Model.ActionKey where

import qualified Data.ByteString.Builder as BS
import qualified Data.ByteString.Char8 as BS
import qualified Database.PostgreSQL.Simple.FromRow as PG
import qualified Database.PostgreSQL.Simple.FromField as PG
import qualified Database.PostgreSQL.Simple.ToField as PG
import qualified Data.Time.Clock as DTC

import Debug.Trace (traceShow)

#ifdef __HASTE__
type Text = String
#else
import Data.Text (Text)
#endif

{-# ANN module ("HLint: ignore Use camelCase" :: String) #-}

type ActionKeyKey = Text

data Action = ConfirmRegistration | ResetPassword deriving (Show, Read)

instance PG.FromField Action where
  fromField f bs =
    case bs of
      Nothing -> PG.returnError PG.UnexpectedNull f ""
      Just val -> pure $ read (traceShow val (BS.unpack val))

instance PG.ToField Action where
    toField val  = PG.Plain $ PG.inQuotes $ BS.stringUtf8 $ show val

data ActionKey = ActionKey
  { ac_id :: Int
  , ac_user_id :: Int
  , ac_action :: Action
  , ac_key :: ActionKeyKey
  , ac_created :: DTC.UTCTime
  } deriving (Show)

instance PG.FromRow ActionKey where
  fromRow = ActionKey <$> PG.field <*> PG.field <*> PG.field <*> PG.field <*> PG.field

