{-# LANGUAGE OverloadedStrings #-}

module App
  ( WizardAction
  ) where

import qualified Database.PostgreSQL.Simple as PG
import qualified Web.Spock as W

type WizardAction ctx b a = W.ActionCtxT ctx (W.WebStateM PG.Connection b ()) a

