module Config.Server.Config where

import qualified Database.PostgreSQL.Simple as PG

port :: Int
port = 8002

pgCreds :: PG.ConnectInfo
pgCreds =
    PG.ConnectInfo
        { PG.connectHost     = "localhost"
        , PG.connectPort     = 5432
        , PG.connectUser     = "elixir"
        , PG.connectPassword = "elixir"
        , PG.connectDatabase = "elixir-dswizard"
        }

