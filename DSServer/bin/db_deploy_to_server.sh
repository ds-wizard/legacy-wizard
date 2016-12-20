#!/bin/bash

pg_dump --host localhost --port 5432 --username "postgres" --role "elixir" --format tar --blobs --encoding UTF8 --verbose --file "tmp.backup" "elixir-dswizard"
pg_restore --host ccmi.fit.cvut.cz --port 5432 --username "postgres" --dbname "elixir-dswizard" --role "elixir" --clean --verbose "tmp.backup"
rm tmp.backup
