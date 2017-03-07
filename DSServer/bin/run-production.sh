#!/bin/bash

S="dmp.fairdata.solutions"

killall $S
cd /srv/ghc/$S
./$S
