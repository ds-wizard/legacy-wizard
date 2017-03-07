#!/bin/bash

S="dmp.fairdata.solutions-testing"

killall $S
cd /srv/ghc/$S
./$S
