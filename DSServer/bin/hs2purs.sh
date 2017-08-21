#!/bin/bash

I="$1"
O="$2"

sed -e '
  /import/d
  s/\[\([^]]\+\)\]/(Array \1)/g
  s/deriving (Eq, Show)/derive instance
  ' $I > $O
