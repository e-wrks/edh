#!/usr/bin/env bash

cabal run edhi --RTS -- +RTS -N3 -A16m -H64m -qg -I0 -s <simple.edh
