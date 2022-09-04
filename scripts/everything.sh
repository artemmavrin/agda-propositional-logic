#!/bin/bash

# This script generates a single Agda file that imports all Agda modules in the
# library. The resulting file is placed in the src directory.

# First and only command-line argument is the name of the resulting module.
if [ "$#" -ne 1 ]; then
  echo "Usage: $0 ModuleName" >&2
  exit 1
fi

# Generate OPTIONS header
sed -n -e '/^flags: /p' *.agda-lib \
  | sed -e 's/^flags: \(.*\)/{-# OPTIONS \1 #-}/' \
  > src/$1.agda

# Module declaration
echo -e "\nmodule $1 where\n" >> src/$1.agda

# Comment about link clickability
echo -e "-- This module imports every module in the library." >> src/$1.agda
echo -e "-- All module names are clickable links.\n" >> src/$1.agda

# Import all modules in the library
find src -type f -name "*.agda" \
    | grep -vx src/$1.agda      \
    | sort                      \
    | sed -e 's/^src\///'       \
    | cut -f1 -d'.'             \
    | sed 's/\//\./g'           \
    | sed 's/^/open import /'   \
    >> src/$1.agda
