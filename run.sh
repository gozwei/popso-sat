#!/bin/sh
# SAT Competition entry point: run.sh <input.cnf> <proof-directory>
# The DRAT proof (binary format) is written to <proof-directory>/proof.out.
DIR="$(cd "$(dirname "$0")" && pwd)"
if [ -n "$2" ]; then
  exec "$DIR/bin/popso-sat" "$1" "$2/proof.out"
fi
exec "$DIR/bin/popso-sat" "$1"
