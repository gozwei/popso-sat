#!/bin/sh
# Builds bin/popso-sat without CMake (SAT Competition style: no arguments, plain C++20 compiler).
# For development use CMake instead (see README.md).
set -e
cd "$(dirname "$0")"
CXX="${CXX:-c++}"
VERSION=$(sed -n 's/^project(popso-sat LANGUAGES CXX VERSION \([0-9.]*\)).*/\1/p' CMakeLists.txt)
mkdir -p bin
# shellcheck disable=SC2046
"$CXX" -std=c++20 -O3 -DNDEBUG "-DPSAT_VERSION=\"$VERSION\"" -Isrc -pthread \
  -o bin/popso-sat $(find src/psat -name '*.cpp' | sort) apps/popso_sat_main.cpp
echo "built bin/popso-sat $VERSION"
