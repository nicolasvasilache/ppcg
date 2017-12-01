#!/usr/bin/env bash

set -ex

F=/tmp/install/lib/libisl.a
if ! test -e ${F} ; then
    echo "$F missing"
    exit 1
fi

F=/tmp/install/include/isl/interface/isl-noexceptions.h
if ! test -e ${F} ; then
    echo "$F missing"
    exit 1
fi

./build/interface/isl_test_cpp
./build/interface/test/test_islpp
