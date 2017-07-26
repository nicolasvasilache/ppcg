#!/usr/bin/env bash

set -ex

CORES=${CORES:=CORES}

# ISL
if ! test -e /tmp/install/lib/libisl.so; then
    cd ${TRAVIS_BUILD_DIR}/..
    git clone https://github.com/nicolasvasilache/isl.git && cd isl && git checkout ntv_dev
    rm -Rf build && mkdir -p build && cd build
    VERBOSE=1 cmake -DISL_INT=gmp -DCLANG_PREFIX=/tmp/clang+llvm/ -DCMAKE_INSTALL_PREFIX=/tmp/install -DTRAVIS=true ..
    VERBOSE=1 make -j ${CORES}
    make install
fi

# PET
if ! test -e /tmp/install/lib/libpet.so; then
    cd ${TRAVIS_BUILD_DIR}/..
    git clone https://github.com/nicolasvasilache/pet.git && cd pet
    rm -Rf build && mkdir -p build && cd build
    VERBOSE=1 cmake -DISL_PREFIX=/tmp/install -DCLANG_PREFIX=/tmp/clang+llvm/ -DCMAKE_INSTALL_PREFIX=/tmp/install -DTRAVIS=true ..
    VERBOSE=1 make -j ${CORES}
    ctest
    make install
fi

cd ${TRAVIS_BUILD_DIR}
rm -Rf build && mkdir -p build && cd build
VERBOSE=1 cmake -DISL_PREFIX=/tmp/install -DPET_PREFIX=/tmp/install -DCMAKE_INSTALL_PREFIX=/tmp/install -DTRAVIS=true ..
VERBOSE=1 make -j ${CORES}
ctest
make install
