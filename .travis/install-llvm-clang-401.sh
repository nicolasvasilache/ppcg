#!/usr/bin/env bash

if ! test -e /tmp/clang+llvm/bin/llvm-config; then
    OLD=$(pwd)

    cd /tmp && \
        rm -Rf /tmp/clang+llvm && \
        wget http://releases.llvm.org/4.0.1/clang+llvm-4.0.1-x86_64-linux-gnu-debian8.tar.xz && \
        tar -xf clang+llvm-4.0.1-x86_64-linux-gnu-debian8.tar.xz && \
        mv clang+llvm-4.0.1-x86_64-linux-gnu-debian8 clang+llvm

    cd ${OLD}
fi
