#!/bin/sh
rm -f output/z3/*
make
./test/test-gen-assert-discr-fun.out
find output/z3 -type f | time parallel echo {}\; ~/prog/z3/build/z3 {}

