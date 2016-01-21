#!/bin/sh
rm -f test/z3/*
make
./test/test-gen-assert-discr-fun.out
find test/z3 -type f | time parallel echo {}\; ~/prog/z3/build/z3 {}

