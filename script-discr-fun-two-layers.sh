#!/bin/sh
rm -rf output/disrc-fun-two-layers
mkdir -p output/disrc-fun-two-layers/z3
make
./test/test-gen-assert-discr-fun-two-layers.out
find output/disrc-fun-two-layers/z3 -type f | time parallel echo {}\; z3 {}

