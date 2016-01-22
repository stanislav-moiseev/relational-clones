#!/bin/sh
rm -rf output/classes-with-one-subclass
mkdir -p output/classes-with-one-subclass/z3
make
./test/test-find-classes-with-one-subclass.out 
find output/classes-with-one-subclass/z3 -type f | time parallel z3 {} | grep unsat

