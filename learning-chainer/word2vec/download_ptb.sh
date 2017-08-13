#!/bin/sh

set -eux

for v in train valid test; do
    wget "https://raw.githubusercontent.com/tomsercu/lstm/master/data/ptb.${v}.txt"
done
