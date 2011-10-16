#!/bin/sh

# USAGE NOTE:
# make sure the -i has your actual include path to the stdlib before running

# first we make sure all deps are compiled
agda --html -i . -i ~/proj/agda-stdlib/lib/src Test.agda
rm Test.agdai
agda --html -i . -i ~/proj/agda-stdlib/lib/src -v 65535 --show-implicit Test.agda
