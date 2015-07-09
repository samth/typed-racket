#!/bin/bash

set -xe

# Reset Racket in a primitive way:
rm -rf ~/racket-6.2.0.5
cp -a ~/racket-6.2.0.5-bak ~/racket-6.2.0.5

# Now run and get our timings.

raco pkg update typed-racket-lib/ | tee timings.log
