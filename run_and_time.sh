#!/bin/bash

set -xe

export PATH=$HOME/racket-6.2.0.5/bin:$PATH

# Reset Racket in a primitive way:
rm -rf ~/racket-6.2.0.5
cp -a ~/racket-6.2.0.5-bak ~/racket-6.2.0.5

# Now run and get our timings.

(raco pkg update typed-racket-lib/ 2>&1) | tee timings.log
