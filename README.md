## Goals and progress.

Eventually this should draw a class of paths in a discrete hypercube of some size. Currently I am aiming to compute Hamiltonian paths efficiently.

## How to work on it.

This is how I build:

    cabal build --enable-profiling && /bin/timeout 10 /bin/time cabal exec script -- +RTS -p -hy -s

This is how I draw the picture of the memory:

    while true; do inotifywait --event close_write --recursive script.hp || break; hp2ps -c script.hp && ps2pdf script.ps; done

This is how I view the profiling report:

    cat script.prof | sed 's/\<0\.0\>/   /g' | grep -Ev ' {10}$' | less

This is how I abbreviate the profiling report:

    cat script.prof | grep -Ev '\<[0-9]\.[0-9]+\>.*\<[0-9]+\.[0-9]+\>.*\<[0-9]\.[0-9]+\>' | sed 's/\<[0-9]\.[0-9]\+\>/   /g' | less

## How to undersand output.

It prints something out at every step of the main loop. Kindly see the source code for the meaning of columns.

## How to change the problem size.

There are type synonyms in the code for the size and dimension of the cube. They may be changed.
