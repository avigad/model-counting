#!/bin/bash

INTERP=python3
BDIR=../generators
PGEN=$BDIR/gen_pigeon.py

for N in {4..9}
do
     $INTERP $PGEN -r pigeon-sat-tseitin-0$N -L -n $N -p $N
done    

for N in {10..13}
do
     $INTERP $PGEN -r pigeon-sat-tseitin-$N -L -n $N -p $N
done    
