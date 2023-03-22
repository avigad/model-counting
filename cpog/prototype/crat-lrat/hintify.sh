#!/bin/bash

DIR=$(dirname -- "$(readlink -f "${BASH_SOURCE}")")
CNF=$1.cnf
CRAT=$1.crat
DRAT=$1.drat
HCRAT=$1.hcrat

ASIZE=`cat $CRAT | grep " a " | wc | awk '{print $1}'`
DSIZE=`cat $CRAT | grep "dc " | wc | awk '{print $1}'`
BOTH=$(($ASIZE+$DSIZE))

cat $CRAT | awk '/ p / {$1=""; print $0}' | sed 's| p ||' > p-lines

cat $CRAT | awk '/ a / {$1=""; print $0}' | sed 's| a ||' | sed 's| \* 0||' > a-lines

cat $CNF  | awk '/ 0/ {print "d "$0; print $0; print "d "$0}' > d-lines

$DIR/expand p-lines > $DRAT
cat a-lines d-lines >> $DRAT

$DIR/crat-lrat $CNF $DRAT -f | grep -v -e "c " -e "s " > tmp.lrat

cat $CRAT | grep "[sp]" | grep -v "c " > $HCRAT

tail -n $BOTH tmp.lrat  | head -n $ASIZE | awk '{printf "%i a", $1; $1=""; print $0}' >> $HCRAT

tail -n $DSIZE tmp.lrat | sed 's| 0 |:|' | cut -d: -f2- | awk 'BEGIN{i=1} {print "dc "i" "$0; i=i+1}' >> $HCRAT

rm -f a-lines p-lines d-lines $DRAT tmp.lrat
