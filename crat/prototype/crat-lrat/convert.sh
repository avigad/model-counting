CNF=$1.CNF
CRAT=$1.CRAT
DRAT=$1.DRAT

ASIZE=`cat $CRAT | grep " a " | wc | awk '{print $1}'`
DSIZE=`cat $CRAT | grep "dc " | wc | awk '{print $1}'`
BOTH=$(($ASIZE+$DSIZE))

cat $CRAT | awk '/ p / {$1=""; print $0}' | sed 's| p ||' > p-lines

cat $CRAT | awk '/ a / {$1=""; print $0}' | sed 's| a ||' | sed 's| \* 0||' > a-lines

cat $CNF  | awk '/ 0/ {print "d "$0;}' > d-lines
cat $CNF  | awk '/ 0/ {print $0; print "d "$0;}' >> d-lines
#cat $CNF  | awk '/ 0/ {print "d "$0; print $0; print "d "$0;}' > d-lines

./expand p-lines > $DRAT
cat a-lines d-lines >> $DRAT

./crat-lrat $CNF $DRAT -f | grep -v -e "c " -e "s " > tmp.lrat


tail -n $BOTH tmp.lrat  | head -n $ASIZE | awk '{printf "%i a", $1; $1=""; print $0}'

tail -n $DSIZE tmp.lrat | sed 's| 0 |:|' | cut -d: -f2- | awk 'BEGIN{i=1} {print "dc "i" "$0; i=i+1}'
