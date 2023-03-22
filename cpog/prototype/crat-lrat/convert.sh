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

cp $CNF tmp-$$.cnf
./expand p-lines >> tmp-$$.cnf
NVAR=`tail -n 1 tmp-$$.cnf | awk '{if ($1 > 0) print $1; else print $1*-1}'`
NCLS=`cat tmp-$$.cnf | grep -v "c" | wc | awk '{print $1}'`

cat tmp-$$.cnf | awk '/p cnf/ {print "p cnf '$NVAR' '$NCLS'"} / 0/ {print $0}' > base.cnf
rm tmp-$$.cnf

#echo $NVAR" "$NCLS

#cat a-lines d-lines > $DRAT
cat a-lines > $DRAT

./crat-lrat base.cnf $DRAT -f | grep -v -e "c " -e "s " > tmp.lrat


cat tmp.lrat | awk '{printf "%i a", $1; $1=""; print $0}'
#tail -n $BOTH tmp.lrat  | head -n $ASIZE | awk '{printf "%i a", $1; $1=""; print $0}'
#tail -n $DSIZE tmp.lrat | sed 's| 0 |:|' | cut -d: -f2- | awk 'BEGIN{i=1} {print "dc "i" "$0; i=i+1}'

