BASE=$1

cat $BASE.drat | grep -v "d " > $BASE.rat
./negate $BASE.rat > $BASE.cubes
cat $BASE.acnf $BASE.cubes | awk '/p cnf/ {print "p inccnf"} / 0/ {print $0}'> $BASE.icnf
~/cadical/build/cadical $BASE.icnf $BASE.drup --no-binary
#~/GitHub/Mario/cadical/build/cadical $BASE.icnf $BASE.lrat --no-binary --lrat=true
cat $BASE.drup | grep -v "d " > $BASE.rup
../crat-lrat/crat-lrat $BASE.acnf $BASE.rup -f | grep -v "c " | grep " 0" > result.txt
cat result.txt

