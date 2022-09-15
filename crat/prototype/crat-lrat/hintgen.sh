CNF=$1
DRAT=$2

make

cat $DRAT | awk '{print $0"\nd "$0}' > tmp-$$.drat
./crat-lrat $CNF tmp-$$.drat -f | grep " 0" | grep -v "c "
rm tmp-$$.drat
