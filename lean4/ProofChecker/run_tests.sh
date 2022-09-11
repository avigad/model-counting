#!/bin/bash

set -x

lake build checker
export DIR=../../crat/prototype/test
lake exe checker $DIR/clause-gen-5.cnf         $DIR/clause-gen-5.crat
#lake exe checker -v $DIR/clause-proto-5.cnf       $DIR/clause-proto-5.crat
lake exe checker $DIR/conjunct-5.cnf           $DIR/conjunct-5.crat
lake exe checker $DIR/eg1.cnf                  $DIR/eg1-valid.crat
lake exe checker $DIR/eg1.cnf                  $DIR/eg1-nohint.crat
lake exe checker $DIR/eg2.cnf                  $DIR/eg2a.crat
lake exe checker $DIR/eg2.cnf                  $DIR/eg2a-nohint.crat
lake exe checker $DIR/eg2.cnf                  $DIR/eg2b.crat
lake exe checker $DIR/eg2.cnf                  $DIR/eg2b-nohint.crat
lake exe checker $DIR/pigeon-sat-direct-5.cnf  $DIR/pigeon-sat-direct-5.crat
lake exe checker $DIR/pigeon-sat-tseitin-4.cnf $DIR/pigeon-sat-tseitin-4.crat
lake exe checker $DIR/pigeon-sat-tseitin-5.cnf $DIR/pigeon-sat-tseitin-5.crat

lake exe checker $DIR/eg1.cnf $DIR/eg1-badrup.crat
lake exe checker $DIR/eg2.cnf $DIR/eg2a-baddc.crat
lake exe checker $DIR/eg2.cnf $DIR/eg2a-baddo.crat
lake exe checker $DIR/eg2.cnf $DIR/eg2a-badrup1.crat
lake exe checker $DIR/eg2.cnf $DIR/eg2a-nodelete.crat
lake exe checker $DIR/eg2.cnf $DIR/eg2a-twounit.crat