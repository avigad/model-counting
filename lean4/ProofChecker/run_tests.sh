#!/bin/bash

set -x

lake build checker
export DIR=../../cpog/test/cpog
lake exe checker $DIR/clause-gen-5.cnf         $DIR/clause-gen-5.cpog
#lake exe checker -v $DIR/clause-proto-5.cnf       $DIR/clause-proto-5.cpog
lake exe checker $DIR/conjunct-5.cnf           $DIR/conjunct-5.cpog
lake exe checker $DIR/eg1.cnf                  $DIR/eg1-valid.cpog
lake exe checker $DIR/eg2.cnf                  $DIR/eg2a.cpog
lake exe checker $DIR/eg2.cnf                  $DIR/eg2b.cpog
lake exe checker $DIR/pigeon-sat-direct-5.cnf  $DIR/pigeon-sat-direct-5.cpog
lake exe checker $DIR/pigeon-sat-tseitin-4.cnf $DIR/pigeon-sat-tseitin-4.cpog
lake exe checker $DIR/pigeon-sat-tseitin-5.cnf $DIR/pigeon-sat-tseitin-5.cpog

lake exe checker $DIR/eg1.cnf $DIR/eg1-nohint.cpog
lake exe checker $DIR/eg2.cnf $DIR/eg2a-nohint.cpog
lake exe checker $DIR/eg2.cnf $DIR/eg2b-nohint.cpog

lake exe checker $DIR/eg1.cnf $DIR/eg1-badrup.cpog
lake exe checker $DIR/eg2.cnf $DIR/eg2a-baddc.cpog
lake exe checker $DIR/eg2.cnf $DIR/eg2a-baddo.cpog
lake exe checker $DIR/eg2.cnf $DIR/eg2a-badrup1.cpog
lake exe checker $DIR/eg2.cnf $DIR/eg2a-nodelete.cpog
lake exe checker $DIR/eg2.cnf $DIR/eg2a-twounit.cpog