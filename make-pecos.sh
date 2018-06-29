#!/bin/sh

PECOS="/Users/jpg/Research/LP/clptools/predabs/pecos"
#CIAOROOT="/Users/jpg/local/ciao-devel"
#CIAOPATH="/Users/jpg/ciao"

# copy programs from pecos 

cp $PECOS/pe/*.pl pe

# copy preprocessing programs
cp $PECOS/smt2chc/* smt2chc

# copy scripts
cp $PECOS/bin/starexec_run_lia.sh bin
cp $PECOS/bin/starexec_run_lra.sh bin

# Re-compile everything 


ciaoc -S $CIAOPATH/chclibs/src/thresholds1.pl
ciaoc -S $CIAOPATH/chclibs/src/cpascc.pl
ciaoc -S $CIAOPATH/chclibs/src/qa.pl
ciaoc -S $CIAOPATH/RAHFT/src/insertprops.pl
ciaoc -S $CIAOPATH/RAHFT/src/raf

mv $CIAOPATH/chclibs/src/thresholds1 $CIAOPATH/build/bin
mv $CIAOPATH/chclibs/src/cpascc $CIAOPATH/build/bin
mv $CIAOPATH/chclibs/src/qa $CIAOPATH/build/bin
mv $CIAOPATH/RAHFT/src/insertprops $CIAOPATH/build/bin
mv $CIAOPATH/RAHFT/src/raf $CIAOPATH/build/bin

ciaoc -S $PECOS/smt2chc/chcNorm.pl
ciaoc -S $PECOS/pe/peunf_smt_2.pl
ciaoc -S $PECOS/pe/counterExample.pl
ciaoc -S $PECOS/pe/props.pl
ciaoc -S $PECOS/pe/tpclp.pl

