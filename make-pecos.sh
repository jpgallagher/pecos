#!/bin/sh

#PECOS="/Users/jpg/Research/LP/clptools/predabs/pecos"
PECOS="."
export CIAOPATH="$PECOS/ciao_bundles"
#export CIAOROOT="$PECOS/bin/ciao"

# copy programs from pecos 


# copy preprocessing programs

# copy scripts

# Re-compile everything 
rm $CIAOPATH/chclibs/src/*.itf
rm $CIAOPATH/chclibs/src/*.po
rm $CIAOPATH/RAHFT/src/*.itf
rm $CIAOPATH/RAHFT/src/*.po

ciaoc -S $CIAOPATH/chclibs/src/thresholds1.pl
ciaoc -S $CIAOPATH/chclibs/src/cpascc.pl
ciaoc -S $CIAOPATH/chclibs/src/qa.pl
ciaoc -S $CIAOPATH/RAHFT/src/insertProps.pl
ciaoc -S $CIAOPATH/RAHFT/src/raf

mv $CIAOPATH/chclibs/src/thresholds1 $CIAOPATH/build/bin
mv $CIAOPATH/chclibs/src/cpascc $CIAOPATH/build/bin
mv $CIAOPATH/chclibs/src/qa $CIAOPATH/build/bin
mv $CIAOPATH/RAHFT/src/insertProps $CIAOPATH/build/bin
mv $CIAOPATH/RAHFT/src/raf $CIAOPATH/build/bin

ciaoc -S $PECOS/smt2chc/chcNorm.pl
ciaoc -S $PECOS/pe/peunf_smt_2.pl
ciaoc -S $PECOS/pe/counterExample.pl
ciaoc -S $PECOS/pe/props.pl
ciaoc -S $PECOS/pe/tpclp.pl

