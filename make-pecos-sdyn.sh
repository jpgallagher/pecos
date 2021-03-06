#!/bin/sh
# script to be run in the pecos top level directory
PECOS=$(pwd)
export CIAOROOT="$PECOS/bin/ciao"
export CIAOPATH="$PECOS/ciao_bundles"

# copy programs from pecos 

cp $PECOS/pe/*.pl pe

# copy preprocessing programs
cp $PECOS/smt2chc/* smt2chc

# Binaries

cd bin

# Copy scripts
cp $PECOS/bin/starexec_run_lia.sh .
cp $PECOS/bin/starexec_run_lra.sh .
# Re-compile everything and put binaries and dynamic libraries in bin/
ciaoc_sdyn $CIAOPATH/chclibs/src/thresholds1.pl
ciaoc_sdyn $CIAOPATH/chclibs/src/cpascc.pl
ciaoc_sdyn $CIAOPATH/chclibs/src/qa.pl
ciaoc_sdyn $CIAOPATH/RAHFT/src/insertProps.pl
ciaoc_sdyn $CIAOPATH/RAHFT/src/raf
#
ciaoc_sdyn $PECOS/smt2chc/chcNorm.pl
ciaoc_sdyn $PECOS/pe/peunf_smt_2.pl
ciaoc_sdyn $PECOS/pe/counterExample.pl
ciaoc_sdyn $PECOS/pe/props.pl
ciaoc_sdyn $PECOS/pe/tpclp.pl

# Remove some system .so files (which are not part of 3rd-party)
rm -f libc.so.* libgcc_s.so.* libm.so.* libstdc++.so.*
