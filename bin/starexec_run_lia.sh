#!/bin/sh

# $1 = input file
#PECOS="/Users/jpg/Research/LP/clptools/predabs/pecos"
PECOS=".."

PE="$PECOS/pe"
SMT2CHC="$PECOS/smt2chc"

export CIAOPATH="$PECOS/ciao_bundles"
export CIAOROOT="$PECOS/bin/ciao"
export PYTHONPATH="$PECOS/z3/build/python"
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$CIAOROOT/third-party/lib:$PECOS/z3

LIB="$CIAOPATH/build/bin"


# constraint specialisation
function spec() {
   local infile=$1
   local outfile=$2
   #echo "Performing query transformation"
   $LIB_CHCLIB/qa $infile -query false -ans -o $resultdir/$f.qa.pl || exit 1
   #echo "Computing widening thresholds"
   $LIB_CHCLIB/thresholds1 -prg $resultdir/$f.qa.pl -a -o wut.props || exit 1
   #$PE/props -prg "$resultdir/$f.qa.pl" -l 1 -o wut.props
   #echo "Computing convex polyhedron approximation of QA clauses"
   $LIB_CHCLIB/cpascc -prg $resultdir/$f.qa.pl -cex "traceterm.out"  -withwut -wfunc h79 -o $resultdir/$f.qa.cha.pl || exit 1
   #echo "Specialise clauses"
   $LIB_RAHFT/insertProps -prg $infile -props $resultdir/$f.qa.cha.pl -o $outfile || exit 1
}

function checksafe() {
    local file=$1
    $PE/counterExample -prg $file -cex "traceterm.out" -qa -type int 
    retval=$? 
	if [[ $retval -ne 100 && $retval -ne 101 && $retval -ne 102 ]];
	then
		exit 1
	fi
    # return the result from counterExample1
    #if [[ $retval -eq 0 ]]; then
    #	echo "UNSAFE" 
    #elif [[ $retval -eq 1 ]]; then
    #	echo "SAFE"
    #elif [[ $retval -eq 2 ]]; then
	#	echo "UNKNOWN"
    #fi
    return $retval
}

function pe() {
    local file=$1
    local outfile=$2
    $PE/props -prg "$file" -l 3 -o "$resultdir/$f.props" || exit 1
    $PE/peunf_smt_2 -prg "$file" -entry false -props "$resultdir/$f.props" -type int -o "$resultdir/$f.pe.pl" || exit 1
}

#=================

resultdir="temp"
f=`basename $1`
f=${f%.pl} # remove .pl extension
f=${f%.smt2} # remove .pl extension

if (test ! -d $resultdir) then
        mkdir $resultdir
fi

#echo input file $1
#echo "Translation from competition format to Prolog-readable form"
python $SMT2CHC/format.py --split_queries False --simplify False "$1" > "$resultdir/$f.pl" || exit 1
#echo "Translation normalisation"
$SMT2CHC/chcNorm "$resultdir/$f.pl" "$resultdir/$f.norm.pl" -int || exit 1
prog="$resultdir/$f.norm.pl"


#echo "Removal of redundant arguments"

$LIB_RAHFT/raf "$prog" false "$resultdir/$f.raf.pl" || exit 1
prog="$resultdir/$f.raf.pl"

# search for counterexamples first for 15 seconds
#tlimit="0.25m"
#result="unknown"
#timeout $tlimit $PE/tpclp -prg "$prog" -cex || exit 1
#ret=$?
#terminate=0
#if [[ $ret -eq 100 ]]; then
#    	terminate=1
#    elif [[ $ret -eq 101 ]]; then
#    	terminate=1
#	 else
#		terminate=0
#fi

# set very large iteration limit for competition
k=1000
i=1
terminate=0
until [[ $k -eq 0 || $terminate -eq 1 ]];
do
   #echo "Iteration" $i
   #echo "Specialisation"
   spec "$prog" "$resultdir/$f.sp.pl"
   #echo "Checking safety"
   checksafe "$prog"
   ret=$?
   if [ $ret -eq 100 -o $ret -eq 101 ]; then
		terminate=1
   else
		k=`expr $k \- 1`
		i=`expr $i \+ 1`
		#echo "Partial evaluation"
		pe "$resultdir/$f.sp.pl" "$resultdir/$f.pe.pl" || exit 1
		prog="$resultdir/$f.pe.pl"
		
   fi
done 


if [[ $ret -eq 101 ]]; then
    	echo "unknown" 
    elif [[ $ret -eq 100 ]]; then
    	echo "sat" 
    elif [[ $ret -eq 102 ]]; then
	echo "unknown" 
fi

#rm widenpoints wut.props traceterm.out temp/*


