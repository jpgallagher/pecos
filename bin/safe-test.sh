#!/bin/sh

resultfile="results.txt"
tlimit="0.2m"
echo "Run benchmarks in $1\n\n" > $resultfile

shopt -s nullglob
for file in $1/*.{smt,smt2}
do
   echo "`basename $file`"
   echo "`basename $file`" >> "$resultfile"
   START=$(date +%s)
   timeout "$tlimit" sh starexec_run_lia.sh $file 
   case $? in
			"124") 
				echo "TIMEOUT "$tlimit"" >> "$resultfile"
				;;
			"137")
				echo "TIMEOUT "$tlimit"" >> "$resultfile"
				;;
			"1")
				echo "TERMINATED BEFORE TIMEOUT" >> "$resultfile"
				;;
			*)  END=$(date +%s)
   				DIFF=$(( $END - $START ))
				echo "TIME: "$DIFF" secs" >> "$resultfile"
				;;
		esac
   echo "================\n" >> "$resultfile"
done
shopt -u nullglob
#rm  -r temp widenpoints wut.props traceterm.out 
