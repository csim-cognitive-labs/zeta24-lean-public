#!/bin/bash
F=/opt/NeuroSymbolicModel/formalization
D=$F/RHV6Fresh/experiments/audit_semantique/data
for p in rhv3_lean rhv2_fresh rhv4_lean RHV5Fresh RHV6Fresh rh_gap_criterion; do
  cd $F/$p
  s=$(date +%s)
  lake build > $D/${p}_build.log 2>&1
  echo "$p exit=$? secs=$(( $(date +%s)-s ))" >> $D/build_results.txt
done
echo DONE >> $D/build_results.txt
