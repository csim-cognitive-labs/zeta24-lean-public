#!/bin/bash
cd /opt/NeuroSymbolicModel/formalization/RHV6Fresh/experiments/audit_semantique
for p in RHV6Fresh rhv3_lean rhv2_fresh rhv4_lean RHV5Fresh rh_gap_criterion; do
  s=$(date +%s); python3 run_extract.py $p >> data/extract_log.txt 2>&1; echo "$p secs=$(( $(date +%s)-s ))" >> data/extract_log.txt
done; echo FIN >> data/extract_log.txt
