#!/bin/bash
# usage: modlist.sh <project> <root1,root2,...>  -> prints module names having olean
F=/opt/NeuroSymbolicModel/formalization
cd $F/$1/.lake/build/lib/lean
for r in ${2//,/ }; do
  [ -f $r.olean ] && echo $r
  [ -d $r ] && find $r -name '*.olean' | sed 's/\.olean$//; s#/#.#g'
done | sort -u
