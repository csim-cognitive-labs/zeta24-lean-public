# E423 — ON/OFF comparison at the contacts: real displacements of the contacts and associated values (pre-registered 2026-11-03)

> Français : [README.fr.md](README.fr.md)

Objective: compare, at the same height T* (midpoint of two consecutive real zeros: never the height of a real zero), an
ON Tower (β = ½) and an OFF Tower (β ≠ ½, alone or in a mirror pair β, 1−β), keeping the true displacements of the contacts
and the real values at the displaced contacts. Synthetic scenario, separate file, no primes, gaps, cells or li.

Predictions (Lean module `ContactRealValue.lean`, written before execution):
* logarithmic displacement of contact k: (φ(β) − φ(½))/T*, the same for all k, of modulus < π/(2T*) (less than half a step);
* value at the displaced contact: (−1)^k C_k(β)^β/|ρ_β| against (−1)^k C_k(½)^{½}/|ρ_½|: same sign at the same k, ratio of the moduli
  C_k(β)^β |ρ_½| / (C_k(½)^{½} |ρ_β|);
* mirror pair: the contacts of β and of 1−β never coincide (β ≠ ½); at the contact of member β, member 1−β has a nonzero imaginary
  part; the sum of the two members (with conjugates) crosses the axis at proper positions (roots of Im of the
  complex sum), to be measured and compared with the ON contacts;
* in the family of the 2,001,052 line zeros (E422), the insertion of the OFF Tower or of the pair changes S_F at the ON contacts of
  height T* by the inserted contribution alone (identity), which is measured in value and in share.
None of these measures is read as an exclusion of OFF zeros.
