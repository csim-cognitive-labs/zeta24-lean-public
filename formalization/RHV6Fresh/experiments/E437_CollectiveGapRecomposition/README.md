# E437 — Collective recomposition of a gap by the partial remainders of several Towers, raw channel (2026-11-07)

> Français : [README.fr.md](README.fr.md)

Compilation-only experiment (no numerical measurement). Author's order (§19.53): knowledge and mastery of the
gaps and the contacts BEFORE any radial hunt. No radial position enters a conclusion; no OFF zero;
no infinite sum; no return to spectral analysis.

## Written verification of the nine points (CLAUDE.md (private research repository))
(1) nothing on the synchronization; (2) no criterion on the structure; (3) nothing read on a mixed signal: each share
is the variation of the Tower between the two bounds of the gap; (4) no definition requested; (5) no word attributed;
(6) action delivered; (7) no pair treated; (8) gaps never linked to the height; (9) no Tower touches a prime:
the bounds of the gap are the primes, the contacts cut out the share of each Tower.

## Question posed (before compilation)
In the raw channel (demand `ψ(x) − x` on the real axis), how does a FINITE family of Towers recompose a gap through
the partial remainders of each, what does the explicit remainder carry, and how does the balance pass to the next gap? And, point
of the author: is the remainder necessary (can a finite family recompose the gap alone)?

## Hypotheses admitted
None.

## Established results reused (Lean form checked before use)
`Chebyshev.psi` (Mathlib), `massA`, `massA_succ`, `massA_eq_psi`, `psiRemainder`, `towerRe`, `breakResidual`,
`breakResidual_erase`, `PrimeGapInterval` (`lower`, `upper`, `one_lt_lower`, `lower_lt_upper`), `meetingPoint`,
`thm_primeAtRank_isPrime`, `GapHasContact`, `gap_variation_eq_remainders`, `initialEdgeRemainder`, `wholeCellSum`,
`finalEdgeRemainder`, `consecutive_lower_eq_upper`, `ArithmeticFunction.vonMangoldt_apply_prime`.

## Protocol
1. Pre-registration (this file, commit) before any compilation.
2. Name probes in `CollectiveGapRecomposition_SCRATCH.lean` (unversioned, deleted after capture; outputs in
   `logs/probe_attempt*.txt`).
3. Isolated module `Terminal/CollectiveGapRecomposition.lean` (not added to `RHV6Fresh.lean`), at most two attempts,
   logged (`logs/lean_attempt{1,2}.txt`), no `sorry`, axioms displayed, `lake build RHV6Fresh` green.

## Targeted statements and expectations (written before execution)
- **R1 Collective recomposition.** For a finite family each member of which has a contact in the gap, the sum of the
  shares = sum over the members of (initial partial remainder + whole cells + final partial remainder). Expected: compiles
  (sum of `gap_variation_eq_remainders`).
- **R2 Balance of a gap with explicit remainder.** Demand of the gap = shares of the family + variation of the explicit remainder
  over the gap. Expected: identity, compiles.
- **R3 Passage to the next gap.** Over a series of gaps, the variations of the remainder and the demands telescope.
  Expected: compiles.
- **R4 Descent between meetings.** Between two consecutive integers the raw demand descends linearly; at the passage
  of the integer it jumps by the weight of the integer. Expected: compiles (`massA_succ`, floor).
- **R5 Continuity of the family.** Every finite family of Towers is continuous at every positive abscissa. Expected: compiles.
- **R6 The remainder carries the jump.** For every finite family, the variation of the explicit remainder at the passage of a meeting
  tends to the weight of the prime (the whole jump). Expected: compiles.
- **R7 No finite family recomposes the meeting.** The explicit remainder cannot be constant to the left of a
  prime. Expected: compiles by R6 (uniqueness of the limit, weight of a prime > 0).
If R6/R7 fail, goals are reproduced in full, never renamed "what is missing".

## Criteria
A compiled closure; B new unconditional reduction (collective recomposition of a gap by the partial remainders,
explicit remainder carrying the whole jump, compiled); C equivalence to RH; D nothing compilable. Expected: B.
