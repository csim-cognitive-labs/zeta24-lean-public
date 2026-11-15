# E463 — Φ7: the recomposition of the primes read on the cells of a Tower — pre-registration

> Français : [README.fr.md](README.fr.md)

Reference: `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.93; E462 (§19.92), E436–E438 (§19.52–19.56). Author's order of
2026-11-09: "Do this audit and continue". No hypothesis admitted, no axiom, no `sorry`; isolated module
`RHV6Fresh/Terminal/RecompositionOnCells.lean`, NOT added to `RHV6Fresh.lean`. This commit precedes any compilation (no probe).

## Audit (done before this pre-registration)
* E436–E438 cut a gap by the contacts of ONE Tower, in the raw channel, for FINITE families with an explicit remainder;
  E437 compiles that the jump of a meeting is carried entirely by this remainder, never by a finite family.
* E462 recomposes the SMOOTHED signal of the primes by the entire family, without remainder, uniquely.
* The two were never brought together. The bridge: multiplied by the abscissa, the smoothed kernel of a Tower is a primitive of its raw
  value; its variation from one abscissa to the abscissa located one cell further is therefore the share of the Tower on that cell.

## What the module must compile (statements pre-written, in words)
* K1 `integratedKernel` (definition: abscissa times smoothed kernel) and its closed form `integratedKernel_eq`.
* K2 `cell_step_cpow`, `cell_step_kernel`: advancing by one cell of the Tower multiplies its integrated kernel by an exact factor,
  negative, whose modulus depends only on the frequency and the radial position.
* K3 `towerCellShare` (definition: share of the Tower on a cell) and `towerCellShare_eq` (closed form).
* K4 `towerCellShare_next`: the shares on two consecutive cells are in this same ratio (alternating sign, fixed amplitude).
* K5 `cell_ratio_reads_radial`: at a given frequency, this ratio determines the radial position.
* K6 `towerCellShare_ne_zero_iff`: the share on a cell is non-zero if and only if the weight is non-zero.
* K7 `recomposition_piece_balance`: for every arithmetic recomposition and every piece, the sum of the shares of all the members
  equals the variation of the smoothed signal of the primes (background removed), multiplied by the abscissa.
* K8 `recomposition_cellShare_ne_zero_of_isCarrier`, `recomposition_cellShare_eq_zero_of_not_isCarrier`: in every recomposition,
  a carrier Tower has a non-zero share on EACH of its cells; a non-carrier Tower has a zero share on each.

## Classification against RH (stated before compilation)
No hypothesis posed. K1–K8 hold on the line as well as off the line. The ratio of K4 reads the radial position (third order respected)
but forbids none: nothing excludes an off-line zero. Not done here: write the arithmetic member of K7 as a sum of slopes
of the raw demand on the pieces of E438 (finite identity, to be done in a second stage if the author wants).

## Pre-written verdicts
A: K1–K8 compiled in at most two attempts, standard axioms, full build green. B: a statement changes form (stated as is).
C: failure after two attempts (recorded, module removed). No numerical twin: exact identities.
