# E465 — Φ8: the collective balance written in slopes of the demand on the pieces cut by the contacts — pre-registration

> Français : [README.fr.md](README.fr.md)

Reference: `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.95; E463 (§19.93), E438 (§19.55–19.56), E464 (§19.94). Author's order of
2026-11-09: "I agree with the next task […] do it completely". No hypothesis admitted, no axiom, no `sorry`;
isolated module `RHV6Fresh/Terminal/CollectiveSlopeOnPieces.lean`, NOT added to `RHV6Fresh.lean`. This commit contains the final module and
precedes any compilation (no probe).

## Audit (done before this pre-registration)
* E463 (K7): on every piece, the sum of the shares of all the members of a recomposition equals the variation of the SMOOTHED signal of the
  primes multiplied by the abscissa. The arithmetic member was not written with the raw demand.
* E438: the raw demand, on every piece, descends by one unit per unit of length and receives the weight of each integer crossed;
  the cutting of a gap by the contacts (`gap_variation_eq_remainders`) holds for ANY function.
* The bridge: the abscissa times the smoothed signal is the sum of the weights crossed since the origin, each multiplied by its distance to
  the abscissa; it is an integrated quantity (second order) of the demand. On a piece it therefore varies by an AREA of the demand.
* Names checked by grep: no duplicate (`integratedSignal`, `demandArea`, `residualBackground`, `integratedDemandC`, …).

## What the module must compile (statements pre-written, in words)
* S1 the abscissa times the smoothed signal is the integrated signal (sum of weights times distance).
* S2 on a piece, the integrated signal varies by the starting level times the length, plus each weight crossed times its distance to the end.
* S3 main term removed, this variation is the area of the demand: demand at the start times length, minus half the square of the
  length (descent of slope one), plus each weight crossed times its distance to the end of the piece.
* S4 piece without weight: pure descent. S5 the areas add up from piece to piece.
* S6 piece interior to a gap: only non-prime weights.
* S7 piece of a gap going up to the meeting: the weight of the prime of the meeting enters with a ZERO distance; no prime weight
  enters the area of a gap (it enters through the starting level of the next gap).
* S8 piece crossing a single integer, prime: its weight enters through its distance to the end of the piece.
* S9 a piece shorter than an integer step crosses at most one integer (lesson of E464, see below).
* S10 collective balance: the sum of the shares of all the members on a piece equals the area of the demand, minus the variation of the residual
  background (background of E462 deprived of its main term).
* S11 on a cell between two consecutive contacts of a Tower: the term of this Tower in the total is its share from E463; the total
  is the area of the demand on the cell.
* S12 the area of the demand on a gap is cut by the contacts of a Tower (initial remainder, whole cells, final remainder);
  each remainder is an area; collective balance of the entire gap.

## Lessons of E464 used
* L1 (scale): the predictor separates an integer only if the cell of the highest Tower is clearly shorter than an integer
  step. Hence S9: it is the geometric threshold below which a cell isolates at most one weight; beyond, the area of a cell
  mixes several weights and no "one prime per cell" reading is permitted (consistent with E446: finite regime).
* L2 (reading order): the predictor reads a JUMP of the reconstructed raw demand; the signal recomposed without remainder is second
  order: a meeting makes no jump in it, it changes the slope. Hence S7–S8: the weight enters through a distance, zero at the meeting.
* L3 (method): the numerical horizon announced before E464 was wrong by a factor 2 to 3. Here no numerical threshold is announced;
  the twin verifies only exact identities, with a pre-written rounding tolerance.

## Classification against RH (stated before compilation)
No hypothesis posed. S1–S12 are unconditional identities, valid for every recomposition, on the line as well as off the line.
They exclude no off-line zero. The share of ONE Tower remains unread on the primes of its cell: only the total is.

## Deterministic twin (pre-written)
`twin.py`: 50-digit arithmetic; verifies S1–S3, S5, S7, S8 and S12 on the contact cells of the first 5 Towers of the
line and on the first 200 gaps; criterion: relative gap at most 10^-30 everywhere. Bounded (under a minute), under `nohup`.

## Pre-written verdicts
A: S1–S12 compiled in at most two attempts, standard axioms, full build green, twin conforming. B: a statement changes form
(stated as is). C: failure after two attempts (recorded, module removed).
