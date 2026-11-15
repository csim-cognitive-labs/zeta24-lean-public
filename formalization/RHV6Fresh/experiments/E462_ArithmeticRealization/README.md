# E462 — Φ6: the arithmetic realization of a Tower, defined by the collective recomposition of the primes — pre-registration

> Français : [README.fr.md](README.fr.md)

Reference: `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.92; §19.90–19.91 (E461, author's proposal, lifting of the ban on the
collective); `Terminal/SpectralUniqueness.lean` (uniqueness of the representation of the channel, 2026-09-30). Author's order of 2026-11-09:
"I validate, continue" (track named in §19.91). No hypothesis admitted, no axiom, no `sorry`; isolated module
`RHV6Fresh/Terminal/ArithmeticRealization.lean`, NOT added to `RHV6Fresh.lean`. No prime nor off-line zero tested. This commit precedes
any compilation of the module (no prior probe).

## Prior audit of the collective modules (done before this pre-registration)
`SpectralUniqueness.lean` already compiles, without premise: the channel of the zeros is a function of the arithmetic side alone
(`channel_eq_arithmetic`: smoothed sum of von Mangoldt minus the background); every representation of this channel by a locally
finite family of distinct points contains each zero with its multiplicity (`contains_member`) and carries no weight outside the zeros
(`no_intruder`). This module was never linked to the Towers nor to the reader of E461. E462 makes this junction, without proving anything new in
analysis.

## Proposed definition (independent of the weight and of the vanishing of zeta at the point of the Tower)
* `ArithmeticRecomposition`: a locally finite family of distinct points of the plane, equipped with weights, whose series of kernels gives back,
  for every `x > 1`, the smoothed sum of von Mangoldt minus the smooth background. The right-hand side reads only the primes and a FIXED background,
  the same for all Towers. Said honestly: this background contains the series of trivial zeros and two constants of zeta (logarithmic
  derivative at 0 and at −1); it contains neither the point of the Tower, nor its weight, nor any non-trivial zero.
* `ArithmeticallyRealized β T`: there exists an arithmetic recomposition which carries a non-zero weight at the point of the Tower.

## What the module must compile (statements pre-written, in words)
* R1 `ArithmeticRecomposition.toSpectral`: every arithmetic recomposition is a representation of the channel (by `channel_eq_arithmetic`).
* R2 `trueRecomposition`: an arithmetic recomposition exists (that of the zeros).
* R3 `arithmeticallyRealized_iff_isCarrier`: for every strictly positive height, realized ⟺ carrier.
* R4 `arithmeticallyRealized_iff_zeta_eq_zero`: for every strictly positive height, realized ⟺ zeta vanishes at the point of the Tower.
  This is the statement requested by the external re-reading: "exact arithmetic realization ⟺ Tower coming from a zero".
* R5 `recomposition_contains_carrier`: EVERY arithmetic recomposition carries a non-zero weight at the point of every carrier Tower;
  `recomposition_weight_eq_zero_of_not_isCarrier`: NONE carries a weight at the point of a non-carrier Tower. (There exists ⟺ for all.)
* R6 `arithmeticWordCarrier` and `readsCarriers_arithmeticWordCarrier`: the total-word reader defined by the arithmetic realization
  reads the selection (it is a `ReadsCarriers` of E461, this time defined without the weight).
* R7 `arithmeticWordCarrier_iff_totalWordCarrier`: it coincides with the reader of E461 on all the words.
* R8 `riemannHypothesis_iff_realized_on_line`: RH ⟺ every realized Tower (positive height) is on the line.

## Classification against RH (stated before compilation)
* The definition is not a hypothesis: nothing is posed. R3–R7 are unconditional and hold for the carriers of the line as well as off
  the line; they exclude no off-line zero. This is not a reformulation of RH.
* R8 is the classification itself: "realized ⟹ on the line" is EQUIVALENT to RH (implication and converse compiled); it is never a
  premise. The frontier does not move: it remains to find why an off-line Tower cannot appear in the recomposition.
* Limit stated in advance: the realization so defined is COLLECTIVE and existential (it quantifies over the recompositions of the entire
  signal of the primes); it is not a criterion read on the cells of the Tower alone. "The primes fall in the cells
  when they must", read cell by cell on a single Tower, is not supplied; E457 moreover forbids any finite window.

## Pre-written verdicts
* A: R1–R8 compiled in at most two attempts, standard axioms, full build green.
* B: a statement requires a form different from the pre-written one (stated as is).
* C: failure after two attempts (recorded, module removed).
No numerical twin: no numerical statement, everything is logical.
