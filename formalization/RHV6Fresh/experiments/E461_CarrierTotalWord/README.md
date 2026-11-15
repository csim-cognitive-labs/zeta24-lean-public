# E461 — Φ5: the selection of carriers read on the TOTAL word (author's proposal of 2026-11-09) — pre-registration

> Français : [README.fr.md](README.fr.md)

Reference: `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.90; §19.71 (E449, the word determines the Tower), §19.82 and §19.85 (E457, exact scope),
§19.86 (E460, audit of the weight). No hypothesis admitted, no axiom, no `sorry`; isolated module
`RHV6Fresh/Terminal/CarrierTotalWord.lean`, NOT added to `RHV6Fresh.lean`. No spectral theory. No prime nor off-line zero
tested. This commit precedes any compilation of the module (no prior probe).

## Author's proposal
"Totality of the contacts of a Tower = same rhythm, same phase, same frequency, same relation to the primes ⟹ it is a zero."
External re-reading transmitted by the author: the geometric uniqueness is established; the arithmetic implication is the theorem to establish,
in the form "exact arithmetic realization of the Tower ⟺ Tower coming from a zero", provided the realization is defined
INDEPENDENTLY of the vanishing of zeta.

## What the module must compile (statements pre-written, in words)
* T1 `tower_eq_of_same_towerWord`: two Towers (radial position and height strictly positive) with the same total word are the same Tower
  (rewriting of E449 on `towerWord`).
* T2 `isCarrier_iff_of_same_towerWord`: two Towers with the same total word are carriers together or non-carriers together.
* T3 `ReadsCarriers P` (definition): the predicate `P` on words reads the selection — on every Tower, `P` of the word ⟺ carrier.
  `totalWordCarrier` (definition) and `readsCarriers_totalWordCarrier`: such a reader EXISTS. It is defined BY the weight: this is
  existence, not the independent arithmetic definition.
* T4 `readsCarriers_unique_on_tower_words`: two readers coincide on all the words of Towers (the reader is unique where it matters).
* T5 `readsCarriers_zeroWord`: every reader is true on the word of every true zero, on the line as well as off the line.
* T6 `readsCarriers_not_finite_window`: no reader depends on a finite window of ranks (as soon as a true zero is given) —
  the author's proposal requires the TOTALITY, in exact agreement with E457.
* T7 `zero_data_eq_of_same_zeroWord`: two true zeros with the same word have the same height and the same radial position.

## Classification against RH (stated before compilation)
* "Realization ⟺ zero" characterizes the carriers, those of the line as well as off the line (T5): it is NOT a reformulation of RH
  and by itself it excludes no off-line zero. RH would require IN ADDITION: "no off-line Tower is realized".
* The direction "realization ⟹ zero" has content only if the realization is defined without the weight and without the vanishing of zeta. The corpus has
  no definition of this kind read on a single Tower (E460); the only exact relation known between Towers and primes is collective,
  and the collective channel is forbidden. The independent definition is the object to look for; it is NOT supplied by this module.

## Pre-written verdicts
* A: T1–T7 compiled in at most two attempts, standard axioms, ban at zero, full build green.
* B: a statement requires a form different from the pre-written one (stated as is).
* C: failure after two attempts (recorded, module removed).
No numerical twin: no numerical statement, everything is logical.
