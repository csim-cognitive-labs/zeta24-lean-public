# E447 — The break mechanism on the critical line, written with the contacts (pre-registration, §19.69, 2026-11-07)

> Français : [README.fr.md](README.fr.md)

Author's order (R-LINE): as long as Lean remains to be written, do not look for the contradiction; master the break
mechanism from the line (ON zeros, `β = 1/2`) perfectly before any deduction on the OFF. Authorized objects: one
Tower `(1/2, T)`, its contacts, its cells, its real values at the contacts; the primes, `rawDemand`, `cellDemand`,
`cellWeight`, `cellPrimeWeight`; the signed rules. No sum of Towers, no spectral object, no hypothesis, no statement
on `β ≠ 1/2`.

## Hypotheses (to be decided by the compiler, then by the numbers)
* H1 (exact attribution): the break `log q` at the prime `q` enters the weighted budget with the value of the last
  contact before `q`; on the line this value is EXACTLY `√q · e^{−π f/(2T)} / ‖(1/2, T)‖` with `f` the cell
  fraction at the point `q`; hence between `√q · e^{−π/(2T)}` and `√q` (over the norm).
* H2 (Abel balance): the weighted sum of the cell slopes of a block is, EXACTLY, the boundary term (value × raw
  demand at the two extreme contacts) plus `(1 + e^{π/(2T)})` times the weighted sum of the raw demands at the
  interior contacts: the collective budget is read on the raw demand AT THE CONTACTS, not on the cells.
* H3 (square rule on the line): the square of the value at the contact is the abscissa of the contact over the square
  of the norm; the ratio of the squares of two consecutive values is the ratio of the cell lengths.
* H4 (break then descent): in a cell that crosses only one weight, the raw demand between the contact and the
  prime equals `log q − (q − C_k)`: a jump up at once, linear descent.
* H5 (size of the weighted demand at the contacts): `|v_k · R(C_k)| / C_k^{3/2} → 0` along the Tower (PNT ported).

## Planned statements (isolated module `Terminal/BreakMechanismOnLine.lean`, import `MeetingRegimeFinite`)
L1 `demandAtContact`, `cellDemand_telescope`; L2 `valueCellSum_abel` (any `β`), `contactRealValue_succ`,
`valueCellSum_abel_signed`; L3 `line_contactRealValue_sq`, `line_value_sq_succ`, `line_value_sq_ratio_eq_length_ratio`;
L4 `contact_of_fraction` (`C_k = x·e^{−π f/T}`), `line_break_amplitude_exact`, `line_break_amplitude_bounds`,
`line_break_price_bounds`; L5 `rawDemand_prime_from_contact`, `break_then_descent`; L6 `demandAtContact_div_tendsto_zero`,
`line_weighted_demand_at_contact_small`. At most two compilation attempts, each output kept in `attempts/`.

## Experiment (after compilation; Odlyzko zeros, `β = 1/2`, 7 heights, primes ≤ 10⁷)
(a) residual of the Abel identity on blocks of 50 cells at each decade; (b) exact formula of the amplitude at the
break against direct computation, and bracketing; (c) `|v_k R(C_k)| / C_k^{3/2}` per decade; (d) H4 on cells with a
single weight. mpmath deterministic twin with 30 digits on a subset. Criterion: A if all identities are exact to
floating-point precision and (c) decreases; B if an identity compiles but the number contradicts; C otherwise.
No conclusion on the OFF is drawn, by order.
