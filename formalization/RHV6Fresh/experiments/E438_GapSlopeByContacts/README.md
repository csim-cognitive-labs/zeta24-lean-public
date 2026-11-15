# E438 — The slope of the gap reconstructed by the contacts, the intervals and their signs

> Français : [README.fr.md](README.fr.md)

Pre-registration (2026-11-07), before any compilation. Author's order: prohibition of any spectral theory
(CLAUDE.md (private research repository) "SPECTRAL PROHIBITION" (INTERDICTION SPECTRALE), master document §19.55). Thread: the slope of the gap and the reconstruction of the gaps by the
contacts.

## Verification of the nine mistakes
1. No new hypothesis. 2. The compiler decides. 3. Names checked by grep (`rawDemand`, `initialEdgeRemainder`,
`wholeCellSum`, `finalEdgeRemainder`, `GapHasContact`, `contactRealValue`, `wholeCellCount`, `lastContactBefore`,
`cellFraction`, `thm_noPrimeStrictlyBetweenSuccessivePrimes` reused; no duplicated name). 4. `lake build RHV6Fresh`
after any change. 5. No prime or OFF tested directly. 6. No radial position. 7. No sum of Towers,
no family, no zero channel: ONE Tower, ITS contacts, the pieces they cut out, their signs. 8. Isolated module,
not added to `RHV6Fresh.lean`. 9. The contact intervals are partial gap remainders, never linked to the position
of a prime.

## Question
Between two meetings the raw demand `ψ(x) − x` descends by one unit per unit of length; at the meeting it jumps
by the weight `log p`. The contacts of a Tower cut the gap into initial remainder, whole cells, final remainder, each
piece bordered by contacts of alternating signs. How is the slope distributed over these pieces, and what do the
signs say?

## Objects (all existing)
`rawDemand` (E437, raw channel: `ψ(x) − x`), `PrimeGapInterval`, `contactAt`, `contactRealValue` (sign `(−1)^k`),
`lastContactBefore`, `firstContactAfterLower`, `wholeCellCount`, `initialEdgeRemainder`, `wholeCellSum`,
`finalEdgeRemainder`, `GapHasContact`, `gap_variation_eq_remainders`, `thm_noPrimeStrictlyBetweenSuccessivePrimes`.
Mathlib: `Chebyshev.psi_eq_psi_coe_floor`, `Finset.sum_Ioc_consecutive`, `Nat.floor_eq_iff`.

## Targeted statements (isolated module `Terminal/GapSlopeByContacts.lean`)
- R1 `rawDemand_variation`: for `0 ≤ a ≤ b`, variation of the demand = sum of the weights of the integers crossed − (b − a).
- R2 `rawDemand_pure_descent`: if no integer crossed has a weight, variation = −(b − a).
- R3 `gap_length_eq_pieces` / `gap_demand_eq_pieces`: length and demand of the gap cut by the same contacts.
- R4 `no_prime_crossed_inside_gap`: no piece interior to the gap crosses a prime;
  `finalRemainder_carries_meeting`: the weight of the meeting is in the final remainder (when the last contact is
  strictly before the meeting).
- R5 `contactRealValue_add_nat`, `gap_edge_contacts_sign`: sign of the last contact = (−1)^(whole cells) × sign of the
  first contact.
- R6 `cell_linear_length`, `finalRemainder_shorter_than_cell`: linear length of a cell, final remainder < cell.
- R7 `wholeCellCount_bounds`: bracketing of the number of whole cells by `T·log(p_{n+1}/p_n)/π`.
- R8 `alternating_sum_le_last` (attempt): signed sum of a positive increasing sequence bounded by the last term.

## Protocol
Probe `*_SCRATCH.lean` (unversioned, deleted after capture), at most two compilation attempts, logs in
`logs/`, `#print axioms` on each statement, then complete `lake build RHV6Fresh`.

## Criteria
A: a statement contradicts a compiled fact. B: everything compiles, facts recorded, nothing declared missing. C: a statement does not
compile in two attempts (recorded with the exact errors). Expected: B (R8 possibly C).
