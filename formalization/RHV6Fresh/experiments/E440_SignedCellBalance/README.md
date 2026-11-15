# E440 — The signed balance of the cells along the series: the descent cancels to within one cell, the weights of the meetings stay with their sign

> Français : [README.fr.md](README.fr.md)

Pre-registration (2026-11-07), before any compilation. Author's order: "YES CONTINUE. GREEN LIGHT. CONTINUE THE
SAME APPROACH" after E439 (§19.57). Spectral prohibition in force (§19.55).

## Verification of the nine mistakes
1. No new hypothesis. 2. The compiler decides. 3. Names checked by grep (`cellDemand`, `cellWeight`,
`cellPrimeWeight`, `signedCellSum`, `cellLength` free; `rawDemand_variation`, `cell_linear_length`,
`signed_cells_bounded_by_last`, `no_prime_crossed_inside_gap`, `meeting_cell_primes`, `meetingCell` reused).
4. `lake build RHV6Fresh` after any change. 5. No prime or OFF tested directly. 6. No radial
position. 7. No family of Towers, no sum of contributions. 8. Isolated module. 9. Intervals = partial remainders.

## Question
Each cell carries a sign `(−1)^k` and a slope (weights crossed − length). What is the SIGNED sum of the slopes
of consecutive cells along the series? Does the descent, whose lengths grow, cancel by
alternation? What remains: the weights of the meetings with the sign of their cell?

## Targeted statements (isolated module `Terminal/SignedCellBalance.lean`)
- B1 `cellDemand`, `cellLength`, `cellWeight`, `cellDemand_eq`: slope of a cell = weights crossed − length.
- B2 `cellLength_nonneg`, `cellLength_mono`: lengths positive and increasing with the index.
- B3 `inner_cell_demand_le`, `cellDemand_eq_neg_length_of_no_weight`: a cell interior to a gap has a slope
  at most equal to the non-prime weights minus its length; without weights, strictly negative pure descent.
- B4 `signedCellSum`, `signedCellSum_eq`: signed sum of the slopes = signed sum of the weights − signed sum of the lengths.
- B5 `signed_lengths_bounded`, `signedCellSum_near_signed_weights`: the signed sum of the lengths is bounded by the
  last cell; the signed sum of the slopes is, to within one cell, the signed sum of the weights.
- B6 `cellPrimeWeight`, `cellWeight_eq_prime_add_nonprime`, `cellPrimeWeight_inner_eq_zero`,
  `cellPrimeWeight_meeting`: the weight of a cell separates into prime weight and non-prime weight; zero in prime
  weight on an interior cell; equal to `log p_{n+1}` on the meeting cell.
- B7 `meeting_cell_demand_nonneg_of_short`: the meeting cell rises as soon as it is shorter than the weight
  of the meeting.

## Protocol and criteria
Unversioned probe, at most two attempts for the final module, logs, `#print axioms`, complete build.
A: contradiction; B: everything compiles; C: failure in two attempts. Expected: B.
