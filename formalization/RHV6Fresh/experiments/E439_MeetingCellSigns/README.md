# E439 — The sign of the cell that contains the meeting, along a series of gaps

> Français : [README.fr.md](README.fr.md)

Pre-registration (2026-11-07), before any compilation. Author's order: "yes continue" after E438 (§19.56);
spectral prohibition in force (CLAUDE.md (private research repository) "SPECTRAL PROHIBITION" (INTERDICTION SPECTRALE), §19.55).

## Verification of the nine mistakes
1. No new hypothesis. 2. The compiler decides. 3. Names checked by grep (`meetingCell`, `cellSign`,
`lastContactBefore_mono`, `contactRealValue_sign_shift` free; `lastContactBefore`, `wholeCellCount`,
`firstContact_add_count`, `contactRealValue_add_nat`, `rawDemand_variation`, `no_prime_crossed_inside_gap`,
`lastContact_difference_bounds`, `thm_noPrimeStrictlyBetweenSuccessivePrimes` reused). 4. `lake build RHV6Fresh`
after any change. 5. No prime or OFF tested directly. 6. No radial position. 7. No family of
Towers, no sum of contributions: ONE Tower, ITS contacts, the cells, their signs, the series of gaps.
8. Isolated module, not added to `RHV6Fresh.lean`. 9. The contact intervals are partial gap remainders.

## Question
Each meeting `p_{n+1}` is in the cell opened by the last contact before it (E438). What is the sign of
this cell along the series of gaps, how is the parity transmitted from one meeting to the next, and what
do the partial remainders on either side of a meeting impose on the slope of this cell?

## Objects
New (definitions only): `meetingCell β T I = lastContactBefore β T I.upper` (index of the cell that
contains the meeting), `cellSign k = (−1)^k`. All others exist.

## Targeted statements (isolated module `Terminal/MeetingCellSigns.lean`)
- S1 `contactRealValue_eq_sign_mul`, `contactRealValue_sign_shift`: the value at the contact carries the sign `(−1)^k`; the
  contact `m` ranks further has the sign multiplied by `(−1)^m`.
- S2 `meetingCell_eq_next_lower`: the cell of the meeting of gap `n` is the cell that opens gap `n+1`
  (the sign is transmitted to the next gap).
- S3 `lastContactBefore_mono`, `meetingCell_step`: if gap `n+1` contains a contact, the index of the meeting cell
  advances by the number of contacts crossed (whole cells + 1); `meetingCell_eq_of_no_contact`: otherwise the
  two meetings are in the same cell.
- S4 `meeting_sign_step`: the sign of the meeting cell changes according to the parity (whole cells + 1) of the
  gap crossed; `meeting_sign_same_of_no_contact`.
- S5 `meetingCell_telescope`, `meeting_sign_series`, `meetingCell_series_read_by_frequency`: over a series, the
  displacement of the index telescopes, the sign is the parity of the total displacement, and this displacement is read by the
  frequency and the ratio of the two meetings to within one unit.
- S6 `inner_cell_variation`: every whole cell strictly interior to a gap is a pure descent (non-prime weights
  only); `meeting_cell_demand`: the meeting cell, recomposed by the final remainder of the gap
  and the initial remainder of the next, carries exactly ONE prime weight, that of the meeting, plus non-prime
  weights, minus its length; `meeting_cell_demand_ge`.

## Protocol and criteria
Unversioned probe `*_SCRATCH.lean`, at most two attempts for the final module, logs in `logs/`,
`#print axioms`, then complete build. A: contradiction with a compiled fact; B: everything compiles, nothing declared missing;
C: a statement does not compile in two attempts. Expected: B.
