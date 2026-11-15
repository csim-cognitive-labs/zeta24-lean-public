# E444 — The signed balance carried by the frequency AND the amplitude: the contacts read the radial position

> Français : [README.fr.md](README.fr.md)

Pre-registration (2026-11-07), before any compilation and any execution. Follows E443 (§19.62) under the
**author's correction §19.63**: the contacts recover the radial position through the project's tangential formulas;
a Tower has a frequency AND an amplitude; the interval on the real axis is defined by both. Spectral ban in force
(§19.55, a single Tower); working order §19.53 (we write the balance, we do not chase an OFF).

## Check of the nine errors
1. No new hypothesis. 2. The compiler decides. 3. Names checked by grep (reused: `contactRealValue`,
   `contactRealValue_succ`, `abs_contactRealValue_ratio`, `radial_of_contact_tangent`, `height_of_contact_log_step`,
   `cellLength_add_nat`, `meetingOffset`, `meetingOffset_eq`, `cellPrimeWeight_meeting`,
   `cellPrimeWeight_inner_eq_zero`, `lastContactBefore_of_mem_cell`, `meetingCell_displacement_lt`; new:
   `stagePosition_sub_radial`, `towerPhase_lt_of_radial_lt`, `stagePosition_lt_of_radial_lt`,
   `radial_of_stagePosition`, `radial_of_cellFraction`, `cellLength_ratio`, `height_of_cellLength_ratio`,
   `radial_of_value_and_length_ratios`, `contactRealValue_add_nat`, `valueLengthSum`, `valueLengthSum_closed_form`,
   `valueCellSum`, `valueCellSum_eq_signed`, `valuePrimeSum`, `valuePrimeSum_eq_primes_in_block`,
   `amplitudeMeetingSum`, `valuePrimeSum_eq_meetings`, `meeting_value_step`, `meeting_value_ratio_sign`,
   `meetingOffset_lt_bertrand`). 4. `lake build RHV6Fresh` after every change. 5. No prime and no OFF tested
   directly. 6. Radial position: READ by the contacts (§19.63), never chased. 7. No family, a single Tower.
   8. Isolated module. 9. Intervals = partial remainders.

## Question
Resume the signed balance of the series (§19.60–19.62) with the two variables of the Tower: each cell weighs by the
real value of the Tower at its contact (sign AND amplitude, `contactRealValue β T k = (−1)^k C_k^β/‖ρ‖`), and not
by its sign alone. Show that (i) the sign of the cell of a real number and the cell fraction read `β`; (ii) the
interval returns `T` through its ratio of lengths and `β` through its ratio of amplitudes; (iii) the balance of
lengths weighted by the amplitude has a closed form whose ratio reads `β + 1`; (iv) the prime weight weighted over a
block of cells (several meetings per cell, above `x*`) is the sum of the meetings weighted by the value of their
cell; (v) between two consecutive meetings, the ratio of values is `(−e^{βπ/T})^{Δ}` with `Δ` the displacement,
bounded by Bertrand: the number of sign changes is `< T log 2/π + 1` and the amplitude ratio reads `β`.

## Targeted statements (isolated module `Terminal/AmplitudeSignedBalance.lean`, imports `GapsAboveThreshold` and `ContactRealValue`)
- B1 `stagePosition_sub_radial`, `towerPhase_lt_of_radial_lt`, `stagePosition_lt_of_radial_lt`: at fixed `T` and `x`,
  the cell position increases strictly with `β`; the sign of the cell of a real number depends on `β`.
- B2 `radial_of_stagePosition`, `radial_of_cellFraction`: `β = T / tan(T log x − π·(cell + fraction))`.
- B3 `cellLength_ratio`, `height_of_cellLength_ratio`, `radial_of_value_and_length_ratios`:
  `T = π/log(L_{k+1}/L_k)` and `β = log(|v_{k+1}|/|v_k|) / log(L_{k+1}/L_k)`: the interval is defined by both.
- B4 `contactRealValue_add_nat`, `valueLengthSum_closed_form`: ratio `−e^{(β+1)π/T}`.
- B5 `valueCellSum_eq_signed`: the weighted balance = initial value × signed sum with geometric weight `e^{βπ/T}`.
- B6 `valuePrimeSum_eq_primes_in_block`, `valuePrimeSum_eq_meetings`: meetings weighted by their cell.
- B7 `meeting_value_step`, `meeting_value_ratio_sign`, `meetingOffset_lt_bertrand`.

## Numerical experiment (`scripts/e444a_amplitude_balance.py`, twin `scripts/e444b_twin_mpmath.py`)
Towers of ranks 1, 10, 100, 10³, 10⁴, 10⁵, 2·10⁶ (β = ½), meetings up to 10⁶, exact Λ. Controls (0 violations
expected): B2 (β read at each meeting from the cell fraction), B3 (β and `T` read on each cell), B4 (closed form),
B6 (block identity), B7 (ratio of values and Bertrand bound on sign changes).
Measurements: **R9** share of meetings whose sign changes when `β` goes from ½ to `β'` ∈ {0.1; 0.3; 0.7; 0.9; 1},
against the phase shift `|arctan(T/β) − arctan(T/β')|/π`; **R10** growth of the sum of meetings weighted by the
amplitude, relative to the value of the last cell; **R11** above `x*`, number of meetings per cell and of sign
changes between consecutive meetings against the Bertrand bound.

## Protocol and criteria
Unversioned probe, at most two attempts for the final module, logs, `#print axioms`, full build; bounded scripts
(< 10 min), `nohup`, no fabricated output. A: contradiction; B: everything compiles and 0 violations;
C: failure in two attempts. Expected: B.
