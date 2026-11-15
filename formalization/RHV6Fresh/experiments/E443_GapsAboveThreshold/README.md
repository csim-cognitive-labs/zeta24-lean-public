# E443 — Gaps above the threshold: what the contacts and their signs alone say

> Français : [README.fr.md](README.fr.md)

Pre-registration (2026-11-07), before any compilation and any execution. Follows E442 (§19.61), under the order
"pursue as far as possible". Spectral ban in force (§19.55); working order §19.53.

## Check of the nine errors
1. No new hypothesis (Bertrand and the Chebyshev bounds `ψ − θ ≤ 2√x log x` are theorems of Mathlib / of the corpus,
   no asymptotics, no PNT, no spectral theory). 2. The compiler decides. 3. Names checked by grep
   (`primeSuccessor_le_two_mul` reused from `ContinuousProgression`; `gap_le_lower`, `wholeCellCount_lt_log_two`,
   `meetingCell_displacement_lt`, `gap_in_cell_of_no_contact`, `gap_demand_variation`, `gap_primes_singleton`,
   `cellNonPrimeWeight_le_sqrt`, `meeting_falls_above_second_threshold` free). 4. `lake build RHV6Fresh` after every
   change. 5. No prime and no OFF tested directly. 6. No radial position. 7. No family. 8. Isolated module.
   9. Intervals = partial remainders.

## Question
Above the threshold `x*` of a Tower (`x*(r−1) = log x*`), its cells are longer than the weights of the meetings;
most gaps no longer have a contact and fit in a single signed cell. What do the contacts, the intervals and their
signs then say: how many contacts at most per gap (Bertrand), where does a gap without contact fit, what is the
slope of an entire gap, and from what height (second threshold `x**`) does every meeting cell surely descend, the
non-prime weight being bounded by Chebyshev.

## Targeted statements (isolated module `Terminal/GapsAboveThreshold.lean`, imports `ExactDisplacementAndThreshold` and `ContinuousProgression`)
- A1 `gap_le_lower`, `upper_le_two_lower`: Bertrand on the gap (`p_{n+1} − p_n ≤ p_n`).
- A2 `wholeCellCount_lt_log_two`: fewer than `T log 2/π` whole cells in any gap.
- A3 `meetingCell_displacement_lt`: the displacement of the meeting cell between two consecutive gaps is
  `< T log 2/π + 1`.
- A4 `gap_in_cell_of_no_contact`: a gap without contact fits in the cell of its meeting.
- A5 `gap_primes_singleton`, `gap_demand_variation`: the slope of an entire gap = `log p_{n+1}` + non-prime
  weights − length of the gap (no contact hypothesis).
- A6 `cellNonPrimeWeight_le_sqrt`: non-prime weight of a cell `≤ 2√C_{k+1} log C_{k+1}` (Chebyshev,
  Mathlib `psi_sub_theta_le`).
- A7 `meeting_falls_above_second_threshold`: if `log p + 2√(p r) log(p r) < p(1 − 1/r)`, the meeting cell
  descends (condition in `p` and `T` alone).

## Numerical experiment (`scripts/e443a_above_threshold.py`, twin `scripts/e443b_twin_mpmath.py`)
Towers of ranks 1, 100, 10³, 10⁴, 10⁵ (β = ½), primes ≤ 10⁶, exact Λ. Controls (0 violations expected): A1–A7.
Measurements: share of gaps with a contact per decade against the rule `mean(min(1, g/L))`; second threshold `x**`
(solved) against the smallest `p` beyond which every meeting cell descends; between `x*` and `x**`, share of meeting
cells that descend; primes per cell against `L/log p`; share of cells of positive slope above `x*` (measurement
without theorem, labelled as such).

## Protocol and criteria
Unversioned probe, at most two attempts for the final module, logs, `#print axioms`, full build; bounded scripts
(< 10 min), `nohup`, no fabricated output. A: contradiction; B: everything compiles and 0 violations;
C: failure in two attempts. Expected: B.
