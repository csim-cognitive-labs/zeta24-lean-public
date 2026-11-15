# E428 — Reading of the transitions by the complete progression of the contacts over a series of gaps, individual–collective junction and radial information of the mirror (pre-registered 2026-11-04)

> Français : [README.fr.md](README.fr.md)

Plan: §19.42 (proposal), §19.42.5 (author's obligations A–D), §19.42.6 (author's four corrections,
conditional green light). Directives: series of gaps, never an isolated gap; do not reduce the study to frequency
alone; no OFF hypothesis, no bound posed, no anticipated contradiction; the primes serve only to
validate afterwards; predictions compiled before measurement; deterministic twin; criteria fixed here, not modified afterwards.

Reference Lean module, compiled BEFORE execution: `Terminal/ContactSeriesReading.lean` (isolated, not added to
`RHV6Fresh.lean`; no `sorry`; at most two attempts, each logged in `logs/lean_attempt{1,2}.log`).

## Objects reused (never rebuilt)
`cellIndexAt`, `stagePosition`, `cellIndexAt_eq_ceil` (CellRestitution, FirstExceedanceRaccord); `contactAt`,
`contactAt_ratio`, `accumulationFrom`, `contact_accumulation_eq_endpoint_difference` (ContactValueGeometry);
`contactRealValue` (ContactRealValue); `truncatedStep`, `truncatedStep_eq`, `lowFrequencies`, `integratedTowerTerm`,
`reconstructedVonMangoldt_eq_limit_contact_accumulation` (RawEventReconstruction); `complexMode`, `mirrorMode_add`,
`mirrorMode_sub`, `mirrorMode_add_norm`, `mirrorMode_add_norm_ge` (HarmonicRestoringLaw);
`inversion_from_consecutive_contacts` (JointParameterReading); `transitionOf_cls`, `eventOrientation_of_gap`
(TransitionRigidity, GrammarContactStability); `logRatio_not_determined_by_transition` (GrammarContactStability).

## Compiled predictions that the measurement must recover (statements of the module)
* **A0** `truncatedStep_eq_sum_individual`: truncated step = background + finite sum (over `lowFrequencies H`) of the
  individual contributions; `individual_contribution_eq_own_contact_accumulation`: each contribution is
  the accumulation of its own Tower on its own contacts, whatever `(β, T, k₀, n)`;
  `collective_eq_individual_add_rest`: collective = one Tower + the rest (safeguard: never a single Tower alone);
  `reconstructedVonMangoldt_eq_limit_of_individual_sums`: the limit in `H` of these sums is `Λ̂(N)` (same
  truncation, same smoothing, same limit as the compiled theorem).
* **A1** `seriesShift_telescopes`: the consecutive index shifts of a series add up to the total shift.
* **A2** `cellIndex_difference_bounds`: `|Δk − T·log(q'/q)/π| < 1` for all `(β, T > 0)`;
  `log_ratio_bracket`: `|log(q'/q) − hΔk| < h`, `h = π/T`.
* **A3 corrected** `estimate_brackets`: `q̂e^{−h} < q < q̂e^{h}`; `certified_rounding`: `q̂(e^h − 1) < ½ ⟹ |q − q̂| < ½`;
  `certified_unique_integer`: a single integer within ½ of `q̂`. The certification reads only `(p, T, Δk)`.
  `old_threshold_not_certifying`: counterexample where `q(e^h − 1) < ½` but `q̂(e^h − 1) ≥ ½` (former threshold of the plan).
* **A4** `mirror_series_amplitude_difference`: over a series, amplitude of the mirror − amplitude of the Tower =
  `(1 − 2β)·log(q/p)`, zero ⟺ `β = ½` (identity; no law posed).
* **C corrected** `mirror_contact_log_ratio`: `log(C_k(β)/C_k(1−β)) = (φ_β − φ_{1−β})/T`;
  `mirrorPhaseShift_eq_zero_iff`: zero ⟺ `β = ½`; `mirror_stagePosition_difference`: constant in `q`;
  `mirror_series_shift_difference_le_one`: the index differences of the Tower and of the mirror over the same series
  differ by at most one unit (to be checked in measurement, never presumed equal);
  `mirrorMode_sub_norm`: `‖v₊ − v₋‖ = 2|sinh(dt)|` (no floor: the lower bound ≥ 2 holds only for the sum).

## Data
Zeros `experiments/data/odlyzko_zeros6_2001052.txt` (SHA-256 checked by `contact_common.load_zeros`); primes by
sieve in the script (exact integers); authentic Towers of the zeros of ranks 1, 10, 100, 1,000, 10,000, 100,000,
1,000,000, 2,001,052 (β = ½); separation Towers: same heights, β ∈ {0.3; 0.7} (synthetic, always in mirror
pair, never at the heights of another real zero).

## E428(a) — certified reading by series (`scripts/e428a_series_reading.py`)
Anchors r ∈ {2, 100, 1000} (p_r = 5, 541, 7,919); series m ∈ {12, 120, 1200}; all the Towers above.
For each (Tower, r, m) and each j ≤ m: Δk_j = k(p_{r+j}) − k(p_r) read in the Tower; `q̂_j = p_r·exp(πΔk_j/T)`;
certification `q̂_j(e^h − 1) < ½`; integer read = rounding of `q̂_j`; word of transitions of the series read (class mod 6 of the
gaps read, orientation). Validation afterwards: comparison with the true primes and the true word.
Criteria: (i) **0 false certified readings** (otherwise refutation of a compiled statement: error to be located);
(ii) number of certified readings, number of exact uncertified readings (recorded, never claimed);
(iii) comparison former threshold / corrected threshold: number of cases where the former would certify wrongly;
(iv) at the same height, β = 0.3 / 0.5 / 0.7: fraction of distinct Δk_j (radial information of the indices, obligation C);
the certified word read is expected identical (it is a function of the prime read, unique) even when Δk differs.
Twin: mpmath 30 digits, Tower of zero 1 and of zero 2,001,052, anchor 2, j ≤ 12.

## E428(b) — mirror, individual–collective junction, search for a law on a series (`scripts/e428b_mirror_series.py`)
Events r = 2..2001 (5 ≤ p ≤ 17,393), same Towers in pairs (β, 1 − β).
1. **C**: phase shift `(φ_β − φ_{1−β})/π`; absolute Tower/mirror indices at each p (fraction of inequality,
   difference ∈ {⌊s⌋, ⌈s⌉} where s = shift/π); differences over series from each anchor: Tower/mirror difference
   in {−1, 0, +1} (0 violations expected), nonzero fraction (measurement); log-ratio of contacts against the formula;
   norm of the mirror sum `2cosh(dt)` and of the difference `2|sinh(dt)|` at abscissas `t = log p` (identities).
2. **A0**: for N ∈ {5, 7, 11, 101, 1009}, H = 1,000: truncated collective step (sum over zeros of height ≤ H) against
   sum of the individual contributions (identity, difference expected ≤ 10⁻¹⁰ relative); contribution of a single Tower
   against the collective (never equal: safeguard).
3. **A4, search for a law**: sliding windows of 12 events (1,989 windows, words of 12 transitions);
   candidates on the series: total amplitude `β·log(p_{end}/p_{start})`, sum of the signed values at the meeting
   contacts, weighted oriented sum, number of nonzero Tower/mirror index differences in the window, Tower/mirror
   amplitude difference. Pre-registered criterion for a law: at identical word (windows sharing the same word of 12
   transitions, groups of at least 2 windows), range of the candidate ≤ 10⁻⁹ for all groups. Expected (compiled
   `logRatio_not_determined_by_transition`): no length candidate satisfies it; the candidate "Tower/mirror
   index differences" is measured with no expectation.
Twin: mpmath 30 digits on 10 events for the pair (0.3; 0.7) at the height of zero 1.

## Verdict on three levels (criteria fixed)
* **A0 / A1–A3**: succeeded ⟺ compiled statements and 0 false certified readings; otherwise error recorded.
* **C**: succeeded ⟺ 0 violations of the {−1, 0, +1} difference; the nonzero fraction is the measured radial information.
* **A4 / B**: a law is declared only if the word criterion is satisfied; expected: none for the length
  candidates; result of the mirror candidate recorded as is.
* **D**: not executed here; frontier unchanged unless A4 provides a law (then only, next step).
No criterion will be modified after execution. Results, including negative ones, in `RESULTS.md`.
