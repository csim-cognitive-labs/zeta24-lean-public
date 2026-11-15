# E427 — Grammar of the prime gaps reconstructed from the Towers, and stability of the contacts (pre-registered 2026-11-04)

> Français : [README.fr.md](README.fr.md)

Author's directive (two messages of 2026-11-04). Corrected absolute priority: **reconstruct the grammar of the prime
gaps from the Towers of the authentic zeros** (states, transitions, alternation, bounded oriented balance, exact return),
the primes serving only to **validate** afterwards; only then, say whether the grammatical balance corresponds to a
geometric conservation at the contacts; finally, only then, the constraints on the Towers. No spectral projection posed
as a hypothesis, no OFF hypothesis, no contradiction sought, no premise equivalent to RH.

Reference Lean module, compiled BEFORE execution: `Terminal/GrammarContactStability.lean` (isolated, not added to
`RHV6Fresh.lean`; no `sorry`, standard axioms; three attempts logged in `logs/lean_attempt{1,2,3}.log` —
the third fixes a single tactic bookkeeping error (missing `congr 1`) in the proposition
`pathOfWord_wordOfPath`, with no change of statement; recorded as is).

## Objects reused (never rebuilt)
* Reference grammar: `TransitionRigidity.lean` (`PrimeTransition`, `pairTransition`, `raccord_exact`,
  `eventTransition`, `event_word_valid`, `event_gap_eq`), `Grammar/Mod6Rigidity.lean` (`state6`, `GoodMod6`, `gapClass6`),
  `GrammarDwellDecomposition.lean` (`ind1`, `orientation_telescopes`, `weighted_orientation_variation_bound`).
* Compiled spectral reconstruction: `RawEventReconstruction.lean` (`reconstructedVonMangoldt`, `reconstructedPrimeEvent`,
  `reconstructedPsi_eq_limit_contact_accumulation`), `PrimeGapReconstruction.lean` (`reconstructedPrimeAtRank`,
  `reconstructedPrimeGap_eq_actualGap`, `contact_accumulation_reconstructs_prime_gaps`).
* Authentic contacts: `ContactRealValue.lean` (`contactRealValue`), `FirstExceedanceRaccord.lean` (`cellIndexAt`),
  `MeetingPoint.lean` (`meetingPoint` = end of a prime gap, `relativeAmplitude`), `GrammarDrift.lean`
  (`meeting_drift`, `meeting_drift_eq_one_iff`), E420–E426.

## Compiled predictions that the experiment must recover
* `orientedBalance_telescopes`, `orientedBalance_abs_le_one`: oriented balance = indicator of the initial state − indicator
  of the final state; confinement in {−1, 0, +1}.
* `crossings_cancel_15_51`, `crossings_cancel_51_15`, `orientedBalance_dwell`: exact return after two inverse
  crossings, whatever the number of intermediate dwells; neutrality of the holds.
* `confinement_not_dwell_equality`: confinement does not imply equality of the numbers of dwells.
* `card_validWords_twelve`: 8,192 valid words of twelve transitions.
* `eventOrientation_of_gap`: orientation ⟺ gap ≡ 4, 2, 0 (mod 6).
* `reconstructedState_goodMod6`, `reconstructedTransition_cls`, `reconstructedWord_valid`,
  `reconstructedBalance_abs_le_one`, `reconstructedTransition_eq_actual`: the reconstructed sequence (spectral predicate) carries
  the two states, the four transitions, the junction, the confinement; rank-by-rank validation.
* `weightedBalance_abs_le`, `contact_weighted_balance_abs_le`: balance weighted by real values at the contacts bounded
  by the total variation of the weights, for every height and every radial position.
* `logRatio_not_determined_by_transition`, `amplitude_ratio_not_determined_by_transition`: same transition, distinct
  ratios (29 → 31 against 113 → 127).
* `return_drift_eq_one_iff`: on a segment of zero balance, the relative amplitude drift is neutral ⟺ β = ½.

## Data (provenance and fingerprints)
* Zeros: `experiments/data/odlyzko_zeros6_2001052.txt` (2,001,052 heights, SHA-256 checked at loading by
  `contact_common.load_zeros`, `.sha256` file alongside).
* Primes: sieve of Eratosthenes computed in the script (exact integers), no external list; twin: second
  independent sieve in pure Python integers up to 10⁶.
* Spectral weights of E415 (`experiments/E415_RawEventReconstruction/data/lam{A,B}_W*.npy`) for the truncation scale;
  the values at full truncation are **recomputed** here from the zeros (fingerprint of the npy files recorded).

## E427(a) — exact reference grammar (`scripts/e427a_grammar_reference.py`, integers)
Primes 5 ≤ p ≤ 10⁸ (5,761,453 primes > 3). Measures, all expected-exact **identities**:
1. conformity: each transition (state of p, state of p') has the prescribed class (p' − p) mod 6 (0 hold, 4 for 1 → 5,
   2 for 5 → 1); number of violations expected 0;
2. cumulative oriented balance ∈ {−1, 0, +1} at every rank (0 violations expected); histogram of the three values (measurement);
3. return: for each crossing `t15` (resp. `t51`), the balance at the next inverse crossing equals 0 (0 violations
   expected); distribution of dwell lengths between two inverse crossings (measurement, no law);
4. equality of dwells: N11 − N55 at each rank (measurement: unbounded expected, Chebyshev bias; no law);
5. enumeration: 8,192 valid words of twelve transitions by brute-force enumeration of the 4¹² = 16,777,216 words (identity);
   number of words of twelve transitions **realized** by the primes ≤ 10⁸ (measurement, no property attributed).
Twin: second independent sieve up to 10⁶, same counts (exact equality required).

## E427(b) — level 1, grammar reconstructed from the Towers (`scripts/e427b_level1_reconstruction.py`)
Windows W1 = [3, 300], W2 = [10,000, 10,060], W3 = [100,000, 100,030]; truncations H ∈ {1,000, 5,000, 100,000, 10⁶,
2,001,052}. Chain, with no arithmetic data:
1. Towers of the zeros (β = ½, heights of the file) → collective sum of the signed values (raw channel A: ψ̂₀ at half-integers;
   integrated channel B) → Λ̂(n); **route by authentic contacts** (H = 1,000, W1, raw channel): accumulation of each Tower
   on its own contacts in [n − ½, n + ½] (`accumulate_one`), compared with the difference of the values at the edges
   (compiled identity `contact_accumulation_eq_endpoint_difference`, difference expected ≤ 10⁻¹⁰ relative);
2. pre-registered rule of E416 (closest admissible value of {0, log n, log n / k}) → reconstructed prime
   events;
3. **reconstructed states** = residue modulo 6 of each reconstructed prime (reading on the reconstructed sequence only);
   **reconstructed transitions** (consecutive states, class = reconstructed gap mod 6); validity of the junction; alternation
   of the crossings; cumulative oriented balance; return after inverse crossings — all computed on the reconstructed sequence;
4. **validation (afterwards)**: comparison state by state, transition by transition, balance by balance with the grammar of the
   true primes of the window (sieve). Success criterion of level 1: at full truncation, 0 disagreements on W1,
   W2, W3 (states, transitions, balance); truncation scale recorded (disagreements expected at small truncations, E416).
5. **Separation controls** (synthetic, never at the heights of real zeros): (i) same heights, β = 0.3 for all
   Towers (displaced family); (ii) pseudo-random heights of the same density (Riemann–von Mangoldt, seed 20261104,
   verification that no height coincides with a real zero to within 10⁻⁹), β = ½. Same chain 1–4. Reading: if the
   grammar is recovered only with the authentic zeros, the arithmetic information is in the collective of the zeros;
   the contacts are only the partition.
Deterministic twin: Λ̂(n) at 30 digits (mpmath) for n ∈ {3, 5, 7, 97, 101} and H = 1,000, difference ≤ 10⁻⁹.

## E427(c) — level 2, transport of the balance at the contacts (`scripts/e427c_level2_contacts.py`)
Prime events of ranks 2 to 2,001 (5 ≤ p ≤ 17,393); authentic Towers of the zeros of ranks 1, 10, 100, 1,000, 10,000,
100,000, 1,000,000, 2,001,052 (β = ½); separation Towers: same heights, β ∈ {0.3; 0.7} (synthetic).
For each Tower and each event r: contact that opens the cell of the meeting point p_{r+1} (`cellIndexAt`), its signed
real value (`contactRealValue`), the relative amplitude at the meeting points.
1. weighted balance Σ orientation(r)·v_r over sliding windows of 12 and 120 events, against the compiled Abel bound
   (0 violations expected: identity); balance/bound ratio (measurement);
2. transport candidates: (α) shift of contact index between successive meeting points, (β') variation of
   log-amplitude β·log(p_{r+2}/p_{r+1}); distributions conditional on orientation (+1, −1, 0); mutual information
   orientation ↔ candidate, compared with the mutual information orientation ↔ gap (orientation is a function of the
   gap mod 6: `eventOrientation_of_gap`); pre-registered criterion for a transport: a function f such that
   candidate = f(orientation) to within 10⁻⁹ for all events; expected (compiled): no candidate satisfies it;
3. correction of drifts: segments of zero balance (crossing then inverse crossing) against segments of nonzero balance;
   relative amplitude drift on each segment; at β = ½ expected exactly 1 on ALL segments (identity
   `meeting_drift_eq_one_iff`), at β ≠ ½ never 1; the return of the balance does not modify the drift (compiled
   `return_drift_eq_one_iff`);
4. separation: same measures for the synthetic Towers; identical conclusions expected.
Twin: values at the contacts at 30 digits (mpmath) for the Tower of zero 1 and ten events, difference ≤ 10⁻¹².

## Refutation and success criteria (fixed before execution)
* Level 1 succeeded ⟺ 0 disagreements at full truncation on W1–W3 and separation controls failing (grammar not
  recovered from the synthetic families). Otherwise: failure recorded.
* Level 2: a geometric conservation law is declared only if a candidate satisfies the transport criterion;
  expected (compiled): none; the Abel bound is an identity, not a law.
* Level 3: no constraint on β is sought or read in this experiment.
No criterion will be modified after execution. Results, including negative ones, in `RESULTS.md`.
