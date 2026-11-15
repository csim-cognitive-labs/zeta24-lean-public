# E466 — confrontation of four readings of the prime predictor (pre-registration, 2026-11-12)

> Français : [README.fr.md](README.fr.md)

LATERAL experiment (outside the proof route, like E464). Response to the external audit transmitted by the author on 2026-11-12, whose points
are accepted and taken up here as specifications: (A) E464 used no grammar; (B) the threshold 0.75 is arbitrary and masked
a separation still present at cell 0.55–0.83; (C) the Fejér effect must be MEASURED, not explained; (D) the second difference
of the integrated signal (E465) equals the exact weight only for the exact signal, the truncation error remains in the second difference and
must be measured, the background required by the formula must be kept; (E) the horizon "max height / pi" is a resolution scale of the
method, supported by the measurements, NOT a proved impossibility (the theorem `short_piece_crosses_at_most_one` proves only one
direction). Rectification recorded: my sentence of 2026-11-12 "horizon out of reach for a reason of theorem" is WITHDRAWN.

## What is frozen
* E464 remains the immutable reference (code, results, log unchanged). Its channel is reproduced here as is (variant J-F).
* Data: `experiments/data/odlyzko_zeros6_2001052.txt`, two families (2 001 052 Towers; 500 000 Towers), as in E464.
* Windows of 300 integers. Reference windows (those of E464): 10^3, 10^4, 10^5, 2·10^5, 3·10^5, 5·10^5, 10^6, 10^7, 10^8.
  NEW windows (never read before): 5·10^4, 1.5·10^5, 2.5·10^5, 4·10^5, 7·10^5.
* No sieve, no primality test in the prediction. Exact control (division) AT THE END only, categorized: primes,
  prime powers, other composites (point 6 of the audit).

## The four score channels (all normalized by the logarithm of the integer)
* J-F: jump of the reconstructed demand between n−1/2 and n+1/2, Fejér weight (= E464 exactly).
* J-noF: same jump, without Fejér (sharp cut-off at the maximal height).
* D2-F: second difference over an integer step of the reconstructed INTEGRATED signal (E465: x times the smoothed sum), Fejér weight.
  The reconstructed integrated signal keeps the background required by the formula: half the square, linear term of the logarithm of two pi,
  sum of the trivial zeros (five terms); the constants disappear in the second difference, the half-square gives exactly one.
* D2-noF: same second difference, without Fejér.
Expected exact value of the score (exact signal): 1 on a prime, 1/k on a k-th power, 0 elsewhere.

## Pre-written decisions (none will be modified after reading the results)
* R0: "prime" if score > 0.75 (E464 rule, kept for comparison).
* R1: "prime" if score > 0.75 AND the integer passes the mod 6 grammar (remainder 1 or 5; necessary, never sufficient). It can
  only remove false positives; it cannot create any miss.
* R2 (geometric abstention): the decision is DEFERRED on every window where the cell of the highest Tower exceeds 1 integer
  step (information of the contacts/cells usable BEFORE the prediction, non-circular). Errors are counted separately
  on decided and deferred windows.
* The raw scores (min on primes, max on composites, max on prime powers, margin = min primes − max composites)
  are kept for each window and each channel, independently of any threshold.
* Reconstruction error (point D): for each channel, max over the window of |score − exact value|, on each category.

## Information from the contacts: what I looked for and what I did not find (stated before execution)
Apart from the resolution (length of the finest cell, used by R2), I have identified no NON-circular use of the
contacts that discriminates two neighbouring integers: the succession theorems (gap, meeting, final remainder) take the true primes
as input. Any variant that used them would be circular. This point is recorded as a negative research finding, to be reopened if a compiled
statement gives a reading of the contacts computable without the primes.

## Expectations written before execution
* A1: J-F reproduces E464 identically (same counts, same scores to 10^-9).
* A2: the D2 and J channels give very close scores (the second difference of the truncated integrated signal is, to first order,
  the jump of the truncated signal); I do NOT expect a resolution gain from the sole passage to the second difference.
* A3: without Fejér, sharper separation where it exists (cell < 1) but stronger parasitic oscillations: margin may
  increase OR decrease; I announce no direction. My conjecture "Fejér divides the effective height by two" is TESTED by the
  comparison of the positive-margin horizons between F and noF; it is refuted if the positive-margin horizon does not move.
* A4: the mod 6 grammar changes nothing in the counts (E464 had no false positive).
* A5: new windows: same regimes as E464 at the same cells (exact ≤ 0.28; separation without threshold 0.5–0.85; overlap ≥ 1).

## Pre-written verdicts
* A: A1 true, and at least one channel has a positive margin on a window where J-F has none (information gain measured).
* B: A1 true, no channel extends the positive-margin horizon of J-F (the change of reading brings nothing; only the
  calibration of the threshold mattered).
* C: A1 false (reproduction of E464 failed): everything else is suspended.
Bounded execution under `nohup`, `timeout` 45 min, log `logs/run.txt` versioned, results `results.json`.
