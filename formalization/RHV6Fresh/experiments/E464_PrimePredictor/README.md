# E464 — experiment requested by the author: a prime "predictor" through the Towers — pre-registration

> Français : [README.fr.md](README.fr.md)

Author's order (2026-11-09): attempt a prime predictor with the grammar, the reconstruction by the contacts and the
discoveries of the project; goal mentioned: a prime of a million digits, checked only at the end. LATERAL experiment: it does not
belong to the proof route (the rule "never test the primes directly", §19.40, holds for the route; the author here explicitly
orders this experiment). No fabricated output; this commit precedes any execution.

## Method (fixed before execution)
* Data: `experiments/data/odlyzko_zeros6_2001052.txt` (2 001 052 zero heights, all on the line in this range).
* Predictor: for an integer `n`, the sum of the Towers (real value of each Tower, Fejér weight `1 − height/max height`) gives
  a reconstructed demand; the prediction reads its JUMP between `n − 1/2` and `n + 1/2`. Rule: "`n` is prime" if and only if
  the jump exceeds three quarters of `log n` (a prime square jumps by half, a composite by zero).
* No sieve, no primality test in the prediction. The control (exact sieve) is done only AT THE END, on the entire window.
* Windows: 300 consecutive integers starting from 10^3, 10^4, 10^5, 2·10^5, 3·10^5, 5·10^5, 10^6, 10^7, 10^8.
* Two families: the 2 001 052 Towers, then the first 500 000 (to read how the horizon depends on the maximal height).
* Measurements per window: true primes, predicted, correct, missed, false; length of the cell of the highest Tower at this abscissa.

## Expectation written before execution (threshold rule, E441–E443)
The cell of the highest Tower measures about `π·x / max height`. As long as it is shorter than an integer step, the jump
is resolved and the prediction must be exact; beyond, the Towers no longer separate two neighbouring integers. Expected horizon: `x` of the order
of the maximal height divided by π (about 360 000 for 2 million Towers, about 100 000 for 500 000).

## Feasibility of the million digits (stated before execution)
If the horizon follows this law, locating a prime near `10^(10^6)` requires Towers up to a height of that order, hence a number
of zeros itself of about a million digits: out of any reach. Moreover, checking "the last 30 digits" does not check
primality: it depends on the whole integer. The experiment therefore measures the real horizon and the scaling law; it does not promise the
million digits.

## Pre-written verdicts
* A: exact prediction (no miss, no false) in all the windows under the expected horizon, degraded beyond, horizon
  proportional to the maximal height between the two families.
* B: exact under the horizon but scaling law different from the expectation (stated as is).
* C: errors under the expected horizon (the predictor does not hold).
Bounded execution under `nohup`, log versioned as `.txt`.
