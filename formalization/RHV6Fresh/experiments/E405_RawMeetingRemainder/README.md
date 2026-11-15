# E405 — The raw remainder at the meeting points: numerical twin of the module `RawMeetingRemainder.lean` (2026-11-02)

> Français : [README.fr.md](README.fr.md)

Pre-registered BEFORE execution (committed before launch; results added afterwards). Bounded execution (< 10 min),
real (sieve), no fabricated output. Three SEPARATE parts: real (primes by sieve, Odlyzko zeros on the line),
synthetic OFF twin (heights never equal to an existing ON height), deterministic identities.

## What the Lean compiles (to be checked numerically, not discovered)
1. Raw remainder `r(N) = ψ(N) − N`. Between two meetings (integers of nonzero weight), `r` descends by exactly one unit per
   integer; at a meeting it jumps by the weight. Hence, between two meetings, `|r|` is bounded by the maximum of its values
   at the two ends (`abs_rawRemainder_le_of_noEvent`).
2. Raw → smoothed bridge at the integer: `M·A(M) = Σ_{k<M} ψ(k)` (`natMul_smoothedVonMangoldtSum_eq`,
   `rawCumulative_eq_sum_massA`).
3. A bound `|r(E)| ≤ C·E^θ` and `|r(E−1)| ≤ C·E^θ` at the meetings `E` only gives the same bound at every integer
   (factor `C·2^θ + 1`, Bertrand), then `‖smoothed remainder(x)‖ ≤ C'·x^θ` for every `x > 1`, then `β ≤ θ` for every member
   (`zero_re_le_of_rawRemainder_at_events`).

## Part 1 — real, identities (deterministic)
- Sieve of Λ up to X = 2,000,000; `r(N)` for all N ≤ X.
- Exact verification of 1 (descent of one unit between meetings, over all N) and of 2 (for M in a fixed list).
- For θ ∈ {0.50, 0.52, 0.55, 0.60}: maximum of `|r(E)|/E^θ` and `|r(E−1)|/E^θ` over the meetings E ≤ X, maximum of
  `|r(N)|/N^θ` over all N ≤ X, and verification of the compiled inequality `max_N ≤ (2^θ·max_E + 1)` (the +1 comes from N = 1).
- By dyadic slice [2^j, 2^{j+1}): maximum of `|r(E)|/√E` at the meetings (reading: does it grow? does not decide θ).

## Part 2 — attempt A (pre-registered in §19.34.5), real
- At the meeting points p_{n+1} (primes ≤ 100,000): exact smoothed remainder `R(p) = A(p) − B(p)` (background of E401 via mpmath),
  = telescoped sum of the demands of the preceding gaps + R(p_1). Sign of each demand, number of sign changes,
  maximum of `|R(p)|/p^θ` for θ ∈ {0.5, 0.6, 0.7}. Declared failure criterion: if no cancellation law can be written
  other than "the partial sum IS the remainder", A is a tautology (executor's prediction).

## Part 3 — attempt B (pre-registered in §19.34.6), real + synthetic twin, minimal
- Six consecutive gaps n = 614..619 (those of E404). At the meeting point p = p_{n+1}: raw channel, sum of the terms
  `x^ρ/ρ` of the zeros of height < π·p (head) against the true raw remainder averaged over the two sides (sieve); tail = true − head.
- Synthetic pair β = 0.6 at a height T chosen in the middle of two consecutive ON heights (never an ON height):
  raw deposit of the pair at the six meetings, step between consecutive meetings, compared to the head and to the tail.
- Declared failure criterion: if the absorption of the pair's step by the head is constrained only by per-member constancy
  (⟺ RH, §19.21), B is dead (executor's prediction).

## Rule
No conclusion about β will be drawn from the numerical maxima: what is missing is the exponent at the meetings, and only the
compiler decides it. The figures serve as a twin of the identities and as a reading, not as proof.

## Results (added after execution; `e405_results.txt`, 4.2 s; a first launch stopped after
part 1 on a numpy → mpmath cast, fixed with `int(p)`, relaunched in full, part 1 identical)
Part 1 (real, identities). Sieve up to two million: 148,933 primes, 149,235 raw meetings. The descent
of one unit per integer between meetings is exact on the 1,850,765 non-meeting integers (difference zero). The identity
"M times the smoothed sum at M equals the sum of ψ(k) for k < M" holds up to machine rounding for the seven M
tested. The maxima of |ψ(N) − N|/N^θ at all meetings (both sides) and at every integer respect the compiled
inequality (factor 2^θ plus one) for the four exponents; the global maximum is attained at N = 1 (value one).
Dyadic slices up to two million: the maximum of |ψ(E) − E|/√E at the meetings oscillates between 0.19 and 0.71
with no readable trend at this scale. No conclusion about θ: ultimate growth is not a measurement.
Part 2 (attempt A). 9,592 meetings (primes ≤ 100,000): 4,777 positive demands, 4,814 negative, 471
sign changes; the telescoped sum of the demands is, identically, the smoothed remainder at the last point minus the
remainder at the first. The quotients |R(p)|/p^θ are all small (maximum attained on the very first p) and
decreasing. Verdict by the declared criterion: A is a tautology. The "cancellation law" is only the value of the
remainder; no identity on the primes alone appears that would give the exponent otherwise.
Part 3 (attempt B, minimal). Six consecutive meetings (4547 to 4591): the head (zeros of height below
π times the prime, about fifteen thousand) carries almost all of the true sum; the tail is of the order of a tenth.
The synthetic pair (β = 0.6, never an ON height) deposits between −0.31 and +0.36 at each meeting, of the same order as
the tail. Its step between consecutive meetings (−0.43 to +0.67) is dominated by the phase rotation; the radial factor
between two consecutive meetings is only 1.0003 to 1.0021. Reading β on a step would require separating
phase from amplitude at this scale, which neither the head nor the tail does. Verdict by the declared criterion:
B is dead (only per-member constancy would constrain the absorption, and it is equivalent to RH).
