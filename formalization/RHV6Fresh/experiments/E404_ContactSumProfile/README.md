# E404 — Sum of the contacts on the real axis along each gap: rise, break, descent (2026-11-02)

> Français : [README.fr.md](README.fr.md)

Pre-registered BEFORE execution (this file is committed before the script is launched; results are added afterwards).

## Author's request (restated in words)
Study no longer the amplitude of an isolated contact but the sum of all contacts on the real axis, followed along
the axis inside a gap up to the meeting point, then in the next gap. Two cases compared on the same
true gaps: the chaining of zeros on the line (frequency advancing at each zero, stable amplitude) and
the degenerate chaining of an OFF chain (two members on a frequency that does not advance, amplitude split into
a growth that is too weak and one that is too strong). No projection, no statistics: each chosen gap is read alone,
value by value. Behavior to isolate: the progressive rise of the sum up to a very precise maximum at the meeting
point, which must be the exact gap (the break), then the immediate descent to let the next gap
start again. The author's reading, measured and not posed: the rise toward the break is carried by the frequency that
increases strongly from one ON zero to the next. Both channels are done, at the author's request (raw first).

## Two channels, separate
- **Raw channel** (twin NOT compiled in the corpus): the Chebyshev step function against its regular background.
  On the axis, between two consecutive primes, the sum over the zeros rises with a regular slope equal to one, and at the
  next prime it drops at once by a height equal to the logarithm of that prime. The running total since the start of
  the gap therefore reaches, just before the meeting, the exact arithmetic gap (difference of the two primes, up to one
  background term), then drops by the logarithm of the prime: this is the raw break.
- **Smoothed channel** (compiled channel, that of E402/E403): the demand A(x) = Σ_{m<x} Λ(m)(1 − m/x) against the background B(x)
  of E401. The sum of the deposits is continuous; the break there is a change of slope at the meeting point, and the
  running total since the start of the gap equals at the meeting point the exact demand of the gap (Z_n of E402/E403).
In both channels the same phase factor exp(iγ log x) is used for all zeros; only the weight changes (1/ρ for the
raw, −1/(ρ(ρ+1)) for the smoothed).

## What is computed (deterministic, bounded, no fabricated output)
1. True gaps: primes ≤ 10 000 (1229 gaps), Λ by sieve, exact ψ and A; raw background and smoothed background.
2. Zeros: the 2,001,052 heights of the Odlyzko file (SHA-256 checked), placed on the line (data hypothesis).
3. Chosen gaps, one by one, no average: n = 4, 614, 1228 (those of E403), the longest arithmetic gap,
   the last gap of length 2, and n = 100, 300, 500, 800, 1000. Plus a window of six consecutive gaps
   (n = 614 to 619) followed continuously, without reset.
4. For each gap, a grid of 100 points of x between p_n + 1/2 and p_{n+1} − 1/2 (never on a prime: the raw formula
   there takes the mean of the two sides), then the point p_{n+1} + 1/2 for the descent. At each point: signed sum
   of all zeros in both channels, true value by sieve, truncation residual. For the raw, also
   the sum truncated in frequency at thresholds 30, 100, 300, 1,000, 3,000, 10,000, 30,000, 100,000, 300,000 and T_max,
   to see HOW the rise and the break are built as the frequency increases (author's reading).
5. Decomposition by increasing frequency at the meeting point: the rise (value at p_{n+1} − 1/2 minus value at
   p_n + 1/2) and the drop (value at p_{n+1} + 1/2 minus value at p_{n+1} − 1/2), both accumulated zero by zero
   by rank, read at the same frequency thresholds and at the crowd threshold π/ℓ. Both channels.
6. Degenerate OFF twin, SEPARATE: a block of consecutive ON zeros removed and replaced by pairs of radial position
   0.3 / 0.7 at the median height between the removed zero and the next one (never the height of an existing zero; checked).
   Three block sizes: 1 (rank 2000, as E403), 50 (ranks 2000–2049), 500 (ranks 2000–2499). The first zero
   is never touched (fact: it is ON). Same grids, same points, same decompositions; point-by-point difference
   with the real, in both channels.
7. mpmath twins (30 decimals): on three gaps, at the point p_{n+1} − 1/2, the raw sum and the smoothed sum over
   the first 2,000 zeros, compared to the numpy sum truncated at the same rank; A and ψ in mpmath.

## Predictions written before execution
Author's predictions: (P-A1) progressive and regular rise; (P-A2) very precise maximum equal to the exact gap at the
meeting point; (P-A3) immediate descent; (P-A4) the last push toward the break is carried by the
frequencies that rise strongly; (P-A5) the OFF chain does not reach the exact maximum and does not descend in the same
way.
Executor's predictions: (P-E1) raw channel: at full truncation, running total before the meeting = exact arithmetic gap
up to a truncation residual of the order of a tenth, and drop = logarithm of the prime up to the same residual;
the rise slope equals one everywhere; (P-E2) raw channel: at low frequency thresholds, the rise is already
almost complete (slope one carried by the low frequencies) but the break is spread out; the break tightens
as the threshold rises, its width in x being of the order of π·p/T; so the final push is indeed carried by the high
frequencies, not the rise; (P-E3) smoothed channel: running total at the meeting point = Z_n to within 10⁻⁷, continuous profile
with a slope break; (P-E4) degenerate OFF twin: point-by-point difference nonzero, growing like p^{0.4}, larger
with the block; at block 500, the difference exceeds the raw truncation residual; (P-E5) nothing is
concluded about β of the real zeros.

## Launch
`cd formalization/RHV6Fresh/experiments/E404_ContactSumProfile`
`nohup timeout 900 python3 -I e404_contact_sum_profile.py ../data/odlyzko_zeros6_2001052.txt 10000 . > e404_run.log`
Bounded (< 15 min). Outputs: `e404_profiles.txt`, `e404_window.txt`, `e404_freq_decomposition.txt`,
`e404_synthetic.txt`, `e404_summary.txt`, `e404_run_log.txt`.

## Results (run of 2026-11-02, 140.6 s, output `e404_summary.txt`; no fabricated output)

Provenance: Odlyzko file checked (SHA-256 identical), 2,001,052 zeros, heights placed on the line (data
hypothesis). Chosen gaps: n = 4, 100, 300, 500, 614, 800, 1000, 1182 (the longest, 9551 → 9587), 1223 (last of
length 2, 9929 → 9931), 1228. Continuous window n = 614 to 619. mpmath twins: raw and smoothed to 10⁻¹² or better.

### Raw channel (non-compiled twin): the rise, the exact maximum, the drop
- **Rise**: on each gap read, the sum of all contacts rises with a regular slope equal to one and reaches,
  just before the meeting, the exact arithmetic gap (the sieve truth is exactly "difference of the two primes
  minus one" on the grid of half-integers, with no interior prime power in the chosen gaps). Values read
  (computed / truth): n = 614: 22.970 / 23; n = 1182: 35.081 / 35; n = 1228: 32.889 / 33; n = 100: 8.9993 / 9;
  n = 4: 0.99940 / 0.99942. The difference between computed and truth is the truncation residual of the list (max 0.06 at x ≈ 10⁴),
  it grows with the abscissa, and it is of the order of the slope measured point by point (min 0.92, max 1.04 for n = 614).
  On the gaps of length two (n = 500, 1223), the grid of one hundred points is finer than the resolution width
  of the list (about π·p / T_max ≈ 0.03): the profile there is dominated by the truncation ripple at both edges
  (slope read from −5.6 to +7.8), the rise equals 0.97 / 1 and 0.91 / 1. P-A1 and P-A2 held at the level of the
  truncation residual; P-E1 held.
- **Drop**: between p_{n+1} − 1/2 and p_{n+1} + 1/2 the sum drops by exactly one minus the logarithm of the prime
  (truth): n = 614: −7.393 computed / −7.422 truth (log p = 8.422); n = 1228: −8.115 / −8.211; n = 4:
  −1.56542 / −1.56541. The raw break is therefore indeed a jump of a very precise height, that of the logarithm of the
  prime met. P-A3 held.
- **Descent "almost to zero"**: NOT held in the literal sense. After the drop, the sum does not return to its starting
  value: it is higher by "arithmetic gap minus logarithm of the prime" (n = 614: 24 − 8.42 = 15.58,
  value read 15.577). The continuous window without reset shows it: start 0 at p_614, then 23 → 15.58 → 16.3 →
  9.16 → 17.5 → 12.7 → 16.5 → 10.3 → 21.7 → 17.9 → 23.2 over six gaps; the sum drifts, it does not return
  to zero gap by gap. What returns toward zero is the drift x − ψ(x) over long ranges, and that is the
  content of the prime number theorem, hence of the projection (R12). In the raw channel, the author's "up and down"
  is exact for the two heights (rise = exact gap, drop = log p) but the return point is not
  zero; it is zero only if the origin is reset at each meeting, which is what the Lean module does
  (`contactSumProfile_continuation`) as a change of origin, not as a return of the sum.
- **Decomposition by increasing frequency** (`e404_freq_decomposition.txt`), gap n = 614 (p = 4523 → 4547, crowd
  threshold π/ℓ = 594): cumulative rise 0.29 with the first three zeros, −0.90 at T ≤ 100, 0.34 at T ≤ 300, 2.79 at the
  crowd threshold (336 zeros), 13.9 at T ≤ 1,000, 16.5 at T ≤ 3,000, 20.1 at T ≤ 10,000, 24.5 at T ≤ 30,000 (overshoot),
  22.96 at T ≤ 100,000, 22.97 with all. The rise is therefore NOT carried by the low frequencies: it is built
  between the crowd threshold and twenty times that threshold. Cumulative drop at the same gap: 0.01 at T ≤ 30, 0.28 at the crowd threshold,
  −0.25 at 1,000, −1.90 at 3,000, −3.24 at 10,000, −8.79 at 30,000 (overshoot), −7.46 at 100,000, −7.39 with all. The
  drop is built even higher: it requires frequencies of the order of π·p_{n+1} ≈ 1.4·10⁴ and beyond, that is,
  twenty-five times the crowd threshold. Same reading on the other gaps (n = 1228: rise 18.2 at the crowd threshold
  587, 31.6 at 10⁴, 33.3 at 3·10⁴, 32.9 with all; drop −0.05 at the crowd threshold, −2.1 at 10⁴, −7.8 at 3·10⁴, −8.1 with
  all). **Reading P-A4 (author): held in this channel.** The last push toward the exact maximum and the break itself
  are realized by the members of highest frequency, well beyond the crowd of the gap; the frequency must
  rise strongly, up to the order of the prime met times π, for the break to be sharp. **Reading P-E2
  (executor): FALSE for the rise** (predicted already carried by the low frequencies; it is not), true for
  the break.

### Smoothed channel (compiled): continuous profile, maximum exact at the demand, slope break
- Maximum: at the meeting point the sum of the contacts equals the exact demand of the gap to within 10⁻⁸ on all
  chosen gaps (n = 614: 1.992073544·10⁻² against Z_n = 1.992072673·10⁻²; max residual on the grid 1.6·10⁻⁸).
  This is the theorem `contactSumProfile_meetingPoint` read numerically.
- Shape: the profile is continuous and curved (n = 614: 0 → 0.0073 → 0.0135 → 0.0184 → 0.0221 → 0.0247 → 0.0260 →
  0.0262 → 0.0251 → 0.0229 → 0.0199 at the meeting → 0.0191 after): it rises, plateaus in the middle of the gap, then
  descends BEFORE the meeting; the break is only a change of slope, the rise is neither regular nor
  monotone up to the maximum. The exact maximum (the demand) is not a maximum of the profile. P-A1 and P-A3 cannot be
  read in this channel; P-A2 can be read (maximum = exact demand), P-E3 held.
- Frequencies: the smoothed rise is almost complete from T ≤ 1,000 (n = 614: 0.0220 against 0.0199; n = 1228: to
  10⁻⁵ from 3,000): the weight in one over T² of this channel extinguishes the high frequencies. This channel therefore does NOT see
  the high-frequency push that makes the raw break; it smooths it.

### Degenerate OFF twin, SEPARATE (block of rank 2000 replaced by pairs 0.3 / 0.7, median heights, no
height of an existing zero, minimal distance to the nearest zero 1.5·10⁻³; blocks of 1, 50 and 500)
- Raw channel: the point-by-point difference with the real, at the point p_{n+1} − 1/2, is for block 1: 3.3·10⁻³
  (n = 4), 0.079 (n = 100), 0.18 (n = 614), 0.43 (n = 1228); block 50: up to 4.2 (n = 1223); block 500: 3.9 to
  11.9, that is, of the order of the break itself (log p ≈ 8 to 9). Along the gap n = 614 the difference of
  block 500 oscillates between −5.7 and +5.1 inside a single gap: the degenerate chain adds neither a regular slope
  nor a jump, it adds a ripple of the size of the break whose position is not that of the prime. These
  differences exceed the real truncation residual (max 0.06) for the three blocks on all chosen gaps
  except block 1 at n = 4 (3.3·10⁻³ against 4.9·10⁻⁶: it exceeds it too). No compiled bound exists in this channel
  (the raw channel is not in the corpus): there is nothing to "violate"; the twin merely disagrees with the
  sieve truth, which only a complete list of zeros reproduces (same situation as E403, R12: comparison made
  on the real axis, true gaps, true step function; no projection).
- Smoothed channel: differences 10⁻⁷ to 3·10⁻³ (block 500, n = 1228: 2.7·10⁻³ against residual 1.4·10⁻⁹), all above the real
  residual, as in E403; the compiled tail bounds of E402/E403 (eps_online ≈ 10⁻⁵ to 7·10⁻⁴) are not
  recomputed here; block 500 would exceed them at n = 1228 (2.7·10⁻³ > 7.4·10⁻⁴ max bound of E403), which is noted
  without being concluded: the E403 bound assumes the real list, not the twin. P-A5 held in the sense "the OFF chain does not
  reproduce the exact maximum nor the exact drop"; P-E4 held (growth with the block and with the abscissa; no
  power law read, the phases mix in).
- P-E5: nothing is concluded about β of the real zeros; the real heights already carry a half.

### What the experiment does not say
It does not explain why the real list makes the sum rise with slope one nor why the drop equals log p:
these are the two faces of the raw identity (sum over the zeros = background minus step function), which is a truth of
the complete list. The raw channel is not compiled; the smoothed channel is (`Terminal/ContactSumProfile.lean`).
