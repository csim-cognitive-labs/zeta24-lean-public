# E406–E411 — the raw channel on the zero side, the frequency decomposition, the break, the bound at the meetings

> Français : [README.fr.md](README.fr.md)

Pre-registered BEFORE execution (2026-11-02). Logical follow-up requested by the author after E404, E405 and
`Terminal/RawMeetingRemainder.lean`: link the organization of the high frequencies (E404) to the control of the raw remainder at the
meetings (terminal condition of E405, `riemannHypothesis_of_psiRemainder_at_events`). Direction kept: real axis →
primes → gaps → breaks → high frequencies → contacts and amplitudes → (β, T). No new hypothesis. The
compiler decides. All theorems inline, no duplicated code, no probe.

## 0. Prior rectification (audit of the corpus, before any writing)
§19.35.2 claimed that "the raw channel had no compiled object on the zero side". This is inaccurate: `Terminal/InverseReading.lean`
(author, 2026-09-30) defines `spectralRemainder N = stepAt zeroChannelPrimitive N`, the step over the cell `[N, N+1]` of the
absolutely convergent primitive `x · Σ' ρ, −m(ρ) x^ρ/(ρ(ρ+1))`, and proves `arithmetic_eq_spectral : exactRemainder N =
spectralRemainder N` (`N ≥ 2`), with `exactRemainder N = ψ(N) − stepAt backgroundPrimitive N`. This is EXACTLY the summation
convention requested by E406: the pointwise raw series `Σ x^ρ/ρ` is not absolutely convergent, but its integral over
the unit cell is; since `ψ` is constant on `[N, N+1[`, the cell integral of `ψ` is `ψ(N)` and the exact identity at the jump
is attributed to an absolutely convergent sum, with no summation order or convention at the jump point.
What was really missing: the link between this object and `psiRemainder N = ψ(N) − N` of E405 (a bounded background correction),
the instantiation by frequency threshold, and a BOUND on what the low frequencies can realize at a break.

## 1. Deliverables and objects (isolated module `Terminal/RawSpectralChannel.lean`, not added to `RHV6Fresh.lean`)
- **E406 (raw channel on the zero side, cell convention)**: `psiRemainder_eq_spectral_add_correction`: at every integer
  `N ≥ 2`, `ψ(N) − N = spectralRemainder N + c(N)` with `‖c(N)‖ ≤ cellBackgroundConstant` (explicit constant: one half,
  the logarithmic derivative of zeta at zero, and twice the sum of the trivial zeros). Convergence: `channelOn_summable`
  (already compiled); the convention is the cell step, recorded in the docstring.
- **E407 (exact frequency decomposition)**: `lowFrequencies H` (indices of absolute height at most `H`, both
  branches), finiteness (`lowFrequencies_finite`, by `explicitIndex_locallyFinite`), and the instance
  `exactRemainder_split_frequency H N : exactRemainder N = localPacket (low H) N + localPacket (low H)ᶜ N`, same sense of
  convergence (subseries of an absolutely convergent series). Same for the increment at the meeting
  (`remainderIncrement_split_frequency`).
- **E408 (junction break / high frequencies)**: the new central theorem,
  `norm_packetIncrement_finite_le : ‖packetIncrement (↑s) N‖ ≤ Σ_{ρ∈s} m(ρ)` for every FINITE family `s` of indices and
  every `N ≥ 1`: the second difference of the cell channel of a zero is bounded by its multiplicity (two mean value
  inequalities, derivatives `x^ρ/ρ` then `x^{ρ−1}`, and `x^{β−1} ≤ 1` since `β ≤ 1`). Hence the low frequencies cannot
  by themselves realize a break larger than their number (counted with multiplicity). Compiled consequence
  `break_realized_by_high_frequencies`: at every integer `N ≥ 2`,
  `‖packetIncrement (low H)ᶜ N‖ ≥ Λ(N+1) − 1 − 4τ − K(H)` where `τ` is the compiled constant of the trivial zeros and
  `K(H) = Σ_{ρ ∈ low H} m(ρ)`. At a prime `p`: the part of the break `log p` that exceeds `1 + 4τ + K(H)` is carried
  NECESSARILY by the frequencies above `H`. This is reading P-A4 of E404 ("the break requires frequencies
  well beyond the crowd") turned into a theorem, with an explicit deficit. Frequency floor
  (`frequency_floor_of_low_realization`): if the frequencies at most `H` alone realize the break at `p` (complement
  of the increment zero), then `K(H) ≥ log p − 1 − 4τ`.
- **E409 (amplitudes and coordinates)**: no new theorem; audit of what is recoverable with the compiled theorems:
  `radial_from_amplitude_step`, `inversion_radial`, `two_contacts_height_quantized` (per member, from ITS
  contacts); `spectral_weights_unique` (the total function on every `x > 1` determines each weight). What is NOT
  compiled: the recovery of the components from the values at the meetings (integers) alone. Recorded as is.
- **E410 (composition of rigidities)**: `off_member_forces_break_and_excess`: a member with `β > θ` forces (E405) a
  raw meeting `E` with excess of the raw remainder, AND at this meeting, for every threshold `H`, the break is realized
  above `H` to a height of at least `Λ(E) − 1 − 4τ − K(H)` (E408). Chain named theorem by theorem in §19.36;
  open junctions identified.
- **E411 (search for the bound at the meetings)**: at most two attempts, logged with the exact goal of the compiler
  (`COMPILE_JOURNAL.md`). Attempt 1: reduce `|ψ(E) − E| ≤ C E^{1/2+ε}` by the frequency decomposition
  (bounded correction + low packet + high complement) and read the remaining goals. Declared failure criterion: if the remaining
  goal on the low packet requires `β ≤ 1/2` for the low zeros (circular) or if the remaining goal on the complement is the tail
  bound itself, the attempt is dead and the theorem is withdrawn. Attempt 2: bound the complement by the second
  difference (E408): declared failure criterion: if the second difference does not control the value (it controls the
  variations, not the level), the attempt is dead. No named hypothesis will be posed.

## 2. Numerical twins (script `e406_e411_raw_spectral_channel.py`, bounded, real, no fabricated output)
Data: `experiments/data/odlyzko_zeros6_2001052.txt` (SHA-256 checked), sieve of `Λ` up to `2·10^6`. Background constants
by mpmath (logarithmic derivatives of zeta at 0 and −1, sum of the trivial zeros). Expected time: < 3 minutes.
- Part E406: at the primes `p ∈ {4547, 9587, 9931, 104729, 1000003}` and the neighboring integers, compare `ψ(N) − N` to
  `spectralRemainder N + c(N)` (cell convention, 2,001,052 zeros, two branches per doubled real part); read the
  truncation residual (expected small: the cell series converges like `1/γ²`) and check `‖c(N)‖ ≤ cellBackgroundConstant`.
- Part E407/E408: at `p = 4547` and `p = 9587`, for `H ∈ {30, 100, 300, 594, 1000, 3000, 10^4, 3·10^4, 10^5, all}`:
  increment of the low packet `packetIncrement (low H) (p−1)` against its compiled bound `K(H)` (expected: far below), part
  of the break `log p − 1` carried by the complement, and the minimal `H` such that `K(H) ≥ log p − 1 − 4τ` (compiled floor)
  against the `H` observed in E404 (order `π p`). Prediction written: the compiled floor is far below the observed one
  (it reads only the count, not the phases); the gap between the two is the measure of what E408 does not capture.
- Part E411: `‖localPacket (low H)ᶜ (p)‖ / √p` for the same `H` and `p`: reading only, no conclusion on the
  exponent (twin, not proof).
R12: everything is real axis (true primes, true step function, true zeros); the background constants are
analytic and non-projective; the link `K(H)` ↔ Riemann–von Mangoldt, if invoked, is PROJECTION (R12) and will not
be compiled here.

## 3. Criteria
- The module compiles without `sorry`, standard axioms; otherwise: exact errors logged, two attempts per step.
- E411: success = the derived bound; expected failure = a residual goal displayed by the compiler, copied as is.
- No closure declared as long as the bound is not proved without a hypothesis equivalent to RH.

## Results (run of 2026-11-02, 4.5 s, output `e406_e411_results.txt`; no fabricated output)
Module `Terminal/RawSpectralChannel.lean`: 37 declarations, compiled (`lake build`), no `sorry`, standard axioms;
three passes logged (`COMPILE_JOURNAL.md`). Constants read: c₀ = −log 2π = −1.8379; c₁ = 1.9851; τ = π²/6;
`cellBackgroundConstant` = 5.628.

### Part E406 (cell identity)
`ψ(N) − N = spectralRemainder N + c(N)` verified to the truncation residual of the list: 2.4·10⁻² at N ≈ 9.6·10³ (resolution
π·N/γ_max = 0.027), 0.30 at N = 10⁵ (resolution 0.29), 4.3 at N = 10⁶ (resolution 2.8 > 1: the list no longer resolves the
cell, as expected). The correction `c(N)` equals 1.3379 (constant, to within 10⁻¹¹: the share of the trivial zeros is
negligible), under the compiled bound 5.628. The second difference of the background equals one to within 10⁻¹¹ (compiled bound 4τ = 6.58,
very loose). Prediction held.

### Part E407/E408 (low packet at the meeting against its compiled bound)
For p = 4547, 9587, 104729 and ten thresholds: the increment of the low packet is ALWAYS under the bound `K(H)` (theorem
`norm_packetIncrement_finset_le`), but by three to six orders of magnitude: quotient 10⁻³ at H = 30, 10⁻⁴ at 10³,
10⁻⁵ at 10⁴, 2·10⁻⁶ with the whole list. The compiled floor (`frequency_floor_of_low_realization`) only requires
K(H) ≥ 0.8 to 4.0, that is, H ≥ 14.1 or 21.0: it is trivially satisfied, whereas E404 observes that the sharp break
requires H of the order of π·p (1.4·10⁴, 3.0·10⁴, 3.3·10⁵). Prediction held: the counting theorem is true and
very weak; the gap (four to five orders of magnitude) is the measure of what E408 does not capture, the phase
cancellation between the second differences of the low frequencies. Part of the break (log p − 1) carried above H
(cell convention, exact identity on the total side): p = 4547: 100% up to H = 10³, 57% at 10⁴, 11% at 3·10⁴, 3% at
10⁵; p = 9587: 100% up to 3·10³, 72% at 10⁴, 27% at 3·10⁴, 6% at 10⁵; p = 104729: 96% at 10⁴, 93% at 3·10⁴, 83%
at 10⁵, 32% at 3·10⁵, 6% with the whole list (γ_max = 1.13·10⁶ ≈ π·p/0.3: the list is no longer sufficient). Reading P-A4
of E404 reproduces in the cell convention, with overshoots of 100% at some thresholds (the low packet
transiently opposes the break): the phases organize, they do not add up.

### Part E411 (reading only)
Level of the complement divided by √p, ten thresholds: 0.0002 to 0.08; decreases with H for a fixed list; no reading
of an exponent (twin).

### What the experiment does not say
It says nothing about β: the real heights already carry a half (data hypothesis). It measures the gap between a compiled
theorem (counting) and an observed mechanism (phases), without closing it.
