# E452 — K2b: what the exact meeting imposes on the two terms of the same weight at the same prime — pre-registration

> Français : [README.fr.md](README.fr.md)

Date: 2026-11-08. Status: pre-registered before any compilation and any execution (§19.74). Direction validated by the author.
Orders: total spectral ban (use and citation; two terms only, no sum of Towers, no channel, no explicit formula); third
order (contacts read `β`; frequency AND amplitude; signed balance through `contactRealValue`); R-E446; §19.44; forbidden
"amplitude against budget"; no premise equivalent to RH; at most two compilation attempts, each logged in `attempts/`.

## Check of non-equivalence with RH (done before pre-registration, §19.74.2)
K2b poses no hypothesis: all its statements are theorems for every `β ∈ (0,1)`; the condition `β > 1/2` of the
non-compensation statements is a case on a given pair (the mirror covers `β < 1/2`). Nothing is to be confronted with RH.
No comparison with `log q`, `ψ`, `rawDemand`, a cell length. Consequence recorded in advance: K2b fixes the FORM of the
pair at the shared prime; it does not provide the contradiction; K3 (inversion of the pair) follows.

## Object
Pair `(β, T)`, `(1−β, T)`; at the point `x > 0`: words `k = lastContactBefore β T x`, `k* = lastContactBefore (1−β) T x`,
fractions `f`, `f*`, values `v = contactRealValue β T k`, `v* = contactRealValue (1−β) T k*`, phase shift
`δ = mirrorPhaseShift β T` (zero ⟺ `β = 1/2`, E428); for a true zero, common weight `m = zeroMult ρ ≥ 1` (E451).

## Hypotheses
* H1 (exact word): `k* = k + s`, `s := ⌊f + δ/π⌋` (`mirrorWordShift`).
* H2: `|s| ≤ 1`; `s ∈ {−1, 0, 1}`.
* H3 (window): `k* = k ⟺ −δ/π ≤ f < 1 − δ/π`; on the line `s = 0` everywhere.
* H4 (signs): `v·v* = (−1)^s |v||v*|`; same sign ⟺ `s = 0`.
* H5 (value of the pair): `|v + v*| = | |v| + (−1)^s |v*| |`; `= |v| + |v*|` if `s = 0`, `= ||v| − |v*||` otherwise;
  `|v| − |v*| ≤ |v + v*|` always.
* H6 (non-compensation): if `β > 1/2`, `∀ᶠ x, |v|/2 < |v + v*|`; at every meeting beyond a rank.
* H7 (line): `v + v* = 2v` at `β = 1/2`.
* H8 (true zero, weight): `|m v + m* v*| = m |v + v*| ≥ |v + v*|`; non-compensation at the parameter of an off-line true zero.

## Lean statements (isolated module `Terminal/PairMeetingImposition.lean`, import `PairBreakOfZero` only)
L1 `mirrorWordShift`, `mirror_stagePosition_eq`, `mirror_lastContactBefore`, `abs_mirrorWordShift_le_one`,
`mirrorWordShift_trichotomy`; L2 `pair_same_word_iff`, `line_mirrorWordShift_eq_zero`; L3 `pair_value_tower_eq`,
`pair_value_mirror_eq`, `abs_sign_sum`, `pair_value_product`, `pair_same_sign_iff`; L4 `pair_value_sum_abs`,
`pair_value_sum_of_same_word`, `pair_value_sum_of_shifted_word`, `pair_value_sum_ge`; L5 `pair_value_no_cancellation`,
`pair_meeting_no_cancellation`; L6 `line_pair_value_sum`; L7 `zero_pair_value_no_cancellation`,
`zero_weighted_pair_value_abs`, `zero_weighted_pair_value_ge`.

## Experiments
* (a) `scripts/e452a_pair_imposition.py` (numpy): 18 witness OFF couples `β ∈ {0.3; 0.4; 0.45}` × six frequencies of K0
  (zeros of ranks 1, 10, 100, 1000, 10000, 100000) + six line couples; 10⁵ primes ≤ 10⁷ (seed 452); H1–H7 to `10⁻¹²`;
  first rank of non-compensation; observation without law: share of primes with shifted words against `|δ|/π`.
* (b) `scripts/e452b_twin_mpmath.py`: mpmath twin with 30 digits, 10 primes per couple, gap to the numpy values.

## Criterion
A: module green (≤ 2 attempts), standard axioms, empty grep of the ban, all identities to `10⁻¹²`, twin in agreement;
B: an identity is missing (recorded); no hypothesis, no contradiction drawn.
