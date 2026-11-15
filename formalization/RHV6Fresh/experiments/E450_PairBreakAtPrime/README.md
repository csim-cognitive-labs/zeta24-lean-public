# E450 — The break of the pair at the shared prime, cells included (K0 + K1 of plan §19.72) — pre-registration

> Français : [README.fr.md](README.fr.md)

Date: 2026-11-08. Status: pre-registered before any compilation and any execution. Orders: total spectral ban; third
order; R-E446; §19.44; no premise equivalent to RH; at most two compilation attempts, each logged in
`attempts/`; probes in unversioned `*_SCRATCH.lean`, outputs kept in `attempts/probe*.txt`.

## Object
A pair `(β, T)`, `(1−β, T)` (`0 < β < 1`, `T > 0`) at the shared prime `q`. Objects of the corpus: `contactAt`, `contactRealValue`,
`stagePosition`, `lastContactBefore` (the word), `cellFraction`, `mirrorPhaseShift β T = arctan(T/β) − arctan(T/(1−β))`,
`offPrice`. Nothing spectral.

## Hypotheses
* H1 (exact amplitude of the break, any `β`): `|v_β(k_β(q))| = q^β · e^{−βπ f_β(q)/T} / ‖(β,T)‖` (generalizes
  `line_break_amplitude_exact`).
* H2 (two words): `f_{1−β}(q) = fract(f_β(q) + mirrorPhaseShift β T / π)`; the two words differ by at most one cell at
  every point; zero shift ⟺ line (already `mirrorPhaseShift_eq_zero_iff`).
* H3 (square rule of the pair): `|v_β| · |v_{1−β}| = q · e^{−π(β f_β + (1−β) f_{1−β})/T} / (‖(β,T)‖ ‖(1−β,T)‖)`: the product
  of the two breaks is a line-type break, with effective fraction `β f_β + (1−β) f_{1−β} ∈ [0,1)` and product norm.
* H4 (sum with cells): `|v_β| + |v_{1−β}| ≥ e^{−π/T} (q^β/‖(β,T)‖ + q^{1−β}/‖(1−β,T)‖)` and `≤ q^β/‖(β,T)‖ + q^{1−β}/‖(1−β,T)‖`;
  the price of E445 is recovered up to a bounded cell factor.
* H5 (separation): `|v_β|/|v_{1−β}| = q^{2β−1} · e^{−π(β f_β − (1−β) f_{1−β})/T} · ‖(1−β,T)‖/‖(β,T)‖`; unbounded when
  `q → ∞` as soon as `β > 1/2` (and tends to `0` if `β < 1/2`).
* H6 (K0, line): on the line, the word, the sequence of payment amplitudes and the normalized weighted balance do not
  distinguish the six zeros from the three controls (midpoints between consecutive zeros); recorded in advance as
  expected. If a difference appears, it is recorded as is, without obligation and without link to the OFF (R-E446).

## Lean statements (isolated module `Terminal/PairBreakAtPrime.lean`)
* L1 `break_amplitude_exact (hβ : 0 < β) (hT) (hx)` (H1).
* L2 `mirror_cellFraction`, `mirror_word_difference_le_one` (H2; auxiliary lemma `floor_sub_floor_le_one_of_abs_sub_le`).
* L3 `pair_break_product` (H3), `pair_effective_fraction_mem` (`∈ [0,1)` for `0 ≤ β ≤ 1`).
* L4 `pair_break_sum_bounds` (H4).
* L5 `pair_break_ratio` and `pair_break_ratio_unbounded (hβ : 1/2 < β)`: `∀ K, ∀ᶠ x atTop, K < ratio` (H5).
* L6 `pair_break_product_on_line`: at `β = 1/2`, L3 gives back `line_break_amplitude_exact` squared (consistency).

## Experiments
* (a) K0, `scripts/e450a_census_line.py`: six zeros (ranks 1, 10, 100, 1000, 10000, 100000) and three controls (midpoints
  of ranks 1–2, 100–101, 10000–10001), primes `≤ 10^7`: statistics of the word (mean, min, max of the fractions; share of
  consecutive pairs in the same cell per decade), of the sequence of amplitudes (ratio to `√q`, min/max), and weighted
  balance `valueCellSum` over blocks of 50 cells per decade normalized by the bound P5 (E445). H6 criterion: the ranges
  of zeros and controls overlap (no statistic separates the two groups).
* (b) K1, `scripts/e450b_pair_break.py`: witness pairs `β ∈ {0.3; 0.4; 0.45}` at the frequencies of the six zeros; on a
  sample of 100 000 primes: H1 (relative error `≤ 10^{−12}`), H2 (fractions, 0 violations; count of the points where
  the two words differ), H3 (product, error `≤ 10^{−12}`; effective fraction in `[0,1)`), H4 (0 violations), H5
  (ratio, error `≤ 10^{−12}`; value at `10^3, 10^4, …, 10^7`).
* (c) twin `scripts/e450b_twin_mpmath.py`, 30 digits, ranks 1 and 100, `β = 0.4`, 2 000 primes: identities to `10^{−25}`.

## Verdict
A: L1–L6 compile in ≤ 2 attempts, (b) and (c) within thresholds, (a) recorded. B: compiled, thresholds missed because
of precision (explained). C: a statement does not compile (recorded, exact error). No OFF contradiction conclusion is
drawn from E450: K1 provides the objects, K2 will pose the question.
