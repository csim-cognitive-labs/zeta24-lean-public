# E451 — The Tower is the term of the zero: bridge "true zero → objects of E450" through the computation of zeta (K2a of plan §19.72) — pre-registration

> Français : [README.fr.md](README.fr.md)

Date: 2026-11-08. Status: pre-registered before any compilation and any execution. Orders: total spectral ban (use and
citation; no sum of Towers, no channel, no explicit formula consumed); third order; R-E446; §19.44; no premise
equivalent to RH; at most two compilation attempts, each logged in `attempts/`.

## Author's order verified (§19.73)
"If we compute the zero through zeta, we obtain a Tower; otherwise the Tower does not exist." Compiled in the corpus:
`zeroContribution_eq_mul_zeroTerm` (weight `m(ρ)` = order of vanishing of zeta at `ρ`), `one_le_zeroMult` (`m ≥ 1` at a zero),
`zeroTerm_real_iff_ray` + `contactAt_eq_contactMinusAt` (the grid `(β, T)` is the sequence of the real points of the term),
`zeroTerm_norm` (modulus `x^β/‖ρ‖`), `upperMirror_multiplicity` (the mirror has the same weight). Missing from the corpus
is the explicit corollary "`m(ρ) = 0 ⟺ ζ(ρ) ≠ 0` off the pole": E451 writes it.

## Object
A true zero `z` (`TrueZero`), with point `ρ = zeroPoint z = (β, T)`, its mirror `mirrorMember z` with point `(1−β, T)`, the weight
`zeroMult ρ = (analyticOrderAt riemannZeta ρ).toNat` (`Foundation/ZetaReflect`), the term `zeroTerm z x = x^ρ/ρ`, the objects
of E450 at parameter `(β, T)`: `contactRealValue`, `lastContactBefore`, `cellFraction`.

## Hypotheses
* H1 (weight): `zeroMult ρ = 0 ⟺ riemannZeta ρ ≠ 0` for `ρ ≠ 1`; `1 ≤ zeroMult (zeroPoint z)`; the weighted term of the
  base is `zeroMult · zeroTerm`.
* H2 (mirror): `zeroMult (zeroPoint (mirrorMember z)) = zeroMult (zeroPoint z)`; `mirrorMember z ≠ z` as soon as `β ≠ 1/2`.
* H3 (break of E450 at the zero): `|contactRealValue β T (lastContactBefore β T x)| = ‖zeroTerm z x‖ · e^{−βπ f/T}`.
* H4 (two words): `|lastContactBefore (1−β) T x − lastContactBefore β T x| ≤ 1` for the zero and its mirror.
* H5 (exact product): `‖zeroTerm z x‖ · ‖zeroTerm (mirrorMember z) x‖ = x/(‖ρ‖ ‖ρ*‖)`; weighted: `m² x/(‖ρ‖ ‖ρ*‖)`.
* H6 (separation): `‖zeroTerm z x‖/‖zeroTerm (mirrorMember z) x‖ = x^{2β−1} ‖ρ*‖/‖ρ‖`; unbounded if `β > 1/2`.

## Lean statements (isolated module `Terminal/PairBreakOfZero.lean`, import `PairBreakAtPrime` only)
* L1 `zeroMult_eq_zero_iff (hρ : ρ ≠ 1)`, `one_le_zeroMult_zeroPoint (z)`, `zeroContribution_eq_zeroMult_mul (z) (x)`.
* L2 `zeroMult_mirrorMember (z)`, `mirrorMember_ne_self_of_off (hβ : β ≠ 1/2)`.
* L3 `zero_break_amplitude_exact (z) (hx)`.
* L4 `zero_mirror_word_difference_le_one (z) (x)`.
* L5 `zero_pair_term_product (z) (hx)`, `zero_pair_weighted_product (z) (hx)`.
* L6 `zero_pair_term_ratio (z) (hx)`, `zero_pair_term_ratio_unbounded (z) (hβ : 1/2 < β) (K)`.

## Experiments
* (a) `scripts/e451a_zeta_weight.py` (mpmath, 30 digits): `|ζ(1/2 + iγ)|` at the six zeros of K0 (ranks 1, 10, 100, 1000,
  10000, 100000, heights from the Odlyzko file) and at the three controls of K0 (midpoints of ranks 1–2, 100–101, 10000–10001).
  Criterion: `< 10^{−20}` at the zeros (to the precision of the heights read, `~10^{−9}`: the value is recorded as is and
  compared with `|ζ'|·δγ`), `> 10^{−3}` at the controls. It is the "computation of zeta" that decides the existence of the Tower.
* (b) `scripts/e451b_zero_terms.py` (numpy, 100 000 primes, seed 451): H3, H5, H6 for the six zeros (`β = 1/2`,
  mirror = zero) and for three witness OFF pairs `β ∈ {0.3; 0.4; 0.45}` at the same frequencies; relative errors
  `≤ 10^{−12}`; H4: 0 violations.
Expected verdict: A.
