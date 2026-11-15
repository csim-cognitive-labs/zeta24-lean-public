/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GrammarWindowEstimate

/-!
# Comparaison signée sur la fenêtre du passage (auteur, 2026-10-11)

La réduction `passage_window_reduction` majore séparément `‖part première filtrée‖`, l'historique filtré `B_P` et la
moitié conjuguée par `Σ'‖terme‖` : ces trois opérations perdent les compensations exactes. Ce module conserve les trois
contributions SIGNÉES (parties réelles exactes) ; seule la borne filtrée du complément `B_Q` (oscillations conservées
dans chaque terme) reste une norme.

* §1 partie réelle exacte du retrait : `Re L(Y) = Σ_{n<N} Λ(n)·Re Φ_λ(n) − Re L(fond) − Re L(P_H)` (`removal_re_eq`) ;
  sous le filtre accordé, `Re Φ_λ(n) = Σ_{r : n < ⌈x_r⌉} c_r cos(T log x_r)(1 − n/x_r)` (`primeFilter_re_phaseMatched`) ;
  historique filtré signé développé en série à coefficients propres (`history_filtered_series`).
* §2 partie réelle exacte de la moitié conjuguée : `Re Σ' = Σ' Re`, terme `w_σ·Σ_r c_r x_r^{β_σ} x_r^{−2iT}`
  (`lower_re_tsum`, `lower_re_term`).
* §3 composition signée (`window_closes_signed`) : `Re L(Y) − Re(moitié conjuguée) + B_Q < U` et `U ≤ Re(moitié
  supérieure)` ⟹ `False`. Elle est au plus aussi exigeante que la précédente (`signed_of_norm_separation`).
* §4 réduction signée du passage (`passage_window_reduction_signed`), démontrée ; son antécédent n'est PAS démontré.
-/

namespace RHV6Fresh

open RHV3Lean Complex

/-! ## 1. Partie réelle exacte du retrait -/

/-- **Retrait, partie réelle exacte** : poids premiers filtrés − fond filtré − historique filtré, tous signés. -/
theorem removal_re_eq (H : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (N : ℕ) (hN : ∀ r, ⌈x r⌉₊ ≤ N) :
    (historyRemoved H x lam).re =
      ∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n : ℝ) * (primeFilter x lam n).re
        - (∑ r, lam r * smoothedZeroBackground (x r)).re - (∑ r, lam r * precedingSum H (x r)).re := by
  rw [historyRemoved_filtered_primes H x lam N hN, Complex.sub_re, Complex.sub_re, Complex.re_sum]
  congr 2
  exact Finset.sum_congr rfl fun n _ => Complex.re_ofReal_mul _ _

/-- `Re x^{−iT} = cos(T log x)`. -/
theorem cpow_neg_I_re {x : ℝ} (hx : 0 < x) (T : ℝ) :
    ((x : ℂ) ^ (-(T : ℂ) * I)).re = Real.cos (T * Real.log x) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le, Complex.exp_re]
  have h1 : ((Real.log x : ℂ) * (-(T : ℂ) * I)).re = 0 := by simp
  have h2 : ((Real.log x : ℂ) * (-(T : ℂ) * I)).im = -(T * Real.log x) := by simp; ring
  rw [h1, h2, Real.exp_zero, one_mul, Real.cos_neg]

/-- **Filtre premier accordé, partie réelle** : `Re Φ_λ(n) = Σ_{r : n < ⌈x_r⌉} c_r cos(T log x_r)(1 − n/x_r)`. -/
theorem primeFilter_re_phaseMatched (T : ℝ) {m : ℕ} (c x : Fin m → ℝ) (hx : ∀ r, 1 < x r) (n : ℕ) :
    (primeFilter x (phaseMatched T c x) n).re =
      ∑ r, if n < ⌈x r⌉₊ then c r * Real.cos (T * Real.log (x r)) * (1 - n / x r) else 0 := by
  unfold primeFilter phaseMatched
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs
  · have hx0 : 0 < x r := lt_trans one_pos (hx r)
    rw [show (1 - (n : ℂ) / (x r : ℂ)) = ((1 - n / x r : ℝ) : ℂ) by push_cast; ring, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.re_ofReal_mul, cpow_neg_I_re hx0]
  · simp

/-- **Historique filtré signé** : `Σ_r λ_r P_H(x_r) = Σ'_σ w_σ^H·Σ_r λ_r x_r^σ` (coefficients propres, aucune norme). -/
theorem history_filtered_series (H : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    ∑ r, lam r * precedingSum H (x r) = ∑' σ, precedingWeight H σ * ∑ r, lam r * (x r : ℂ) ^ (σ : ℂ) := by
  have h : ∑ r, lam r * precedingSum H (x r) = ∑ r, lam r * ∑' σ, precedingWeight H σ * (x r : ℂ) ^ (σ : ℂ) :=
    Finset.sum_congr rfl fun r _ => by rw [precedingSum_eq_series]
  rw [h]; exact filtered_series_eq _ (precedingWeight_norm_summable H) x lam hx

/-! ## 2. Partie réelle exacte de la moitié conjuguée -/

theorem lower_re_tsum (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    (∑' σ, lowerFiltered H H' x lam σ).re = ∑' σ, (lowerFiltered H H' x lam σ).re :=
  Complex.re_tsum (lowerFiltered_summable H H' x lam hx)

/-- Terme conjugué signé : `Re(w_σ·Σ_r c_r x_r^{β_σ} x_r^{−2iT})`, coefficient propre conservé. -/
theorem lower_re_term {H H' : ℝ} (hHH' : H ≤ H')
    (hFib : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' → |(σ : ℂ).im| = H')
    {m : ℕ} (c x : Fin m → ℝ) (hx : ∀ r, 1 < x r) (σ : ExplicitIndex) (hσ : (σ : ℂ).im ≤ 0) :
    (lowerFiltered H H' x (phaseMatched H' c x) σ).re =
      (fiberWeight H H' σ * ∑ r, ((c r * x r ^ (σ : ℂ).re : ℝ) : ℂ) * (x r : ℂ) ^ (-(2 * H' : ℂ) * I)).re := by
  rw [lower_term_eq hHH' hFib c x hx σ hσ]

/-! ## 3. Composition signée -/

/-- **Composition signée** : `U ≤ Re(moitié supérieure)`, `‖L(Q)‖ ≤ B_Q`, et
`Re L(Y) − Re(moitié conjuguée) + B_Q < U` ⟹ `False`. Le retrait et la moitié conjuguée restent signés. -/
theorem window_closes_signed {H H' : ℝ} {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r)
    {U BQ : ℝ} (hU : U ≤ (∑' σ, upperFiltered H H' x lam σ).re)
    (hQ : ‖∑ r, lam r * followingSum H' (x r)‖ ≤ BQ)
    (hsep : (historyRemoved H x lam).re - (∑' σ, lowerFiltered H H' x lam σ).re + BQ < U) : False := by
  have hY := congrArg Complex.re (window_same_quantity H H' x lam hx)
  have hG := congrArg Complex.re (groupSignal_split H H' x lam hx)
  rw [Complex.sub_re] at hY
  rw [Complex.add_re] at hG
  have hq := neg_le_of_abs_le ((Complex.abs_re_le_norm (∑ r, lam r * followingSum H' (x r))).trans hQ)
  linarith

/-- La comparaison signée est impliquée par la séparation en normes : elle est au plus aussi exigeante. -/
theorem signed_of_norm_separation {H H' : ℝ} {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r)
    (N : ℕ) (hN : ∀ r, ⌈x r⌉₊ ≤ N) {U BQ : ℝ}
    (hsep : ‖primeSideFiltered N x lam‖ + filteredSeriesBound (precedingWeight H) x lam + BQ
      + ∑' σ, ‖lowerFiltered H H' x lam σ‖ < U) :
    (historyRemoved H x lam).re - (∑' σ, lowerFiltered H H' x lam σ).re + BQ < U := by
  have a := Complex.re_le_norm (historyRemoved H x lam)
  have b := historyRemoved_le_primeSide H x lam hx N hN
  have c := neg_le_of_abs_le ((Complex.abs_re_le_norm (∑' σ, lowerFiltered H H' x lam σ)).trans
    (lower_half_le x lam hx))
  linarith

/-! ## 4. Réduction signée du passage -/

/-- **Réduction signée** : fenêtre du passage `p_{n₀}, …, p_{n₀+m−1}`, filtre accordé. Si, sur une longueur `m`,
`Σ_{n<p_{n₀+m}} Λ(n)·Re Φ_λ(n) − Re L(fond) − Re L(P_H) − Re(moitié conjuguée) + B_Q` reste sous la minoration de la
paire arrivée + miroir, contradiction. Démontrée ; l'antécédent ne l'est pas. -/
theorem passage_window_reduction_signed {H H' : ℝ} (hHH' : H ≤ H')
    (hFib : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' → |(σ : ℂ).im| = H')
    (hT : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' →
      (σ : ℂ).re * ((σ : ℂ).re + 1) < (σ : ℂ).im ^ 2)
    (n₀ : ℕ) (l : TrueZero) (hH : H < rZeroHeight l.1) (hH' : rZeroHeight l.1 ≤ H')
    (hβ : rZeroRadialPosition l.1 < 1 / 2)
    (hsep : ∃ m : ℕ,
      ∑ n ∈ Finset.range (fnPrimeAtRank (n₀ + m)), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (primeFilter (primeWindow n₀ m) (phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m)) n).re
        - (∑ r, phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m) r *
            smoothedZeroBackground (primeWindow n₀ m r)).re
        - (∑ r, phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m) r *
            precedingSum H (primeWindow n₀ m r)).re
        - (∑' σ, lowerFiltered H H' (primeWindow n₀ m)
            (phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m)) σ).re
        + filteredSeriesBound (followingWeight H') (primeWindow n₀ m)
            (phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m)) <
      (-(zetaZeroMultiplicity (zeroPoint l) : ℂ) / (zeroPoint l * (zeroPoint l + 1))).re *
          ∑ r, gapWeights n₀ m r * primeWindow n₀ m r ^ rZeroRadialPosition l.1 +
        (-(zetaZeroMultiplicity (zeroPoint l) : ℂ) /
            (zeroPoint (mirrorMember l) * (zeroPoint (mirrorMember l) + 1))).re *
          ∑ r, gapWeights n₀ m r * primeWindow n₀ m r ^ (1 - rZeroRadialPosition l.1)) : False := by
  obtain ⟨m, hm⟩ := hsep
  have hx := primeWindow_gt_one n₀ m
  refine window_closes_signed (H := H) (H' := H') (primeWindow n₀ m) _ hx
    (arrival_mirror_minoration hHH' hFib hT (gapWeights n₀ m) (primeWindow n₀ m)
      (fun r => (gapWeights_pos n₀ m r).le) hx l hH hH' hβ)
    (complement_filtered_le H' _ _ hx) ?_
  rw [removal_re_eq H _ _ _ (primeWindow_ceil_le n₀ m)]
  linarith

#print axioms removal_re_eq
#print axioms primeFilter_re_phaseMatched
#print axioms window_closes_signed
#print axioms signed_of_norm_separation
#print axioms passage_window_reduction_signed

/-! ## 5. Portée : la comparaison signée est toujours renversée par les identités exactes -/

/-- **Membre de gauche toujours au-dessus de la minoration** : par `Y − F = Q` et `F` = supérieure + conjuguée,
`Re L(Y) − Re(conjuguée) + B_Q = Re(supérieure) + (Re L(Q) + B_Q) ≥ U`. La comparaison signée est donc la négation d'un
énoncé démontré : son existence équivaut, dans le contexte, à `False` ; aucune estimation de la part première ne peut
l'établir sans contradiction déjà présente dans le contexte. -/
theorem signed_comparison_lhs_ge {H H' : ℝ} {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r)
    {U BQ : ℝ} (hU : U ≤ (∑' σ, upperFiltered H H' x lam σ).re)
    (hQ : ‖∑ r, lam r * followingSum H' (x r)‖ ≤ BQ) :
    U ≤ (historyRemoved H x lam).re - (∑' σ, lowerFiltered H H' x lam σ).re + BQ := by
  by_contra h
  exact window_closes_signed x lam hx hU hQ (not_le.mp h)

/-- Instance sur la fenêtre du passage, forme exacte du but de la réduction signée : pour TOUTE longueur `m`, le membre de
gauche est au moins la minoration de la paire. -/
theorem passage_signed_comparison_reversed {H H' : ℝ} (hHH' : H ≤ H')
    (hFib : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' → |(σ : ℂ).im| = H')
    (hT : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' →
      (σ : ℂ).re * ((σ : ℂ).re + 1) < (σ : ℂ).im ^ 2)
    (n₀ : ℕ) (l : TrueZero) (hH : H < rZeroHeight l.1) (hH' : rZeroHeight l.1 ≤ H')
    (hβ : rZeroRadialPosition l.1 < 1 / 2) (m : ℕ) :
    (-(zetaZeroMultiplicity (zeroPoint l) : ℂ) / (zeroPoint l * (zeroPoint l + 1))).re *
          ∑ r, gapWeights n₀ m r * primeWindow n₀ m r ^ rZeroRadialPosition l.1 +
        (-(zetaZeroMultiplicity (zeroPoint l) : ℂ) /
            (zeroPoint (mirrorMember l) * (zeroPoint (mirrorMember l) + 1))).re *
          ∑ r, gapWeights n₀ m r * primeWindow n₀ m r ^ (1 - rZeroRadialPosition l.1) ≤
      ∑ n ∈ Finset.range (fnPrimeAtRank (n₀ + m)), (ArithmeticFunction.vonMangoldt n : ℝ) *
          (primeFilter (primeWindow n₀ m) (phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m)) n).re
        - (∑ r, phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m) r *
            smoothedZeroBackground (primeWindow n₀ m r)).re
        - (∑ r, phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m) r *
            precedingSum H (primeWindow n₀ m r)).re
        - (∑' σ, lowerFiltered H H' (primeWindow n₀ m)
            (phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m)) σ).re
        + filteredSeriesBound (followingWeight H') (primeWindow n₀ m)
            (phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m)) := by
  have hx := primeWindow_gt_one n₀ m
  have h := signed_comparison_lhs_ge (H := H) (H' := H') (primeWindow n₀ m) _ hx
    (arrival_mirror_minoration hHH' hFib hT (gapWeights n₀ m) (primeWindow n₀ m)
      (fun r => (gapWeights_pos n₀ m r).le) hx l hH hH' hβ)
    (complement_filtered_le H' _ _ hx)
  rw [removal_re_eq H _ _ _ (primeWindow_ceil_le n₀ m)] at h
  linarith

#print axioms signed_comparison_lhs_ge
#print axioms passage_signed_comparison_reversed

end RHV6Fresh
