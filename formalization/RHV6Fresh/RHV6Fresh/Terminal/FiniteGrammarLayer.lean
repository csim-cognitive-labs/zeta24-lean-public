/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.StageCell
import RHV6Fresh.Terminal.PairCurvature
import RHV6Fresh.Terminal.WindowProgression

/-!
# Couche grammaticale finie sur un petit ensemble de Tours (auteur, 2026-10-10)

Objets : un ensemble fini `F` de membres consécutifs = la fibre des hauteurs dans `]H, H']` (`nextFiberSum H H'`, miroirs et
multiplicités compris) ; l'historique acquis `P_H` ; le complément `Q_{H'}` (toute la queue au-dessus de `H'`). Fenêtres
d'événements premiers : les abscisses sont les premiers `p_r`, les incréments `ΔX_r = X(p_{r+1}) − X(p_r)`.

Tout est DÉMONTRÉ (axiomes standard) :
* §1 identité de l'attendu par événement et par fenêtre : `Y_r := ΔR_r − ΔP_r = ΔF_r + ΔQ_r` et sa somme télescopée sur une
  fenêtre ; le complément reste une erreur COMMUNE, bornée par les théorèmes acquis (`tail_window_increment_bound`,
  `tail_joint_functional_bound`), jamais ajustée fenêtre par fenêtre ;
* §2 discriminabilité : deux profils dont l'écart dépasse DEUX fois la borne du complément ne sont jamais tous deux
  admissibles ; comme la fibre vraie est admissible par l'identité, tout profil alternatif trop éloigné d'elle est exclu
  (`true_fiber_excludes_alternative`) ; forme conjointe sur une famille de fenêtres ;
* §3 écart de réponse imposé par une rupture : enveloppe de la paire basse `x^{β−1/2} + x^{1/2−β} = 2 + κ(x, 1/2 − β)`,
  courbure `κ ≥ ((1/2 − β) log x)²` ; sur une fenêtre de `m` événements (m pair), plancher GRAMMATICAL
  `κ(p_{n+m}/p_n, d) ≥ (d·log(1 + 3m/p_n))²` (`primeAtRank_window_ge_three_mul`) : la grammaire minore l'écart, elle ne lit
  pas `β` ;
* §4 la séparation « écart imposé par une rupture > compensation maximale démontrée du complément » est écrite comme
  théorème à hypothèses explicites (`separation_excludes_profile`) ; son antécédent « le profil ON est admissible » n'est
  dérivé nulle part : c'est le but [3] sous une autre forme.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Identité de l'attendu par événement et par fenêtre -/

/-- Télescopage des incréments sur une fenêtre de `m` événements : `Σ_{r<m} (f (r+1) − f r) = f m − f 0`. -/
theorem window_increments_telescope (f : ℕ → ℂ) (m : ℕ) :
    ∑ r ∈ Finset.range m, (f (r + 1) - f r) = f m - f 0 :=
  Finset.sum_range_sub f m

/-- **Identité par événement** : pour deux abscisses `a, b > 1`, `(ΔR − ΔP_H) = ΔF + ΔQ_{H'}` (`Y_r = ΔF_r + ΔQ_r`). -/
theorem event_identity (H H' : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    (smoothedRemainder b - smoothedRemainder a) - (precedingSum H b - precedingSum H a) =
      (nextFiberSum H H' b - nextFiberSum H H' a) + (followingSum H' b - followingSum H' a) := by
  rw [expected_next_fiber_increment H H' ha hb]; ring

/-- **Identité sur une fenêtre d'événements** `x_0 < x_1 < … < x_m` (abscisses `> 1`) : la somme des `Y_r` est la somme des
`ΔF_r` plus la somme des `ΔQ_r`, et chacune télescope. Le complément est UNE série, commune à tous les événements. -/
theorem window_identity (H H' : ℝ) (x : ℕ → ℝ) (m : ℕ) (hx : ∀ r, 1 < x r) :
    ∑ r ∈ Finset.range m, ((smoothedRemainder (x (r + 1)) - smoothedRemainder (x r))
        - (precedingSum H (x (r + 1)) - precedingSum H (x r))) =
      (nextFiberSum H H' (x m) - nextFiberSum H H' (x 0)) + (followingSum H' (x m) - followingSum H' (x 0)) := by
  have h : ∀ r ∈ Finset.range m, ((smoothedRemainder (x (r + 1)) - smoothedRemainder (x r))
        - (precedingSum H (x (r + 1)) - precedingSum H (x r))) =
      (nextFiberSum H H' (x (r + 1)) - nextFiberSum H H' (x r))
        + (followingSum H' (x (r + 1)) - followingSum H' (x r)) :=
    fun r _ => event_identity H H' (hx r) (hx (r + 1))
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib,
    window_increments_telescope (fun r => nextFiberSum H H' (x r)) m,
    window_increments_telescope (fun r => followingSum H' (x r)) m]

/-- **Compensation maximale démontrée du complément sur une fenêtre** : `‖Σ_r ΔQ_r‖ = ‖Q(x_m) − Q(x_0)‖ ≤ budget(H')(x_0 + x_m)`. -/
theorem window_complement_bound (H' : ℝ) (x : ℕ → ℝ) (m : ℕ) (hx : ∀ r, 1 < x r) :
    ‖∑ r ∈ Finset.range m, (followingSum H' (x (r + 1)) - followingSum H' (x r))‖ ≤
      followingBudget H' * (x 0 + x m) := by
  rw [window_increments_telescope (fun r => followingSum H' (x r)) m]
  exact tail_window_increment_bound H' (hx 0) (hx m)

/-! ## 2. Discriminabilité de deux profils sous la borne du complément -/

/-- **Deux profils trop éloignés ne sont jamais tous deux admissibles** : si `‖F₁ − F₂‖ > 2τ`, alors `‖Y − F₁‖ ≤ τ` et
`‖Y − F₂‖ ≤ τ` sont incompatibles (inégalité triangulaire). -/
theorem rupture_discriminable {Y F₁ F₂ : ℂ} {τ : ℝ} (h : 2 * τ < ‖F₁ - F₂‖) :
    ¬ (‖Y - F₁‖ ≤ τ ∧ ‖Y - F₂‖ ≤ τ) := by
  rintro ⟨h1, h2⟩
  have : ‖F₁ - F₂‖ ≤ ‖Y - F₁‖ + ‖Y - F₂‖ := by
    calc ‖F₁ - F₂‖ = ‖(Y - F₂) - (Y - F₁)‖ := by ring_nf
      _ ≤ ‖Y - F₂‖ + ‖Y - F₁‖ := norm_sub_le _ _
      _ = ‖Y - F₁‖ + ‖Y - F₂‖ := add_comm _ _
  linarith

/-- **La fibre vraie exclut tout profil alternatif trop éloigné** : en `x > 1`, l'attendu `Y = R − P_H` vérifie
`‖Y − F_vraie‖ = ‖Q_{H'}‖ ≤ budget(H')·x` (identité + borne) ; donc tout profil `G` avec `‖F_vraie − G‖ > 2·budget(H')·x`
n'est pas admissible : `‖Y − G‖ > budget(H')·x`. -/
theorem true_fiber_excludes_alternative (H H' : ℝ) {x : ℝ} (hx : 1 < x) (G : ℂ)
    (hgap : 2 * (followingBudget H' * x) < ‖nextFiberSum H H' x - G‖) :
    followingBudget H' * x < ‖(smoothedRemainder x - precedingSum H x) - G‖ := by
  have hQ : ‖(smoothedRemainder x - precedingSum H x) - nextFiberSum H H' x‖ ≤ followingBudget H' * x := by
    have : (smoothedRemainder x - precedingSum H x) - nextFiberSum H H' x = followingSum H' x := by
      rw [expected_next_fiber H H' hx]; ring
    rw [this]; exact followingSum_norm_le_budget_linear H' hx
  by_contra hle
  push_neg at hle
  exact rupture_discriminable hgap ⟨hQ, hle⟩

/-- **Forme conjointe sur une famille finie de fenêtres** : si `‖Σ_r λ_r (F_vraie − G)(x_r)‖ > 2·budget(H')·M` et si chaque
profil de la queue vérifie `‖Σ_r λ_r x_r^σ‖ ≤ M`, alors `G` n'est pas conjointement admissible :
`‖Σ_r λ_r (Y − G)(x_r)‖ > budget(H')·M`. -/
theorem true_fiber_excludes_alternative_joint (H H' : ℝ) {ι : Type*} (s : Finset ι) (x : ι → ℝ) (lam : ι → ℂ)
    (hx : ∀ r ∈ s, 1 < x r) {M : ℝ}
    (hM : ∀ σ : ExplicitIndex, H' < |(σ : ℂ).im| → ‖∑ r ∈ s, lam r * (x r : ℂ) ^ (σ : ℂ)‖ ≤ M)
    (G : ι → ℂ)
    (hgap : 2 * (followingBudget H' * M) < ‖∑ r ∈ s, lam r * (nextFiberSum H H' (x r) - G r)‖) :
    followingBudget H' * M < ‖∑ r ∈ s, lam r * ((smoothedRemainder (x r) - precedingSum H (x r)) - G r)‖ := by
  have hQ := expected_next_fiber_joint H H' s x lam hx hM
  have e1 : ∑ r ∈ s, lam r * (nextFiberSum H H' (x r) - G r) =
      ∑ r ∈ s, lam r * nextFiberSum H H' (x r) - ∑ r ∈ s, lam r * G r := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun r _ => by ring
  have e2 : ∑ r ∈ s, lam r * ((smoothedRemainder (x r) - precedingSum H (x r)) - G r) =
      ∑ r ∈ s, lam r * (smoothedRemainder (x r) - precedingSum H (x r)) - ∑ r ∈ s, lam r * G r := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun r _ => by ring
  rw [e1] at hgap; rw [e2]
  by_contra hle
  push_neg at hle
  exact rupture_discriminable (Y := ∑ r ∈ s, lam r * (smoothedRemainder (x r) - precedingSum H (x r)))
    (F₁ := ∑ r ∈ s, lam r * nextFiberSum H H' (x r)) (F₂ := ∑ r ∈ s, lam r * G r) hgap ⟨hQ, hle⟩

/-! ## 3. Écart de réponse imposé par une rupture : enveloppe de la paire et plancher grammatical -/

/-- **Enveloppe de la paire basse à l'échelle ON** : `x^{−d} + x^{d} = 2 + κ(x, d)` pour `x > 0`, où `d = 1/2 − β` et `κ` est la
courbure radiale ; donc `x^{β−1/2} + x^{1/2−β} ≥ 2 + (d log x)²`. -/
theorem low_pair_envelope_eq {x : ℝ} (hx : 0 < x) (d : ℝ) :
    x ^ (-d) + x ^ d = 2 + radialCurvature x d := by
  unfold radialCurvature
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, Real.cosh_eq]
  ring_nf

theorem low_pair_envelope_ge {x : ℝ} (hx : 0 < x) (d : ℝ) :
    2 + (d * Real.log x) ^ 2 ≤ x ^ (-d) + x ^ d := by
  rw [low_pair_envelope_eq hx d]
  linarith [radialCurvature_ge_sq x d]

/-- **Plancher grammatical de la courbure sur une fenêtre de `m` événements (`m` pair, premiers `> 3`)** :
`κ(p_{n+m}/p_n, d) ≥ (d · log(1 + 3m/p_n))²`. La grammaire minore l'écart imposé par une rupture ; elle ne lit pas `β`. -/
theorem rupture_window_curvature_floor (n m : ℕ) (hm : Even m) (h3 : 3 < fnPrimeAtRank n) (d : ℝ) :
    (d * Real.log (1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ))) ^ 2 ≤
      radialCurvature ((fnPrimeAtRank (n + m) : ℝ) / (fnPrimeAtRank n : ℝ)) d := by
  have h0 : (0 : ℝ) < fnPrimeAtRank n := by exact_mod_cast thm_primeAtRank_pos n
  have hw : (fnPrimeAtRank n : ℝ) + 3 * (m : ℝ) ≤ (fnPrimeAtRank (n + m) : ℝ) := by
    exact_mod_cast primeAtRank_window_ge_three_mul n m hm h3
  have hbase : 1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ) ≤ (fnPrimeAtRank (n + m) : ℝ) / (fnPrimeAtRank n : ℝ) := by
    have hrew : (1 : ℝ) + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ) =
        ((fnPrimeAtRank n : ℝ) + 3 * (m : ℝ)) / (fnPrimeAtRank n : ℝ) := by field_simp
    rw [hrew]
    exact div_le_div_of_nonneg_right hw h0.le
  have h1 : (0 : ℝ) < 1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ) := by positivity
  have hlog : Real.log (1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ)) ≤
      Real.log ((fnPrimeAtRank (n + m) : ℝ) / (fnPrimeAtRank n : ℝ)) := Real.log_le_log h1 hbase
  have hlog0 : 0 ≤ Real.log (1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ)) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) ≤ 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ) by positivity])
  calc (d * Real.log (1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ))) ^ 2
      = d ^ 2 * (Real.log (1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ))) ^ 2 := by ring
    _ ≤ d ^ 2 * (Real.log ((fnPrimeAtRank (n + m) : ℝ) / (fnPrimeAtRank n : ℝ))) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg d)
        exact pow_le_pow_left₀ hlog0 hlog 2
    _ = (d * Real.log ((fnPrimeAtRank (n + m) : ℝ) / (fnPrimeAtRank n : ℝ))) ^ 2 := by ring
    _ ≤ _ := radialCurvature_ge_sq _ d

/-! ## 4. La séparation, écrite exactement -/

/-- **Séparation « écart imposé par une rupture > compensation maximale démontrée du complément »** : sous un historique ON
jusqu'à `H`, si en une abscisse `x > 1` un profil `G` (par exemple le profil ON de la hauteur atteinte) est admissible,
`‖R − P_H − G‖ ≤ budget(H')·x`, alors la fibre vraie est à moins de `2·budget(H')·x` de `G`. Contraposée : un écart
`> 2·budget(H')·x` exclut l'admissibilité de `G`. L'antécédent « le profil ON est admissible » n'est dérivé nulle part : c'est
le but [3] (`‖R − Q_{H'}‖ ≤ C√x`) sous une autre forme. -/
theorem separation_excludes_profile (H H' : ℝ) {x : ℝ} (hx : 1 < x) (G : ℂ)
    (hAdm : ‖(smoothedRemainder x - precedingSum H x) - G‖ ≤ followingBudget H' * x) :
    ‖nextFiberSum H H' x - G‖ ≤ 2 * (followingBudget H' * x) := by
  by_contra h
  push_neg at h
  exact absurd hAdm (not_le.mpr (true_fiber_excludes_alternative H H' hx G h))

#print axioms window_identity
#print axioms true_fiber_excludes_alternative
#print axioms true_fiber_excludes_alternative_joint
#print axioms low_pair_envelope_ge
#print axioms rupture_window_curvature_floor
#print axioms separation_excludes_profile

end RHV6Fresh
