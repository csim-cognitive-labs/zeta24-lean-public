/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Tower.Incidences

/-!
# RHV6Fresh — l'origine canonique et le parcours de la Tour (maîtres finaux 2026-09-23, §4)

Niveau GÉOMÉTRIE.  Transcription du maître sémantique final §4 et du maître mathématique final §4 :

* la phase propre vérifie `0 < φ < π/2` ;
* l'**origine canonique** est `C₀ = exp(φ/T)`, premier croisement de l'axe algébrique après
  l'abscisse 1 : `C₋₁ < 1 < C₀`, et `1 < C_k ↔ 0 ≤ k` ;
* le mouvement part de `C₀` et avance d'un **demi-tour** à chaque croisement : le log-rayon du
  croisement `k` est `log C₀ + k·π/T` ; le pas ne dépend que de `T` ;
* à chaque croisement le passage **change de côté** : l'argument `T log C_k − φ` vaut `kπ`, son
  sinus est nul (croisement de l'axe) et son cosinus vaut `(−1)^k` (alternance stricte).

Tout est donné par le seul couple `(β, T)` du zéro : aucun premier, aucun rang, aucun comptage,
aucune production de rayon.  Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. La phase propre est dans `(0, π/2)` -/

theorem towerMotion_phase_pos (z : TrueZero) : 0 < (towerMotionOf z).phase :=
  thm_rTowerPhase_positive z

theorem towerMotion_phase_lt_pi_div_two (z : TrueZero) :
    (towerMotionOf z).phase < Real.pi / 2 :=
  thm_rTowerPhase_lt_piDivTwo z

/-! ## 2. L'ordre des croisements -/

theorem towerMotion_incidence_mono (z : TrueZero) {k l : ℤ} (hkl : k ≤ l) :
    (towerMotionOf z).incidence k ≤ (towerMotionOf z).incidence l := by
  rcases lt_or_eq_of_le hkl with h | h
  · exact le_of_lt (towerMotion_incidence_strictOrder z h)
  · rw [h]

theorem towerMotion_incidence_lt_iff (z : TrueZero) (k l : ℤ) :
    (towerMotionOf z).incidence k < (towerMotionOf z).incidence l ↔ k < l := by
  constructor
  · intro h
    by_contra hle
    exact absurd (lt_of_le_of_lt (towerMotion_incidence_mono z (not_lt.mp hle)) h) (lt_irrefl _)
  · exact towerMotion_incidence_strictOrder z

/-! ## 3. L'origine canonique `C₀ = exp(φ/T)` -/

/-- **L'origine canonique** : le croisement de coordonnée `0`, `C₀ = exp(φ/T)`. -/
noncomputable def canonicalOrigin (z : TrueZero) : ℝ := (towerMotionOf z).incidence 0

theorem canonicalOrigin_eq (z : TrueZero) :
    canonicalOrigin z = Real.exp ((towerMotionOf z).phase / rZeroHeight z.1) := by
  unfold canonicalOrigin
  rw [towerMotion_incidence]
  simp

theorem canonicalOrigin_pos (z : TrueZero) : 0 < canonicalOrigin z :=
  towerMotion_incidence_positive z 0

/-- `1 < C₀` : l'origine canonique est après l'abscisse 1. -/
theorem one_lt_canonicalOrigin (z : TrueZero) : 1 < canonicalOrigin z := by
  rw [canonicalOrigin_eq]
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ < Real.exp ((towerMotionOf z).phase / rZeroHeight z.1) :=
        Real.exp_lt_exp.mpr (div_pos (towerMotion_phase_pos z) z.2)

/-- `C₋₁ < 1` : le croisement précédent est avant l'abscisse 1. -/
theorem incidence_neg_one_lt_one (z : TrueZero) : (towerMotionOf z).incidence (-1) < 1 := by
  rw [towerMotion_incidence]
  have hφ := towerMotion_phase_lt_pi_div_two z
  have hπ := Real.pi_pos
  have hNeg : ((towerMotionOf z).phase + ((-1 : ℤ) : ℝ) * Real.pi) / rZeroHeight z.1 < 0 := by
    apply div_neg_of_neg_of_pos _ z.2
    push_cast
    linarith
  calc Real.exp (((towerMotionOf z).phase + ((-1 : ℤ) : ℝ) * Real.pi) / rZeroHeight z.1)
      < Real.exp 0 := Real.exp_lt_exp.mpr hNeg
    _ = 1 := Real.exp_zero

/-- **`C₀` est le premier croisement après 1** : un croisement dépasse l'abscisse 1 exactement
quand sa coordonnée est au moins `0`. -/
theorem one_lt_incidence_iff (z : TrueZero) (k : ℤ) :
    1 < (towerMotionOf z).incidence k ↔ 0 ≤ k := by
  constructor
  · intro h
    by_contra hk
    have hle : k ≤ -1 := by omega
    have := towerMotion_incidence_mono z hle
    linarith [incidence_neg_one_lt_one z]
  · intro hk
    have h1 := towerMotion_incidence_mono z hk
    have h0 := one_lt_canonicalOrigin z
    unfold canonicalOrigin at h0
    linarith

theorem canonicalOrigin_isLeast (z : TrueZero) :
    IsLeast {k : ℤ | 1 < (towerMotionOf z).incidence k} 0 :=
  ⟨(one_lt_incidence_iff z 0).mpr le_rfl, fun k hk => (one_lt_incidence_iff z k).mp hk⟩

/-! ## 4. Le parcours : un demi-tour par croisement depuis l'origine -/

/-- Le log-rayon du croisement `k` est celui de l'origine plus `k` demi-tours de `π/T`. -/
theorem logIncidence_eq_origin_add_halfTurns (z : TrueZero) (k : ℤ) :
    (towerMotionOf z).logIncidence k =
      Real.log (canonicalOrigin z) + (k : ℝ) * (Real.pi / rZeroHeight z.1) := by
  have h := towerMotion_ringJump_logWidth z 0 k
  unfold canonicalOrigin
  rw [(towerMotionOf z).incidence_eq, Real.log_exp]
  simp only [Int.cast_zero, sub_zero] at h
  linarith

/-- Le pas de log-rayon entre deux croisements consécutifs ne dépend que de `T` (jamais un écart
entre premiers). -/
theorem halfTurn_logStep (z : TrueZero) (k : ℤ) :
    Real.log ((towerMotionOf z).incidence (k + 1)) -
        Real.log ((towerMotionOf z).incidence k) = Real.pi / rZeroHeight z.1 :=
  towerMotion_consecutive_width z k

/-! ## 5. L'alternance de côté à chaque croisement -/

/-- L'argument du mouvement au croisement `k` vaut `kπ`. -/
theorem crossing_argument (z : TrueZero) (k : ℤ) :
    rZeroHeight z.1 * Real.log ((towerMotionOf z).incidence k) - (towerMotionOf z).phase =
      (k : ℝ) * Real.pi := by
  rw [towerMotion_incidence, Real.log_exp]
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  field_simp
  ring

/-- Le croisement `k` est sur l'axe algébrique : le sinus de l'argument est nul. -/
theorem crossing_on_axis (z : TrueZero) (k : ℤ) :
    Real.sin (rZeroHeight z.1 * Real.log ((towerMotionOf z).incidence k) -
      (towerMotionOf z).phase) = 0 := by
  rw [crossing_argument]
  exact Real.sin_int_mul_pi k

/-- Le côté du passage au croisement `k` est `(−1)^k`. -/
theorem crossing_side (z : TrueZero) (k : ℤ) :
    Real.cos (rZeroHeight z.1 * Real.log ((towerMotionOf z).incidence k) -
      (towerMotionOf z).phase) = (-1 : ℝ) ^ k := by
  rw [crossing_argument]
  exact Real.cos_int_mul_pi k

/-- **Alternance stricte** : d'un croisement au suivant, le côté change de signe. -/
theorem crossing_side_alternates (z : TrueZero) (k : ℤ) :
    Real.cos (rZeroHeight z.1 * Real.log ((towerMotionOf z).incidence (k + 1)) -
        (towerMotionOf z).phase) =
      - Real.cos (rZeroHeight z.1 * Real.log ((towerMotionOf z).incidence k) -
        (towerMotionOf z).phase) := by
  rw [crossing_side, crossing_side, zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  ring

/-- Le côté au croisement `k` vaut `±1` : le passage est franc, jamais tangent. -/
theorem crossing_side_abs (z : TrueZero) (k : ℤ) :
    |Real.cos (rZeroHeight z.1 * Real.log ((towerMotionOf z).incidence k) -
      (towerMotionOf z).phase)| = 1 := by
  rw [crossing_argument]
  exact Real.abs_cos_int_mul_pi k

end RHV6Fresh
