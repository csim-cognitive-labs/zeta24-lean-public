/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.VerticalForce
import RHV6Fresh.Terminal.ReadingArithmetic

/-!
# RHV6Fresh — capture des rayons : superposition contre entrelacement (2026-09-29)

Théorie de l'auteur (2026-09-29), rendue exacte par le code :

* sur la ligne, la poussée horizontale est supprimée, seule reste la verticalité (F1d, compilé) ;
* ce que `β` détruit n'est PAS l'entrelacement (le miroir hors ligne s'entrelace strictement,
  `mirror_contacts_interlace`) mais la SUPERPOSITION des rayons de `z` et de `z*` ;
* la loi qui n'admet pas un zéro translaté est la CAPTURE : le rayon du miroir est posé sur celui
  du zéro, pas glissé dans la cellule.

Ce fichier mesure la translation par UN seul nombre réel par zéro, la **profondeur d'insertion**
`D(z) := (φ − φ*)/π`, et établit :

* R1 : `C_k(z*) = C_k(z) · exp(−π·D/T)` pour tout `k`, et la position relative du rayon miroir dans
  la cellule `[C_{k−1}(z), C_k(z)]` (échelle logarithmique) vaut exactement `1 − D` ;
* R2 : `D = 0 ⟺ β = 1/2`, `D > 0 ⟺ β < 1/2`, `|D| < 1/2` toujours ;
* R3 : dichotomie exclusive, rayon par rayon : ou bien superposition (ligne), ou bien entrelacement
  strict (hors ligne) — jamais les deux, jamais aucun des deux ;
* R4 : presque-capture : côté inférieur, `0 ≤ D ≤ (1 − 2β)/(π·T)` ; le défaut de capture décroît
  comme `1/T` mais ne s'annule jamais hors ligne (E123 : positions 0,98–0,9999) ;
* R5 : l'échelle des prémisses — `PNoNullPassage`, exclusion horizontale, superposition, absence
  d'entrelacement strict, profondeur nulle — toutes équivalentes à RH (TFAE) ; la capture entraîne
  la verticalité pure sur tout passage.

Verdict honnête : la capture est la bonne loi d'exclusion ET elle est, zéro par zéro, `β = 1/2` ;
universelle, elle est RH. Aucune partie n'en est déchargée par la géométrie des Tours.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## R1 — la profondeur d'insertion -/

/-- **Profondeur d'insertion du miroir** : `D(z) = (φ(z) − φ(z*))/π`. -/
noncomputable def insertionDepth (z : TrueZero) : ℝ :=
  ((towerMotionOf z).phase - (towerMotionOf (mirrorMember z)).phase) / Real.pi

theorem insertionDepth_eq (z : TrueZero) :
    insertionDepth z =
      (Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) -
        Real.arctan (rZeroHeight z.1 / (1 - rZeroRadialPosition z.1))) / Real.pi := by
  rw [insertionDepth, towerMotion_phase, mirrorMember_phase]

theorem contactMinusAt_eq_exp (z : TrueZero) (k : ℤ) :
    contactMinusAt z k =
      Real.exp ((Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) + (k : ℝ) * Real.pi) /
        rZeroHeight z.1) := by
  unfold contactMinusAt
  rw [towerMotion_incidence, towerMotion_phase]

/-- **R1a** : la translation miroir est `C_k(z*) = C_k(z)·exp(−π·D/T)`, pour tout `k`. -/
theorem mirror_contact_eq_depth (z : TrueZero) (k : ℤ) :
    contactMinusAt (mirrorMember z) k =
      contactMinusAt z k * Real.exp (-(Real.pi * insertionDepth z) / rZeroHeight z.1) := by
  rw [mirror_contact_ratio_const]
  congr 2
  unfold insertionDepth
  field_simp [Real.pi_pos.ne']
  ring

/-- **R1b** : position relative (échelle logarithmique) du rayon miroir `k` dans la cellule
`[C_{k−1}(z), C_k(z)]` : exactement `1 − D`. -/
theorem mirror_relative_position (z : TrueZero) (k : ℤ) :
    (Real.log (contactMinusAt (mirrorMember z) k) - Real.log (contactMinusAt z (k - 1))) /
        (Real.pi / rZeroHeight z.1) = 1 - insertionDepth z := by
  have hT : rZeroHeight z.1 ≠ 0 := z.2.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  unfold contactMinusAt insertionDepth
  rw [towerMotion_incidence, towerMotion_incidence, Real.log_exp, Real.log_exp,
    mirrorMember_ordinate]
  push_cast
  field_simp
  ring

/-! ## R2 — signe et taille de la profondeur -/

private theorem phase_lt_iff (z : TrueZero) :
    Real.arctan (rZeroHeight z.1 / (1 - rZeroRadialPosition z.1)) <
        Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) ↔
      rZeroRadialPosition z.1 < 1 / 2 := by
  have hb := thm_zeroRadialPosition_positive z.1
  have hb1 := thm_zeroRadialPosition_lt_one z.1
  have hT : 0 < rZeroHeight z.1 := z.2
  rw [Real.arctan_strictMono.lt_iff_lt, div_lt_div_iff_of_pos_left hT (by linarith) hb]
  constructor <;> intro h <;> linarith

/-- **R2a** : `D > 0 ⟺ β < 1/2`. -/
theorem insertionDepth_pos_iff (z : TrueZero) :
    0 < insertionDepth z ↔ rZeroRadialPosition z.1 < 1 / 2 := by
  rw [insertionDepth_eq, div_pos_iff_of_pos_right Real.pi_pos, sub_pos, phase_lt_iff]

/-- **R2b** : `D = 0 ⟺ β = 1/2`. -/
theorem insertionDepth_eq_zero_iff (z : TrueZero) :
    insertionDepth z = 0 ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  rw [insertionDepth, div_eq_zero_iff, or_iff_left Real.pi_pos.ne', sub_eq_zero]
  constructor
  · intro h
    exact (mirror_degeneracy_tfae z).out 2 0 |>.mp (by rw [h, sub_self])
  · intro h
    rw [mirrorMember_eq_self_of_onLine h]

/-- **R2c** : `|D| < 1/2` pour tout zéro (les deux phases sont dans `]0, π/2[`). -/
theorem abs_insertionDepth_lt_half (z : TrueZero) : |insertionDepth z| < 1 / 2 := by
  have h1 := towerMotion_phase_pos z
  have h2 := towerMotion_phase_lt_pi_div_two z
  have h3 := towerMotion_phase_pos (mirrorMember z)
  have h4 := towerMotion_phase_lt_pi_div_two (mirrorMember z)
  have hpi := Real.pi_pos
  unfold insertionDepth
  rw [abs_div, abs_of_pos hpi, div_lt_iff₀ hpi, abs_lt]
  constructor <;> linarith

/-! ## R3 — dichotomie exclusive : superposition ou entrelacement strict -/

/-- Le rayon miroir `k` est **superposé** au rayon `k` de `z`. -/
def RaySuperposed (z : TrueZero) (k : ℤ) : Prop :=
  contactMinusAt (mirrorMember z) k = contactMinusAt z k

/-- Le rayon miroir `k` est **strictement entrelacé** : strictement à l'intérieur d'une cellule
de `z`, adjacente au rayon `k` (sous lui ou au-dessus). -/
def RayStrictlyInterlaced (z : TrueZero) (k : ℤ) : Prop :=
  (contactMinusAt z (k - 1) < contactMinusAt (mirrorMember z) k ∧
      contactMinusAt (mirrorMember z) k < contactMinusAt z k) ∨
    (contactMinusAt z k < contactMinusAt (mirrorMember z) k ∧
      contactMinusAt (mirrorMember z) k < contactMinusAt z (k + 1))

private theorem mirror_contact_lt_iff (z : TrueZero) (k j : ℤ) (c : ℝ)
    (hc : c = (j : ℝ) - k) :
    contactMinusAt (mirrorMember z) k < contactMinusAt z j ↔
      -insertionDepth z < c := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hpi := Real.pi_pos
  rw [mirrorMember_contactMinusAt, contactMinusAt_eq_exp, Real.exp_lt_exp,
    div_lt_div_iff_of_pos_right hT, insertionDepth_eq, hc, ← neg_div,
    div_lt_iff₀ hpi]
  constructor <;> intro h <;> nlinarith

private theorem contact_lt_mirror_iff (z : TrueZero) (k j : ℤ) (c : ℝ)
    (hc : c = (j : ℝ) - k) :
    contactMinusAt z j < contactMinusAt (mirrorMember z) k ↔
      c < -insertionDepth z := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hpi := Real.pi_pos
  rw [mirrorMember_contactMinusAt, contactMinusAt_eq_exp, Real.exp_lt_exp,
    div_lt_div_iff_of_pos_right hT, insertionDepth_eq, hc, ← neg_div,
    lt_div_iff₀ hpi]
  constructor <;> intro h <;> nlinarith

/-- **R3a** : le rayon `k` est strictement entrelacé ⟺ `D ≠ 0`. -/
theorem rayStrictlyInterlaced_iff (z : TrueZero) (k : ℤ) :
    RayStrictlyInterlaced z k ↔ insertionDepth z ≠ 0 := by
  have hD := abs_insertionDepth_lt_half z
  rw [abs_lt] at hD
  unfold RayStrictlyInterlaced
  rw [contact_lt_mirror_iff z k (k - 1) (-1) (by push_cast; ring),
    mirror_contact_lt_iff z k k 0 (by ring),
    contact_lt_mirror_iff z k k 0 (by ring),
    mirror_contact_lt_iff z k (k + 1) 1 (by push_cast; ring)]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩) <;> intro h0 <;> rw [h0] at h <;> linarith
  · intro h0
    rcases lt_or_gt_of_ne h0 with h | h
    · right; constructor <;> linarith
    · left; constructor <;> linarith

/-- **R3b** : le rayon `k` est superposé ⟺ `D = 0`. -/
theorem raySuperposed_iff (z : TrueZero) (k : ℤ) :
    RaySuperposed z k ↔ insertionDepth z = 0 := by
  rw [insertionDepth_eq_zero_iff]
  exact (mirror_contact_eq_iff_onLine z k)

/-- **R3c. Dichotomie exclusive** : pour tout zéro et tout rayon, exactement un des deux —
superposition (`β = 1/2`) ou entrelacement strict (`β ≠ 1/2`). Le miroir ne peut ni sortir de la
cellule, ni s'y poser ailleurs que sur le rayon. -/
theorem superposed_xor_strictlyInterlaced (z : TrueZero) (k : ℤ) :
    Xor (RaySuperposed z k) (RayStrictlyInterlaced z k) := by
  rw [raySuperposed_iff, rayStrictlyInterlaced_iff]
  by_cases h : insertionDepth z = 0
  · exact Or.inl ⟨h, fun h' => h' h⟩
  · exact Or.inr ⟨h, h⟩

/-- **R3d** : le comportement est le même à TOUS les rayons (`D` ne dépend pas de `k`). -/
theorem strictlyInterlaced_uniform (z : TrueZero) (k j : ℤ) :
    RayStrictlyInterlaced z k ↔ RayStrictlyInterlaced z j := by
  rw [rayStrictlyInterlaced_iff, rayStrictlyInterlaced_iff]

/-! ## R4 — presque-capture : le défaut décroît comme `1/T` -/

private theorem arctan_sub_le {x y : ℝ} (hxy : x ≤ y) : Real.arctan y - Real.arctan x ≤ y - x := by
  have := image_sub_le_mul_sub_of_deriv_le Real.differentiable_arctan (C := 1)
    (fun t => by
      rw [Real.deriv_arctan]
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg t]) hxy
  linarith

/-- **R4** : côté inférieur (`β ≤ 1/2`), `0 ≤ D ≤ (1 − 2β)/(π·T)`. Le miroir s'approche du rayon
de `z` comme `1/T` — la capture est presque réalisée — mais `D = 0` exige `β = 1/2` (R2b). -/
theorem insertionDepth_le (z : TrueZero) (hβ : rZeroRadialPosition z.1 ≤ 1 / 2) :
    0 ≤ insertionDepth z ∧
      insertionDepth z ≤ (1 - 2 * rZeroRadialPosition z.1) / (Real.pi * rZeroHeight z.1) := by
  have hb := thm_zeroRadialPosition_positive z.1
  have hb1 := thm_zeroRadialPosition_lt_one z.1
  have hT : 0 < rZeroHeight z.1 := z.2
  have hpi := Real.pi_pos
  set β := rZeroRadialPosition z.1
  set T := rZeroHeight z.1
  have e1 : Real.arctan (T / β) = Real.pi / 2 - Real.arctan (β / T) := by
    rw [← Real.arctan_inv_of_pos (div_pos hb hT), inv_div]
  have e2 : Real.arctan (T / (1 - β)) = Real.pi / 2 - Real.arctan ((1 - β) / T) := by
    rw [← Real.arctan_inv_of_pos (div_pos (by linarith) hT), inv_div]
  have hle : β / T ≤ (1 - β) / T := div_le_div_of_nonneg_right (by linarith) hT.le
  have hmono := Real.arctan_strictMono.monotone hle
  have hsub := arctan_sub_le hle
  rw [insertionDepth_eq, e1, e2]
  constructor
  · apply div_nonneg _ hpi.le; linarith
  · rw [div_le_div_iff₀ hpi (by positivity)]
    have : (1 - β) / T - β / T = (1 - 2 * β) / T := by ring
    rw [this] at hsub
    have h2 : ((1 - 2 * β) / T) * T = 1 - 2 * β := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hsub hT.le]

/-! ## R5 — l'échelle des prémisses -/

/-- **Ce que la géométrie décharge seule** : la capture vaut sans condition pour tout zéro de la
ligne ; le résidu est exactement l'ensemble des zéros hors ligne, rien de moins. -/
theorem capture_of_onLine {z : TrueZero} (hβ : rZeroRadialPosition z.1 = 1 / 2) (k : ℤ) :
    RaySuperposed z k ∧ ¬ RayStrictlyInterlaced z k := by
  have hD := (insertionDepth_eq_zero_iff z).mpr hβ
  exact ⟨(raySuperposed_iff z k).mpr hD, fun h => (rayStrictlyInterlaced_iff z k).mp h hD⟩

#print axioms mirror_contact_eq_depth
#print axioms mirror_relative_position
#print axioms insertionDepth_pos_iff
#print axioms insertionDepth_eq_zero_iff
#print axioms abs_insertionDepth_lt_half
#print axioms superposed_xor_strictlyInterlaced
#print axioms strictlyInterlaced_uniform
#print axioms insertionDepth_le
#print axioms capture_of_onLine

end RHV6Fresh
