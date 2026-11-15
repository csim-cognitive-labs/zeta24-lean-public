/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GapSynchronization
import RHV6Fresh.Terminal.FrequencyCap
import RHV6Fresh.Terminal.OffCarrier
import RHV6Fresh.Terminal.RegimeTower

/-!
# Régimes de contact d'un écart premier et foule d'un écart (module isolé, 2026-11-01)

Correction de stratégie de l'auteur (2026-11-01, §19.29) : la demande d'un écart n'est jamais portée par deux ou trois
zéros ; elle est portée collectivement par tous les zéros dont le pas de contact est au moins la longueur de l'écart.
Les contacts font partie intégrante de l'axe réel où se trouvent les premiers et leurs écarts ; les formules
tangentielles aux contacts sont à la base de toute démarche. Ce module compile la lecture par contacts des trois
régimes de contribution d'une Tour à un écart, la foule d'un écart, et ce que les contacts lisent de la position radiale.

## 1. L'écart lu en cellules de contact
* `cells_read_eq_length_over_pitch` : l'écart `[p_n, p_{n+1}]` est lu par la Tour `z` par `ℓ / pas(z)` cellules, où `ℓ`
  est sa longueur logarithmique et `pas(z) = π/T_z` le pas de contact (`towerPitch_eq_contacts`).
* Trois régimes par contacts : `BelowOneContact` (l'écart est plus court qu'un pas : au plus un contact dedans),
  `OneContactPitch` (l'écart est exactement un pas), `SeveralContacts` (plusieurs contacts dedans) ; trichotomie.
  `belowOneContact_iff_height_lt` : « moins d'un pas » ⟺ `T_z < π/ℓ`.

## 2. La contribution de l'oscillateur unitaire par régime (phase conservée)
* `unit_contribution_norm` : `‖∫_a^b e^{iTt} dt‖ = 2·|sin(T·ℓ/2)|/T` (chaîne `unitGapTerm_sinc`).
* `unit_contribution_le_length` : `≤ ℓ`, **aveugle à la hauteur** : toutes les Tours sous un pas contribuent au plateau.
* `unit_contribution_le_two_over_height` : `≤ 2/T`, enveloppe décroissante au-delà.
* `unit_contribution_at_one_pitch` : à exactement un pas, `= 2ℓ/π`.
* `unit_contribution_vanishes_at_full_periods` : quand l'écart vaut un nombre pair de pas, la contribution est nulle.
* `gapTerm_norm_le_length_mul` (toute Tour, `β ≥ 0`) : `‖Δ‖ ≤ e^{β b}·ℓ` ; `gapTerm_norm_le_cap` : `‖Δ‖ ≤ (e^{βb}+e^{βa})/‖ρ‖`.

## 3. La foule d'un écart
* `crowd I := upperWindow (π/ℓ)` ; `mem_crowd_iff_pitch` : une Tour est dans la foule de l'écart ⟺ son pas de contact est
  au moins la longueur de l'écart ; `crowd_rank_iff` : le membre de rang `k+1` est dans la foule ⟺ `ℓ ≤ pas(k)`.
* `OffCarrier.pair_same_crowds` : le zéro OFF et son membre sortant (même pas) sont dans les foules des mêmes écarts.

## 4. Ce que les contacts lisent de la position radiale (formules tangentielles)
* `contact_tangent_reads_radial` : en tout contact, `tan(T·log C_k) = T/β` (`contactAt_tangent_minus`) : le contact porte
  la position radiale sur l'axe réel.
* `OffCarrier.pair_contacts_shifted` : les contacts du zéro OFF et de son miroir, de même pas, sont décalés de
  `(arctan(T/(1−β)) − arctan(T/β))/T`, non nul (`pair_contacts_shift_ne_zero`) : même pas, contacts différents.

Aucun énoncé ne conclut sur `β`. Aucun `sorry`, aucun axiome, aucune hypothèse nouvelle. Non ajouté à `RHV6Fresh.lean`.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. L'écart lu en cellules de contact -/

/-- Longueur logarithmique de l'écart `ℓ = log p_{n+1} − log p_n`. -/
noncomputable def PrimeGapInterval.logLength (I : PrimeGapInterval) : ℝ := I.b - I.a

theorem PrimeGapInterval.logLength_pos (I : PrimeGapInterval) : 0 < I.logLength :=
  sub_pos.mpr I.a_lt_b

/-- **L'écart est lu par `ℓ / pas` cellules de contact** de la Tour `z`. -/
theorem cells_read_eq_length_over_pitch (z : TrueZero) (I : PrimeGapInterval) :
    towerPosition z I.upper - towerPosition z I.lower = I.logLength / towerPitch z := by
  rw [gap_reading_height_only]
  unfold towerPitch PrimeGapInterval.logLength PrimeGapInterval.b PrimeGapInterval.a
  rw [div_div_eq_mul_div]
  ring

/-- L'écart est plus court qu'un pas de contact de `z` : au plus un contact de `z` dedans. -/
def BelowOneContact (z : TrueZero) (I : PrimeGapInterval) : Prop := I.logLength < towerPitch z

/-- L'écart vaut exactement un pas de contact de `z`. -/
def OneContactPitch (z : TrueZero) (I : PrimeGapInterval) : Prop := I.logLength = towerPitch z

/-- L'écart contient plusieurs contacts de `z`. -/
def SeveralContacts (z : TrueZero) (I : PrimeGapInterval) : Prop := towerPitch z < I.logLength

theorem contact_regime_trichotomy (z : TrueZero) (I : PrimeGapInterval) :
    BelowOneContact z I ∨ OneContactPitch z I ∨ SeveralContacts z I :=
  lt_trichotomy _ _

/-- « Moins d'un pas » ⟺ `T_z < π/ℓ`. -/
theorem belowOneContact_iff_height_lt (z : TrueZero) (I : PrimeGapInterval) :
    BelowOneContact z I ↔ rZeroHeight z.1 < Real.pi / I.logLength := by
  have hT : 0 < rZeroHeight z.1 := z.2
  unfold BelowOneContact towerPitch
  rw [lt_div_iff₀ hT, mul_comm, ← lt_div_iff₀ I.logLength_pos]

/-! ## 2. La contribution de l'oscillateur unitaire par régime -/

/-- `‖∫_a^b e^{iTt} dt‖ = 2·|sin(T·ℓ/2)|/T`. -/
theorem unit_contribution_norm {T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) :
    ‖gapTerm (T * Complex.I) I.a I.b‖ = 2 * |Real.sin (T * (I.logLength / 2))| / T := by
  rw [unitGapTerm_sinc hT.ne' I.a_lt_b.ne]
  have hh : 0 < gapHalfWidth I.a I.b := by
    unfold gapHalfWidth; linarith [I.a_lt_b]
  have he : ‖Complex.exp (↑T * ↑(gapCenter I.a I.b) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [norm_mul, norm_mul, norm_mul, he, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hh, abs_div, abs_of_pos (mul_pos hT hh)]
  have hℓ : I.logLength / 2 = gapHalfWidth I.a I.b := rfl
  rw [hℓ]
  norm_num
  field_simp

/-- **Plateau aveugle à la hauteur** : `‖∫_a^b e^{iTt} dt‖ ≤ ℓ` pour toute fréquence. -/
theorem unit_contribution_le_length (T : ℝ) (I : PrimeGapInterval) :
    ‖gapTerm (T * Complex.I) I.a I.b‖ ≤ I.logLength := by
  unfold gapTerm
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := I.a) (b := I.b) (C := 1)
    (f := fun t : ℝ => Complex.exp (T * Complex.I * t)) (fun x _ => by
      rw [Complex.norm_exp]; simp)
  rw [one_mul, abs_of_pos (sub_pos.mpr I.a_lt_b)] at h
  unfold PrimeGapInterval.logLength
  exact h

/-- **Enveloppe décroissante** : `‖∫_a^b e^{iTt} dt‖ ≤ 2/T`. -/
theorem unit_contribution_le_two_over_height {T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) :
    ‖gapTerm (T * Complex.I) I.a I.b‖ ≤ 2 / T := by
  rw [unit_contribution_norm hT I]
  apply div_le_div_of_nonneg_right _ hT.le
  have := Real.abs_sin_le_one (T * (I.logLength / 2))
  linarith

/-- **À exactement un pas** : `‖∫_a^b e^{iT_z t} dt‖ = 2ℓ/π`. -/
theorem unit_contribution_at_one_pitch (z : TrueZero) (I : PrimeGapInterval) (h : OneContactPitch z I) :
    ‖gapTerm (rZeroHeight z.1 * Complex.I) I.a I.b‖ = 2 * I.logLength / Real.pi := by
  have hT : 0 < rZeroHeight z.1 := z.2
  rw [unit_contribution_norm hT I]
  unfold OneContactPitch towerPitch at h
  have harg : rZeroHeight z.1 * (I.logLength / 2) = Real.pi / 2 := by rw [h]; field_simp
  rw [harg, Real.sin_pi_div_two, abs_one, h]
  field_simp

/-- **Nullité aux périodes entières** : si l'écart vaut un nombre pair `2m` de pas de `z`, la contribution de
l'oscillateur unitaire de `z` est nulle. -/
theorem unit_contribution_vanishes_at_full_periods (z : TrueZero) (I : PrimeGapInterval) (m : ℤ)
    (h : I.logLength = 2 * m * towerPitch z) :
    ‖gapTerm (rZeroHeight z.1 * Complex.I) I.a I.b‖ = 0 := by
  have hT : 0 < rZeroHeight z.1 := z.2
  rw [unit_contribution_norm hT I]
  have harg : rZeroHeight z.1 * (I.logLength / 2) = m * Real.pi := by
    rw [h]; unfold towerPitch; field_simp
  rw [harg, Real.sin_int_mul_pi, abs_zero]
  simp

/-- **Plafond aveugle à la hauteur, toute Tour** (`β ≥ 0`) : `‖∫_a^b e^{ρt} dt‖ ≤ e^{β b}·(b − a)`. -/
theorem gapTerm_norm_le_length_mul {ρ : ℂ} (hρ : 0 ≤ ρ.re) {a b : ℝ} (hab : a ≤ b) :
    ‖gapTerm ρ a b‖ ≤ Real.exp (ρ.re * b) * (b - a) := by
  unfold gapTerm
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := Real.exp (ρ.re * b))
    (f := fun t : ℝ => Complex.exp (ρ * t)) (fun x hx => by
      rw [Complex.norm_exp]
      have hre : (ρ * (x : ℂ)).re = ρ.re * x := by simp [Complex.mul_re]
      rw [hre]
      apply Real.exp_le_exp.mpr
      have hxb : x ≤ b := by
        rcases Set.mem_uIoc.mp hx with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact h2
        · exact h2.trans hab
      exact mul_le_mul_of_nonneg_left hxb hρ)
  rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at h

/-- **Enveloppe décroissante, toute Tour** : `‖∫_a^b e^{ρt} dt‖ ≤ (e^{β b} + e^{β a})/‖ρ‖`. -/
theorem gapTerm_norm_le_cap {ρ : ℂ} (hρ : ρ ≠ 0) (a b : ℝ) :
    ‖gapTerm ρ a b‖ ≤ (Real.exp (ρ.re * b) + Real.exp (ρ.re * a)) / ‖ρ‖ := by
  rw [gapTerm_eq hρ, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_exp, Complex.norm_exp]
  have h1 : (ρ * (b : ℂ)).re = ρ.re * b := by simp [Complex.mul_re]
  have h2 : (ρ * (a : ℂ)).re = ρ.re * a := by simp [Complex.mul_re]
  rw [h1, h2]

/-! ## 3. La foule d'un écart -/

/-- **La foule de l'écart** : les points-zéros dont le pas de contact est au moins `ℓ` (hauteur `≤ π/ℓ`). -/
noncomputable def crowd (I : PrimeGapInterval) : Finset ℂ := upperWindow (Real.pi / I.logLength)

/-- Une Tour est dans la foule de l'écart ⟺ son pas de contact est au moins la longueur de l'écart. -/
theorem mem_crowd_iff_pitch (I : PrimeGapInterval) (w : TrueZero) :
    zeroPoint w ∈ crowd I ↔ I.logLength ≤ towerPitch w := by
  unfold crowd
  rw [mem_upperWindow_iff]
  constructor
  · rintro ⟨w', hw', hle⟩
    have hww : w' = w := by apply Subtype.ext; apply Subtype.ext; exact hw'
    subst hww
    have hT : 0 < rZeroHeight w'.1 := w'.2
    unfold towerPitch
    rwa [le_div_iff₀ hT, mul_comm, ← le_div_iff₀ I.logLength_pos]
  · intro h
    refine ⟨w, rfl, ?_⟩
    have hT : 0 < rZeroHeight w.1 := w.2
    unfold towerPitch at h
    rwa [le_div_iff₀ hT, mul_comm, ← le_div_iff₀ I.logLength_pos] at h

/-- Le membre de rang `k+1` est dans la foule ⟺ la foule compte au moins `k+1` points ⟺ `ℓ ≤ pas(k)`. -/
theorem crowd_rank_iff (k : ℕ) (I : PrimeGapInterval) :
    k + 1 ≤ (crowd I).card ↔ I.logLength ≤ towerPitch (canonicalMember k) := by
  unfold crowd
  rw [← height_le_iff_card]
  have hT : 0 < rZeroHeight (canonicalMember k).1 := (canonicalMember k).2
  unfold towerPitch
  rw [le_div_iff₀ hT, mul_comm, ← le_div_iff₀ I.logLength_pos]

/-- Les foules sont emboîtées : un écart plus court a une foule plus grande. -/
theorem crowd_mono {I J : PrimeGapInterval} (h : I.logLength ≤ J.logLength) : crowd J ⊆ crowd I := by
  intro ρ hρ
  unfold crowd at hρ ⊢
  rw [mem_upperWindow] at hρ ⊢
  refine ⟨hρ.1, hρ.2.1, hρ.2.2.trans ?_⟩
  exact div_le_div_of_nonneg_left Real.pi_pos.le I.logLength_pos h

namespace OffCarrier

variable (C : OffCarrier)

/-- **Le zéro OFF et son membre sortant ont le même pas** et sont donc dans les foules des mêmes écarts. -/
theorem pair_same_crowds (I : PrimeGapInterval) :
    zeroPoint C.zero ∈ crowd I ↔ zeroPoint C.outgoingMember ∈ crowd I := by
  rw [mem_crowd_iff_pitch, mem_crowd_iff_pitch]
  unfold towerPitch
  rw [show rZeroHeight C.outgoingMember.1 = rZeroHeight C.zero.1 from C.outgoing_same_height]

end OffCarrier

/-! ## 4. Ce que les contacts lisent de la position radiale -/

/-- **Formule tangentielle au contact** : `tan(T·log C_k) = T/β`. Le contact, point de l'axe réel, porte `β`. -/
theorem contact_tangent_reads_radial (z : TrueZero) (k : ℤ) :
    Real.tan (rZeroHeight z.1 * Real.log (contactMinusAt z k)) =
      rZeroHeight z.1 / rZeroRadialPosition z.1 :=
  contactAt_tangent_minus z k

namespace OffCarrier

variable (C : OffCarrier)

/-- **Les contacts du zéro OFF et de son miroir sont décalés** : même pas, contacts différents, décalage
`(arctan(T/(1−β)) − arctan(T/β))/T` en logarithme, le même pour toute cellule. -/
theorem pair_contacts_shifted (k : ℤ) :
    Real.log (contactMinusAt (mirrorMember C.zero) k) - Real.log (contactMinusAt C.zero k) =
      (Real.arctan (rZeroHeight C.zero.1 / (1 - rZeroRadialPosition C.zero.1)) -
        Real.arctan (rZeroHeight C.zero.1 / rZeroRadialPosition C.zero.1)) / rZeroHeight C.zero.1 := by
  rw [log_contact_eq, log_contact_eq, towerMotion_phase, towerMotion_phase, mirrorMember_ordinate,
    mirrorMember_radial]
  have hT : 0 < rZeroHeight C.zero.1 := C.zero.2
  field_simp
  ring

/-- Le décalage des contacts de la paire n'est pas nul : la paire est lue par les contacts, pas par le pas. -/
theorem pair_contacts_shift_ne_zero (k : ℤ) :
    Real.log (contactMinusAt (mirrorMember C.zero) k) - Real.log (contactMinusAt C.zero k) ≠ 0 := by
  rw [C.pair_contacts_shifted k]
  have hT : 0 < rZeroHeight C.zero.1 := C.zero.2
  have hβ := C.zero_low
  refine div_ne_zero ?_ hT.ne'
  intro h
  have harg : rZeroHeight C.zero.1 / (1 - rZeroRadialPosition C.zero.1) =
      rZeroHeight C.zero.1 / rZeroRadialPosition C.zero.1 :=
    Real.arctan_strictMono.injective (sub_eq_zero.mp h)
  have h1 : (1 - rZeroRadialPosition C.zero.1) ≠ 0 := by linarith
  by_cases hb : rZeroRadialPosition C.zero.1 = 0
  · rw [hb, div_zero, sub_zero, div_one] at harg
    exact hT.ne' harg
  · rw [div_eq_div_iff h1 hb] at harg
    have : rZeroRadialPosition C.zero.1 = 1 - rZeroRadialPosition C.zero.1 := by
      have := mul_left_cancel₀ hT.ne' harg
      linarith
    linarith

end OffCarrier

#print axioms cells_read_eq_length_over_pitch
#print axioms unit_contribution_norm
#print axioms unit_contribution_le_length
#print axioms unit_contribution_le_two_over_height
#print axioms unit_contribution_at_one_pitch
#print axioms unit_contribution_vanishes_at_full_periods
#print axioms gapTerm_norm_le_length_mul
#print axioms gapTerm_norm_le_cap
#print axioms mem_crowd_iff_pitch
#print axioms crowd_rank_iff
#print axioms crowd_mono
#print axioms OffCarrier.pair_same_crowds
#print axioms contact_tangent_reads_radial
#print axioms OffCarrier.pair_contacts_shifted
#print axioms OffCarrier.pair_contacts_shift_ne_zero

end RHV6Fresh
