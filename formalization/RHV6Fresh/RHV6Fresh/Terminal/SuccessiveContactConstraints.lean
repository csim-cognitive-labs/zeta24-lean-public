/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ContactRealValue
import RHV6Fresh.Terminal.OffCarrier
import RHV6Fresh.Terminal.TowerTwoSidedRoom

/-!
# RHV6Fresh — Terminal/SuccessiveContactConstraints : contraintes entre Tours lues aux contacts
(§19.39, 2026-11-03, directive « stratégie des contacts réels »)

Module isolé (non ajouté à `RHV6Fresh.lean`). Il prolonge `ContactRealValue` : ce qu'une Tour
impose à une autre quand toutes deux sont lues **aux contacts de la seconde** sur l'axe réel.

## 1. Pas complexe d'une Tour quelconque sur la grille de contacts d'une autre
* `towerValue_step_at_contacts` : entre deux contacts consécutifs de la grille `(β, T)`, toute
  Tour `ρ` est multipliée par `exp(ρ · π/T)` — module `exp(Re ρ · π/T)`, phase `Im ρ · π/T`.
* `crossAmplitudeRatio`, `crossAmplitudeRatio_eq` : le rapport des modules vaut `exp(Re ρ · π/T)`.
* `radial_of_crossAmplitudeRatio` : la position radiale de `ρ` est lue dans ce rapport ;
  `radial_difference_of_crossRatios` : la différence des positions radiales de deux Tours est lue
  dans le quotient de leurs rapports croisés ; `crossRatios_eq_iff_same_radial` : rapports égaux
  ⟺ même position radiale ; `crossRatio_onLine_iff` : prédécesseur sur la ligne ⟹ (égalité ⟺
  successeur sur la ligne).

## 2. La paire miroir lue aux contacts d'un membre
* `mirrorRelativePhase` : `arctan(T/β) − arctan(T/(1−β))`, nulle ⟺ `β = ½`, positive ⟺ `β < ½`,
  de module `< π/2`.
* `towerValue_polar` : forme module–phase de `x^ρ/ρ` pour `x > 0`.
* `mirror_at_contact`, `mirror_im_at_contact` : au contact `k` du membre `(β, T)`, le miroir vaut
  `(−1)^k C_k^{1−β}/‖ρ'‖ · exp(i · phase relative)` ; sa partie imaginaire est proportionnelle au
  sinus de la phase relative.
* `mirror_im_at_contact_eq_zero_iff`, `pair_axis_at_contact_iff` : **la somme de la paire miroir
  passe sur l'axe réel au contact d'un membre si et seulement si ce membre est sur la ligne.**

## 3. Le porteur OFF (première arrivée OFF après une Tour ON)
* `contactAt_eq_contactMinusAt` : pont entre la grille `(β, T)` et les incidences d'un zéro.
* `arrival_crossRatio_ne` : aux contacts du zéro OFF, le rapport croisé du dernier membre ON et
  celui du zéro OFF diffèrent ; `radialShift_read_at_contacts` : le décalage radial est lu
  exactement dans le quotient de ces rapports.
* `pair_not_on_axis_at_zero_contact` : la somme du zéro OFF et de son miroir ne passe pas sur l'axe
  aux contacts du zéro OFF.

Ce que ce module ne fait pas : il ne dérive aucune contradiction. Chaque énoncé est une identité
ou une équivalence exacte qui **rend la position radiale lisible** aux contacts ; aucune loi n'y
force `β = ½`. Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Pas complexe d'une Tour quelconque sur la grille de contacts d'une autre -/

/-- **Entre deux contacts consécutifs de la grille `(β, T)`, toute Tour `ρ` est multipliée par
`exp(ρ · π/T)`.** -/
theorem towerValue_step_at_contacts {β T : ℝ} (hT : T ≠ 0) (ρ : ℂ) (k : ℤ) :
    towerValue ρ (contactAt β T (k + 1)) =
      Complex.exp (ρ * ((Real.pi / T : ℝ) : ℂ)) * towerValue ρ (contactAt β T k) := by
  have hx : 0 < contactAt β T k := contactAt_pos β T k
  have hx1 : 0 < contactAt β T (k + 1) := contactAt_pos β T (k + 1)
  have hlog : Real.log (contactAt β T (k + 1)) = Real.pi / T + Real.log (contactAt β T k) := by
    linarith [contactAt_log_step (β := β) hT k]
  have hrpow : contactAt β T (k + 1) ^ ρ.re =
      Real.exp (ρ.re * (Real.pi / T)) * contactAt β T k ^ ρ.re := by
    rw [Real.rpow_def_of_pos hx1, Real.rpow_def_of_pos hx, hlog, ← Real.exp_add]
    congr 1
    ring
  have hsplit : ρ * ((Real.pi / T : ℝ) : ℂ) =
      ((ρ.re * (Real.pi / T) : ℝ) : ℂ) + Complex.I * ((ρ.im * (Real.pi / T) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hphase : Complex.exp (Complex.I * (ρ.im * Real.log (contactAt β T (k + 1)))) =
      Complex.exp (Complex.I * ((ρ.im * (Real.pi / T) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (ρ.im * Real.log (contactAt β T k))) := by
    rw [← Complex.exp_add, hlog]
    congr 1
    push_cast
    ring
  unfold towerValue
  rw [ofReal_cpow_eq_rpow_mul_exp hx, ofReal_cpow_eq_rpow_mul_exp hx1, hrpow, hphase, hsplit,
    Complex.exp_add, ← Complex.ofReal_exp]
  push_cast
  ring

/-- Module de `x^ρ/ρ` en un contact de la grille `(β, T)` : `C_k^{Re ρ}/‖ρ‖`. -/
theorem norm_towerValue_at_contact (β T : ℝ) (ρ : ℂ) (k : ℤ) :
    ‖towerValue ρ (contactAt β T k)‖ = contactAt β T k ^ ρ.re / ‖ρ‖ := by
  have hx : 0 < contactAt β T k := contactAt_pos β T k
  unfold towerValue
  rw [norm_div, ofReal_cpow_eq_rpow_mul_exp hx, norm_mul,
    Complex.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
  have h : Complex.I * (ρ.im * Real.log (contactAt β T k)) =
      ((ρ.im * Real.log (contactAt β T k) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **Rapport croisé** : module de la Tour `ρ` au contact `k+1` de la grille `(β, T)` sur son module
au contact `k`. -/
noncomputable def crossAmplitudeRatio (ρ : ℂ) (β T : ℝ) (k : ℤ) : ℝ :=
  ‖towerValue ρ (contactAt β T (k + 1))‖ / ‖towerValue ρ (contactAt β T k)‖

/-- **Le rapport croisé vaut `exp(Re ρ · π/T)`** : il ne dépend ni de `k`, ni de la position radiale
`β` de la grille, ni de la hauteur de `ρ`. -/
theorem crossAmplitudeRatio_eq {β T : ℝ} (hT : T ≠ 0) {ρ : ℂ} (hρ : ρ ≠ 0) (k : ℤ) :
    crossAmplitudeRatio ρ β T k = Real.exp (ρ.re * (Real.pi / T)) := by
  unfold crossAmplitudeRatio
  rw [towerValue_step_at_contacts hT ρ k, norm_mul, Complex.norm_exp]
  have hne : ‖towerValue ρ (contactAt β T k)‖ ≠ 0 := by
    rw [norm_towerValue_at_contact]
    exact (div_pos (Real.rpow_pos_of_pos (contactAt_pos β T k) _) (norm_pos_iff.mpr hρ)).ne'
  rw [mul_div_assoc, div_self hne, mul_one]
  congr 1
  simp [Complex.mul_re]

theorem crossAmplitudeRatio_pos {β T : ℝ} (hT : T ≠ 0) {ρ : ℂ} (hρ : ρ ≠ 0) (k : ℤ) :
    0 < crossAmplitudeRatio ρ β T k := by
  rw [crossAmplitudeRatio_eq hT hρ k]; exact Real.exp_pos _

/-- **La position radiale de `ρ` est lue dans son rapport croisé** sur la grille `(β, T)`. -/
theorem radial_of_crossAmplitudeRatio {β T : ℝ} (hT : T ≠ 0) {ρ : ℂ} (hρ : ρ ≠ 0) (k : ℤ) :
    ρ.re = T / Real.pi * Real.log (crossAmplitudeRatio ρ β T k) := by
  rw [crossAmplitudeRatio_eq hT hρ k, Real.log_exp]
  field_simp [Real.pi_ne_zero]

/-- **La différence des positions radiales de deux Tours est lue dans le quotient de leurs rapports
croisés** sur la même grille. -/
theorem radial_difference_of_crossRatios {β T : ℝ} (hT : T ≠ 0) {ρ₁ ρ₂ : ℂ} (h₁ : ρ₁ ≠ 0)
    (h₂ : ρ₂ ≠ 0) (k : ℤ) :
    ρ₁.re - ρ₂.re =
      T / Real.pi * Real.log (crossAmplitudeRatio ρ₁ β T k / crossAmplitudeRatio ρ₂ β T k) := by
  rw [Real.log_div (crossAmplitudeRatio_pos hT h₁ k).ne' (crossAmplitudeRatio_pos hT h₂ k).ne',
    mul_sub, ← radial_of_crossAmplitudeRatio hT h₁ k, ← radial_of_crossAmplitudeRatio hT h₂ k]

/-- **Rapports croisés égaux ⟺ même position radiale.** -/
theorem crossRatios_eq_iff_same_radial {β T : ℝ} (hT : T ≠ 0) {ρ₁ ρ₂ : ℂ} (h₁ : ρ₁ ≠ 0)
    (h₂ : ρ₂ ≠ 0) (k : ℤ) :
    crossAmplitudeRatio ρ₁ β T k = crossAmplitudeRatio ρ₂ β T k ↔ ρ₁.re = ρ₂.re := by
  rw [crossAmplitudeRatio_eq hT h₁ k, crossAmplitudeRatio_eq hT h₂ k]
  constructor
  · intro h
    have := Real.exp_injective h
    have hπ : Real.pi / T ≠ 0 := div_ne_zero Real.pi_ne_zero hT
    exact mul_right_cancel₀ hπ this
  · intro h; rw [h]

/-- **Prédécesseur sur la ligne : le successeur a le même rapport croisé si et seulement s'il est
sur la ligne.** -/
theorem crossRatio_onLine_iff {β T : ℝ} (hT : T ≠ 0) {ρ₁ ρ₂ : ℂ} (h₁ : ρ₁ ≠ 0) (h₂ : ρ₂ ≠ 0)
    (hOn : ρ₁.re = 1 / 2) (k : ℤ) :
    crossAmplitudeRatio ρ₁ β T k = crossAmplitudeRatio ρ₂ β T k ↔ ρ₂.re = 1 / 2 := by
  rw [crossRatios_eq_iff_same_radial hT h₁ h₂ k, hOn, eq_comm]

/-! ## 2. La paire miroir lue aux contacts d'un membre -/

/-- **Phase relative du miroir** : `arctan(T/β) − arctan(T/(1−β))`. -/
noncomputable def mirrorRelativePhase (β T : ℝ) : ℝ := towerPhase β T - towerPhase (1 - β) T

theorem mirrorRelativePhase_eq_zero_iff {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) :
    mirrorRelativePhase β T = 0 ↔ β = 1 / 2 := by
  unfold mirrorRelativePhase towerPhase
  rw [sub_eq_zero]
  constructor
  · intro h
    have h' := Real.arctan_injective h
    have h1 : (0 : ℝ) < 1 - β := by linarith
    field_simp at h'
    nlinarith [h', hT]
  · intro h
    rw [h]; norm_num

theorem mirrorRelativePhase_pos_iff {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) :
    0 < mirrorRelativePhase β T ↔ β < 1 / 2 := by
  unfold mirrorRelativePhase towerPhase
  rw [sub_pos, Real.arctan_strictMono.lt_iff_lt,
    div_lt_div_iff_of_pos_left hT (by linarith) hβ]
  constructor <;> intro h <;> linarith

theorem abs_mirrorRelativePhase_lt {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) :
    |mirrorRelativePhase β T| < Real.pi / 2 := by
  unfold mirrorRelativePhase towerPhase
  have h1 : (0 : ℝ) < 1 - β := by linarith
  have a1 := Real.arctan_pos.mpr (div_pos hT hβ)
  have a2 := Real.arctan_pos.mpr (div_pos hT h1)
  have b1 := Real.arctan_lt_pi_div_two (T / β)
  have b2 := Real.arctan_lt_pi_div_two (T / (1 - β))
  rw [abs_lt]
  constructor <;> linarith

/-- **Forme module–phase de `x^ρ/ρ`** pour `x > 0`, `ρ = β' + iT`, `β' > 0`. -/
theorem towerValue_polar {β' T : ℝ} (hβ' : 0 < β') {x : ℝ} (hx : 0 < x) :
    towerValue (⟨β', T⟩ : ℂ) x =
      ((x ^ β' / ‖(⟨β', T⟩ : ℂ)‖ : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((T * Real.log x - towerPhase β' T : ℝ) : ℂ)) := by
  have hρ : (⟨β', T⟩ : ℂ) ≠ 0 := mk_ne_zero_of_re_pos hβ'
  have hn : (‖(⟨β', T⟩ : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_mk_pos (T := T) hβ').ne'
  have hpolar : (⟨β', T⟩ : ℂ) = ‖(⟨β', T⟩ : ℂ)‖ * Complex.exp (towerPhase β' T * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I (⟨β', T⟩ : ℂ)
    rw [arg_mk_eq_towerPhase hβ'] at this
    exact this.symm
  have hre : (⟨β', T⟩ : ℂ).re = β' := rfl
  have him : (⟨β', T⟩ : ℂ).im = T := rfl
  have key : Complex.exp (Complex.I * ((T * Real.log x - towerPhase β' T : ℝ) : ℂ)) *
      Complex.exp (towerPhase β' T * Complex.I) =
      Complex.exp (Complex.I * ((T : ℂ) * (Real.log x : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold towerValue
  rw [ofReal_cpow_eq_rpow_mul_exp hx, hre, him, div_eq_iff hρ]
  conv_rhs => rhs; rw [hpolar]
  push_cast
  push_cast at key
  rw [← key]
  field_simp

/-- **Le miroir au contact `k` du membre `(β, T)`** :
`(−1)^k · C_k^{1−β}/‖ρ'‖ · exp(i · phase relative)`. -/
theorem mirror_at_contact {β T : ℝ} (hβ1 : β < 1) (hT : 0 < T) (k : ℤ) :
    towerValue (⟨1 - β, T⟩ : ℂ) (contactAt β T k) =
      ((contactAt β T k ^ (1 - β) / ‖(⟨1 - β, T⟩ : ℂ)‖ : ℝ) : ℂ) * (((-1 : ℝ) ^ k : ℝ) : ℂ) *
        Complex.exp (Complex.I * (mirrorRelativePhase β T : ℂ)) := by
  have h1 : (0 : ℝ) < 1 - β := by linarith
  rw [towerValue_polar h1 (contactAt_pos β T k)]
  have harg : T * Real.log (contactAt β T k) - towerPhase (1 - β) T =
      mirrorRelativePhase β T + k * Real.pi := by
    rw [height_mul_log_contactAt hT.ne' k]; unfold mirrorRelativePhase; ring
  rw [harg]
  have hsplit : Complex.I * ((mirrorRelativePhase β T + k * Real.pi : ℝ) : ℂ) =
      Complex.I * (mirrorRelativePhase β T : ℂ) + (k : ℂ) * (Real.pi * Complex.I) := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  push_cast
  ring

/-- **Partie imaginaire du miroir au contact du membre** : proportionnelle au sinus de la phase
relative. -/
theorem mirror_im_at_contact {β T : ℝ} (hβ1 : β < 1) (hT : 0 < T) (k : ℤ) :
    (towerValue (⟨1 - β, T⟩ : ℂ) (contactAt β T k)).im =
      contactAt β T k ^ (1 - β) / ‖(⟨1 - β, T⟩ : ℂ)‖ * (-1 : ℝ) ^ k *
        Real.sin (mirrorRelativePhase β T) := by
  rw [mirror_at_contact hβ1 hT k, mul_comm Complex.I, ← Complex.ofReal_mul, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_im]

/-- **Le miroir est réel au contact du membre si et seulement si le membre est sur la ligne.** -/
theorem mirror_im_at_contact_eq_zero_iff {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T)
    (k : ℤ) :
    (towerValue (⟨1 - β, T⟩ : ℂ) (contactAt β T k)).im = 0 ↔ β = 1 / 2 := by
  rw [mirror_im_at_contact hβ1 hT k]
  have h1 : (0 : ℝ) < 1 - β := by linarith
  have hA : contactAt β T k ^ (1 - β) / ‖(⟨1 - β, T⟩ : ℂ)‖ * (-1 : ℝ) ^ k ≠ 0 :=
    mul_ne_zero (div_pos (Real.rpow_pos_of_pos (contactAt_pos β T k) _)
      (norm_mk_pos (T := T) h1)).ne' (zpow_ne_zero k (by norm_num))
  rw [mul_eq_zero, or_iff_right hA]
  have hb := abs_mirrorRelativePhase_lt hβ hβ1 hT
  rw [abs_lt] at hb
  rw [Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  exact mirrorRelativePhase_eq_zero_iff hβ hβ1 hT

/-- **La somme de la paire miroir passe sur l'axe réel au contact d'un membre si et seulement si ce
membre est sur la ligne.** -/
theorem pair_axis_at_contact_iff {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) (k : ℤ) :
    (towerValue (⟨β, T⟩ : ℂ) (contactAt β T k) +
      towerValue (⟨1 - β, T⟩ : ℂ) (contactAt β T k)).im = 0 ↔ β = 1 / 2 := by
  rw [Complex.add_im, towerValue_at_contact hβ hT k, Complex.ofReal_im, zero_add]
  exact mirror_im_at_contact_eq_zero_iff hβ hβ1 hT k

/-! ## 3. Le porteur OFF : première arrivée OFF après une Tour ON -/

/-- Pont : la grille `(β, T)` d'un zéro est la suite de ses incidences. -/
theorem contactAt_eq_contactMinusAt (z : TrueZero) (k : ℤ) :
    contactAt (rZeroRadialPosition z.1) (rZeroHeight z.1) k = contactMinusAt z k :=
  (contactMinusAt_eq_windingContact z k).symm

theorem zeroPoint_eq_mk (z : TrueZero) :
    zeroPoint z = (⟨rZeroRadialPosition z.1, rZeroHeight z.1⟩ : ℂ) :=
  Complex.ext rfl rfl

namespace OffCarrier

variable (C : OffCarrier)

/-- Le dernier membre ON (membre d'arrivée) comme zéro vrai. -/
noncomputable def arrivalZero : TrueZero := ⟨C.arrival.zEarlierMember, C.arrival_earlier_pos⟩

/-- **Aux contacts du zéro OFF, le rapport croisé du dernier membre ON diffère de celui du zéro
OFF.** -/
theorem arrival_crossRatio_ne (k : ℤ) :
    crossAmplitudeRatio (zeroPoint C.arrivalZero) (rZeroRadialPosition C.zero.1)
        (rZeroHeight C.zero.1) k ≠
      crossAmplitudeRatio (zeroPoint C.zero) (rZeroRadialPosition C.zero.1)
        (rZeroHeight C.zero.1) k := by
  intro h
  have hT : rZeroHeight C.zero.1 ≠ 0 := C.zero.2.ne'
  rw [crossRatios_eq_iff_same_radial hT (zeroPoint_ne_zero _) (zeroPoint_ne_zero _) k,
    zeroPoint_re, zeroPoint_re] at h
  have h1 : rZeroRadialPosition C.arrivalZero.1 = 1 / 2 := C.arrival_earlier_onLine
  have h2 := C.zero_low
  rw [h1] at h
  linarith

/-- **Le décalage radial du zéro OFF est lu exactement dans le quotient des rapports croisés** du
dernier membre ON et du zéro OFF, aux contacts du zéro OFF. -/
theorem radialShift_read_at_contacts (k : ℤ) :
    C.radialShift = rZeroHeight C.zero.1 / Real.pi *
      Real.log (crossAmplitudeRatio (zeroPoint C.arrivalZero) (rZeroRadialPosition C.zero.1)
          (rZeroHeight C.zero.1) k /
        crossAmplitudeRatio (zeroPoint C.zero) (rZeroRadialPosition C.zero.1)
          (rZeroHeight C.zero.1) k) := by
  have hT : rZeroHeight C.zero.1 ≠ 0 := C.zero.2.ne'
  rw [← radial_difference_of_crossRatios hT (zeroPoint_ne_zero _) (zeroPoint_ne_zero _) k,
    zeroPoint_re, zeroPoint_re]
  have h1 : rZeroRadialPosition C.arrivalZero.1 = 1 / 2 := C.arrival_earlier_onLine
  rw [h1]
  unfold radialShift
  ring

/-- **La somme du zéro OFF et de son miroir ne passe pas sur l'axe réel aux contacts du zéro
OFF.** -/
theorem pair_not_on_axis_at_zero_contact (k : ℤ) :
    (towerValue (zeroPoint C.zero) (contactMinusAt C.zero k) +
      towerValue (zeroPoint (mirrorMember C.zero)) (contactMinusAt C.zero k)).im ≠ 0 := by
  have hβ : 0 < rZeroRadialPosition C.zero.1 := zeroPoint_re_pos C.zero
  have hβ1 : rZeroRadialPosition C.zero.1 < 1 := by linarith [C.zero_low]
  have hT : 0 < rZeroHeight C.zero.1 := C.zero.2
  rw [← contactAt_eq_contactMinusAt, zeroPoint_eq_mk, zeroPoint_eq_mk, mirrorMember_radial,
    mirrorMember_ordinate, Ne, pair_axis_at_contact_iff hβ hβ1 hT k]
  exact C.zero_low.ne

end OffCarrier

end RHV6Fresh

#print axioms RHV6Fresh.towerValue_step_at_contacts
#print axioms RHV6Fresh.crossRatios_eq_iff_same_radial
#print axioms RHV6Fresh.pair_axis_at_contact_iff
#print axioms RHV6Fresh.OffCarrier.arrival_crossRatio_ne
#print axioms RHV6Fresh.OffCarrier.radialShift_read_at_contacts
#print axioms RHV6Fresh.OffCarrier.pair_not_on_axis_at_zero_contact
