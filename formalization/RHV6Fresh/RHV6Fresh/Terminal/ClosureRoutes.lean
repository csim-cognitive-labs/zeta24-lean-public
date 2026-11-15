/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RadialSlope
import RHV6Fresh.Terminal.ArithmeticReading
import RHV6Fresh.Terminal.NoRegimeChange

/-!
# RHV6Fresh — les routes de fermeture : transport vertical `W`, transport radial `D`, pont arithmétique (E152, auteur, 2026-10-02)

Assemblage de E151 (enroulement), E150 (pente) et de la lecture compilée du reste arithmétique. Deux observables
orthogonaux entre deux membres `e`, `l` :

* **Transport vertical** `W` (§1) : la position d'un même réel `q` passe de la Tour de `e` à celle de `l` de
  `((T_l − T_e)·log q − (φ_l − φ_e))/π` (`vertical_transport_eq`) : hauteurs et phases seules.
* **Transport radial** `D` (§1) : le logarithme du rapport d'amplitude avance de `(β_l − β_e)·log(y/x)`
  (`radial_transport_log_slope`) : positions radiales seules ; `D = 0` ⟺ transport plat (`energyRatio_const_iff`).

Le pont (§2), du côté arithmétique défini sans aucun zéro vers `D` :

* une borne `‖A(x)‖ ≤ C·x^θ` du reste lissé place tout membre dans la bande `1 − θ ≤ β ≤ θ`
  (`radial_strip_of_remainder_growth`), force `θ ≥ 1/2` (`remainder_exponent_ge_half`), et borne **tout** transport
  radial : `|β_l − β_e| ≤ 2θ − 1` (`radial_transport_le_of_remainder_growth`) ;
* à `θ = 1/2` tous les transports sont plats (`all_transports_flat_of_remainder_sqrt_growth`) ;
* forme robuste aux facteurs logarithmiques : RH ⟺ pour tout `ε > 0`, `‖A(x)‖ ≤ C_ε·x^{1/2+ε}`
  (`riemannHypothesis_iff_remainder_growth_all_eps`).

L'ancre (§3) : le transport radial d'un membre vers son miroir (même hauteur) vaut `1 − 2β`
(`mirror_radial_transport`) ; RH ⟺ tous les transports miroirs sont plats (`riemannHypothesis_iff_mirror_transport_flat`)
⟺ tous les transports sont plats (`riemannHypothesis_iff_all_transports_flat`). Le paquet de hauteur d'un membre et de
son miroir a une amplitude `x^β + x^{1−β} ≥ 2√x`, avec égalité (pour `x ≠ 1`) ⟺ en ligne (`pair_amplitude_ge_critical`,
`pair_amplitude_eq_critical_iff`) : un membre hors ligne ne peut qu'élever l'exposant lu à sa fréquence.

Borne : aucune de ces équivalences ne dérive la borne du reste ; elles ramènent toutes les routes à la seule
quantité `θ`, exposant de croissance du reste lissé, défini par les premiers seuls.
Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Real RHV3Lean

/-! ## 1. Deux transports orthogonaux -/

/-- **Transport vertical** : passage de la position d'un même réel `q` d'une Tour à l'autre. -/
theorem vertical_transport_eq (e l : TrueZero) (q : ℝ) :
    towerPosition l q - towerPosition e q =
      ((rZeroHeight l.1 - rZeroHeight e.1) * Real.log q -
        ((towerMotionOf l).phase - (towerMotionOf e).phase)) / Real.pi := by
  unfold towerPosition
  ring

/-- **Transport radial** : le logarithme du rapport d'amplitude avance de `(β_l − β_e)·(log y − log x)`. -/
theorem radial_transport_log_slope (e l : TrueZero) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (energyRatio e l y) - Real.log (energyRatio e l x) =
      (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * (Real.log y - Real.log x) := by
  have hN : 0 < ‖zeroPoint e‖ / ‖zeroPoint l‖ := div_pos (zeroPoint_norm_pos e) (zeroPoint_norm_pos l)
  rw [energyRatio_eq e l hx, energyRatio_eq e l hy,
    Real.log_mul (Real.rpow_pos_of_pos hy _).ne' hN.ne', Real.log_mul (Real.rpow_pos_of_pos hx _).ne' hN.ne',
    Real.log_rpow hy, Real.log_rpow hx]
  ring

/-! ## 2. Le pont : exposant du reste arithmétique → transports radiaux -/

/-- **Bande** : une borne de croissance `C·x^θ` du reste lissé place tout membre dans `[1 − θ, θ]`. -/
theorem radial_strip_of_remainder_growth {θ C : ℝ}
    (h : ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ θ) (z : TrueZero) :
    1 - θ ≤ rZeroRadialPosition z.1 ∧ rZeroRadialPosition z.1 ≤ θ := by
  refine ⟨?_, radial_le_of_remainder_growth h z⟩
  have hm := radial_le_of_remainder_growth h (mirrorMember z)
  rw [mirrorMember_radial] at hm
  linarith

/-- **L'exposant du reste vaut au moins `1/2`**, sans condition. -/
theorem remainder_exponent_ge_half {θ C : ℝ}
    (h : ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ θ) : 1 / 2 ≤ θ := by
  obtain ⟨z, -, -⟩ := exists_two_heights
  have := radial_strip_of_remainder_growth h z
  linarith [this.1, this.2]

/-- **Le pont** : l'exposant du reste borne tout transport radial, `|β_l − β_e| ≤ 2θ − 1`. -/
theorem radial_transport_le_of_remainder_growth {θ C : ℝ}
    (h : ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ θ) (e l : TrueZero) :
    |rZeroRadialPosition l.1 - rZeroRadialPosition e.1| ≤ 2 * θ - 1 := by
  have he := radial_strip_of_remainder_growth h e
  have hl := radial_strip_of_remainder_growth h l
  rw [abs_le]
  constructor <;> linarith [he.1, he.2, hl.1, hl.2]

/-- **À l'exposant critique, tous les transports sont plats.** -/
theorem all_transports_flat_of_remainder_sqrt_growth {C : ℝ}
    (h : ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 : ℝ)) (e l : TrueZero) :
    rZeroRadialPosition l.1 = rZeroRadialPosition e.1 := by
  have := radial_transport_le_of_remainder_growth h e l
  have h0 : |rZeroRadialPosition l.1 - rZeroRadialPosition e.1| ≤ 0 := by linarith
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)

/-- **Forme robuste aux facteurs logarithmiques** : RH ⟺ `∀ ε > 0, ∃ C, ‖A(x)‖ ≤ C·x^{1/2+ε}`. -/
theorem riemannHypothesis_iff_remainder_growth_all_eps :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 + ε) := by
  constructor
  · intro hRH ε hε
    obtain ⟨C, hC⟩ := remainder_sqrt_growth_of_riemannHypothesis hRH
    have hC0 : 0 ≤ C := by
      have h2 := hC 2 (by norm_num)
      have hp : 0 < (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      by_contra hneg
      push Not at hneg
      have : C * (2 : ℝ) ^ (1 / 2 : ℝ) < 0 := mul_neg_of_neg_of_pos hneg hp
      linarith [norm_nonneg (smoothedRemainder 2)]
    refine ⟨C, fun x hx => (hC x hx).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)) hC0
  · intro h
    refine riemannHypothesis_of_noLowerSide fun z hβ => ?_
    have hm : ∀ ε : ℝ, 0 < ε → 1 - rZeroRadialPosition z.1 ≤ 1 / 2 + ε := by
      intro ε hε
      obtain ⟨C, hC⟩ := h ε hε
      have := radial_le_of_remainder_growth hC (mirrorMember z)
      rwa [mirrorMember_radial] at this
    have := hm ((1 / 2 - rZeroRadialPosition z.1) / 2) (by linarith)
    linarith

/-! ## 3. L'ancre : le miroir et le paquet de hauteur -/

/-- **Transport radial vers le miroir** (même hauteur) : `β(z*) − β(z) = 1 − 2β`. -/
theorem mirror_radial_transport (z : TrueZero) :
    rZeroRadialPosition (mirrorMember z).1 - rZeroRadialPosition z.1 = 1 - 2 * rZeroRadialPosition z.1 := by
  rw [mirrorMember_radial]; ring

/-- **RH ⟺ tout transport miroir est plat.** -/
theorem riemannHypothesis_iff_mirror_transport_flat :
    RiemannHypothesis ↔
      ∀ z : TrueZero, ∀ q₁ q₂ : ℝ, 0 < q₁ → 0 < q₂ →
        energyRatio z (mirrorMember z) q₁ = energyRatio z (mirrorMember z) q₂ := by
  constructor
  · intro hRH z
    refine (energyRatio_const_iff z (mirrorMember z)).mpr ?_
    rw [mirrorMember_radial, thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1]
    norm_num
  · intro h
    refine riemannHypothesis_of_noLowerSide fun z hβ => ?_
    have := (energyRatio_const_iff z (mirrorMember z)).mp (h z)
    rw [mirrorMember_radial] at this
    linarith

/-- **RH ⟺ tous les transports radiaux sont plats** (entre deux membres quelconques). -/
theorem riemannHypothesis_iff_all_transports_flat :
    RiemannHypothesis ↔ ∀ e l : TrueZero, rZeroRadialPosition l.1 = rZeroRadialPosition e.1 := by
  constructor
  · intro hRH e l
    rw [thm_zeroRadialPosition_half_of_riemannHypothesis hRH l.1,
      thm_zeroRadialPosition_half_of_riemannHypothesis hRH e.1]
  · intro h
    refine riemannHypothesis_of_noLowerSide fun z hβ => ?_
    have := h z (mirrorMember z)
    rw [mirrorMember_radial] at this
    linarith

/-- **Le paquet de hauteur est au-dessus de la loi critique** : `x^β + x^{1−β} ≥ 2√x`. -/
theorem pair_amplitude_ge_critical (β : ℝ) {x : ℝ} (hx : 0 < x) :
    2 * x ^ (1 / 2 : ℝ) ≤ x ^ β + x ^ (1 - β) := by
  have ha : x ^ β = (x ^ (β / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have hb : x ^ (1 - β) = (x ^ ((1 - β) / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have hc : x ^ (1 / 2 : ℝ) = x ^ (β / 2) * x ^ ((1 - β) / 2) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  rw [ha, hb, hc]
  nlinarith [sq_nonneg (x ^ (β / 2) - x ^ ((1 - β) / 2))]

/-- **Égalité ⟺ en ligne** (pour `x > 0`, `x ≠ 1`). -/
theorem pair_amplitude_eq_critical_iff (β : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    x ^ β + x ^ (1 - β) = 2 * x ^ (1 / 2 : ℝ) ↔ β = 1 / 2 := by
  constructor
  · intro h
    have ha : x ^ β = (x ^ (β / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
    have hb : x ^ (1 - β) = (x ^ ((1 - β) / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
    have hc : x ^ (1 / 2 : ℝ) = x ^ (β / 2) * x ^ ((1 - β) / 2) := by
      rw [← Real.rpow_add hx]; congr 1; ring
    rw [ha, hb, hc] at h
    have hsq : (x ^ (β / 2) - x ^ ((1 - β) / 2)) ^ 2 = 0 := by nlinarith
    have heq : x ^ (β / 2) = x ^ ((1 - β) / 2) := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      linarith
    have hlog := congrArg Real.log heq
    rw [Real.log_rpow hx, Real.log_rpow hx] at hlog
    have hl : Real.log x ≠ 0 := by
      intro h0
      rcases Real.log_eq_zero.mp h0 with h0 | h0 | h0 <;> [linarith; exact hx1 h0; linarith]
    have := mul_right_cancel₀ hl hlog
    linarith
  · intro hβ
    rw [hβ]; norm_num; ring

#print axioms vertical_transport_eq
#print axioms radial_transport_log_slope
#print axioms radial_strip_of_remainder_growth
#print axioms remainder_exponent_ge_half
#print axioms radial_transport_le_of_remainder_growth
#print axioms all_transports_flat_of_remainder_sqrt_growth
#print axioms riemannHypothesis_iff_remainder_growth_all_eps
#print axioms mirror_radial_transport
#print axioms riemannHypothesis_iff_mirror_transport_flat
#print axioms riemannHypothesis_iff_all_transports_flat
#print axioms pair_amplitude_ge_critical
#print axioms pair_amplitude_eq_critical_iff

end RHV6Fresh
