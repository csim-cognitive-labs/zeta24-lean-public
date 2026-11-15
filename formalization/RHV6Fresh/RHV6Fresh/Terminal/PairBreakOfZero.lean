/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PairBreakAtPrime

/-!
# RHV6Fresh — Terminal/PairBreakOfZero : la Tour est le terme du zéro ; les objets d'E450 au paramètre d'un
zéro vrai (E451, §19.73, 2026-11-08 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse, aucun
axiome, aucun `sorry`)

Ordre de l'auteur vérifié (§19.73) : « si on calcule le zéro par zêta, on obtient une Tour ; dans le cas
contraire la Tour n'existe pas ». Ce module écrit ce chaînon dans la forme de la route des contacts, au POINT
`ρ` seul (ordre d'annulation de zêta) : aucune somme de Tours, aucun canal, aucune formule explicite n'est
consommée.

## 1. Le poids d'une Tour est l'ordre d'annulation de zêta
* `zeroMult_eq_zero_iff` : hors du pôle, le poids est nul si et seulement si zêta ne s'annule pas (la Tour
  n'existe pas hors zéro) ; `one_le_zeroMult_zeroPoint` : en un zéro vrai, le poids vaut au moins un ;
  `zeroContribution_eq_zeroMult_mul` : le terme pondéré de la base est le poids fois `x^ρ/ρ`.
## 2. Le miroir
* `zeroMult_mirrorMember` : le zéro réfléchi a le même poids (équation fonctionnelle, `Foundation/ZetaReflect`) ;
  `mirrorMember_ne_self_of_off` : hors ligne, c'est une seconde Tour, distincte, à la même fréquence.
## 3. Les objets d'E450 au paramètre `(β, T)` d'un zéro vrai
* `zero_break_amplitude_exact` : l'amplitude de la cassure (valeur au dernier contact avant `x`) est le module
  du terme du zéro `‖x^ρ/ρ‖` multiplié par le facteur de cellule `e^{−βπf/T}` ;
* `zero_mirror_word_difference_le_one` : les mots du zéro et de son miroir diffèrent d'au plus une cellule ;
* `zero_pair_term_product` : le produit des modules des deux termes vaut exactement `x/(‖ρ‖‖ρ*‖)` ;
  `zero_pair_weighted_product` : pondéré, `m² · x/(‖ρ‖‖ρ*‖)` ;
* `zero_pair_term_ratio` : le rapport des modules vaut `x^{2β−1} · ‖ρ*‖/‖ρ‖` ; `zero_pair_term_ratio_unbounded` :
  non borné dès que `β > 1/2`.

Portée : pont entre un zéro vrai et les objets compilés d'E445–E450 ; aucune contradiction n'est tirée.
-/

namespace RHV6Fresh

open Real Filter Topology RHV3Lean

/-! ## 1. Le poids d'une Tour est l'ordre d'annulation de zêta -/

theorem zeroMult_eq_zero_iff {ρ : ℂ} (hρ : ρ ≠ 1) : zeroMult ρ = 0 ↔ riemannZeta ρ ≠ 0 := by
  have han : AnalyticAt ℂ riemannZeta ρ := riemannZeta_analyticOnNhd_compl_one ρ hρ
  have htop := analyticOrderAt_riemannZeta_ne_top hρ
  unfold zeroMult
  rw [ENat.toNat_eq_zero, han.analyticOrderAt_eq_zero]
  exact ⟨fun h => h.resolve_right htop, fun h => Or.inl h⟩

theorem one_le_zeroMult_zeroPoint (z : TrueZero) : 1 ≤ zeroMult (zeroPoint z) :=
  one_le_zeroMult _ z.1.2

theorem zeroContribution_eq_zeroMult_mul (z : TrueZero) (x : ℝ) :
    cZeroContribution x (zeroPoint z) = (zeroMult (zeroPoint z) : ℂ) * zeroTerm z x := rfl

/-! ## 2. Le miroir a le même poids ; hors ligne, c'est une seconde Tour -/

theorem zeroMult_mirrorMember (z : TrueZero) :
    zeroMult (zeroPoint (mirrorMember z)) = zeroMult (zeroPoint z) := by
  show (nZeroMultiplicity (zUpperMirrorZero z).1).toNat = (nZeroMultiplicity z.1).toNat
  rw [upperMirror_multiplicity]

theorem mirrorMember_ne_self_of_off {z : TrueZero} (hβ : rZeroRadialPosition z.1 ≠ 1 / 2) :
    mirrorMember z ≠ z := by
  intro h
  have h1 := mirrorMember_radial z
  rw [h] at h1
  apply hβ
  linarith

/-! ## 3. Les objets d'E450 au paramètre d'un zéro vrai -/

theorem zero_radial_pos (z : TrueZero) : 0 < rZeroRadialPosition z.1 := zeroPoint_re_pos z

theorem zero_radial_lt_one (z : TrueZero) : rZeroRadialPosition z.1 < 1 :=
  thm_zeroRadialPosition_lt_one z.1

theorem zero_height_pos (z : TrueZero) : 0 < rZeroHeight z.1 := z.2

theorem zero_break_amplitude_exact (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    |contactRealValue (rZeroRadialPosition z.1) (rZeroHeight z.1)
        (lastContactBefore (rZeroRadialPosition z.1) (rZeroHeight z.1) x)| =
      ‖zeroTerm z x‖ * Real.exp (-(rZeroRadialPosition z.1 * Real.pi *
        cellFraction (rZeroRadialPosition z.1) (rZeroHeight z.1) x / rZeroHeight z.1)) := by
  rw [break_amplitude_exact (zero_radial_pos z) (zero_height_pos z) hx, zeroTerm_norm hx,
    zeroPoint_eq_mk]
  ring

theorem zero_mirror_word_difference_le_one (z : TrueZero) (x : ℝ) :
    |lastContactBefore (rZeroRadialPosition (mirrorMember z).1) (rZeroHeight (mirrorMember z).1) x -
      lastContactBefore (rZeroRadialPosition z.1) (rZeroHeight z.1) x| ≤ 1 := by
  rw [mirrorMember_radial, mirrorMember_ordinate]
  exact mirror_word_difference_le_one _ _ _

theorem zero_pair_term_product (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm z x‖ * ‖zeroTerm (mirrorMember z) x‖ =
      x / (‖zeroPoint z‖ * ‖zeroPoint (mirrorMember z)‖) := by
  rw [zeroTerm_norm hx, mirror_zeroTerm_norm hx, div_mul_div_comm, ← Real.rpow_add hx]
  simp

theorem zero_pair_weighted_product (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    ‖cZeroContribution x (zeroPoint z)‖ * ‖cZeroContribution x (zeroPoint (mirrorMember z))‖ =
      (zeroMult (zeroPoint z) : ℝ) ^ 2 * (x / (‖zeroPoint z‖ * ‖zeroPoint (mirrorMember z)‖)) := by
  rw [zeroContribution_eq_zeroMult_mul, zeroContribution_eq_zeroMult_mul, zeroMult_mirrorMember,
    norm_mul, norm_mul, Complex.norm_natCast, ← zero_pair_term_product z hx]
  ring

theorem zero_pair_term_ratio (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm z x‖ / ‖zeroTerm (mirrorMember z) x‖ =
      x ^ (2 * rZeroRadialPosition z.1 - 1) * (‖zeroPoint (mirrorMember z)‖ / ‖zeroPoint z‖) := by
  conv_rhs => rw [show 2 * rZeroRadialPosition z.1 - 1 =
    rZeroRadialPosition z.1 - (1 - rZeroRadialPosition z.1) by ring, Real.rpow_sub hx]
  rw [zeroTerm_norm hx, mirror_zeroTerm_norm hx, div_div_div_comm, div_div_eq_mul_div,
    mul_div_assoc]

theorem zero_pair_term_ratio_unbounded (z : TrueZero) (hβ : 1 / 2 < rZeroRadialPosition z.1)
    (K : ℝ) : ∀ᶠ x : ℝ in atTop, K < ‖zeroTerm z x‖ / ‖zeroTerm (mirrorMember z) x‖ := by
  have h1 : 0 < ‖zeroPoint z‖ := norm_pos_iff.mpr (zeroPoint_ne_zero z)
  have h2 : 0 < ‖zeroPoint (mirrorMember z)‖ := norm_pos_iff.mpr (zeroPoint_ne_zero _)
  have hexp : 0 < 2 * rZeroRadialPosition z.1 - 1 := by linarith
  have ht : Tendsto (fun x : ℝ => x ^ (2 * rZeroRadialPosition z.1 - 1) *
      (‖zeroPoint (mirrorMember z)‖ / ‖zeroPoint z‖)) atTop atTop :=
    (tendsto_rpow_atTop hexp).atTop_mul_const (div_pos h2 h1)
  filter_upwards [ht.eventually (eventually_gt_atTop K), eventually_gt_atTop (0 : ℝ)] with x hK hx
  rw [zero_pair_term_ratio z hx]
  exact hK

end RHV6Fresh
