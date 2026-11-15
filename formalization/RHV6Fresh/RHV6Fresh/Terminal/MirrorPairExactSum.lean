/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ExplicitFormulaLink
import RHV6Fresh.Terminal.RayEnergy
import RHV6Fresh.Direct.MirrorCount
import RHV6Fresh.Terminal.RaccordDetector

/-!
# Identités exactes de l'audit E118 / E163b / E172 (2026-10-05)

Objets : le terme BRUT `x^ρ/ρ` d'un zéro (`zeroTerm`, la Tour), pas le terme lissé
`x^ρ/(ρ(ρ+1))` du reste lissé. Aucune borne n'est transportée d'un objet à l'autre.

* signe au contact propre : `Re zeroTerm(C_k) = (−1)^k · ‖zeroTerm(C_k)‖` (E118) : la contribution
  signée ALTERNE, seule l'amplitude est positive ;
* paire miroir avec ses dénominateurs exacts (E163b) : `‖paire‖² = ‖terme‖² + ‖terme miroir‖² +
  2·Re(x/(ρ(1−ρ)))`, terme croisé strictement positif : la paire dépasse chacun de ses deux membres
  en tout point ; cela ne dit rien de la somme avec les autres zéros.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **Signe au contact propre** : au contact d'indice `k` de sa propre Tour, la partie réelle du
terme vaut `(−1)^k` fois son amplitude. La contribution signée alterne d'un contact au suivant. -/
theorem zeroTerm_re_at_contact (z : TrueZero) (k : ℤ) :
    (zeroTerm z (contactMinusAt z k)).re =
      (-1 : ℝ) ^ k * ‖zeroTerm z (contactMinusAt z k)‖ := by
  have hq := contactMinusAt_positive z k
  rw [zeroTerm_re_eq_cos_towerPosition hq, towerPosition_contactMinusAt, zeroTerm_norm hq,
    mul_comm Real.pi, Real.cos_int_mul_pi]
  ring

/-- Le point du membre miroir : `1 − conj ρ`. -/
theorem zeroPoint_mirrorMember (z : TrueZero) :
    zeroPoint (mirrorMember z) = 1 - (starRingEnd ℂ) (zeroPoint z) := by
  apply Complex.ext
  · have h1 : (zeroPoint (mirrorMember z)).re = 1 - (zeroPoint z).re := mirrorMember_radial z
    rw [h1, Complex.sub_re, Complex.one_re, Complex.conj_re]
  · have h2 : (zeroPoint (mirrorMember z)).im = (zeroPoint z).im := mirrorMember_ordinate z
    rw [h2, Complex.sub_im, Complex.one_im, Complex.conj_im]
    ring

/-- **Terme croisé d'une paire miroir**, dénominateurs exacts : le produit du terme par le conjugué
du terme miroir vaut `x/(ρ(1−ρ))` ; les deux phases en `x` se compensent exactement. -/
theorem mirror_cross_term {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    (x : ℂ) ^ ρ / ρ *
        (starRingEnd ℂ) ((x : ℂ) ^ (1 - (starRingEnd ℂ) ρ) / (1 - (starRingEnd ℂ) ρ)) =
      (x : ℂ) / (ρ * (1 - ρ)) := by
  have hc : (starRingEnd ℂ) ((x : ℂ) ^ (1 - (starRingEnd ℂ) ρ)) = (x : ℂ) ^ (1 - ρ) := by
    have h := Complex.cpow_conj (x : ℂ) (1 - (starRingEnd ℂ) ρ)
      (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne)
    rw [Complex.conj_ofReal] at h
    rw [← h]
    congr 1
    simp
  rw [map_div₀, hc, map_sub, map_one, Complex.conj_conj, div_mul_div_comm,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),
    show ρ + (1 - ρ) = 1 by ring, Complex.cpow_one]

/-- **Carré de l'amplitude d'une paire miroir, dénominateurs exacts.** -/
theorem mirror_pair_normSq (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm z x + zeroTerm (mirrorMember z) x‖ ^ 2 =
      ‖zeroTerm z x‖ ^ 2 + ‖zeroTerm (mirrorMember z) x‖ ^ 2 +
        2 * ((x : ℂ) / (zeroPoint z * (1 - zeroPoint z))).re := by
  have hcross : zeroTerm z x * (starRingEnd ℂ) (zeroTerm (mirrorMember z) x) =
      (x : ℂ) / (zeroPoint z * (1 - zeroPoint z)) := by
    unfold zeroTerm
    rw [zeroPoint_mirrorMember]
    exact mirror_cross_term hx _
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, hcross]

/-- **Le terme croisé d'une paire miroir est strictement positif** en tout point de l'axe. -/
theorem mirror_cross_re_pos (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    0 < ((x : ℂ) / (zeroPoint z * (1 - zeroPoint z))).re := by
  have hβ0 : 0 < (zeroPoint z).re := zeroPoint_re_pos z
  have hβ1 : (zeroPoint z).re < 1 := thm_zeroRadialPosition_lt_one z.1
  have hT : 0 < (zeroPoint z).im := z.2
  have hre : 0 < (zeroPoint z * (1 - zeroPoint z)).re := by
    rw [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith [mul_pos hβ0 (sub_pos.mpr hβ1), mul_pos hT hT]
  have hne : zeroPoint z * (1 - zeroPoint z) ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre
    exact lt_irrefl _ hre
  rw [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  exact div_pos (mul_pos hx hre) (Complex.normSq_pos.mpr hne)

/-- **Aucune compensation à l'intérieur de la paire** : en tout point de l'axe, l'amplitude de la
somme d'un zéro et de son miroir (termes bruts, dénominateurs exacts) dépasse strictement
l'amplitude de chacun des deux. Énoncé sur la paire seule ; la somme avec les autres zéros n'est
pas concernée. -/
theorem mirror_pair_no_internal_compensation (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm z x‖ < ‖zeroTerm z x + zeroTerm (mirrorMember z) x‖ ∧
      ‖zeroTerm (mirrorMember z) x‖ < ‖zeroTerm z x + zeroTerm (mirrorMember z) x‖ := by
  have hsq := mirror_pair_normSq z hx
  have hpos := mirror_cross_re_pos z hx
  have hs := norm_nonneg (zeroTerm z x + zeroTerm (mirrorMember z) x)
  constructor
  · by_contra h
    have h' := not_lt.mp h
    nlinarith [mul_self_le_mul_self hs h', sq_nonneg ‖zeroTerm (mirrorMember z) x‖]
  · by_contra h
    have h' := not_lt.mp h
    nlinarith [mul_self_le_mul_self hs h', sq_nonneg ‖zeroTerm z x‖]

#print axioms zeroTerm_re_at_contact
#print axioms mirror_pair_normSq
#print axioms mirror_pair_no_internal_compensation

/-! ## Termes LISSÉS `x^ρ/(ρ(ρ+1))` (objet du reste lissé et de `followingSum`), 2026-10-05

Même calcul pour le terme lissé d'un zéro et de son miroir, avec un facteur commun `c ≠ 0`
(en pratique `c = −m`, la multiplicité, égale pour un zéro et son miroir par `zeta_mult_reflect`).
Énoncés sur la paire seule ; la somme avec les autres zéros n'est pas concernée. -/

/-- **Terme croisé d'une paire miroir, termes lissés** : le produit du terme lissé par le conjugué
du terme lissé miroir vaut `x/(w(w+2))`, `w = ρ(1−ρ)`. -/
theorem mirror_cross_term_smoothed {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    (x : ℂ) ^ ρ / (ρ * (ρ + 1)) *
        (starRingEnd ℂ) ((x : ℂ) ^ (1 - (starRingEnd ℂ) ρ) /
          ((1 - (starRingEnd ℂ) ρ) * ((1 - (starRingEnd ℂ) ρ) + 1))) =
      (x : ℂ) / (ρ * (1 - ρ) * (ρ * (1 - ρ) + 2)) := by
  have hc : (starRingEnd ℂ) ((x : ℂ) ^ (1 - (starRingEnd ℂ) ρ)) = (x : ℂ) ^ (1 - ρ) := by
    have h := Complex.cpow_conj (x : ℂ) (1 - (starRingEnd ℂ) ρ)
      (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne)
    rw [Complex.conj_ofReal] at h
    rw [← h]
    congr 1
    simp
  rw [map_div₀, hc, map_mul, map_add, map_sub, map_one, Complex.conj_conj, div_mul_div_comm,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),
    show ρ + (1 - ρ) = 1 by ring, Complex.cpow_one]
  congr 1
  ring

/-- **Le terme croisé lissé d'une paire miroir est strictement positif** en tout point de l'axe. -/
theorem mirror_cross_re_pos_smoothed (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    0 < ((x : ℂ) / (zeroPoint z * (1 - zeroPoint z) *
      (zeroPoint z * (1 - zeroPoint z) + 2))).re := by
  have hβ0 : 0 < (zeroPoint z).re := zeroPoint_re_pos z
  have hβ1 : (zeroPoint z).re < 1 := thm_zeroRadialPosition_lt_one z.1
  have hT : 0 < (zeroPoint z).im := z.2
  set w := zeroPoint z * (1 - zeroPoint z) with hw
  have hwre : w.re = (zeroPoint z).re - (zeroPoint z).re ^ 2 + (zeroPoint z).im ^ 2 := by
    rw [hw, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]; ring
  have hwim : w.im = (zeroPoint z).im - 2 * (zeroPoint z).re * (zeroPoint z).im := by
    rw [hw, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]; ring
  have hre : 0 < (w * (w + 2)).re := by
    have e : (w * (w + 2)).re = w.re * (w.re + 2) - w.im * w.im := by
      rw [Complex.mul_re, Complex.add_re, Complex.add_im]; norm_num
    rw [e, hwre, hwim]
    nlinarith [mul_pos hβ0 (sub_pos.mpr hβ1), mul_pos hT hT, mul_pos (mul_pos hT hT) hβ0,
      mul_pos (mul_pos hT hT) (sub_pos.mpr hβ1),
      mul_pos (mul_pos hβ0 (sub_pos.mpr hβ1)) (mul_pos hT hT)]
  have hne : w * (w + 2) ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre
    exact lt_irrefl _ hre
  rw [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  exact div_pos (mul_pos hx hre) (Complex.normSq_pos.mpr hne)

/-- **Aucune compensation à l'intérieur de la paire, termes lissés** : pour tout facteur commun
`c ≠ 0` et tout `x > 0`, l'amplitude de la somme des termes lissés d'un zéro et de son miroir
dépasse strictement celle de chacun des deux. Énoncé sur la paire seule. -/
theorem mirror_pair_no_internal_compensation_smoothed (z : TrueZero) (c : ℂ) (hcz : c ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    ‖c * ((x : ℂ) ^ zeroPoint z / (zeroPoint z * (zeroPoint z + 1)))‖ <
        ‖c * ((x : ℂ) ^ zeroPoint z / (zeroPoint z * (zeroPoint z + 1)) +
          (x : ℂ) ^ zeroPoint (mirrorMember z) /
            (zeroPoint (mirrorMember z) * (zeroPoint (mirrorMember z) + 1)))‖ ∧
      ‖c * ((x : ℂ) ^ zeroPoint (mirrorMember z) /
          (zeroPoint (mirrorMember z) * (zeroPoint (mirrorMember z) + 1)))‖ <
        ‖c * ((x : ℂ) ^ zeroPoint z / (zeroPoint z * (zeroPoint z + 1)) +
          (x : ℂ) ^ zeroPoint (mirrorMember z) /
            (zeroPoint (mirrorMember z) * (zeroPoint (mirrorMember z) + 1)))‖ := by
  set a := (x : ℂ) ^ zeroPoint z / (zeroPoint z * (zeroPoint z + 1)) with ha
  set b := (x : ℂ) ^ zeroPoint (mirrorMember z) /
    (zeroPoint (mirrorMember z) * (zeroPoint (mirrorMember z) + 1)) with hb
  have hcross : a * (starRingEnd ℂ) b = (x : ℂ) / (zeroPoint z * (1 - zeroPoint z) *
      (zeroPoint z * (1 - zeroPoint z) + 2)) := by
    rw [ha, hb, zeroPoint_mirrorMember]
    exact mirror_cross_term_smoothed hx _
  have hsq : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * (a * (starRingEnd ℂ) b).re := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
  have hpos : 0 < (a * (starRingEnd ℂ) b).re := by
    rw [hcross]; exact mirror_cross_re_pos_smoothed z hx
  have hs := norm_nonneg (a + b)
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hcz
  have h1 : ‖a‖ < ‖a + b‖ := by
    by_contra h
    have h' := not_lt.mp h
    nlinarith [mul_self_le_mul_self hs h', sq_nonneg ‖b‖]
  have h2 : ‖b‖ < ‖a + b‖ := by
    by_contra h
    have h' := not_lt.mp h
    nlinarith [mul_self_le_mul_self hs h', sq_nonneg ‖a‖]
  rw [norm_mul, norm_mul, norm_mul]
  exact ⟨mul_lt_mul_of_pos_left h1 hcn, mul_lt_mul_of_pos_left h2 hcn⟩

#print axioms mirror_pair_no_internal_compensation_smoothed

end RHV6Fresh
