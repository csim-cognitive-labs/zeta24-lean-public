/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PacketSeriesBalance

/-!
# L'effet de bords de la paire lu par les contacts (E434, §19.49)

Module isolé (non ajouté à `RHV6Fresh.lean`). Après E433 (§19.48), « absorber sur la série » est une équation par
fenêtre entre le contenu arithmétique et l'effet de bords de la paire. Ici cet effet de bords est lu par les contacts
des deux membres, pour que la lecture radiale des contacts et le contenu arithmétique se fassent face dans une même
équation.

* §1 Partie imaginaire de la Tour par le dernier contact (`towerIm_from_lastContact`) : valeur au contact × croissance
  sur la fraction de cellule × sinus de la fraction.
* §2 Le canal intégré `Tour/(ρ+1)` lit les contacts avec un retard d'angle : combinaison des deux parties de la Tour à
  poids `β+1` et `T` sur `‖ρ+1‖²` (`integratedTower_re_eq`, `integratedTower_re_from_lastContact`).
* §3 Partie réelle de la primitive de la paire : `−2m·x` fois la somme des deux canaux intégrés (`pairPrimitive_re`),
  puis entièrement par les contacts des deux membres, `β = 1/2 − δ` et `1/2 + δ`, même hauteur
  (`pairPrimitive_re_from_contacts`).
* §4 Bilan de fenêtre en partie réelle (`pair_window_re_balance`) : somme des poids de von Mangoldt − variation réelle
  du pas du fond − effet de bords réel = partie réelle du complément.

Aucune hypothèse posée, aucun `sorry`.
-/
open Real RHV3Lean

namespace RHV6Fresh

/-! ## 1. La partie imaginaire de la Tour par le dernier contact -/

/-- Partie imaginaire de la Tour `(β, T)` : `x^β/‖ρ‖ · sin(T log x − φ)`. -/
noncomputable def towerIm (β T x : ℝ) : ℝ :=
  x ^ β / ‖(⟨β, T⟩ : ℂ)‖ * Real.sin (T * Real.log x - towerPhase β T)

theorem towerIm_eq_im {β T : ℝ} (hβ : 0 < β) {x : ℝ} (hx : 0 < x) :
    (towerValue (⟨β, T⟩ : ℂ) x).im = towerIm β T x := by
  rw [towerValue_polar hβ hx, mul_comm Complex.I, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_im]
  rfl

theorem towerIm_from_lastContact {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    towerIm β T x =
      contactRealValue β T (lastContactBefore β T x) *
        (x / contactAt β T (lastContactBefore β T x)) ^ β *
        Real.sin (Real.pi * cellFraction β T x) := by
  have hC := contactAt_pos β T (lastContactBefore β T x)
  have hphase : T * Real.log x - towerPhase β T =
      Real.pi * cellFraction β T x + (lastContactBefore β T x : ℝ) * Real.pi := by
    rw [height_mul_log_eq]
    ring
  unfold towerIm contactRealValue
  rw [hphase, Real.sin_add_int_mul_pi, Real.div_rpow hx.le hC.le]
  have hCk : contactAt β T (lastContactBefore β T x) ^ β ≠ 0 :=
    (Real.rpow_pos_of_pos hC β).ne'
  have hn : ‖(⟨β, T⟩ : ℂ)‖ ≠ 0 := (norm_mk_pos hβ).ne'
  field_simp

/-! ## 2. Le canal intégré lit les contacts avec un retard d'angle -/

/-- Partie réelle du canal intégré : combinaison des deux parties de la Tour à poids `β+1` et `T`. -/
theorem integratedTower_re_eq {β T : ℝ} (hβ : 0 < β) {x : ℝ} (hx : 0 < x) :
    (integratedTower (⟨β, T⟩ : ℂ) x).re =
      ((β + 1) * towerRe β T x + T * towerIm β T x) / Complex.normSq ((⟨β, T⟩ : ℂ) + 1) := by
  rw [integratedTower_eq_geometric_div, Complex.div_re, ← towerRe_eq_re hβ hx, ← towerIm_eq_im hβ hx]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
  ring

/-- **Le canal intégré par le dernier contact** : valeur au contact × croissance × retard d'angle. -/
theorem integratedTower_re_from_lastContact {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    (integratedTower (⟨β, T⟩ : ℂ) x).re =
      contactRealValue β T (lastContactBefore β T x) *
        (x / contactAt β T (lastContactBefore β T x)) ^ β *
        ((β + 1) * Real.cos (Real.pi * cellFraction β T x) + T * Real.sin (Real.pi * cellFraction β T x)) /
        Complex.normSq ((⟨β, T⟩ : ℂ) + 1) := by
  rw [integratedTower_re_eq hβ hx, towerRe_from_lastContact hβ hT hx, towerIm_from_lastContact hβ hT hx]
  ring

/-! ## 3. La primitive de la paire par les contacts des deux membres -/

namespace OffCarrier
variable (C : OffCarrier)

theorem zeroPoint_mk (z : TrueZero) : zeroPoint z = (⟨rZeroRadialPosition z.1, rZeroHeight z.1⟩ : ℂ) :=
  Complex.ext rfl rfl

theorem zeroTerm_div_eq_integrated (z : TrueZero) (x : ℝ) :
    zeroTerm z x / (zeroPoint z + 1) = integratedTower (zeroPoint z) x := by
  rw [integratedTower_eq_geometric_div]; rfl

/-- Partie réelle de la primitive de la paire : `−2m·x` fois la somme des deux canaux intégrés. -/
theorem pairPrimitive_re (x : ℝ) :
    (C.pairPrimitive x).re =
      -2 * (zetaZeroMultiplicity (zeroPoint C.zero) : ℝ) * x *
        ((integratedTower (zeroPoint C.zero) x).re + (integratedTower (zeroPoint (mirrorMember C.zero)) x).re) := by
  unfold pairPrimitive
  rw [zeroTerm_div_eq_integrated, zeroTerm_div_eq_integrated]
  simp only [Complex.mul_re, Complex.add_re, Complex.neg_re, Complex.natCast_re, Complex.natCast_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.mul_im, Complex.add_im,
    Complex.neg_im]
  ring

theorem mirror_height_eq : rZeroHeight (mirrorMember C.zero).1 = rZeroHeight C.zero.1 := mirrorMember_ordinate C.zero

/-- **L'effet de bords lu par les contacts des deux membres** (`x > 0`). -/
theorem pairPrimitive_re_from_contacts {x : ℝ} (hx : 0 < x) :
    (C.pairPrimitive x).re =
      -2 * (zetaZeroMultiplicity (zeroPoint C.zero) : ℝ) * x *
        (contactRealValue (1 / 2 - C.radialShift) (rZeroHeight C.zero.1)
              (lastContactBefore (1 / 2 - C.radialShift) (rZeroHeight C.zero.1) x) *
            (x / contactAt (1 / 2 - C.radialShift) (rZeroHeight C.zero.1)
              (lastContactBefore (1 / 2 - C.radialShift) (rZeroHeight C.zero.1) x)) ^ (1 / 2 - C.radialShift) *
            ((1 / 2 - C.radialShift + 1) *
                Real.cos (Real.pi * cellFraction (1 / 2 - C.radialShift) (rZeroHeight C.zero.1) x) +
              rZeroHeight C.zero.1 *
                Real.sin (Real.pi * cellFraction (1 / 2 - C.radialShift) (rZeroHeight C.zero.1) x)) /
            Complex.normSq ((⟨1 / 2 - C.radialShift, rZeroHeight C.zero.1⟩ : ℂ) + 1) +
          contactRealValue (1 / 2 + C.radialShift) (rZeroHeight C.zero.1)
              (lastContactBefore (1 / 2 + C.radialShift) (rZeroHeight C.zero.1) x) *
            (x / contactAt (1 / 2 + C.radialShift) (rZeroHeight C.zero.1)
              (lastContactBefore (1 / 2 + C.radialShift) (rZeroHeight C.zero.1) x)) ^ (1 / 2 + C.radialShift) *
            ((1 / 2 + C.radialShift + 1) *
                Real.cos (Real.pi * cellFraction (1 / 2 + C.radialShift) (rZeroHeight C.zero.1) x) +
              rZeroHeight C.zero.1 *
                Real.sin (Real.pi * cellFraction (1 / 2 + C.radialShift) (rZeroHeight C.zero.1) x)) /
            Complex.normSq ((⟨1 / 2 + C.radialShift, rZeroHeight C.zero.1⟩ : ℂ) + 1)) := by
  have hβ : 0 < 1 / 2 - C.radialShift := by rw [← C.zero_radial_eq]; exact zeroPoint_re_pos C.zero
  have hβ' : 0 < 1 / 2 + C.radialShift := by linarith [C.radialShift_pos]
  have hT : 0 < rZeroHeight C.zero.1 := C.zero.2
  rw [C.pairPrimitive_re, zeroPoint_mk C.zero, zeroPoint_mk (mirrorMember C.zero), C.mirror_height_eq,
    C.zero_radial_eq, C.mirror_radial_eq, integratedTower_re_from_lastContact hβ hT hx,
    integratedTower_re_from_lastContact hβ' hT hx]

/-! ## 4. Le bilan de fenêtre en partie réelle -/

/-- **Le contenu arithmétique face aux contacts** : sur une fenêtre, partie réelle du complément = somme des poids de
von Mangoldt − variation réelle du pas du fond − effet de bords réel de la paire. -/
theorem pair_window_re_balance (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) {a : ℕ}
    (ha : 2 ≤ a) (m : ℕ) :
    (∑ k ∈ Finset.range m, packetIncrement C.packetᶜ (a + k)).re =
      (∑ k ∈ Finset.range m, (ArithmeticFunction.vonMangoldt (a + k + 1) : ℝ)) -
        (stepAt backgroundPrimitive (a + m) - stepAt backgroundPrimitive a).re -
        (((C.pairPrimitive (((a + m : ℕ) : ℝ) + 1)).re - (C.pairPrimitive ((a + m : ℕ) : ℝ)).re) -
          ((C.pairPrimitive ((a : ℝ) + 1)).re - (C.pairPrimitive a).re)) := by
  rw [C.pair_complement_series_balance h ha m, remainderIncrement_series_arithmetic]
  simp only [Complex.sub_re, Complex.re_sum, Complex.ofReal_re]

end OffCarrier

#print axioms towerIm_from_lastContact
#print axioms integratedTower_re_from_lastContact
#print axioms OffCarrier.pairPrimitive_re
#print axioms OffCarrier.pairPrimitive_re_from_contacts
#print axioms OffCarrier.pair_window_re_balance

end RHV6Fresh
