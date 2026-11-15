/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RaccordPhaseRigidity
import RHV6Fresh.Terminal.FirstGainPremise
import RHV6Fresh.Terminal.PrimalEventRaccord

/-!
# Le pont densité → canal des paquets : surplus de la paire dans le canal des Tours (E432, §19.47)

Module isolé (non ajouté à `RHV6Fresh.lean`). La sonde S2 de E431 laissait « reste exact = paquet de la paire » face à
« surplus de densité non nul », sans pont compilé. Ici le pas du canal des paquets est écrit comme intégrale de sa
dérivée (termes de Tour), et le surplus de la paire y est calculé.

* §1 `lineTerm` (terme de Tour du point de ligne) ; identité ponctuelle `pair_zeroTerm_surplus` : dans le canal des
  Tours, Tour(z) + Tour(z*) − 2·ligne = 2(cosh(δ log x) − 1)·ligne + (δ/ρ_L)·(Tour(z) − Tour(z*)).
  Le facteur hyperbolique de la densité survit, PLUS une déformation proportionnelle au décalage radial.
* §2 Dérivée de la primitive du paquet à quatre membres (cas (a)) : `−m·(quatre Tours)` ; le pas local du paquet sur
  `[N, N+1]` est l'intégrale de cette dérivée (`localPacket_eq_integral`) ; surplus de la dérivée par rapport au jumeau
  en ligne de mêmes multiplicités (`packetTowerDerivative_surplus`).
* §3 Au changement de signe de la densité, le terme de ligne du canal des Tours ne s'annule pas (partie réelle
  `(−1)^k·T·e^{t/2}/(1/4 + T²)`) : la condition « dépôt en ligne » du canal des paquets n'est pas celle de la densité.

Aucune hypothèse posée, aucun `sorry`.
-/
open Real RHV3Lean

namespace RHV6Fresh
namespace OffCarrier
variable (C : OffCarrier)

noncomputable def lineTerm (x : ℝ) : ℂ := (x : ℂ) ^ C.linePoint / C.linePoint

theorem linePoint_ne_zero : C.linePoint ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [C.linePoint_im, Complex.zero_im] at this
  exact C.zero.2.ne' this

theorem line_sub_shift_ne_zero : C.linePoint - (C.radialShift : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [Complex.sub_im, C.linePoint_im, Complex.ofReal_im, Complex.zero_im, sub_zero] at this
  exact C.zero.2.ne' this

theorem line_add_shift_ne_zero : C.linePoint + (C.radialShift : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [Complex.add_im, C.linePoint_im, Complex.ofReal_im, Complex.zero_im, add_zero] at this
  exact C.zero.2.ne' this

/-- Surplus de la paire dans le canal des Tours. -/
theorem pair_zeroTerm_surplus {x : ℝ} (hx : 0 < x) :
    zeroTerm C.zero x + zeroTerm (mirrorMember C.zero) x - 2 * C.lineTerm x =
      2 * (Complex.cosh ((C.radialShift : ℂ) * Real.log x) - 1) * C.lineTerm x +
        ((C.radialShift : ℂ) / C.linePoint) * (zeroTerm C.zero x - zeroTerm (mirrorMember C.zero) x) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  unfold zeroTerm lineTerm
  rw [C.zeroPoint_eq_line_sub_shift, C.mirrorPoint_eq_line_add_shift, Complex.cpow_sub _ _ hx0,
    Complex.cpow_add _ _ hx0]
  have hd : (x : ℂ) ^ (C.radialShift : ℂ) = Complex.exp (C.radialShift * Real.log x) := by
    rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le, mul_comm]
  rw [hd]
  simp only [Complex.cosh]
  have hL := C.linePoint_ne_zero
  have hm := C.line_sub_shift_ne_zero
  have hp := C.line_add_shift_ne_zero
  have he : Complex.exp (C.radialShift * Real.log x) ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.exp_neg]
  field_simp
  ring

theorem mirror_multiplicity_eq :
    zetaZeroMultiplicity (zeroPoint (mirrorMember C.zero)) = zetaZeroMultiplicity (zeroPoint C.zero) := by
  rw [zeroPoint_mirrorMember]
  exact zetaZeroMultiplicity_mirrorPoint C.zero.1.2

/-- Dérivée du terme conjugué : conjugué de la dérivée. -/
theorem explicit_conj_term_derivative (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * nontrivialZeroResidueTerm y (conjIndex z))
      (-(zetaZeroMultiplicity (zeroPoint z) : ℂ) * (starRingEnd ℂ) (zeroTerm z x)) x := by
  have h := (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x (explicit_term_derivative z hx))
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [Function.comp, Complex.conjCLE_apply]
    rw [residueTerm_conjIndex z hy, map_mul, Complex.conj_ofReal]
    rfl
  · simp

/-- La dérivée des quatre membres du paquet (cas (a)). -/
noncomputable def packetTowerDerivative (x : ℝ) : ℂ :=
  -(zetaZeroMultiplicity (zeroPoint C.zero) : ℂ) *
    (zeroTerm C.zero x + (starRingEnd ℂ) (zeroTerm C.zero x) +
      zeroTerm (mirrorMember C.zero) x + (starRingEnd ℂ) (zeroTerm (mirrorMember C.zero) x))

theorem channelPrimitive_packet_hasDerivAt (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) {x : ℝ}
    (hx : 1 < x) :
    HasDerivAt (channelPrimitive C.packet) (C.packetTowerDerivative x) x := by
  have hx0 : 0 < x := by linarith
  have h1 := explicit_term_derivative C.zero hx0
  have h2 := explicit_term_derivative (mirrorMember C.zero) hx0
  have h3 := explicit_conj_term_derivative C.zero hx0
  have h4 := explicit_conj_term_derivative (mirrorMember C.zero) hx0
  have hsum := ((h1.add h2).add h3).add h4
  refine (hsum.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioi_mem_nhds hx] with y hy
    unfold channelPrimitive
    rw [C.packet_channel_four_of_mirror h hy]
    simp only [memberIndex, Pi.add_apply]
    ring
  · unfold packetTowerDerivative
    rw [C.mirror_multiplicity_eq]
    ring

theorem packetTowerDerivative_continuousAt {x : ℝ} (hx : 0 < x) :
    ContinuousAt C.packetTowerDerivative x := by
  unfold packetTowerDerivative
  have h1 := (zeroTerm_hasDerivAt C.zero hx).continuousAt
  have h2 := (zeroTerm_hasDerivAt (mirrorMember C.zero) hx).continuousAt
  have hc : Continuous (starRingEnd ℂ) := Complex.continuous_conj
  exact continuousAt_const.mul (((h1.add (hc.continuousAt.comp h1)).add h2).add (hc.continuousAt.comp h2))

/-- **Le pas local du paquet est l'intégrale de la dérivée de Tour sur le pas** (`N ≥ 2`). -/
theorem localPacket_eq_integral (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) {N : ℕ} (hN : 2 ≤ N) :
    localPacket C.packet N = ∫ x in (N : ℝ)..(N : ℝ) + 1, C.packetTowerDerivative x := by
  unfold localPacket stepAt
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact C.channelPrimitive_packet_hasDerivAt h (by linarith [hx.1])
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact (C.packetTowerDerivative_continuousAt (by linarith [hx.1])).continuousWithinAt

/-- Dérivée de Tour du jumeau en ligne (mêmes multiplicités, deux membres en ligne). -/
noncomputable def lineTwinDerivative (x : ℝ) : ℂ :=
  -(zetaZeroMultiplicity (zeroPoint C.zero) : ℂ) * (2 * C.lineTerm x + 2 * (starRingEnd ℂ) (C.lineTerm x))

/-- **Surplus de la dérivée du paquet** : facteur hyperbolique sur la ligne plus déformation, et leurs conjugués. -/
theorem packetTowerDerivative_surplus {x : ℝ} (hx : 0 < x) :
    C.packetTowerDerivative x - C.lineTwinDerivative x =
      -(zetaZeroMultiplicity (zeroPoint C.zero) : ℂ) *
        (2 * (Complex.cosh ((C.radialShift : ℂ) * Real.log x) - 1) * C.lineTerm x +
            ((C.radialShift : ℂ) / C.linePoint) * (zeroTerm C.zero x - zeroTerm (mirrorMember C.zero) x) +
          (starRingEnd ℂ) (2 * (Complex.cosh ((C.radialShift : ℂ) * Real.log x) - 1) * C.lineTerm x +
            ((C.radialShift : ℂ) / C.linePoint) * (zeroTerm C.zero x - zeroTerm (mirrorMember C.zero) x))) := by
  rw [← C.pair_zeroTerm_surplus hx]
  unfold packetTowerDerivative lineTwinDerivative
  simp only [map_sub, map_add, map_mul, map_ofNat]
  ring

/-- Partie réelle du terme de ligne en `x = e^t` : `e^{t/2}((1/2)cos(Tt) + T sin(Tt))/(1/4 + T²)`. -/
theorem lineTerm_exp_re (t : ℝ) :
    (C.lineTerm (Real.exp t)).re =
      Real.exp (t / 2) * ((1 / 2) * Real.cos (rZeroHeight C.zero.1 * t) +
        rZeroHeight C.zero.1 * Real.sin (rZeroHeight C.zero.1 * t)) /
        (1 / 4 + rZeroHeight C.zero.1 ^ 2) := by
  have hx : 0 < Real.exp t := Real.exp_pos t
  have hx0 : ((Real.exp t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  unfold lineTerm
  rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le, Real.log_exp, Complex.div_re,
    Complex.normSq_apply, C.linePoint_re, C.linePoint_im]
  have e1 : ((t : ℝ) : ℂ) * C.linePoint = ((t / 2 : ℝ) : ℂ) + ((rZeroHeight C.zero.1 * t : ℝ) : ℂ) * Complex.I := by
    unfold linePoint; push_cast; ring
  rw [e1, Complex.exp_add]
  simp only [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_re, Complex.exp_ofReal_im]
  have hd : (1 / 2 : ℝ) * (1 / 2) + rZeroHeight C.zero.1 * rZeroHeight C.zero.1 = 1 / 4 + rZeroHeight C.zero.1 ^ 2 := by
    ring
  rw [hd]
  ring

/-- **Au changement de signe de la densité, le terme de ligne du canal des Tours ne s'annule pas** :
sa partie réelle vaut `(−1)^k · T · e^{t/2}/(1/4 + T²)`. -/
theorem lineTerm_re_at_signChange (k : ℤ) :
    (C.lineTerm (Real.exp (densitySignChangeLog (rZeroHeight C.zero.1) k))).re =
      (-1) ^ k * rZeroHeight C.zero.1 * Real.exp (densitySignChangeLog (rZeroHeight C.zero.1) k / 2) /
        (1 / 4 + rZeroHeight C.zero.1 ^ 2) := by
  rw [C.lineTerm_exp_re]
  have hT : rZeroHeight C.zero.1 ≠ 0 := C.zero.2.ne'
  have e : rZeroHeight C.zero.1 * densitySignChangeLog (rZeroHeight C.zero.1) k = k * Real.pi + Real.pi / 2 := by
    unfold densitySignChangeLog; field_simp; ring
  rw [e, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, Real.sin_int_mul_pi, Real.cos_int_mul_pi]
  ring

theorem lineTerm_re_at_signChange_ne_zero (k : ℤ) :
    (C.lineTerm (Real.exp (densitySignChangeLog (rZeroHeight C.zero.1) k))).re ≠ 0 := by
  rw [C.lineTerm_re_at_signChange]
  have hT : 0 < rZeroHeight C.zero.1 := C.zero.2
  have h1 : ((-1 : ℝ) ^ k) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have h2 : 0 < 1 / 4 + rZeroHeight C.zero.1 ^ 2 := by positivity
  exact div_ne_zero (mul_ne_zero (mul_ne_zero h1 hT.ne') (Real.exp_pos _).ne') h2.ne'

/-- **Le surplus hyperbolique du canal des Tours ne s'annule pas au changement de signe de la densité**
(partie réelle du terme en ligne) : la condition « dépôt en ligne » du canal des paquets n'est pas celle de la densité. -/
theorem hyperbolic_surplus_re_at_signChange_ne_zero (k : ℤ) :
    (2 * (Real.cosh (C.radialShift * densitySignChangeLog (rZeroHeight C.zero.1) k) - 1) : ℝ) *
      (C.lineTerm (Real.exp (densitySignChangeLog (rZeroHeight C.zero.1) k))).re ≠ 0 := by
  have hk : 0 < densitySignChangeLog (rZeroHeight C.zero.1) k ∨ densitySignChangeLog (rZeroHeight C.zero.1) k < 0 ∨
      densitySignChangeLog (rZeroHeight C.zero.1) k = 0 := by
    rcases lt_trichotomy 0 (densitySignChangeLog (rZeroHeight C.zero.1) k) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h.symm)
    · exact Or.inr (Or.inl h)
  have hne : densitySignChangeLog (rZeroHeight C.zero.1) k ≠ 0 := by
    unfold densitySignChangeLog
    intro h0
    have hT : rZeroHeight C.zero.1 ≠ 0 := C.zero.2.ne'
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · have : (k : ℝ) * Real.pi = -(Real.pi / 2) := by linarith
      have hk2 : (2 * k + 1 : ℝ) * Real.pi = 0 := by linarith
      have : (2 * k + 1 : ℝ) = 0 := (mul_eq_zero.mp hk2).resolve_right Real.pi_pos.ne'
      have : (2 * k + 1 : ℤ) = 0 := by exact_mod_cast this
      omega
    · exact hT h0
  have hcosh : 1 < Real.cosh (C.radialShift * densitySignChangeLog (rZeroHeight C.zero.1) k) :=
    Real.one_lt_cosh.mpr (mul_ne_zero C.radialShift_pos.ne' hne)
  exact mul_ne_zero (by linarith) (C.lineTerm_re_at_signChange_ne_zero k)

end OffCarrier
end RHV6Fresh

#print axioms RHV6Fresh.OffCarrier.pair_zeroTerm_surplus
#print axioms RHV6Fresh.OffCarrier.channelPrimitive_packet_hasDerivAt
#print axioms RHV6Fresh.OffCarrier.localPacket_eq_integral
#print axioms RHV6Fresh.OffCarrier.packetTowerDerivative_surplus
#print axioms RHV6Fresh.OffCarrier.lineTerm_re_at_signChange
#print axioms RHV6Fresh.OffCarrier.hyperbolic_surplus_re_at_signChange_ne_zero
