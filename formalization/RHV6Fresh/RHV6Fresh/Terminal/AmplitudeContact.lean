/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PrimeCapsContactsBridge
import RHV6Fresh.Terminal.RemainderRegime
import RHV6Fresh.Terminal.TripletReadings

/-!
# Contact porteur d'amplitude (module isolé, 2026-11-02)

Réponse à la question de l'auteur du 2026-11-02 : les énoncés « le OFF ne viole aucune contrainte » reposaient sur des
projections (comptage de Riemann–von Mangoldt, disparition des écarts logarithmiques) ou sur une définition de contact
qui ne contient que la fréquence et la longueur (`contactLog_step_blind_to_radial` : le pas de contact ne lit que `T`).
Ce module donne au contact la troisième coordonnée qui manquait : **l'amplitude du zéro à son propre contact**, lue sur
l'axe réel, et consigne ce que cette amplitude impose et ce qu'elle n'impose pas.

## 1. Le contact porteur d'amplitude
* `contactAmplitude z k = ‖terme lissé de z en C_k‖ = w_z · C_k^β` (`contactAmplitude_eq`, instance de `norm_residueTerm_eq`) ;
  `amplitudeContact z k = (log C_k, contactAmplitude z k)`.
* **Le pas d'amplitude lit la position radiale** : `contactAmplitude_ratio : A_{k+1}/A_k = exp(β·π/T)` ;
  `contactAmplitude_ratio_eq_iff` : à même `T`, même pas d'amplitude ⟺ même `β` ;
  `radial_from_amplitude_step : β = T·log(A_{k+1}/A_k)/π`. Contraste exact avec `contactLog_step_blind_to_radial`.

## 2. Les dépôts aux vrais points de rencontre (axe réel, vrais écarts)
* `meetingDeposit z I = terme lissé de z en p_{n+1}` ; `meetingDeposit_norm : ‖·‖ = w_z · p_{n+1}^β`.
* `meeting_demand_eq_tsum_deposits` : la demande lue en `p_{n+1}` est la somme (signée, absolument convergente) de tous
  les dépôts ; `gap_demand_eq_deposits` : la demande de l'écart `[p_n, p_{n+1}]` est la différence des deux sommes.
* `crowdAmplitudeSum I` = somme des **modules** des contributions de la foule ; `norm_crowdSum_le_amplitudeSum` : la somme
  signée de la foule est majorée par la somme des amplitudes. La somme des amplitudes n'est pas la demande.

## 3. Ce que l'amplitude dit d'une paire OFF
* `OffCarrier.mirror_deposit_ratio` : au point de rencontre, `‖dépôt du miroir‖ / ‖dépôt du OFF‖ = (w'/w) · p_{n+1}^{1−2β}` ;
  `OffCarrier.mirror_amplitude_ratio_tendsto` : ce rapport tend vers `+∞` avec l'abscisse (exposant `1 − 2β > 0`).
  L'amplitude de la paire croît avec le point de rencontre : c'est la phrase de l'auteur, compilée.

## 4. Ce que le contact porteur d'amplitude ne donne pas
* `AmplitudeContactRigidity` (but nommé, jamais posé) : tout pas d'amplitude vaut `exp(π/(2T))` ;
  `amplitudeContactRigidity_iff_riemannHypothesis` : ce but EST RH. Lire `β = 1/2` sur les amplitudes des contacts,
  c'est RH ; aucune identité de ce module ne fixe l'amplitude d'un contact depuis les premiers seuls.

Aucun `sorry`, aucun axiome, aucune hypothèse nouvelle. Non ajouté à `RHV6Fresh.lean`.
-/

namespace RHV6Fresh

open RHV3Lean Filter

/-! ## 1. Le contact porteur d'amplitude -/

/-- Amplitude du membre `z` à son contact `C_k` : module du terme lissé que `z` dépose au contact. -/
noncomputable def contactAmplitude (z : TrueZero) (k : ℤ) : ℝ :=
  ‖nontrivialZeroResidueTerm (contactMinusAt z k) (memberIndex z)‖

/-- Contact porteur d'amplitude : position logarithmique et amplitude. -/
noncomputable def amplitudeContact (z : TrueZero) (k : ℤ) : ℝ × ℝ :=
  (contactLog z k, contactAmplitude z k)

theorem amplitudeContact_fst (z : TrueZero) (k : ℤ) : (amplitudeContact z k).1 = contactLog z k := rfl
theorem amplitudeContact_snd (z : TrueZero) (k : ℤ) : (amplitudeContact z k).2 = contactAmplitude z k := rfl

theorem indexWeight_memberIndex_pos (z : TrueZero) : 0 < indexWeight (memberIndex z) := by
  unfold indexWeight
  apply div_pos _ (indexDenominator_pos _)
  exact_mod_cast zetaZeroMultiplicity_pos (zeroPoint_isNontrivial z).1

/-- `A_{z,k} = w_z · C_k^β` : l'amplitude au contact porte la position radiale. -/
theorem contactAmplitude_eq (z : TrueZero) (k : ℤ) :
    contactAmplitude z k = indexWeight (memberIndex z) * contactMinusAt z k ^ rZeroRadialPosition z.1 := by
  unfold contactAmplitude
  rw [norm_residueTerm_eq _ (contactMinusAt_positive z k)]
  rfl

theorem contactAmplitude_pos (z : TrueZero) (k : ℤ) : 0 < contactAmplitude z k := by
  rw [contactAmplitude_eq]
  exact mul_pos (indexWeight_memberIndex_pos z) (Real.rpow_pos_of_pos (contactMinusAt_positive z k) _)

/-- Deux contacts consécutifs : `log C_{k+1} − log C_k = π/T` (même fait que `contactLog_step`). -/
theorem log_contactMinusAt_succ_sub (z : TrueZero) (k : ℤ) :
    Real.log (contactMinusAt z (k + 1)) - Real.log (contactMinusAt z k) = Real.pi / rZeroHeight z.1 :=
  contactAt_consecutive_logWidth z k

/-- **Le pas d'amplitude lit `β`** : `A_{k+1}/A_k = exp(β·π/T)`. -/
theorem contactAmplitude_ratio (z : TrueZero) (k : ℤ) :
    contactAmplitude z (k + 1) / contactAmplitude z k =
      Real.exp (rZeroRadialPosition z.1 * (Real.pi / rZeroHeight z.1)) := by
  rw [contactAmplitude_eq, contactAmplitude_eq]
  have hw := indexWeight_memberIndex_pos z
  have hk := contactMinusAt_positive z k
  have hk1 := contactMinusAt_positive z (k + 1)
  rw [mul_div_mul_left _ _ hw.ne', ← Real.div_rpow hk1.le hk.le, Real.rpow_def_of_pos (div_pos hk1 hk),
    Real.log_div hk1.ne' hk.ne', log_contactMinusAt_succ_sub, mul_comm]

/-- Contraste avec `contactLog_step_blind_to_radial` : à même `T`, même pas d'amplitude ⟺ même `β`. -/
theorem contactAmplitude_ratio_eq_iff {z w : TrueZero} (hT : rZeroHeight z.1 = rZeroHeight w.1) (k j : ℤ) :
    contactAmplitude z (k + 1) / contactAmplitude z k = contactAmplitude w (j + 1) / contactAmplitude w j ↔
      rZeroRadialPosition z.1 = rZeroRadialPosition w.1 := by
  rw [contactAmplitude_ratio, contactAmplitude_ratio, Real.exp_eq_exp, hT]
  have hc : Real.pi / rZeroHeight w.1 ≠ 0 := (div_pos Real.pi_pos w.2).ne'
  exact mul_left_inj' hc

/-- **La position radiale se lit sur le pas d'amplitude** : `β = T·log(A_{k+1}/A_k)/π`. -/
theorem radial_from_amplitude_step (z : TrueZero) (k : ℤ) :
    rZeroRadialPosition z.1 =
      rZeroHeight z.1 * Real.log (contactAmplitude z (k + 1) / contactAmplitude z k) / Real.pi := by
  rw [contactAmplitude_ratio, Real.log_exp]
  have hT : rZeroHeight z.1 ≠ 0 := z.2.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp

/-! ## 2. Les dépôts aux vrais points de rencontre -/

/-- Dépôt du membre `z` au point de rencontre de l'écart `I` (le premier suivant `p_{n+1}`), avec sa vraie amplitude. -/
noncomputable def meetingDeposit (z : TrueZero) (I : PrimeGapInterval) : ℂ :=
  nontrivialZeroResidueTerm (meetingPoint I) (memberIndex z)

/-- `‖dépôt‖ = w_z · p_{n+1}^β`. -/
theorem meetingDeposit_norm (z : TrueZero) (I : PrimeGapInterval) :
    ‖meetingDeposit z I‖ = indexWeight (memberIndex z) * meetingPoint I ^ rZeroRadialPosition z.1 := by
  unfold meetingDeposit
  rw [norm_residueTerm_eq _ (by linarith [one_lt_meetingPoint I])]
  rfl

/-- **Identité à la rencontre** : la demande lue en `p_{n+1}` est la somme signée de tous les dépôts (compilé :
`smoothedRemainder_eq_tsum_residueTerm`). -/
theorem meeting_demand_eq_tsum_deposits (I : PrimeGapInterval) :
    smoothedRemainder (meetingPoint I) = ∑' σ : ExplicitIndex, nontrivialZeroResidueTerm (meetingPoint I) σ :=
  smoothedRemainder_eq_tsum_residueTerm (one_lt_meetingPoint I)

/-- **Identité de l'écart** : la demande de `[p_n, p_{n+1}]` est la différence des deux sommes de dépôts. -/
theorem gap_demand_eq_deposits (I : PrimeGapInterval) :
    localArithmeticTarget I =
      (∑' σ : ExplicitIndex, nontrivialZeroResidueTerm I.upper σ) -
        ∑' σ : ExplicitIndex, nontrivialZeroResidueTerm I.lower σ := by
  unfold localArithmeticTarget
  rw [smoothedRemainder_eq_tsum_residueTerm I.one_lt_upper, smoothedRemainder_eq_tsum_residueTerm I.one_lt_lower]

/-- Somme des **modules** (amplitudes) des contributions de la foule à l'écart : objet distinct de la somme signée. -/
noncomputable def crowdAmplitudeSum (I : PrimeGapInterval) : ℝ :=
  ∑ σ ∈ (precedingIndices_finite I.threshold).toFinset,
    ‖nontrivialZeroResidueTerm I.upper σ - nontrivialZeroResidueTerm I.lower σ‖

/-- La somme signée de la foule est majorée par la somme des amplitudes ; elle ne lui est pas égale en général. -/
theorem norm_crowdSum_le_amplitudeSum (I : PrimeGapInterval) : ‖gapCrowdSum I‖ ≤ crowdAmplitudeSum I := by
  rw [crowdSum_eq_finite_sum]
  exact norm_sum_le _ _

/-- Chaque module de contribution est encadré par les deux amplitudes aux bornes (`w·p_n^β`, `w·p_{n+1}^β`). -/
theorem norm_contribution_le_amplitudes (z : TrueZero) (I : PrimeGapInterval) :
    ‖nontrivialZeroResidueTerm I.upper (memberIndex z) - nontrivialZeroResidueTerm I.lower (memberIndex z)‖ ≤
      indexWeight (memberIndex z) * I.upper ^ rZeroRadialPosition z.1 +
        indexWeight (memberIndex z) * I.lower ^ rZeroRadialPosition z.1 := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_residueTerm_eq _ (by linarith [I.one_lt_upper]), norm_residueTerm_eq _ (by linarith [I.one_lt_lower])]
  exact le_of_eq rfl

/-! ## 3. Ce que l'amplitude dit d'une paire OFF -/

namespace OffCarrier

variable (C : OffCarrier)

theorem one_sub_two_radial_pos : 0 < 1 - 2 * rZeroRadialPosition C.zero.1 := by
  have := C.zero_low; linarith

/-- **Rapport des dépôts de la paire à la rencontre** : `‖miroir‖/‖OFF‖ = (w'/w) · p_{n+1}^{1−2β}`. -/
theorem mirror_deposit_ratio (I : PrimeGapInterval) :
    ‖meetingDeposit (mirrorMember C.zero) I‖ / ‖meetingDeposit C.zero I‖ =
      (indexWeight (memberIndex (mirrorMember C.zero)) / indexWeight (memberIndex C.zero)) *
        meetingPoint I ^ (1 - 2 * rZeroRadialPosition C.zero.1) := by
  rw [meetingDeposit_norm, meetingDeposit_norm, mirrorMember_radial]
  have hp : 0 < meetingPoint I := by linarith [one_lt_meetingPoint I]
  have h : 1 - 2 * rZeroRadialPosition C.zero.1 = (1 - rZeroRadialPosition C.zero.1) - rZeroRadialPosition C.zero.1 := by
    ring
  rw [h, Real.rpow_sub hp (1 - rZeroRadialPosition C.zero.1) (rZeroRadialPosition C.zero.1), div_mul_div_comm]

/-- **L'amplitude de la paire croît avec l'abscisse** : le rapport miroir/OFF tend vers `+∞` (exposant `1 − 2β > 0`). -/
theorem mirror_amplitude_ratio_tendsto :
    Tendsto (fun x : ℝ => ‖nontrivialZeroResidueTerm x (memberIndex (mirrorMember C.zero))‖ /
      ‖nontrivialZeroResidueTerm x (memberIndex C.zero)‖) atTop atTop := by
  have hw := indexWeight_memberIndex_pos C.zero
  have hw' := indexWeight_memberIndex_pos (mirrorMember C.zero)
  have hc : 0 < indexWeight (memberIndex (mirrorMember C.zero)) / indexWeight (memberIndex C.zero) := div_pos hw' hw
  have hmain : Tendsto (fun x : ℝ => (indexWeight (memberIndex (mirrorMember C.zero)) / indexWeight (memberIndex C.zero)) *
      x ^ (1 - 2 * rZeroRadialPosition C.zero.1)) atTop atTop :=
    (tendsto_rpow_atTop C.one_sub_two_radial_pos).const_mul_atTop hc
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [norm_residueTerm_eq _ hx, norm_residueTerm_eq _ hx]
  change _ = indexWeight (memberIndex (mirrorMember C.zero)) * x ^ rZeroRadialPosition (mirrorMember C.zero).1 /
    (indexWeight (memberIndex C.zero) * x ^ rZeroRadialPosition C.zero.1)
  rw [mirrorMember_radial]
  have h : 1 - 2 * rZeroRadialPosition C.zero.1 = (1 - rZeroRadialPosition C.zero.1) - rZeroRadialPosition C.zero.1 := by
    ring
  rw [h, Real.rpow_sub hx (1 - rZeroRadialPosition C.zero.1) (rZeroRadialPosition C.zero.1), div_mul_div_comm]

end OffCarrier

/-! ## 4. Ce que le contact porteur d'amplitude ne donne pas -/

/-- **But nommé, jamais posé** : tout pas d'amplitude vaut `exp(π/(2T))` (amplitude de la ligne). -/
def AmplitudeContactRigidity : Prop :=
  ∀ (z : TrueZero) (k : ℤ),
    contactAmplitude z (k + 1) / contactAmplitude z k = Real.exp (Real.pi / (2 * rZeroHeight z.1))

/-- **Lire `β = 1/2` sur les amplitudes des contacts, c'est RH.** -/
theorem amplitudeContactRigidity_iff_riemannHypothesis : AmplitudeContactRigidity ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_noLowerSide
    intro z hβ
    have hz := h z 0
    rw [contactAmplitude_ratio, Real.exp_eq_exp] at hz
    have hT : rZeroHeight z.1 ≠ 0 := z.2.ne'
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    have : rZeroRadialPosition z.1 = 1 / 2 := by
      field_simp at hz
      linarith
    linarith
  · intro hRH z k
    rw [contactAmplitude_ratio, thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1]
    congr 1
    ring

end RHV6Fresh

#print axioms RHV6Fresh.contactAmplitude_ratio
#print axioms RHV6Fresh.radial_from_amplitude_step
#print axioms RHV6Fresh.OffCarrier.mirror_amplitude_ratio_tendsto
#print axioms RHV6Fresh.amplitudeContactRigidity_iff_riemannHypothesis
