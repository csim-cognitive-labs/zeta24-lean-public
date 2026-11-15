/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MirrorDegeneracy
import RHV6Fresh.Terminal.EnergyIdentity
import RHV6Fresh.Terminal.VerticalEnergyPush
import RHV6Fresh.Terminal.HorizontalExclusion
import RHV6Fresh.Terminal.EventHeightProgression
import RHV6Fresh.Grammar.ExpectedMinimum

/-!
# RHV6Fresh — la force verticale : hypothèses F1a–F4 compilées (2026-09-29)

Plan : `experiments/PLAN_VERTICAL_FORCE_HYPOTHESES_20260929.md`. Chaque hypothèse reçoit un verdict.

* **F1a** THÉORÈME : la résultante horizontale `δ(z) + δ(z*)` (`δ = β − 1/2`) est nulle pour TOUT
  zéro, hors ligne compris ; elle ne sépare donc rien.
* **F1b** THÉORÈME : la tension `δ(z)² + δ(z*)² = 2δ²` est nulle ssi `β = 1/2`.
* **F1c** THÉORÈME : `V(z,z*) = log‖ρ*‖ − log‖ρ‖ = 0` ssi `β = 1/2` ; pour `β < 1/2`,
  `V(z,z*) > 0` (même hauteur, `‖ρ*‖² = (1−β)² + T² > β² + T²`).
* **F1d** THÉORÈME : verticalité pure sur un passage ON.
* **F2a** THÉORÈME : (phase, norme) déterminent `ρ` ; injectivité polaire.
* **F2b** THÉORÈME d'entrelacement, qui RÉFUTE la non-insertion : hors ligne, le miroir s'insère
  dans chaque cellule de `z` (`C_{k−1}(z) < C_k(z*) < C_k(z)`).
* **F2c** THÉORÈME : `p_min(z*) ≠ p_min(z)` hors ligne — l'exclusion vit dans le pointeur premier.
* **F4** THÉORÈME de composition : F1a, F1b, F2b, F2c vrais ET `‖zeroTerm z q‖ < ‖zeroTerm z* q‖`
  pour tout `q ≥ 2`, c'est-à-dire que la poussée verticale échoue à tout premier sur le passage
  miroir. Donc ces éléments n'impliquent pas la force verticale.

Non compilé : `PVerticalForce` et `verticalForce_iff_riemannHypothesis` — la seule direction
prouvable de l'existant est `verticalDominates_of_verticalEnergyPush`, pas une équivalence ;
rien n'est inventé.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## F1 — forces horizontales et verticales de la paire miroir -/

/-- **F1a** : la force horizontale nette de la paire `(z, z*)` est nulle pour tout zéro. -/
theorem mirror_net_horizontal_force_zero (z : TrueZero) :
    (rZeroRadialPosition z.1 - 1 / 2) + (rZeroRadialPosition (mirrorMember z).1 - 1 / 2) = 0 := by
  rw [mirrorMember_radial]; ring

/-- **F1b** : la tension horizontale vaut `2(β − 1/2)²` et s'annule ssi `β = 1/2`. -/
theorem mirror_horizontal_tension_eq_zero_iff (z : TrueZero) :
    (rZeroRadialPosition z.1 - 1 / 2) ^ 2 + (rZeroRadialPosition (mirrorMember z).1 - 1 / 2) ^ 2 =
        2 * (rZeroRadialPosition z.1 - 1 / 2) ^ 2 ∧
      ((rZeroRadialPosition z.1 - 1 / 2) ^ 2 +
          (rZeroRadialPosition (mirrorMember z).1 - 1 / 2) ^ 2 = 0 ↔
        rZeroRadialPosition z.1 = 1 / 2) := by
  have h : (rZeroRadialPosition z.1 - 1 / 2) ^ 2 +
      (rZeroRadialPosition (mirrorMember z).1 - 1 / 2) ^ 2 =
        2 * (rZeroRadialPosition z.1 - 1 / 2) ^ 2 := by
    rw [mirrorMember_radial]; ring
  refine ⟨h, ?_⟩
  rw [h]
  constructor
  · intro h0
    have : (rZeroRadialPosition z.1 - 1 / 2) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    linarith
  · intro h0; rw [h0]; norm_num

/-- **F1c** : `V(z, z*) = 0` ssi `β = 1/2`. -/
theorem mirror_verticalEnergy_eq_zero_iff (z : TrueZero) :
    verticalEnergy z (mirrorMember z) = 0 ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro h
    unfold verticalEnergy at h
    have hN : ‖zeroPoint (mirrorMember z)‖ = ‖zeroPoint z‖ :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr (zeroPoint_norm_pos _))
        (Set.mem_Ioi.mpr (zeroPoint_norm_pos _)) (by linarith)
    have h2 : ‖zeroPoint (mirrorMember z)‖ ^ 2 = ‖zeroPoint z‖ ^ 2 := by rw [hN]
    rw [zeroPoint_norm_sq, zeroPoint_norm_sq, mirrorMember_radial, mirrorMember_ordinate] at h2
    nlinarith
  · intro h
    unfold verticalEnergy
    rw [zeroPoint_norm_eq_of_eq z (mirrorMember z)
      (by rw [mirrorMember_radial, h]; norm_num) (mirrorMember_ordinate z).symm, sub_self]

/-- **F1c, signe** : pour `β < 1/2`, `‖ρ‖ < ‖ρ*‖` donc `0 < V(z, z*)`. -/
theorem mirror_verticalEnergy_pos {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    0 < verticalEnergy z (mirrorMember z) := by
  have hlt : ‖zeroPoint (mirrorMember z)‖ ^ 2 > ‖zeroPoint z‖ ^ 2 := by
    rw [zeroPoint_norm_sq, zeroPoint_norm_sq, mirrorMember_radial, mirrorMember_ordinate]
    have := thm_zeroRadialPosition_positive z.1
    nlinarith
  have hlt' : ‖zeroPoint z‖ < ‖zeroPoint (mirrorMember z)‖ :=
    lt_of_pow_lt_pow_left₀ 2 (zeroPoint_norm_pos _).le hlt
  have hl := Real.log_lt_log (zeroPoint_norm_pos z) hlt'
  unfold verticalEnergy
  linarith

/-- **F1d** : sur un passage dont les deux membres sont ON, `T_e < T_l`, l'énergie horizontale est
nulle en tout `q`, l'énergie verticale est strictement positive, et la poussée verticale
`‖zeroTerm l q‖ < ‖zeroTerm e q‖` vaut pour tout `q > 0`. Verticalité pure. -/
theorem onLine_passage_pure_vertical (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOnE : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hOnL : rZeroRadialPosition p.zLaterMember = 1 / 2) :
    rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
      (∀ q : ℝ, horizontalEnergy ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ q = 0) ∧
      0 < verticalEnergy ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ ∧
      (∀ q : ℝ, 0 < q →
        ‖zeroTerm (⟨p.zLaterMember, hL⟩ : TrueZero) q‖ <
          ‖zeroTerm (⟨p.zEarlierMember, hE⟩ : TrueZero) q‖) := by
  have hT := passage_height_lt_of_onLine p hOnE hOnL
  refine ⟨hT, ?_, ?_, ?_⟩
  · intro q
    unfold horizontalEnergy
    show (rZeroRadialPosition p.zLaterMember - rZeroRadialPosition p.zEarlierMember) *
      Real.log q = 0
    rw [hOnE, hOnL]; ring
  · unfold verticalEnergy
    have := zeroPoint_norm_lt_of_height_lt (⟨p.zEarlierMember, hE⟩ : TrueZero)
      ⟨p.zLaterMember, hL⟩ (by
        show rZeroRadialPosition p.zEarlierMember = rZeroRadialPosition p.zLaterMember
        rw [hOnE, hOnL]) hT
    have := Real.log_lt_log (zeroPoint_norm_pos (⟨p.zEarlierMember, hE⟩ : TrueZero)) this
    linarith
  · intro q hq
    exact onLine_amplitude_lt_of_height_lt (⟨p.zEarlierMember, hE⟩ : TrueZero)
      ⟨p.zLaterMember, hL⟩ hOnE hOnL hT hq

/-! ## F2 — la Tour enveloppe son zéro -/

/-- **F2a** : deux vrais zéros de même norme de support et de même phase de Tour ont la même
position radiale et la même hauteur (donc sont le même zéro). -/
theorem zeroPoint_eq_of_phase_norm_eq (z w : TrueZero)
    (hN : ‖zeroPoint z‖ = ‖zeroPoint w‖)
    (hφ : (towerMotionOf z).phase = (towerMotionOf w).phase) :
    rZeroRadialPosition z.1 = rZeroRadialPosition w.1 ∧ rZeroHeight z.1 = rZeroHeight w.1 ∧
      z = w := by
  have hz : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hw : 0 < rZeroRadialPosition w.1 := thm_zeroRadialPosition_positive w.1
  have htz : 0 < rZeroHeight z.1 := z.2
  have htw : 0 < rZeroHeight w.1 := w.2
  rw [towerMotion_phase, towerMotion_phase] at hφ
  have hr : rZeroHeight z.1 / rZeroRadialPosition z.1 = rZeroHeight w.1 / rZeroRadialPosition w.1 :=
    Real.arctan_injective hφ
  have hN2 : ‖zeroPoint z‖ ^ 2 = ‖zeroPoint w‖ ^ 2 := by rw [hN]
  rw [zeroPoint_norm_sq, zeroPoint_norm_sq] at hN2
  rw [div_eq_div_iff hz.ne' hw.ne'] at hr
  -- Tz*bw = Tw*bz  et bz²+Tz² = bw²+Tw²
  have hb : rZeroRadialPosition z.1 = rZeroRadialPosition w.1 := by
    have h1 : rZeroRadialPosition z.1 ^ 2 * (rZeroRadialPosition w.1 ^ 2 + rZeroHeight w.1 ^ 2) =
        rZeroRadialPosition w.1 ^ 2 * (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) := by
      have : (rZeroHeight z.1 * rZeroRadialPosition w.1) ^ 2 =
          (rZeroHeight w.1 * rZeroRadialPosition z.1) ^ 2 := by rw [hr]
      nlinarith
    have h2 : rZeroRadialPosition z.1 ^ 2 = rZeroRadialPosition w.1 ^ 2 := by
      rw [← hN2] at h1
      have hpos : 0 < rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2 := by positivity
      have : (rZeroRadialPosition z.1 ^ 2 - rZeroRadialPosition w.1 ^ 2) *
          (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    nlinarith
  have hT : rZeroHeight z.1 = rZeroHeight w.1 := by
    rw [hb] at hr
    exact mul_right_cancel₀ hw.ne' hr
  refine ⟨hb, hT, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Complex.ext
  · exact hb
  · exact hT

/-- **F2a, contraposée** : deux zéros distincts ont des couples (phase, norme) distincts. -/
theorem phase_norm_ne_of_ne {z w : TrueZero} (h : z ≠ w) :
    ‖zeroPoint z‖ ≠ ‖zeroPoint w‖ ∨ (towerMotionOf z).phase ≠ (towerMotionOf w).phase := by
  by_contra hc
  push Not at hc
  exact h (zeroPoint_eq_of_phase_norm_eq z w hc.1 hc.2).2.2

/-- **F2b** : hors ligne (`β < 1/2`), le miroir s'insère STRICTEMENT dans chaque cellule de `z` :
`C_{k−1}(z) < C_k(z*) < C_k(z)`. La « non-insertion dans les cellules » est RÉFUTÉE. -/
theorem mirror_contacts_interlace {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) (k : ℤ) :
    contactMinusAt z (k - 1) < contactMinusAt (mirrorMember z) k ∧
      contactMinusAt (mirrorMember z) k < contactMinusAt z k := by
  have hb := thm_zeroRadialPosition_positive z.1
  have hT : 0 < rZeroHeight z.1 := z.2
  have hlt : rZeroHeight z.1 / (1 - rZeroRadialPosition z.1) <
      rZeroHeight z.1 / rZeroRadialPosition z.1 :=
    div_lt_div_of_pos_left hT hb (by linarith)
  have hφ : Real.arctan (rZeroHeight z.1 / (1 - rZeroRadialPosition z.1)) <
      Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) := Real.arctan_strictMono hlt
  have hφ0 := Real.arctan_lt_pi_div_two (rZeroHeight z.1 / rZeroRadialPosition z.1)
  have hφ1 : 0 < Real.arctan (rZeroHeight z.1 / (1 - rZeroRadialPosition z.1)) :=
    Real.arctan_pos.mpr (div_pos hT (by linarith))
  have hpi := Real.pi_pos
  rw [mirrorMember_contactMinusAt]
  unfold contactMinusAt
  rw [towerMotion_incidence, towerMotion_incidence, towerMotion_phase]
  constructor
  · apply Real.exp_lt_exp.mpr
    apply div_lt_div_of_pos_right _ hT
    push_cast
    nlinarith
  · apply Real.exp_lt_exp.mpr
    apply div_lt_div_of_pos_right _ hT
    linarith

/-- **F2c** : hors ligne, `p_min(z*) ≠ p_min(z)` (injectivité du pointeur `pmin`). -/
theorem mirror_expectedMinimum_ne {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    expectedMinimumPrime (mirrorMember z) ≠ expectedMinimumPrime z := fun h =>
  mirrorMember_ne hβ (expectedMinimumPrime_injective h)

/-! ## F4 — composition : tous les éléments tiennent, la force verticale échoue -/

/-- **F4** : pour `z` hors ligne (`β < 1/2`) et `T ≥ 2`, la force horizontale nette est nulle (F1a),
la tension est strictement positive (F1b), le miroir s'insère dans les cellules (F2b), les pointeurs
premiers diffèrent (F2c), ET la poussée verticale échoue à tout `q ≥ 2` :
`‖zeroTerm z q‖ < ‖zeroTerm z* q‖`. Donc F1∧F2 n'impliquent pas la force verticale. -/
theorem offMirror_all_elements_hold_and_vertical_force_fails {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2) (hT2 : 2 ≤ rZeroHeight z.1) :
    ((rZeroRadialPosition z.1 - 1 / 2) + (rZeroRadialPosition (mirrorMember z).1 - 1 / 2) = 0) ∧
      (0 < (rZeroRadialPosition z.1 - 1 / 2) ^ 2 +
        (rZeroRadialPosition (mirrorMember z).1 - 1 / 2) ^ 2) ∧
      (∀ k : ℤ, contactMinusAt z (k - 1) < contactMinusAt (mirrorMember z) k ∧
        contactMinusAt (mirrorMember z) k < contactMinusAt z k) ∧
      expectedMinimumPrime (mirrorMember z) ≠ expectedMinimumPrime z ∧
      (∀ q : ℝ, 2 ≤ q → ‖zeroTerm z q‖ < ‖zeroTerm (mirrorMember z) q‖) := by
  refine ⟨mirror_net_horizontal_force_zero z, ?_, fun k => mirror_contacts_interlace hβ k,
    mirror_expectedMinimum_ne hβ, ?_⟩
  · have h := (mirror_horizontal_tension_eq_zero_iff z).1
    rw [h]
    have : rZeroRadialPosition z.1 - 1 / 2 ≠ 0 := by linarith
    positivity
  · intro q hq
    exact sameHeight_amplitude_inverts_at_primes z (mirrorMember z)
      (mirrorMember_ordinate z).symm hT2 (mirror_radial_gt hβ) hq

#print axioms mirror_net_horizontal_force_zero
#print axioms mirror_horizontal_tension_eq_zero_iff
#print axioms mirror_verticalEnergy_eq_zero_iff
#print axioms mirror_verticalEnergy_pos
#print axioms onLine_passage_pure_vertical
#print axioms zeroPoint_eq_of_phase_norm_eq
#print axioms phase_norm_ne_of_ne
#print axioms mirror_contacts_interlace
#print axioms mirror_expectedMinimum_ne
#print axioms offMirror_all_elements_hold_and_vertical_force_fails

end RHV6Fresh
