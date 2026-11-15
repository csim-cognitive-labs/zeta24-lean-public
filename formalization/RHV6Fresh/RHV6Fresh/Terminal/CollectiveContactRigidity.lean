/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GapContactRegimes
import RHV6Fresh.Terminal.SameGapsAudit
import RHV6Fresh.Terminal.SynchronizationAudit
import RHV6Fresh.Terminal.LogGapsTheorem

/-!
# Rigidité collective des contacts (module isolé, mission R9, 2026-11-01)

Mission R9 de l'auteur (§19.30) : les contacts sont les observables principales ; les fréquences et les foules sont les
structures d'encadrement ; la reconstruction de chaque écart est collective (tous les zéros). Ce module formalise, à
partir des théorèmes compilés existants et sans aucune hypothèse nouvelle :

## 1. Observables de contact (les deux coordonnées se lisent sur les contacts)
* `contactLog z k = log C_k = (arctan(T/β) + kπ)/T` ; `contactLog_step : u_{k+1} − u_k = π/T` ;
  `height_from_contactLog : T = π/(u_{k+1} − u_k)` ; `contactLog_tangent : tan(T u_k) = T/β` ;
  `radial_from_contactLog : β = T / tan(T u_k)` (instances de `height_from_contacts`, `radial_from_contact`, T2/T3).
* `contactLog_branch_bounds` : la branche de l'inversion tangentielle est `T u_k − kπ = arctan(T/β) ∈ ]0, π/2[`.
* `coordinates_from_two_contacts` : deux contacts consécutifs rendent `(T, β)` ; `coordinates_eq_of_contacts_eq` :
  mêmes contacts ⟹ mêmes coordonnées. **Les contacts ne se réduisent jamais à leur espacement.**
* Dérive de fréquence contre dérive radiale : `contactLog_step_blind_to_radial` (le pas ne lit que `T`),
  `contactLog_shift_of_same_height` (à même `T`, `β` déplace tous les contacts de `(arctan(T/β') − arctan(T/β))/T`),
  `contactLog_shift_ne_zero_of_radial_ne` (déplacement non nul), `OffCarrier.mirror_density_dominates` (l'amplitude
  `x^{β−1}` du zéro OFF est dominée par celle `x^{−β}` de son miroir en tout `x > 1`).

## 2. Phase de contact dans un écart
* `contactPhase z q = T log q − arctan(T/β)` ; entrée/sortie : `contactPhase_exit_sub_entry : θ_out − θ_in = T ℓ` ;
  `contactPhase_at_contact : θ(C_k) = kπ` ; monotonie `contactPhase_lt_iff`.
* `contactsCrossed z I = ⌊Π(p_{n+1})⌋ − ⌊Π(p_n)⌋` : nombre de contacts effectivement traversés ;
  `mem_crossed_iff` (`k` traversé ⟺ `a < u_k ≤ b`), `contactsCrossed_eq_card`, `contactsCrossed_nonneg`,
  `contactsCrossed_le_one_of_mem_crowd` (un membre de la foule traverse au plus un contact),
  `one_le_contactsCrossed_of_several`.

## 3. Foule et queue : décomposition exacte de la demande (canal lissé compilé, C126)
* `PrimeGapInterval.threshold I = π/ℓ` ; `crowd I = upperWindow (threshold I)` ; `mem_crowd_iff_height_le`.
* `gapCrowdSum I` (contributions de hauteur absolue `≤ π/ℓ`, conjugués compris, **somme finie** `crowdSum_eq_finite_sum`) ;
  `gapTailSum I` (tous les zéros au-dessus du seuil, jamais supprimée).
* `crowd_tail_decomposition : localArithmeticTarget I = gapCrowdSum I + gapTailSum I` (identité, toute position radiale) ;
  `collective_residual_eq_tail : D − S_foule = S_queue` ; `collective_residual_bound : ‖D − S_foule‖ ≤ budget(π/ℓ)·(p_n + p_{n+1})`
  (borne d'erreur indépendante du résidu observé, exposant 1, sans RH).
* `OffCarrier.crowdSum_split_zero` : le terme du zéro OFF est isolé dans la part de foule ; `OffCarrier.mirror_mem_crowd_iff`.
* `crowd_alone_never_accomplishes_demand` (F8) : la foule seule n'égale la demande sur aucun voisinage d'une rencontre.

## 4. Transitions entre écarts
* `crowd_transition_nested`, `crowd_card_transition`, `mem_crowd_sdiff_iff` (la différence de deux foules est faite des
  points de hauteur entre les deux seuils), `crowd_eq_filter_of_window` : **les foules sont des fenêtres de lecture d'un
  ensemble spectral fixe** ; une variation de foule n'est pas l'apparition d'un zéro.

## 5. Ce que la rigidité des contacts de la foule vaudrait
* `every_zero_in_some_crowd` : par le théorème `logGapsVanish_holds` du port PNT (importé ; le conflit d'import PNT/Zeta23
  signalé en R9 est résolu par réexport, directive R11 du 2026-11-01), tout zéro
  est dans la foule d'au moins un écart.
* `CrowdRadialRigidity` (but nommé, jamais posé) : tout membre de toute foule est en ligne ;
  `crowdRadialRigidity_iff_riemannHypothesis` (sans hypothèse) : ce but EST RH. Aucun énoncé intermédiaire du
  module ne lit `β` autrement que par les identités (contacts ⟺ coordonnées, `D = foule + queue` pour toute `β`).

Aucun `sorry`, aucun axiome, aucune hypothèse nouvelle. Non ajouté à `RHV6Fresh.lean`. Le premier but non résolu est
affiché par la sonde hors build `experiments/E402_CollectiveContacts/ProbeCollectiveContactRigidity.lean`.
-/

namespace RHV6Fresh

open RHV3Lean Filter

/-! ## 1. Observables de contact -/

/-- Contact logarithmique `u_{z,k} = log C_k`. -/
noncomputable def contactLog (z : TrueZero) (k : ℤ) : ℝ := Real.log (contactMinusAt z k)

/-- `u_{z,k} = (arctan(T/β) + kπ)/T`. -/
theorem contactLog_eq (z : TrueZero) (k : ℤ) :
    contactLog z k =
      (Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) + (k : ℝ) * Real.pi) / rZeroHeight z.1 := by
  unfold contactLog
  rw [log_contact_eq, towerMotion_phase]
  ring

/-- `u_{k+1} − u_k = π/T`. -/
theorem contactLog_step (z : TrueZero) (k : ℤ) :
    contactLog z (k + 1) - contactLog z k = Real.pi / rZeroHeight z.1 := by
  unfold contactLog
  rw [contact_log_step, towerPitch]

/-- **La fréquence se lit sur deux contacts consécutifs** : `T = π/(u_{k+1} − u_k)`. -/
theorem height_from_contactLog (z : TrueZero) (k : ℤ) :
    rZeroHeight z.1 = Real.pi / (contactLog z (k + 1) - contactLog z k) := by
  rw [contactLog_step]
  have hT : 0 < rZeroHeight z.1 := z.2
  field_simp

/-- **Formule tangentielle au contact** : `tan(T u_k) = T/β`. -/
theorem contactLog_tangent (z : TrueZero) (k : ℤ) :
    Real.tan (rZeroHeight z.1 * contactLog z k) = rZeroHeight z.1 / rZeroRadialPosition z.1 :=
  contactAt_tangent_minus z k

/-- **La position radiale se lit sur un contact** : `β = T / tan(T u_k)`. -/
theorem radial_from_contactLog (z : TrueZero) (k : ℤ) :
    rZeroRadialPosition z.1 = rZeroHeight z.1 / Real.tan (rZeroHeight z.1 * contactLog z k) :=
  radial_from_contact z k

/-- Branche de l'inversion : `T u_k − kπ = arctan(T/β)`. -/
theorem contactLog_branch (z : TrueZero) (k : ℤ) :
    rZeroHeight z.1 * contactLog z k - (k : ℝ) * Real.pi = (towerMotionOf z).phase := by
  unfold contactLog
  rw [height_mul_log_contact]
  ring

/-- **Validité de l'inversion tangentielle** : la phase réduite est dans `]0, π/2[`, branche principale de `arctan`. -/
theorem contactLog_branch_bounds (z : TrueZero) (k : ℤ) :
    0 < rZeroHeight z.1 * contactLog z k - (k : ℝ) * Real.pi ∧
      rZeroHeight z.1 * contactLog z k - (k : ℝ) * Real.pi < Real.pi / 2 := by
  rw [contactLog_branch]
  exact ⟨towerMotion_phase_pos z, towerMotion_phase_lt_pi_div_two z⟩

/-- **Les contacts rendent les deux coordonnées du zéro.** -/
theorem coordinates_from_two_contacts (z : TrueZero) (k : ℤ) :
    rZeroHeight z.1 = Real.pi / (contactLog z (k + 1) - contactLog z k) ∧
      rZeroRadialPosition z.1 = (Real.pi / (contactLog z (k + 1) - contactLog z k)) /
        Real.tan ((Real.pi / (contactLog z (k + 1) - contactLog z k)) * contactLog z k) := by
  refine ⟨height_from_contactLog z k, ?_⟩
  rw [← height_from_contactLog z k]
  exact radial_from_contactLog z k

/-- **Mêmes contacts ⟹ mêmes coordonnées** : deux contacts consécutifs égaux donnent `T` et `β` égaux. -/
theorem coordinates_eq_of_contacts_eq {z w : TrueZero} (k : ℤ)
    (h0 : contactLog z k = contactLog w k) (h1 : contactLog z (k + 1) = contactLog w (k + 1)) :
    rZeroHeight z.1 = rZeroHeight w.1 ∧ rZeroRadialPosition z.1 = rZeroRadialPosition w.1 := by
  have hT : rZeroHeight z.1 = rZeroHeight w.1 := by
    rw [height_from_contactLog z k, height_from_contactLog w k, h0, h1]
  refine ⟨hT, ?_⟩
  rw [radial_from_contactLog z k, radial_from_contactLog w k, hT, h0]

/-- **Dérive de fréquence seule** : le pas des contacts ne lit que la hauteur. -/
theorem contactLog_step_blind_to_radial {z w : TrueZero} (hT : rZeroHeight z.1 = rZeroHeight w.1) (k : ℤ) :
    contactLog z (k + 1) - contactLog z k = contactLog w (k + 1) - contactLog w k := by
  rw [contactLog_step, contactLog_step, hT]

/-- **Dérive radiale seule** : à même hauteur, la position radiale déplace tous les contacts de la même quantité. -/
theorem contactLog_shift_of_same_height {z w : TrueZero} (hT : rZeroHeight z.1 = rZeroHeight w.1) (k : ℤ) :
    contactLog w k - contactLog z k =
      (Real.arctan (rZeroHeight z.1 / rZeroRadialPosition w.1) -
        Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1)) / rZeroHeight z.1 := by
  rw [contactLog_eq, contactLog_eq, ← hT, div_sub_div_same]
  congr 1
  ring

/-- Le déplacement radial des contacts n'est jamais nul : même pas, contacts différents. -/
theorem contactLog_shift_ne_zero_of_radial_ne {z w : TrueZero} (hT : rZeroHeight z.1 = rZeroHeight w.1)
    (hβ : rZeroRadialPosition z.1 ≠ rZeroRadialPosition w.1) (k : ℤ) :
    contactLog w k - contactLog z k ≠ 0 := by
  rw [contactLog_shift_of_same_height hT k]
  have hT0 : 0 < rZeroHeight z.1 := z.2
  have hbz : rZeroRadialPosition z.1 ≠ 0 := (thm_zeroRadialPosition_positive z.1).ne'
  have hbw : rZeroRadialPosition w.1 ≠ 0 := (thm_zeroRadialPosition_positive w.1).ne'
  refine div_ne_zero ?_ hT0.ne'
  intro h
  have harg := Real.arctan_strictMono.injective (sub_eq_zero.mp h)
  rw [div_eq_div_iff hbw hbz] at harg
  exact hβ (mul_left_cancel₀ hT0.ne' harg)

/-- **Dérive radiale et amplitude** : en tout `x > 1`, la densité `x^{β−1}` du zéro OFF est strictement dominée par
celle `x^{−β}` de son miroir. -/
theorem OffCarrier.mirror_density_dominates (C : OffCarrier) {x : ℝ} (hx : 1 < x) :
    ‖(x : ℂ) ^ (zeroPoint C.zero - 1)‖ < ‖(x : ℂ) ^ (zeroPoint (mirrorMember C.zero) - 1)‖ := by
  rw [density_norm _ (by linarith), density_norm _ (by linarith)]
  have hβ := C.zero_low
  have h1 : (zeroPoint C.zero).re = rZeroRadialPosition C.zero.1 := rfl
  have h2 : (zeroPoint (mirrorMember C.zero)).re = 1 - rZeroRadialPosition C.zero.1 := mirrorMember_radial C.zero
  rw [h1, h2]
  exact Real.rpow_lt_rpow_of_exponent_lt hx (by linarith)

/-! ## 2. Phase de contact dans un écart -/

/-- Phase de contact de la Tour `z` au point `q` : `θ = T log q − arctan(T/β)`. -/
noncomputable def contactPhase (z : TrueZero) (q : ℝ) : ℝ :=
  rZeroHeight z.1 * Real.log q - (towerMotionOf z).phase

theorem contactPhase_eq_pi_mul_position (z : TrueZero) (q : ℝ) :
    contactPhase z q = Real.pi * towerPosition z q := by
  unfold contactPhase towerPosition
  field_simp

/-- **Phase de sortie moins phase d'entrée** `= T ℓ`. -/
theorem contactPhase_exit_sub_entry (z : TrueZero) (I : PrimeGapInterval) :
    contactPhase z I.upper - contactPhase z I.lower = rZeroHeight z.1 * I.logLength := by
  unfold contactPhase PrimeGapInterval.logLength PrimeGapInterval.a PrimeGapInterval.b
  ring

/-- La phase vaut `kπ` au contact `C_k`. -/
theorem contactPhase_at_contact (z : TrueZero) (k : ℤ) :
    contactPhase z (contactMinusAt z k) = (k : ℝ) * Real.pi := by
  unfold contactPhase
  rw [height_mul_log_contact]
  ring

theorem contactPhase_lt_iff (z : TrueZero) {q₁ q₂ : ℝ} (h1 : 0 < q₁) (h2 : 0 < q₂) :
    contactPhase z q₁ < contactPhase z q₂ ↔ q₁ < q₂ := by
  have hT : 0 < rZeroHeight z.1 := z.2
  unfold contactPhase
  rw [sub_lt_sub_iff_right, ← Real.log_lt_log_iff h1 h2]
  exact ⟨fun h => lt_of_mul_lt_mul_left h hT.le, fun h => mul_lt_mul_of_pos_left h hT⟩

theorem towerPosition_lt_iff (z : TrueZero) {q₁ q₂ : ℝ} (h1 : 0 < q₁) (h2 : 0 < q₂) :
    towerPosition z q₁ < towerPosition z q₂ ↔ q₁ < q₂ := by
  refine Iff.trans ?_ (contactPhase_lt_iff z h1 h2)
  simp only [contactPhase_eq_pi_mul_position]
  exact ⟨fun hh => mul_lt_mul_of_pos_left hh Real.pi_pos, fun hh => lt_of_mul_lt_mul_left hh Real.pi_pos.le⟩

theorem towerPosition_le_iff (z : TrueZero) {q₁ q₂ : ℝ} (h1 : 0 < q₁) (h2 : 0 < q₂) :
    towerPosition z q₁ ≤ towerPosition z q₂ ↔ q₁ ≤ q₂ := by
  rw [← not_lt, ← not_lt, towerPosition_lt_iff z h2 h1]

/-- **Nombre de contacts effectivement traversés** par l'écart : `⌊Π(p_{n+1})⌋ − ⌊Π(p_n)⌋`. -/
noncomputable def contactsCrossed (z : TrueZero) (I : PrimeGapInterval) : ℤ :=
  ⌊towerPosition z I.upper⌋ - ⌊towerPosition z I.lower⌋

/-- Le contact `C_k` est dans l'écart (`a < u_k ≤ b`) ⟺ `Π(p_n) < k ≤ Π(p_{n+1})`. -/
theorem contact_in_gap_iff (z : TrueZero) (I : PrimeGapInterval) (k : ℤ) :
    (I.a < contactLog z k ∧ contactLog z k ≤ I.b) ↔
      (towerPosition z I.lower < k ∧ (k : ℝ) ≤ towerPosition z I.upper) := by
  have hC := contactMinusAt_positive z k
  have hl : 0 < I.lower := by linarith [I.one_lt_lower]
  have hu : 0 < I.upper := by linarith [I.one_lt_upper]
  unfold contactLog PrimeGapInterval.a PrimeGapInterval.b
  rw [← towerPosition_contactMinusAt z k, towerPosition_lt_iff z hl hC, towerPosition_le_iff z hC hu,
    Real.log_lt_log_iff hl hC, Real.log_le_log_iff hC hu]

/-- Les indices traversés sont exactement `Ioc ⌊Π(p_n)⌋ ⌊Π(p_{n+1})⌋`. -/
theorem mem_crossed_iff (z : TrueZero) (I : PrimeGapInterval) (k : ℤ) :
    k ∈ Finset.Ioc ⌊towerPosition z I.lower⌋ ⌊towerPosition z I.upper⌋ ↔
      (I.a < contactLog z k ∧ contactLog z k ≤ I.b) := by
  rw [Finset.mem_Ioc, Int.floor_lt, Int.le_floor, contact_in_gap_iff]

theorem towerPosition_lower_le_upper (z : TrueZero) (I : PrimeGapInterval) :
    towerPosition z I.lower ≤ towerPosition z I.upper :=
  (towerPosition_le_iff z (by linarith [I.one_lt_lower]) (by linarith [I.one_lt_upper])).mpr
    I.lower_lt_upper.le

theorem contactsCrossed_eq_card (z : TrueZero) (I : PrimeGapInterval) :
    contactsCrossed z I = ((Finset.Ioc ⌊towerPosition z I.lower⌋ ⌊towerPosition z I.upper⌋).card : ℤ) := by
  unfold contactsCrossed
  rw [Int.card_Ioc, Int.toNat_of_nonneg (sub_nonneg.mpr (Int.floor_mono (towerPosition_lower_le_upper z I)))]

theorem contactsCrossed_nonneg (z : TrueZero) (I : PrimeGapInterval) : 0 ≤ contactsCrossed z I :=
  sub_nonneg.mpr (Int.floor_mono (towerPosition_lower_le_upper z I))

/-- Sous un pas (`ℓ ≤ pas`), au plus un contact est traversé. -/
theorem contactsCrossed_le_one_of_pitch (z : TrueZero) (I : PrimeGapInterval) (h : I.logLength ≤ towerPitch z) :
    contactsCrossed z I ≤ 1 := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hp : 0 < towerPitch z := by unfold towerPitch; exact div_pos Real.pi_pos hT
  have hcell := cells_read_eq_length_over_pitch z I
  have hle : I.logLength / towerPitch z ≤ 1 := (div_le_one hp).mpr h
  have h1 : towerPosition z I.upper ≤ towerPosition z I.lower + 1 := by linarith
  have h2 := Int.floor_mono h1
  rw [Int.floor_add_one] at h2
  unfold contactsCrossed
  omega

/-- **Un membre de la foule traverse au plus un contact dans l'écart.** -/
theorem contactsCrossed_le_one_of_mem_crowd (z : TrueZero) (I : PrimeGapInterval) (h : zeroPoint z ∈ crowd I) :
    contactsCrossed z I ≤ 1 :=
  contactsCrossed_le_one_of_pitch z I ((mem_crowd_iff_pitch I z).mp h)

/-- Au-delà d'un pas, au moins un contact est traversé. -/
theorem one_le_contactsCrossed_of_several (z : TrueZero) (I : PrimeGapInterval) (h : SeveralContacts z I) :
    1 ≤ contactsCrossed z I := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hp : 0 < towerPitch z := by unfold towerPitch; exact div_pos Real.pi_pos hT
  have hcell := cells_read_eq_length_over_pitch z I
  have hgt : 1 < I.logLength / towerPitch z := (one_lt_div hp).mpr h
  have h1 : towerPosition z I.lower + 1 ≤ towerPosition z I.upper := by linarith
  have h2 := Int.floor_mono h1
  rw [Int.floor_add_one] at h2
  unfold contactsCrossed
  omega

/-! ## 3. Foule et queue : décomposition exacte de la demande -/

/-- Seuil de fréquence de l'écart : `T_seuil = π/ℓ`. -/
noncomputable def PrimeGapInterval.threshold (I : PrimeGapInterval) : ℝ := Real.pi / I.logLength

theorem PrimeGapInterval.threshold_pos (I : PrimeGapInterval) : 0 < I.threshold :=
  div_pos Real.pi_pos I.logLength_pos

theorem crowd_eq_upperWindow_threshold (I : PrimeGapInterval) : crowd I = upperWindow I.threshold := rfl

/-- Membre de la foule ⟺ hauteur `≤ π/ℓ`. -/
theorem mem_crowd_iff_height_le (I : PrimeGapInterval) (w : TrueZero) :
    zeroPoint w ∈ crowd I ↔ rZeroHeight w.1 ≤ I.threshold := by
  rw [mem_crowd_iff_pitch]
  have hT : 0 < rZeroHeight w.1 := w.2
  unfold towerPitch PrimeGapInterval.threshold
  rw [le_div_iff₀ hT, le_div_iff₀ I.logLength_pos, mul_comm]

/-- Membre de la foule ⟺ indice compté dans la part basse du reste (non « suivant » au seuil). -/
theorem mem_crowd_iff_not_following (I : PrimeGapInterval) (w : TrueZero) :
    zeroPoint w ∈ crowd I ↔ ¬ I.threshold < |(zeroPoint w).im| := by
  have hT : 0 < rZeroHeight w.1 := w.2
  rw [mem_crowd_iff_height_le, not_lt, zeroPoint_im, abs_of_pos hT]

/-- **Part de foule** de la demande : contributions des zéros de hauteur absolue `≤ π/ℓ` (conjugués compris). -/
noncomputable def gapCrowdSum (I : PrimeGapInterval) : ℂ :=
  precedingSum I.threshold I.upper - precedingSum I.threshold I.lower

/-- **Part de queue** : tous les zéros au-dessus du seuil ; jamais supprimée. -/
noncomputable def gapTailSum (I : PrimeGapInterval) : ℂ :=
  followingSum I.threshold I.upper - followingSum I.threshold I.lower

/-- **Décomposition exacte** `D_n = S_foule + S_queue`, pour toute position radiale (C126 + identité du reste). -/
theorem crowd_tail_decomposition (I : PrimeGapInterval) :
    localArithmeticTarget I = gapCrowdSum I + gapTailSum I := by
  unfold localArithmeticTarget gapCrowdSum gapTailSum
  rw [remainder_eq_preceding_add_following I.threshold I.one_lt_upper,
    remainder_eq_preceding_add_following I.threshold I.one_lt_lower]
  ring

/-- **Le résidu collectif après la foule est exactement la queue.** -/
theorem collective_residual_eq_tail (I : PrimeGapInterval) :
    localArithmeticTarget I - gapCrowdSum I = gapTailSum I := by
  rw [crowd_tail_decomposition]; ring

theorem tailSum_eq_localHeightResidual (I : PrimeGapInterval) :
    gapTailSum I = localHeightResidual I.threshold I :=
  (localHeightResidual_eq_tail_increment I.threshold I).symm

/-- **Borne d'erreur indépendante du résidu observé** : `‖D − S_foule‖ ≤ budget(π/ℓ)·(p_n + p_{n+1})`, sans RH. -/
theorem collective_residual_bound (I : PrimeGapInterval) :
    ‖localArithmeticTarget I - gapCrowdSum I‖ ≤ followingBudget I.threshold * (I.lower + I.upper) := by
  rw [collective_residual_eq_tail, tailSum_eq_localHeightResidual]
  exact localHeightResidual_bound I.threshold I

/-- **La part de foule est une somme FINIE**, phases et signes conservés. -/
theorem crowdSum_eq_finite_sum (I : PrimeGapInterval) :
    gapCrowdSum I = ∑ σ ∈ (precedingIndices_finite I.threshold).toFinset,
      (nontrivialZeroResidueTerm I.upper σ - nontrivialZeroResidueTerm I.lower σ) := by
  unfold gapCrowdSum
  rw [precedingSum_eq_finite_sum, precedingSum_eq_finite_sum, Finset.sum_sub_distrib]

/-- L'indice d'un membre est dans la famille finie de la foule ⟺ le membre est dans la foule. -/
theorem memberIndex_mem_crowdIndices_iff (I : PrimeGapInterval) (w : TrueZero) :
    memberIndex w ∈ (precedingIndices_finite I.threshold).toFinset ↔ zeroPoint w ∈ crowd I := by
  rw [Set.Finite.mem_toFinset, mem_crowd_iff_not_following]
  exact Iff.rfl

namespace OffCarrier

variable (C : OffCarrier)

/-- **Le terme du zéro OFF est isolé dans la part de foule** de tout écart dont la foule le contient. -/
theorem crowdSum_split_zero (I : PrimeGapInterval) (h : zeroPoint C.zero ∈ crowd I) :
    gapCrowdSum I =
      (nontrivialZeroResidueTerm I.upper (memberIndex C.zero) -
        nontrivialZeroResidueTerm I.lower (memberIndex C.zero)) +
      ∑ σ ∈ (precedingIndices_finite I.threshold).toFinset.erase (memberIndex C.zero),
        (nontrivialZeroResidueTerm I.upper σ - nontrivialZeroResidueTerm I.lower σ) := by
  have hz : rZeroHeight C.zero.1 ≤ I.threshold := (mem_crowd_iff_height_le I C.zero).mp h
  unfold gapCrowdSum
  rw [precedingSum_split_member I.threshold I.upper C.zero hz,
    precedingSum_split_member I.threshold I.lower C.zero hz, Finset.sum_sub_distrib]
  ring

/-- Le miroir est dans les foules des mêmes écarts que le zéro OFF. -/
theorem mirror_mem_crowd_iff (I : PrimeGapInterval) :
    zeroPoint (mirrorMember C.zero) ∈ crowd I ↔ zeroPoint C.zero ∈ crowd I := by
  rw [mem_crowd_iff_height_le, mem_crowd_iff_height_le, mirrorMember_ordinate]

end OffCarrier

/-- **F8, instance foule** : la foule seule (famille finie) n'égale le reste lissé sur aucun voisinage de la rencontre ;
la queue est obligatoire. -/
theorem crowd_alone_never_accomplishes_demand (n : ℕ) :
    ¬ (∀ᶠ x in nhds (meetingPoint ⟨n⟩), smoothedRemainder x =
      ∑ ρ ∈ (precedingIndices_finite (PrimeGapInterval.threshold ⟨n⟩)).toFinset,
        nontrivialZeroResidueTerm x ρ) :=
  no_finite_family_at_any_meeting n _

/-! ## 4. Transitions entre écarts -/

theorem threshold_antitone {I J : PrimeGapInterval} (h : I.logLength ≤ J.logLength) :
    J.threshold ≤ I.threshold :=
  div_le_div_of_nonneg_left Real.pi_pos.le I.logLength_pos h

/-- Deux foules sont toujours emboîtées. -/
theorem crowd_transition_nested (I J : PrimeGapInterval) : crowd I ⊆ crowd J ∨ crowd J ⊆ crowd I :=
  (le_total I.logLength J.logLength).elim (fun h => Or.inr (crowd_mono h)) (fun h => Or.inl (crowd_mono h))

/-- Transition de composition : la grande foule = la petite + la différence. -/
theorem crowd_card_transition {I J : PrimeGapInterval} (h : I.logLength ≤ J.logLength) :
    (crowd I).card = (crowd J).card + (crowd I \ crowd J).card := by
  have := Finset.card_sdiff_add_card_eq_card (crowd_mono h)
  omega

/-- **La différence de deux foules est faite des points de hauteur entre les deux seuils** : aucun zéro n'apparaît. -/
theorem mem_crowd_sdiff_iff {I J : PrimeGapInterval} (w : TrueZero) :
    zeroPoint w ∈ crowd I \ crowd J ↔ J.threshold < rZeroHeight w.1 ∧ rZeroHeight w.1 ≤ I.threshold := by
  rw [Finset.mem_sdiff, mem_crowd_iff_height_le, mem_crowd_iff_height_le, not_le, and_comm]

/-- **Les foules sont des fenêtres de lecture d'un ensemble spectral fixe.** -/
theorem crowd_eq_filter_of_window (I : PrimeGapInterval) {H : ℝ} (hH : I.threshold ≤ H) :
    crowd I = (upperWindow H).filter (fun ρ => ρ.im ≤ I.threshold) := by
  ext ρ
  rw [crowd_eq_upperWindow_threshold, Finset.mem_filter, mem_upperWindow, mem_upperWindow]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2, h3.trans hH⟩, h3⟩
  · rintro ⟨⟨h1, h2, _⟩, h3⟩
    exact ⟨h1, h2, h3⟩

/-! ## 5. Ce que la rigidité des contacts de la foule vaudrait -/

/-- **Tout zéro est dans la foule d'au moins un écart** : THÉORÈME, par `logGapsVanish_holds` (port PNT). Directive R11
(2026-11-01) : l'hypothèse de substitution `hL` de la mission R9 est supprimée, le conflit d'import PNT/Zeta23 ayant été
résolu par réexport (`PNTPort/Sobolev.lean`, `PNTPort/Fourier.lean`, `PNTPort/Mathlib/…/Log/Basic.lean`). -/
theorem every_zero_in_some_crowd (w : TrueZero) : ∃ I : PrimeGapInterval, zeroPoint w ∈ crowd I := by
  have hL : Tendsto (fun n : ℕ => Real.log (fnPrimeAtRank (n + 1)) - Real.log (fnPrimeAtRank n)) atTop (nhds 0) :=
    logGapsVanish_holds
  have hT : 0 < rZeroHeight w.1 := w.2
  have hpos : 0 < Real.pi / rZeroHeight w.1 := div_pos Real.pi_pos hT
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hL _ hpos
  refine ⟨⟨N⟩, ?_⟩
  rw [mem_crowd_iff_pitch]
  have h := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at h
  have h' := (abs_lt.mp h).2
  unfold towerPitch
  exact h'.le

/-- **But nommé, jamais posé** : rigidité radiale de la foule — tout membre de toute foule est en ligne. -/
def CrowdRadialRigidity : Prop :=
  ∀ (I : PrimeGapInterval) (w : TrueZero), zeroPoint w ∈ crowd I → rZeroRadialPosition w.1 = 1 / 2

/-- **Ce but est RH** : il n'est pas un intermédiaire. Sans hypothèse (R11 : `LogGapsVanish` est un théorème). -/
theorem crowdRadialRigidity_iff_riemannHypothesis :
    CrowdRadialRigidity ↔ RiemannHypothesis := by
  constructor
  · intro h
    by_contra hNot
    obtain ⟨C⟩ := exists_offCarrier_of_not_riemannHypothesis hNot
    obtain ⟨I, hI⟩ := every_zero_in_some_crowd C.zero
    have := h I C.zero hI
    linarith [C.zero_low]
  · intro hRH I w _
    exact thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1

#print axioms coordinates_from_two_contacts
#print axioms coordinates_eq_of_contacts_eq
#print axioms contactLog_branch_bounds
#print axioms contactLog_shift_ne_zero_of_radial_ne
#print axioms OffCarrier.mirror_density_dominates
#print axioms contactPhase_exit_sub_entry
#print axioms mem_crossed_iff
#print axioms contactsCrossed_eq_card
#print axioms contactsCrossed_le_one_of_mem_crowd
#print axioms one_le_contactsCrossed_of_several
#print axioms crowd_tail_decomposition
#print axioms collective_residual_bound
#print axioms crowdSum_eq_finite_sum
#print axioms OffCarrier.crowdSum_split_zero
#print axioms crowd_alone_never_accomplishes_demand
#print axioms crowd_card_transition
#print axioms mem_crowd_sdiff_iff
#print axioms crowd_eq_filter_of_window
#print axioms every_zero_in_some_crowd
#print axioms crowdRadialRigidity_iff_riemannHypothesis

end RHV6Fresh
