/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.DiagonalPassage
import RHV6Fresh.Terminal.TangentialInversion
import RHV6Fresh.Terminal.MirrorDegeneracy
import RHV6Fresh.Terminal.WindowFeasibility
import RHV6Fresh.Terminal.TowerWinding
import RHV6Fresh.Terminal.OnCrossReadings
import RHV6Fresh.Terminal.CountingDeficit
import RHV6Fresh.Voyage.FiberSuccessor
import RHV6Fresh.Direct.PairTowers
import RHV6Fresh.Grammar.ExpectedMinimum

/-!
# Trois hypothèses de travail sur la fibre d'arrivée : portée compilée (auteur, 2026-10-12)

(H1) unicité de la grille d'arrivée par les contacts ; (H2) transport du comptage premier vers le comptage spectral ;
(H3) contrôle de la multiplicité. Chaque énoncé ci-dessous fixe ce qui est acquis, ce qui est une caractérisation et
ce qui est faux. Aucune hypothèse n'est ajoutée, aucun énoncé ne ferme le pas de comptage `N(T_l) < N(T_e) + 2`.
-/

namespace RHV6Fresh

open RHV3Lean
open scoped InnerProductSpace ArithmeticFunction

/-- Comptage avec multiplicité de la FIBRE à la hauteur `T` : `Σ_{ρ ∈ fenêtre, Im ρ = T} m_ρ` (tous les points de
hauteur exactement `T`, miroirs compris, avec leurs multiplicités). -/
noncomputable def fiberCountWithMultiplicity (T : ℝ) : ℕ :=
  ∑ ρ ∈ (upperWindow T).filter (fun ρ => ρ.im = T), zetaZeroMultiplicity ρ

/-- **Pas de comptage d'un passage qui monte = fibre d'arrivée** (auteur, 2026-10-12) : la consécutivité interdit tout
point de hauteur strictement entre `T_e` et `T_l` ; donc `N(T_l) = N(T_e) + fibre(T_l)`, la fibre comptée avec toutes
ses multiplicités. Toute position radiale. -/
theorem passage_count_step_eq_fiber (p : TZeroPassage) (hV : VerticalPassage p) :
    upperCountWithMultiplicity (rZeroHeight p.zLaterMember) =
      upperCountWithMultiplicity (rZeroHeight p.zEarlierMember) +
        fiberCountWithMultiplicity (rZeroHeight p.zLaterMember) := by
  unfold upperCountWithMultiplicity fiberCountWithMultiplicity
  rw [← Finset.sum_filter_add_sum_filter_not (upperWindow (rZeroHeight p.zLaterMember))
    (fun ρ => ρ.im = rZeroHeight p.zLaterMember), add_comm]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext ρ
  rw [Finset.mem_filter, mem_upperWindow, mem_upperWindow]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨h1, h2, ?_⟩
    by_contra hgt
    exact consecutive_no_height_between p ⟨ρ, h1⟩ ⟨lt_of_not_ge hgt, lt_of_le_of_ne h3 h4⟩
  · rintro ⟨h1, h2, h3⟩
    have hlt : ρ.im < rZeroHeight p.zLaterMember := lt_of_le_of_lt h3 hV
    exact ⟨⟨h1, h2, hlt.le⟩, ne_of_lt hlt⟩

/-- Le pas de comptage d'un passage qui monte est strictement sous deux ⟺ la fibre d'arrivée a un comptage total un
(un seul point, simple). Caractérisation, aucun côté dérivé. -/
theorem passage_count_step_lt_two_iff (p : TZeroPassage) (hV : VerticalPassage p) :
    upperCountWithMultiplicity (rZeroHeight p.zLaterMember) <
        upperCountWithMultiplicity (rZeroHeight p.zEarlierMember) + 2 ↔
      fiberCountWithMultiplicity (rZeroHeight p.zLaterMember) < 2 := by
  rw [passage_count_step_eq_fiber p hV]; omega

/-- Un membre bas et son miroir, distincts et de même hauteur, sont deux points de la fibre : `fibre(T) ≥ 2`. -/
theorem two_le_fiberCount_of_low (z : TrueZero) (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    2 ≤ fiberCountWithMultiplicity (rZeroHeight z.1) := by
  unfold fiberCountWithMultiplicity
  have hz : zeroPoint z ∈ (upperWindow (rZeroHeight z.1)).filter
      (fun ρ => ρ.im = rZeroHeight z.1) :=
    Finset.mem_filter.mpr ⟨mem_upperWindow_iff.mpr ⟨z, rfl, le_rfl⟩, rfl⟩
  have hm : zeroPoint (mirrorMember z) ∈ (upperWindow (rZeroHeight z.1)).filter
      (fun ρ => ρ.im = rZeroHeight z.1) :=
    Finset.mem_filter.mpr ⟨mem_upperWindow_iff.mpr ⟨mirrorMember z, rfl, (mirrorMember_ordinate z).le⟩,
      mirrorMember_ordinate z⟩
  have hne : zeroPoint (mirrorMember z) ≠ zeroPoint z := fun h =>
    mirrorMember_ne hβ (Subtype.ext (Subtype.ext h))
  have hsub : ({zeroPoint (mirrorMember z), zeroPoint z} : Finset ℂ) ⊆
      (upperWindow (rZeroHeight z.1)).filter (fun ρ => ρ.im = rZeroHeight z.1) := by
    intro ρ hρ
    rcases Finset.mem_insert.mp hρ with rfl | hρ
    · exact hm
    · rw [Finset.mem_singleton.mp hρ]; exact hz
  calc 2 ≤ zetaZeroMultiplicity (zeroPoint (mirrorMember z)) + zetaZeroMultiplicity (zeroPoint z) := by
        have := one_le_multiplicity_of_mem_upperWindow (Finset.mem_filter.mp hm).1
        have := one_le_multiplicity_of_mem_upperWindow (Finset.mem_filter.mp hz).1
        omega
    _ = ∑ ρ ∈ {zeroPoint (mirrorMember z), zeroPoint z}, zetaZeroMultiplicity ρ := (Finset.sum_pair hne).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)


/-! ## 1. H1 : grilles décalées -/

/-- Facteur radial paramétrique `λ(β,T) = exp((arctan(T/β) − arctan(2T))/T)`. -/
noncomputable def paramFactor (β T : ℝ) : ℝ :=
  Real.exp ((Real.arctan (T / β) - Real.arctan (2 * T)) / T)

/-- Acquis : le facteur radial d'un membre est le facteur paramétrique de `(β, T)`. -/
theorem radialFactor_eq_arctan (z : TrueZero) :
    radialFactor z = paramFactor (rZeroRadialPosition z.1) (rZeroHeight z.1) := by
  unfold radialFactor paramFactor linePhase
  rw [towerMotion_phase]
  have : rZeroHeight z.1 / (1 / 2) = 2 * rZeroHeight z.1 := by ring
  rw [this]

/-- Acquis, toute position radiale `β ∈ ]0, 1/2]` : la fenêtre `1 ≤ λ < exp(1/(2T)/T)` et la factorisation des
contacts `windingContact β T k = lineContact T k · λ` sont satisfaites. Les obligations sur les contacts n'excluent
aucune grille décalée de cette bande. -/
theorem parameter_grid_admissible {β T : ℝ} (hT : 0 < T) (hβ : 0 < β) (hβ2 : β ≤ 1 / 2) :
    1 ≤ paramFactor β T ∧ paramFactor β T < Real.exp (1 / (2 * T) / T) ∧
      ∀ k : ℤ, windingContact β T k = lineContact T k * paramFactor β T := by
  have hge : 2 * T ≤ T / β := by
    rw [le_div_iff₀ hβ]; nlinarith
  have h1 : Real.arctan (2 * T) ≤ Real.arctan (T / β) := Real.arctan_strictMono.monotone hge
  refine ⟨?_, ?_, ?_⟩
  · unfold paramFactor
    rw [Real.one_le_exp_iff]
    exact div_nonneg (by linarith) hT.le
  · unfold paramFactor
    apply Real.exp_lt_exp.mpr
    apply div_lt_div_of_pos_right _ hT
    have h2 := phase_window_width_lt (T := 2 * T) (by linarith)
    have h3 := Real.arctan_lt_pi_div_two (T / β)
    linarith
  · intro k
    unfold windingContact lineContact linePhase paramFactor
    rw [← Real.exp_add]
    congr 1
    have : T / (1 / 2) = 2 * T := by ring
    rw [this]
    field_simp
    ring

/-- Acquis : deux membres de même hauteur ont le même facteur radial ssi ils ont la même partie réelle. -/
theorem radialFactor_eq_iff_sameHeight (z w : TrueZero) (hT : rZeroHeight z.1 = rZeroHeight w.1) :
    radialFactor z = radialFactor w ↔ rZeroRadialPosition z.1 = rZeroRadialPosition w.1 := by
  rw [radialFactor_eq_arctan, radialFactor_eq_arctan, ← hT]
  unfold paramFactor
  constructor
  · intro h
    have h1 := Real.exp_injective h
    have hTne : rZeroHeight z.1 ≠ 0 := z.2.ne'
    have h2 : Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) =
        Real.arctan (rZeroHeight z.1 / rZeroRadialPosition w.1) := by
      have := (div_left_inj' hTne).mp h1
      linarith
    have h3 := Real.arctan_injective h2
    have hz := thm_zeroRadialPosition_positive z.1
    have hw := thm_zeroRadialPosition_positive w.1
    field_simp at h3
    nlinarith
  · intro h; rw [h]

/-- Acquis (certificat de portée de H1) : deux membres `z, w` de même hauteur, tous deux sous ou sur la ligne, ont le
même pas logarithmique, des grilles reliées par la translation rigide `exp((φ_w − φ_z)/T)`, chacune égale à la grille
de ligne fois un facteur dans `[1, exp(1/(2T)/T)[` ; et une grille coïncide avec l'autre (en un indice) ⟺ mêmes parties
réelles. Deux grilles décalées admissibles existent donc ⟺ deux positions radiales distinctes de `]0, 1/2]` à la même
hauteur : c'est la rupture elle-même, pas une contradiction. -/
theorem shifted_grids_same_obligations (z w : TrueZero)
    (hT : rZeroHeight z.1 = rZeroHeight w.1)
    (hz : rZeroRadialPosition z.1 ≤ 1 / 2) (hw : rZeroRadialPosition w.1 ≤ 1 / 2) :
    (∀ k : ℤ, Real.log (contactPlusAt w k) - Real.log (contactMinusAt w k) =
        Real.log (contactPlusAt z k) - Real.log (contactMinusAt z k)) ∧
    (∀ k : ℤ, contactMinusAt w k = contactMinusAt z k *
        Real.exp (((towerMotionOf w).phase - (towerMotionOf z).phase) / rZeroHeight z.1)) ∧
    (1 ≤ radialFactor z ∧ radialFactor z < Real.exp (1 / (2 * rZeroHeight z.1) / rZeroHeight z.1)) ∧
    (1 ≤ radialFactor w ∧ radialFactor w < Real.exp (1 / (2 * rZeroHeight z.1) / rZeroHeight z.1)) ∧
    ((∃ k : ℤ, contactMinusAt z k = contactMinusAt w k) ↔
      rZeroRadialPosition z.1 = rZeroRadialPosition w.1) := by
  refine ⟨fun k => sameHeight_pitch_invariant z w hT k, fun k => sameHeight_grid_rigid_translation z w hT k,
    ?_, ?_, ?_⟩
  · have := parameter_grid_admissible z.2 (thm_zeroRadialPosition_positive z.1) hz
    rw [radialFactor_eq_arctan]; exact ⟨this.1, this.2.1⟩
  · have := parameter_grid_admissible (T := rZeroHeight w.1) w.2 (thm_zeroRadialPosition_positive w.1) hw
    rw [radialFactor_eq_arctan, ← hT] at *
    rw [← hT] at this
    exact ⟨this.1, this.2.1⟩
  · constructor
    · rintro ⟨k, hk⟩
      rw [contact_eq_line_mul_radial, contact_eq_line_mul_radial, ← hT] at hk
      have := mul_left_cancel₀ (lineContact_pos _ _).ne' hk
      exact (radialFactor_eq_iff_sameHeight z w hT).mp this
    · intro h
      refine ⟨0, ?_⟩
      rw [contact_eq_line_mul_radial, contact_eq_line_mul_radial, ← hT,
        (radialFactor_eq_iff_sameHeight z w hT).mpr h]

/-- Caractérisation : la grille d'arrivée est la grille de ligne ⟺ `β_l = 1/2`. H1 (unicité de la grille) est ainsi
équivalente au but, non une étape qui le précède. -/
theorem arrival_grid_unique_iff_onLine (l : TrueZero) :
    (∀ k : ℤ, contactMinusAt l k = lineContact (rZeroHeight l.1) k) ↔ rZeroRadialPosition l.1 = 1 / 2 := by
  constructor
  · intro h
    have h0 := h 0
    rw [contact_eq_line_mul_radial] at h0
    have : radialFactor l = 1 := by
      have hp := lineContact_pos (rZeroHeight l.1) 0
      nlinarith [h0, hp, radialFactor_pos l]
    exact (radialFactor_eq_one_iff l).mp this
  · intro h k
    rw [contact_eq_line_mul_radial, (radialFactor_eq_one_iff l).mpr h, mul_one]

/-- Certificat de restitution : la partie réelle se lit sur les contacts et le facteur radial,
`β = T · cot(arctan(2T) + kπ + T · log λ)`. Les contacts calculent la translation ; ils ne l'interdisent pas. -/
theorem inversion_restores_shift (z : TrueZero) (k : ℤ) :
    rZeroRadialPosition z.1 =
      rZeroHeight z.1 * Real.cot (Real.arctan (2 * rZeroHeight z.1) + (k : ℝ) * Real.pi +
        rZeroHeight z.1 * Real.log (radialFactor z)) := by
  rw [← inversion_radial z k]
  congr 2
  rw [contact_eq_line_mul_radial, Real.log_mul (lineContact_pos _ _).ne' (radialFactor_pos z).ne']
  unfold lineContact linePhase
  rw [Real.log_exp]
  have hTne : rZeroHeight z.1 ≠ 0 := z.2.ne'
  have : rZeroHeight z.1 / (1 / 2) = 2 * rZeroHeight z.1 := by ring
  rw [this]
  field_simp

/-! ## 2. H2 : transport du comptage -/

/-- Points de la fibre à la hauteur `T` (fenêtre supérieure fermée, `Im ρ = T`), sans multiplicité. -/
noncomputable def fiberPoints (T : ℝ) : Finset ℂ := (upperWindow T).filter (fun ρ => ρ.im = T)

/-- Acquis : sous la rupture, il existe un passage `q` parti de `z`, de même hauteur, dont l'événement premier avance
d'une unité (rang + 1, premier partagé). L'unité d'événement premier compte un MEMBRE, aveugle à la hauteur : elle
ne borne pas la fibre. -/
theorem rank_step_counts_members_not_heights (z : TrueZero) (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    ∃ s : TrueZero, ∃ hC : PZeroMembersConsecutive z.1 s.1,
      rZeroHeight s.1 = rZeroHeight z.1 ∧
      nZeroSourceIndex s.1 = nZeroSourceIndex z.1 + 1 ∧
      expectedMinimumPrime z = occurrence s ∧
      HorizontalPassage (⟨z.1, s.1, hC⟩ : TZeroPassage) ∧
      ¬ VerticalPassage (⟨z.1, s.1, hC⟩ : TZeroPassage) := by
  obtain ⟨s, hsH, hC⟩ := exists_fiberSuccessor hβ
  refine ⟨s, hC, hsH, ?_, ?_, hsH.symm, fun hv => absurd hsH.symm (ne_of_lt hv)⟩
  · exact eventIndex_succ_of_passage (⟨z.1, s.1, hC⟩ : TZeroPassage) z.2
  · exact expectedMinimumPrime_eq_laterOccurrence (⟨z.1, s.1, hC⟩ : TZeroPassage) z.2 s.2

/-- Acquis : la fibre d'un membre bas contient au moins deux POINTS (lui et son miroir, distincts). -/
theorem fiber_card_ge_two_of_low (z : TrueZero) (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    2 ≤ (fiberPoints (rZeroHeight z.1)).card := by
  have hz : zeroPoint z ∈ fiberPoints (rZeroHeight z.1) :=
    Finset.mem_filter.mpr ⟨mem_upperWindow_iff.mpr ⟨z, rfl, le_rfl⟩, rfl⟩
  have hm : zeroPoint (mirrorMember z) ∈ fiberPoints (rZeroHeight z.1) :=
    Finset.mem_filter.mpr ⟨mem_upperWindow_iff.mpr ⟨mirrorMember z, rfl, (mirrorMember_ordinate z).le⟩,
      mirrorMember_ordinate z⟩
  have hne : zeroPoint (mirrorMember z) ≠ zeroPoint z := fun h =>
    mirrorMember_ne hβ (Subtype.ext (Subtype.ext h))
  have hsub : ({zeroPoint (mirrorMember z), zeroPoint z} : Finset ℂ) ⊆ fiberPoints (rZeroHeight z.1) := by
    intro ρ hρ
    rcases Finset.mem_insert.mp hρ with rfl | hρ
    · exact hm
    · rw [Finset.mem_singleton.mp hρ]; exact hz
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hne] at this

/-- Identité : si tous les points de la fibre sont simples, le comptage avec multiplicité est le nombre de points. -/
theorem count_step_eq_fiber_card_of_simple (T : ℝ)
    (h : ∀ ρ ∈ fiberPoints T, zetaZeroMultiplicity ρ = 1) :
    fiberCountWithMultiplicity T = (fiberPoints T).card := by
  unfold fiberCountWithMultiplicity
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl h

/-! ## 3. H3 : multiplicité -/

private theorem sum_lt_two_iff {S : Finset ℂ} (f : ℂ → ℕ) (h1 : ∀ ρ ∈ S, 1 ≤ f ρ) (hne : S.Nonempty) :
    ∑ ρ ∈ S, f ρ < 2 ↔ ∃ ρ, S = {ρ} ∧ f ρ = 1 := by
  constructor
  · intro h
    obtain ⟨ρ0, h0⟩ := hne
    have hS : S = {ρ0} := by
      by_contra hn
      have : ∃ ρ1 ∈ S, ρ1 ≠ ρ0 := by
        by_contra hc
        push_neg at hc
        exact hn (Finset.eq_singleton_iff_unique_mem.mpr ⟨h0, hc⟩)
      obtain ⟨ρ1, h1m, hne1⟩ := this
      have hsub : ({ρ1, ρ0} : Finset ℂ) ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact h1m
        · rw [Finset.mem_singleton.mp hx]; exact h0
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := f) hsub (fun _ _ _ => Nat.zero_le _)
      rw [Finset.sum_pair hne1] at this
      have := h1 ρ1 h1m
      have := h1 ρ0 h0
      omega
    refine ⟨ρ0, hS, ?_⟩
    rw [hS, Finset.sum_singleton] at h
    have := h1 ρ0 h0
    omega
  · rintro ⟨ρ, hS, hf⟩
    rw [hS, Finset.sum_singleton, hf]; norm_num

/-- Caractérisation (fibre non vide) : le comptage de la fibre est sous deux ⟺ la fibre est un point simple. -/
theorem fiberCount_lt_two_iff (T : ℝ) (hne : (fiberPoints T).Nonempty) :
    fiberCountWithMultiplicity T < 2 ↔ ∃ ρ, fiberPoints T = {ρ} ∧ zetaZeroMultiplicity ρ = 1 :=
  sum_lt_two_iff zetaZeroMultiplicity
    (fun _ hρ => one_le_multiplicity_of_mem_upperWindow (Finset.mem_filter.mp hρ).1) hne

/-- Portée de H3 : si l'arrivée est EN LIGNE mais de multiplicité `≥ 2`, la fibre compte `≥ 2` et le pas de comptage
n'est pas sous deux, alors que `λ_l = 1`. Le sous-but de comptage est donc strictement plus fort que `λ_l = 1` : il
exige simplicité et unicité du point d'arrivée, non nécessaires à `RH` (aucun énoncé du dépôt n'exclut un zéro multiple
en ligne). -/
theorem onLine_double_breaks_count_step (p : TZeroPassage) (hV : VerticalPassage p)
    (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zLaterMember = 1 / 2)
    (hm : 2 ≤ zetaZeroMultiplicity (zeroPoint ⟨p.zLaterMember, hL⟩)) :
    ¬ (upperCountWithMultiplicity (rZeroHeight p.zLaterMember) <
        upperCountWithMultiplicity (rZeroHeight p.zEarlierMember) + 2) ∧
      radialFactor ⟨p.zLaterMember, hL⟩ = 1 := by
  refine ⟨?_, (radialFactor_eq_one_iff _).mpr hOn⟩
  rw [passage_count_step_lt_two_iff p hV]
  have hz : zeroPoint (⟨p.zLaterMember, hL⟩ : TrueZero) ∈ (upperWindow (rZeroHeight p.zLaterMember)).filter
      (fun ρ => ρ.im = rZeroHeight p.zLaterMember) :=
    Finset.mem_filter.mpr ⟨mem_upperWindow_iff.mpr ⟨⟨p.zLaterMember, hL⟩, rfl, le_rfl⟩, rfl⟩
  have := Finset.single_le_sum (f := zetaZeroMultiplicity) (fun _ _ => Nat.zero_le _) hz
  unfold fiberCountWithMultiplicity
  omega

/-- Caractérisation, sous `W(T_e) = 0` : le pas de comptage est sous deux ⟺ l'arrivée est en ligne, seule à sa hauteur
et simple. Le sens ⟸ n'utilise pas `W(T_e) = 0`. Aucune dérivation du côté gauche. -/
theorem count_step_iff_on_unique_simple (p : TZeroPassage) (hV : VerticalPassage p)
    (hL : 0 < rZeroHeight p.zLaterMember)
    (hWe : lowCount (rZeroHeight p.zEarlierMember) = 0) :
    upperCountWithMultiplicity (rZeroHeight p.zLaterMember) <
        upperCountWithMultiplicity (rZeroHeight p.zEarlierMember) + 2 ↔
      (rZeroRadialPosition p.zLaterMember = 1 / 2 ∧
        (∀ w : TrueZero, rZeroHeight w.1 = rZeroHeight p.zLaterMember → w = ⟨p.zLaterMember, hL⟩) ∧
        zetaZeroMultiplicity (zeroPoint ⟨p.zLaterMember, hL⟩) = 1) := by
  have hz : zeroPoint (⟨p.zLaterMember, hL⟩ : TrueZero) ∈ fiberPoints (rZeroHeight p.zLaterMember) :=
    Finset.mem_filter.mpr ⟨mem_upperWindow_iff.mpr ⟨⟨p.zLaterMember, hL⟩, rfl, le_rfl⟩, rfl⟩
  have key : ∀ w : TrueZero, rZeroHeight w.1 = rZeroHeight p.zLaterMember →
      zeroPoint w ∈ fiberPoints (rZeroHeight p.zLaterMember) := fun w hw =>
    Finset.mem_filter.mpr ⟨mem_upperWindow_iff.mpr ⟨w, rfl, hw.le⟩, hw⟩
  rw [passage_count_step_lt_two_iff p hV]
  constructor
  · intro hlt
    obtain ⟨ρ, hS, hm⟩ := (fiberCount_lt_two_iff _ ⟨_, hz⟩).mp hlt
    have hρ : zeroPoint (⟨p.zLaterMember, hL⟩ : TrueZero) = ρ := by
      rw [hS] at hz; exact Finset.mem_singleton.mp hz
    refine ⟨?_, ?_, hρ ▸ hm⟩
    · have hStep : upperCountWithMultiplicity (rZeroHeight p.zLaterMember) <
          upperCountWithMultiplicity (rZeroHeight p.zEarlierMember) + 2 :=
        (passage_count_step_lt_two_iff p hV).mpr hlt
      have hWl := lowCount_eq_zero_of_count_step hV.le hWe hStep
      exact all_onLine_of_lowCount_zero hWl ⟨p.zLaterMember, hL⟩ le_rfl
    · intro w hw
      have h1 := key w hw
      rw [hS] at h1
      have h2 := Finset.mem_singleton.mp h1
      exact Subtype.ext (Subtype.ext (h2.trans hρ.symm))
  · rintro ⟨_, huniq, hm⟩
    have hS : fiberPoints (rZeroHeight p.zLaterMember) = {zeroPoint ⟨p.zLaterMember, hL⟩} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr ⟨hz, ?_⟩
      intro ρ hρ
      obtain ⟨hwin, him⟩ := Finset.mem_filter.mp hρ
      obtain ⟨w, hw, hle⟩ := mem_upperWindow_iff.mp hwin
      have hh : rZeroHeight w.1 = rZeroHeight p.zLaterMember := by
        have : rZeroHeight w.1 = ρ.im := by rw [← hw]; rfl
        rw [this, him]
      rw [← hw, huniq w hh]
    exact (fiberCount_lt_two_iff _ ⟨_, hz⟩).mpr ⟨_, hS, hm⟩

end RHV6Fresh
