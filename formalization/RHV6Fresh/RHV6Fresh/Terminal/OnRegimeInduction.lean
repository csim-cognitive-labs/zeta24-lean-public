/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.LineCountingDefect
import RHV6Fresh.Terminal.AuthenticPassageProfile

/-!
# Induction du régime ON : parité des fibres, premier niveau de défaut, invariant suffisant (E208–E211, 2026-10-13)

Mission E208–E211 : expliquer positivement la permanence du régime ON. Ce module ne contient que des énoncés DÉMONTRÉS
(axiomes standard), composés depuis `CountingDeficit`, `LineCountingDefect`, `ArrivalFiberHypotheses` et
`AuthenticPassageProfile`. Réutilisés, non recréés : `mirror_fixed_iff_onLine` (point fixe du miroir ⟺ ON),
`zeroCountDeficit_nonneg`, `zeroCountDeficit_mono` (déficit `D = N − N₀ ≥ 0`, croissant), `lowCount_eq_zero_iff`,
`exists_first_regime_break`, `first_regime_break_profile`, `riemannHypothesis_of_anchor_and_history_conservation`.

Démontré ici :
* parité de la fibre : à toute hauteur `T`, `fibre(T) − fibre_ON(T) = 2·fibre_BASSE(T)` : la contribution hors ligne d'une
  fibre est paire (`offLine_fiber_contribution_even`) ;
* `D(T) = 0 ⟺` tout membre de hauteur `≤ T` est ON (`zeroDefect_eq_zero_iff_noOffBelow`) ;
* `ΔD(T, U) = 0 ⟺` aucun membre hors ligne de hauteur dans `]T, U]` (`counting_increment_eq_iff_noOffInInterval`) ;
* premier niveau de défaut : au premier rang canonique hors ligne, le déficit est nul strictement en dessous, vaut au moins
  deux à la hauteur, la fibre contient le membre bas et son miroir distinct (`first_off_level_has_mirror_pair`) ;
* les trois sondes E211 sont équivalentes sur un passage dont l'historique est ON : conservation radiale, conservation du
  comptage (`ΔD = 0`), conservation du miroir (`regime_probes_equivalent`) ; aucune n'est dérivée ;
* induction conditionnelle : tout invariant `P` des passages, suffisant pour l'arrivée ON et vrai sur tout passage
  d'historique ON, ferme RH avec l'ancre (`on_regime_induction_of_independent_invariant`) ; instances : pas de comptage `< 2`
  (strictement plus fort que RH : il exige la simplicité) et `ΔD = 0` ; l'invariant `ΔD = 0` quantifié sur tous les passages
  d'historique ON est ÉQUIVALENT à RH (`lineDefect_invariant_iff_riemannHypothesis`) : ce n'est pas une loi plus faible.
Aucun `sorry`, aucun `admit`, aucun axiome nouveau ; aucun invariant indépendant n'est démontré.
-/

namespace RHV6Fresh

open RHV3Lean Finset
open scoped ComplexConjugate

/-! ## 1. Partition radiale et bijection miroir sur une famille finie quelconque -/

/-- Partition radiale d'une somme sur une famille finie de points. -/
theorem sum_split_radial (S : Finset ℂ) (f : ℂ → ℕ) :
    ∑ ρ ∈ S, f ρ = ∑ ρ ∈ S.filter (fun ρ => ρ.re = 1 / 2), f ρ +
      ∑ ρ ∈ S.filter (fun ρ => ρ.re < 1 / 2), f ρ + ∑ ρ ∈ S.filter (fun ρ => 1 / 2 < ρ.re), f ρ := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun ρ => ρ.re < 1 / 2)]
  rw [← Finset.sum_filter_add_sum_filter_not (S.filter fun ρ => ¬ ρ.re < 1 / 2)
    (fun ρ => ρ.re = 1 / 2), Finset.filter_filter, Finset.filter_filter]
  have h1 : (S.filter fun ρ => ¬ ρ.re < 1 / 2 ∧ ρ.re = 1 / 2) = S.filter fun ρ => ρ.re = 1 / 2 := by
    ext ρ; simp only [Finset.mem_filter]; constructor
    · rintro ⟨h, -, h2⟩; exact ⟨h, h2⟩
    · rintro ⟨h, h2⟩; exact ⟨h, by rw [h2]; exact lt_irrefl _, h2⟩
  have h2 : (S.filter fun ρ => ¬ ρ.re < 1 / 2 ∧ ¬ ρ.re = 1 / 2) = S.filter fun ρ => 1 / 2 < ρ.re := by
    ext ρ; simp only [Finset.mem_filter]; constructor
    · rintro ⟨h, h1, h2⟩; exact ⟨h, lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)⟩
    · rintro ⟨h, h1⟩; exact ⟨h, not_lt.mpr h1.le, h1.ne'⟩
  rw [h1, h2]; ring

/-- Sur une famille finie de zéros non triviaux stable par le miroir `ρ ↦ 1 − ρ̄`, la somme des multiplicités des membres
bas égale celle des membres hauts. -/
theorem sum_low_eq_sum_high (S : Finset ℂ) (hNT : ∀ ρ ∈ S, PIsNonTrivialZetaZero ρ)
    (hS : ∀ ρ ∈ S, 1 - conj ρ ∈ S) :
    ∑ ρ ∈ S.filter (fun ρ => ρ.re < 1 / 2), zetaZeroMultiplicity ρ =
      ∑ ρ ∈ S.filter (fun ρ => 1 / 2 < ρ.re), zetaZeroMultiplicity ρ := by
  refine Finset.sum_nbij' (fun ρ => 1 - conj ρ) (fun ρ => 1 - conj ρ) ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ ⊢
    refine ⟨hS ρ hρ.1, ?_⟩
    have := hρ.2; simp; linarith
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ ⊢
    refine ⟨hS ρ hρ.1, ?_⟩
    have := hρ.2; simp; linarith
  · intro ρ _; exact mirrorPoint_mirrorPoint ρ
  · intro ρ _; exact mirrorPoint_mirrorPoint ρ
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ
    exact (zetaZeroMultiplicity_mirrorPoint (hNT ρ hρ.1)).symm

/-! ## 2. Parité de la contribution hors ligne d'une fibre -/

/-- Partie BASSE de la fibre à la hauteur `T`, avec multiplicité. -/
noncomputable def lowFiberCount (T : ℝ) : ℕ :=
  ∑ ρ ∈ ((upperWindow T).filter (fun ρ => ρ.im = T)).filter (fun ρ => ρ.re < 1 / 2), zetaZeroMultiplicity ρ

/-- Partie HAUTE de la fibre à la hauteur `T`, avec multiplicité. -/
noncomputable def highFiberCount (T : ℝ) : ℕ :=
  ∑ ρ ∈ ((upperWindow T).filter (fun ρ => ρ.im = T)).filter (fun ρ => 1 / 2 < ρ.re), zetaZeroMultiplicity ρ

theorem fiberCount_eq_on_add_low_add_high (T : ℝ) :
    fiberCountWithMultiplicity T = onFiberCount T + lowFiberCount T + highFiberCount T :=
  sum_split_radial _ _

/-- La fibre est stable par le miroir (même hauteur). -/
theorem mirrorPoint_mem_fiber {T : ℝ} {ρ : ℂ} (h : ρ ∈ (upperWindow T).filter (fun ρ => ρ.im = T)) :
    1 - conj ρ ∈ (upperWindow T).filter (fun ρ => ρ.im = T) := by
  rw [Finset.mem_filter] at h ⊢
  exact ⟨mirrorPoint_mem_upperWindow h.1, by simp [h.2]⟩

/-- **Bas = hauts dans la fibre** (bijection miroir à hauteur fixée). -/
theorem lowFiberCount_eq_highFiberCount (T : ℝ) : lowFiberCount T = highFiberCount T :=
  sum_low_eq_sum_high _ (fun _ hρ => (mem_upperWindow.mp (Finset.mem_filter.mp hρ).1).1)
    (fun _ hρ => mirrorPoint_mem_fiber hρ)

/-- **La contribution hors ligne d'une fibre est paire** : `fibre(T) − fibre_ON(T) = 2·fibre_BASSE(T)`. -/
theorem offLine_fiber_contribution_even (T : ℝ) :
    (fiberCountWithMultiplicity T : ℤ) - onFiberCount T = 2 * lowFiberCount T := by
  rw [fiberCount_eq_on_add_low_add_high, ← lowFiberCount_eq_highFiberCount]; push_cast; ring

/-- Un membre bas est compté dans la partie basse de sa fibre. -/
theorem one_le_lowFiberCount_of_low (z : TrueZero) (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    1 ≤ lowFiberCount (rZeroHeight z.1) := by
  unfold lowFiberCount
  have hmem : zeroPoint z ∈ ((upperWindow (rZeroHeight z.1)).filter (fun ρ => ρ.im = rZeroHeight z.1)).filter
      (fun ρ => ρ.re < 1 / 2) := by
    rw [Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨mem_upperWindow_iff.mpr ⟨z, rfl, le_rfl⟩, rfl⟩, hβ⟩
  calc 1 ≤ zetaZeroMultiplicity (zeroPoint z) :=
        one_le_multiplicity_of_mem_upperWindow (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).1
    _ ≤ _ := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem

/-- **`fibre_BASSE(T) = 0 ⟺` tout membre de hauteur exactement `T` est ON.** -/
theorem lowFiberCount_eq_zero_iff (T : ℝ) :
    lowFiberCount T = 0 ↔ ∀ z : TrueZero, rZeroHeight z.1 = T → rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro h z hz
    rcases lt_trichotomy (rZeroRadialPosition z.1) (1 / 2) with hlt | heq | hgt
    · exfalso; have := one_le_lowFiberCount_of_low z hlt; rw [hz] at this; omega
    · exact heq
    · exfalso
      have hm : rZeroRadialPosition (mirrorMember z).1 < 1 / 2 := by rw [mirrorMember_radial]; linarith
      have := one_le_lowFiberCount_of_low (mirrorMember z) hm
      rw [mirrorMember_ordinate, hz] at this; omega
  · intro h
    unfold lowFiberCount
    apply Finset.sum_eq_zero
    intro ρ hρ
    rw [Finset.mem_filter, Finset.mem_filter] at hρ
    obtain ⟨w, rfl, -⟩ := mem_upperWindow_iff.mp hρ.1.1
    exact absurd (h w hρ.1.2) (ne_of_lt hρ.2)

/-! ## 3. Déficit nul et accroissement nul : lectures exactes -/

/-- **`D(T) = 0 ⟺` tout membre de hauteur `≤ T` est ON** (côté haut exclu par son miroir bas). -/
theorem zeroDefect_eq_zero_iff_noOffBelow (T : ℝ) :
    zeroCountDeficit T = 0 ↔ ∀ z : TrueZero, rZeroHeight z.1 ≤ T → rZeroRadialPosition z.1 = 1 / 2 := by
  rw [zeroCountDeficit_eq]
  constructor
  · intro h
    have hW : lowCount T = 0 := by omega
    exact all_onLine_of_lowCount_zero hW
  · intro h
    have hW : lowCount T = 0 := (lowCount_eq_zero_iff T).mpr fun z hz hβ => absurd (h z hz) (ne_of_lt hβ)
    rw [hW]; simp

/-- La partie basse de la fenêtre croît exactement de la partie basse de la tranche `]T, U]`. -/
theorem lowCount_sub_eq_slice {T U : ℝ} (hTU : T ≤ U) :
    lowCount U = lowCount T + ∑ ρ ∈ ((upperWindow U).filter (fun ρ => ρ.re < 1 / 2)) \
      ((upperWindow T).filter (fun ρ => ρ.re < 1 / 2)), zetaZeroMultiplicity ρ := by
  unfold lowCount
  have hsub : (upperWindow T).filter (fun ρ => ρ.re < 1 / 2) ⊆ (upperWindow U).filter (fun ρ => ρ.re < 1 / 2) :=
    Finset.filter_subset_filter _ (upperWindow_mono hTU)
  rw [← Finset.sum_sdiff hsub, add_comm]

/-- **`ΔD(T, U) = 0 ⟺` aucun membre hors ligne de hauteur dans `]T, U]`** (`T ≤ U`). -/
theorem counting_increment_eq_iff_noOffInInterval {T U : ℝ} (hTU : T ≤ U) :
    lineDefect T U = 0 ↔
      ∀ z : TrueZero, T < rZeroHeight z.1 → rZeroHeight z.1 ≤ U → rZeroRadialPosition z.1 = 1 / 2 := by
  rw [lineDefect_eq]
  have hslice := lowCount_sub_eq_slice hTU
  constructor
  · intro h z hTz hzU
    have hEq : lowCount U = lowCount T := by omega
    -- aucun membre bas dans la tranche
    have hNoLow : ∀ w : TrueZero, T < rZeroHeight w.1 → rZeroHeight w.1 ≤ U → ¬ rZeroRadialPosition w.1 < 1 / 2 := by
      intro w hTw hwU hβ
      have hmem : zeroPoint w ∈ ((upperWindow U).filter (fun ρ => ρ.re < 1 / 2)) \
          ((upperWindow T).filter (fun ρ => ρ.re < 1 / 2)) := by
        rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
        refine ⟨⟨mem_upperWindow_iff.mpr ⟨w, rfl, hwU⟩, hβ⟩, fun hm => ?_⟩
        obtain ⟨v, hv, hvT⟩ := mem_upperWindow_iff.mp hm.1
        have : v = w := Subtype.ext (Subtype.ext hv)
        rw [this] at hvT
        exact absurd hvT (not_le.mpr hTw)
      have h1 := Finset.single_le_sum (f := zetaZeroMultiplicity) (fun _ _ => Nat.zero_le _) hmem
      have h2 := one_le_multiplicity_of_mem_upperWindow
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp hmem).1).1
      omega
    rcases lt_trichotomy (rZeroRadialPosition z.1) (1 / 2) with hlt | heq | hgt
    · exact absurd hlt (hNoLow z hTz hzU)
    · exact heq
    · exfalso
      apply hNoLow (mirrorMember z) (by rw [mirrorMember_ordinate]; exact hTz)
        (by rw [mirrorMember_ordinate]; exact hzU)
      rw [mirrorMember_radial]; linarith
  · intro h
    have hzero : ∑ ρ ∈ ((upperWindow U).filter (fun ρ => ρ.re < 1 / 2)) \
        ((upperWindow T).filter (fun ρ => ρ.re < 1 / 2)), zetaZeroMultiplicity ρ = 0 := by
      apply Finset.sum_eq_zero
      intro ρ hρ
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hρ
      obtain ⟨w, rfl, hwU⟩ := mem_upperWindow_iff.mp hρ.1.1
      have hTw : T < rZeroHeight w.1 := by
        by_contra hle
        exact hρ.2 ⟨mem_upperWindow_iff.mpr ⟨w, rfl, not_lt.mp hle⟩, hρ.1.2⟩
      exact absurd (h w hTw hwU) (ne_of_lt hρ.1.2)
    rw [hzero] at hslice
    rw [hslice]; simp

/-! ## 4. Premier niveau de défaut : paire miroir, saut pair -/

/-- **Premier niveau de défaut** (sous l'ancre ON) : au premier rang canonique hors ligne `n` (bas, historique ON), le
déficit est nul strictement sous la hauteur `T_n`, vaut au moins deux en `T_n` ; la fibre en `T_n` contient le membre bas
et son miroir, distinct, de même hauteur et de même multiplicité ; sa partie basse est au moins un et sa contribution
hors ligne est paire. Tout est lu sur les vrais membres. -/
theorem first_off_level_has_mirror_pair (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    {n : ℕ} (hLow : rZeroRadialPosition (canonicalMember n).1 < 1 / 2)
    (hHist : ∀ k < n, rZeroRadialPosition (canonicalMember k).1 = 1 / 2) :
    (∀ T : ℝ, T < rZeroHeight (canonicalMember n).1 → zeroCountDeficit T = 0) ∧
    2 ≤ zeroCountDeficit (rZeroHeight (canonicalMember n).1) ∧
    mirrorMember (canonicalMember n) ≠ canonicalMember n ∧
    rZeroHeight (mirrorMember (canonicalMember n)).1 = rZeroHeight (canonicalMember n).1 ∧
    zetaZeroMultiplicity (zeroPoint (mirrorMember (canonicalMember n))) =
      zetaZeroMultiplicity (zeroPoint (canonicalMember n)) ∧
    1 ≤ lowFiberCount (rZeroHeight (canonicalMember n).1) ∧
    2 ≤ fiberCountWithMultiplicity (rZeroHeight (canonicalMember n).1) := by
  obtain ⟨-, -, -, -, -, -, hBelow, hAt, -⟩ := first_regime_break_profile h₁ hLow hHist
  refine ⟨fun T hT => ?_, ?_, mirrorMember_ne hLow, mirrorMember_ordinate _, ?_, one_le_lowFiberCount_of_low _ hLow,
    two_le_fiberCount_of_low _ hLow⟩
  · rw [zeroCountDeficit_eq, (hBelow T hT).1]; simp
  · rw [zeroCountDeficit_eq]; omega
  · rw [zeroPoint_mirrorMember]
    exact zetaZeroMultiplicity_mirrorPoint (canonicalMember n).1.2

/-! ## 5. Les trois sondes sont équivalentes sur un passage d'historique ON -/

/-- Point fixe du miroir en termes de membres : `mirrorMember z = z ⟺ β = 1/2`. -/
theorem mirrorMember_eq_self_iff (z : TrueZero) : mirrorMember z = z ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro h
    have hr := mirrorMember_radial z
    rw [h] at hr; linarith
  · exact mirrorMember_eq_self_of_onLine

/-- **Équivalence des trois sondes** sur un passage `p : e → l` qui monte dont tout membre précédant l'arrivée est ON :
(1) conservation radiale `β_l = 1/2` ; (2) conservation du comptage `ΔD(T_e, T_l) = 0` ; (3) conservation du miroir
`mirror(l) = l` ; et `ΔD = 0 ⟺ fibre_BASSE(T_l) = 0`. L'historique ON exclut tout membre hors ligne de la fibre `T_l` qui
précéderait `l` ; la consécutivité exclut toute hauteur strictement entre `T_e` et `T_l`. Aucun côté n'est dérivé. -/
theorem regime_probes_equivalent (p : TZeroPassage) (hV : VerticalPassage p) (hL : 0 < rZeroHeight p.zLaterMember)
    (hHist : ∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) :
    (rZeroRadialPosition p.zLaterMember = 1 / 2 ↔
      lineDefect (rZeroHeight p.zEarlierMember) (rZeroHeight p.zLaterMember) = 0) ∧
    (rZeroRadialPosition p.zLaterMember = 1 / 2 ↔ mirrorMember ⟨p.zLaterMember, hL⟩ = ⟨p.zLaterMember, hL⟩) ∧
    (lineDefect (rZeroHeight p.zEarlierMember) (rZeroHeight p.zLaterMember) = 0 ↔
      lowFiberCount (rZeroHeight p.zLaterMember) = 0) := by
  refine ⟨?_, (mirrorMember_eq_self_iff ⟨p.zLaterMember, hL⟩).symm, ?_⟩
  · rw [counting_increment_eq_iff_noOffInInterval hV.le]
    constructor
    · intro hOnL z hTz hzU
      -- la consécutivité place z à la hauteur T_l exactement
      have hzT : rZeroHeight z.1 = rZeroHeight p.zLaterMember := by
        by_contra hne
        exact consecutive_no_height_between p z.1 ⟨hTz, lt_of_le_of_ne hzU hne⟩
      rcases lt_trichotomy (rZeroRadialPosition z.1) (1 / 2) with hlt | heq | hgt
      · exfalso
        have hPrec : PZeroMemberPrecedes z.1 p.zLaterMember := by
          rw [thm_zeroMemberPrecedes_iff_height_radial_lex]; right; exact ⟨hzT, by rw [hOnL]; exact hlt⟩
        exact absurd (hHist z hPrec) (ne_of_lt hlt)
      · exact heq
      · exfalso
        have hm : rZeroRadialPosition (mirrorMember z).1 < 1 / 2 := by rw [mirrorMember_radial]; linarith
        have hPrec : PZeroMemberPrecedes (mirrorMember z).1 p.zLaterMember := by
          rw [thm_zeroMemberPrecedes_iff_height_radial_lex]; right
          exact ⟨by rw [mirrorMember_ordinate]; exact hzT, by rw [hOnL]; exact hm⟩
        exact absurd (hHist _ hPrec) (ne_of_lt hm)
    · intro h
      exact h ⟨p.zLaterMember, hL⟩ hV le_rfl
  · rw [passage_lineDefect_eq_fiber p hV, offLine_fiber_contribution_even]; omega

/-! ## 6. Induction conditionnelle depuis un invariant suffisant -/

/-- **Schéma d'induction du régime ON** : si un invariant `P` des passages (défini sans la conclusion ON) est (i) SUFFISANT
— sur un passage qui monte depuis un membre ON de hauteur positive, d'historique ON, `P p` donne l'arrivée ON — et
(ii) VRAI sur tout tel passage, alors, avec l'ancre, RH. Composition de `riemannHypothesis_of_anchor_and_history_conservation`.
Aucun `P` satisfaisant (ii) n'est démontré dans ce module. -/
theorem on_regime_induction_of_independent_invariant (P : TZeroPassage → Prop)
    (hAnchor : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (hSuff : ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      P p → rZeroRadialPosition p.zLaterMember = 1 / 2)
    (hP : ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) → P p) :
    RiemannHypothesis :=
  riemannHypothesis_of_anchor_and_history_conservation hAnchor fun p hE hV hOn hHist =>
    (hSuff p hE hV hOn hHist (hP p hE hV hOn hHist)).trans hOn.symm

/-- Instance (H2, pas de comptage) : `N(T_l) < N(T_e) + 2` est suffisant (`lowCount_eq_zero_of_count_step`). Il exige la
simplicité et l'unicité de l'arrivée (`count_step_iff_on_unique_simple`) : strictement plus fort que l'arrivée ON. -/
theorem count_step_invariant_suffices (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hV : VerticalPassage p)
    (hHist : ∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2)
    (hStep : upperCountWithMultiplicity (rZeroHeight p.zLaterMember) <
      upperCountWithMultiplicity (rZeroHeight p.zEarlierMember) + 2) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 := by
  have hL : 0 < rZeroHeight p.zLaterMember := lt_of_lt_of_le hE (passage_height_le p)
  have hWe : lowCount (rZeroHeight p.zEarlierMember) = 0 := by
    rw [lowCount_eq_zero_iff]
    intro z hz hβ
    have hPrec : PZeroMemberPrecedes z.1 p.zLaterMember := by
      rw [thm_zeroMemberPrecedes_iff_height_radial_lex]; left; exact lt_of_le_of_lt hz hV
    exact absurd (hHist z hPrec) (ne_of_lt hβ)
  exact all_onLine_of_lowCount_zero (lowCount_eq_zero_of_count_step hV.le hWe hStep) ⟨p.zLaterMember, hL⟩ le_rfl

/-- Instance (H2, accroissement) : `ΔD(T_e, T_l) = 0` est suffisant. -/
theorem lineDefect_invariant_suffices (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hV : VerticalPassage p)
    (hΔ : lineDefect (rZeroHeight p.zEarlierMember) (rZeroHeight p.zLaterMember) = 0) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 :=
  (counting_increment_eq_iff_noOffInInterval hV.le).mp hΔ ⟨p.zLaterMember,
    lt_of_lt_of_le hE (passage_height_le p)⟩ hV le_rfl

/-- **L'invariant `ΔD = 0`, quantifié sur tous les passages d'historique ON, est ÉQUIVALENT à RH** (sous l'ancre) : ce n'est
pas une loi plus faible. Sens direct par le schéma d'induction ; sens réciproque parce que sous RH le déficit est
identiquement nul. -/
theorem lineDefect_invariant_iff_riemannHypothesis (hAnchor : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    (∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      lineDefect (rZeroHeight p.zEarlierMember) (rZeroHeight p.zLaterMember) = 0) ↔ RiemannHypothesis := by
  constructor
  · intro hP
    exact on_regime_induction_of_independent_invariant
      (fun p => lineDefect (rZeroHeight p.zEarlierMember) (rZeroHeight p.zLaterMember) = 0) hAnchor
      (fun p hE hV _ _ hΔ => lineDefect_invariant_suffices p hE hV hΔ) hP
  · intro hRH p _ hV _ _
    rw [counting_increment_eq_iff_noOffInInterval hV.le]
    intro z _ _
    exact thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1

end RHV6Fresh

#print axioms RHV6Fresh.sum_split_radial
#print axioms RHV6Fresh.sum_low_eq_sum_high
#print axioms RHV6Fresh.fiberCount_eq_on_add_low_add_high
#print axioms RHV6Fresh.lowFiberCount_eq_highFiberCount
#print axioms RHV6Fresh.offLine_fiber_contribution_even
#print axioms RHV6Fresh.one_le_lowFiberCount_of_low
#print axioms RHV6Fresh.lowFiberCount_eq_zero_iff
#print axioms RHV6Fresh.zeroDefect_eq_zero_iff_noOffBelow
#print axioms RHV6Fresh.lowCount_sub_eq_slice
#print axioms RHV6Fresh.counting_increment_eq_iff_noOffInInterval
#print axioms RHV6Fresh.first_off_level_has_mirror_pair
#print axioms RHV6Fresh.mirrorMember_eq_self_iff
#print axioms RHV6Fresh.regime_probes_equivalent
#print axioms RHV6Fresh.on_regime_induction_of_independent_invariant
#print axioms RHV6Fresh.count_step_invariant_suffices
#print axioms RHV6Fresh.lineDefect_invariant_suffices
#print axioms RHV6Fresh.lineDefect_invariant_iff_riemannHypothesis
