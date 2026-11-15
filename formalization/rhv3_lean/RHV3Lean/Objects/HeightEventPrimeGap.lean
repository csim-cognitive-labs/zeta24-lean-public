/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.MemberSensitiveMZCorrespondence
import RHV3Lean.Objects.FunctionalMirror
import RHV3Lean.Objects.ZetaSmoothedUnsmoothingP5

/-!
# Height nodes and grammatical gap-events drive the prime history

This module separates the fine `(beta,T)` provenance index from the historical
index of distinct positive zero heights.  A height alone is an endpoint node;
the grammatical event is the gap between two consecutive height nodes and is
therefore represented on the prime side by two endpoints.  Functional-equation
mirrors at the same height define one node and consume no grammatical event.
-/

namespace RHV3Lean

/-- A positive height node which is actually inhabited by an upper nontrivial zero.
The data is extensional in the real number `T`; no member, rank, or prime is
stored in the value. -/
def TZeroHeightEvent := {T : ℝ // ∃ z : TUpperNonTrivialZetaZero,
  rZeroHeight z.1 = T}

def TZeroHeightEvent.height (e : TZeroHeightEvent) : ℝ := e.1

noncomputable def tZeroHeightEvent (z : TUpperNonTrivialZetaZero) :
    TZeroHeightEvent := ⟨rZeroHeight z.1, z, rfl⟩

theorem thm_sameHeight_sameHeightEvent
    {z₁ z₂ : TUpperNonTrivialZetaZero}
    (h : rZeroHeight z₁.1 = rZeroHeight z₂.1) :
    tZeroHeightEvent z₁ = tZeroHeightEvent z₂ :=
  Subtype.ext h

/-- The set of inhabited positive zero heights strictly before an event. -/
def sZeroHeightsBelow (e : TZeroHeightEvent) : Set ℝ :=
  {T | (∃ z : TUpperNonTrivialZetaZero, rZeroHeight z.1 = T) ∧ T < e.height}

theorem thm_zeroHeightsBelow_finite (e : TZeroHeightEvent) :
    (sZeroHeightsBelow e).Finite := by
  obtain ⟨zTop, hzTop⟩ := e.2
  have hImage : sZeroHeightsBelow e ⊆ rZeroHeight '' sUpperZerosBelow zTop.1 := by
    intro T hT
    obtain ⟨⟨z, hzPos⟩, hzT⟩ := hT.1
    refine ⟨z, ⟨hzPos, ?_⟩, hzT⟩
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    exact Or.inl (calc
      rZeroHeight z = T := hzT
      _ < e.1 := hT.2
      _ = rZeroHeight zTop.1 := hzTop.symm)
  exact ((thm_upperZerosBelow_finite zTop.1).image rZeroHeight).subset hImage

/-- Historical index: the number of distinct inhabited heights below `e`.
Unlike `nZeroSourceIndex`, multiplicity in `beta` is deliberately quotiented. -/
noncomputable def nZeroHeightEventIndex (e : TZeroHeightEvent) : ℕ :=
  (thm_zeroHeightsBelow_finite e).toFinset.card

theorem thm_heightEventIndex_eq_of_sameHeight
    {z₁ z₂ : TUpperNonTrivialZetaZero}
    (h : rZeroHeight z₁.1 = rZeroHeight z₂.1) :
    nZeroHeightEventIndex (tZeroHeightEvent z₁) =
      nZeroHeightEventIndex (tZeroHeightEvent z₂) := by
  rw [thm_sameHeight_sameHeightEvent h]

/-- A genuine gap between consecutive inhabited heights.  There is no `beta`
coordinate and no member-sensitive consecutivity in this structure. -/
structure TZeroHeightGap where
  earlier : TZeroHeightEvent
  later : TZeroHeightEvent
  height_lt : earlier.height < later.height
  consecutive : ¬ ∃ middle : TZeroHeightEvent,
    earlier.height < middle.height ∧ middle.height < later.height

/-- The grammatical event is the whole height gap, not either endpoint. -/
abbrev TZeroHeightGrammarEvent := TZeroHeightGap

theorem thm_zeroHeightsBelow_of_consecutive (g : TZeroHeightGap) :
    sZeroHeightsBelow g.later = insert g.earlier.height (sZeroHeightsBelow g.earlier) := by
  ext T
  constructor
  · intro hT
    by_cases hEq : T = g.earlier.height
    · exact hEq ▸ Set.mem_insert _ _
    · apply Set.mem_insert_of_mem
      refine ⟨hT.1, ?_⟩
      by_contra hNot
      have hLe : g.earlier.height ≤ T := le_of_not_gt hNot
      have hStrict : g.earlier.height < T := lt_of_le_of_ne hLe (Ne.symm hEq)
      obtain ⟨z, hz⟩ := hT.1
      exact g.consecutive ⟨⟨T, z, hz⟩, hStrict, hT.2⟩
  · intro hT
    rcases Set.mem_insert_iff.mp hT with hEq | hBelow
    · subst T
      exact ⟨g.earlier.2, g.height_lt⟩
    · exact ⟨hBelow.1, lt_trans hBelow.2 g.height_lt⟩

theorem thm_consecutiveHeightEvents_index_succ (g : TZeroHeightGap) :
    nZeroHeightEventIndex g.later = nZeroHeightEventIndex g.earlier + 1 := by
  classical
  have hNotMem : g.earlier.height ∉
      (thm_zeroHeightsBelow_finite g.earlier).toFinset := by
    simp [sZeroHeightsBelow]
  have hFinset : (thm_zeroHeightsBelow_finite g.later).toFinset =
      insert g.earlier.height (thm_zeroHeightsBelow_finite g.earlier).toFinset := by
    ext T
    simp [thm_zeroHeightsBelow_of_consecutive g]
  rw [nZeroHeightEventIndex, nZeroHeightEventIndex, hFinset,
    Finset.card_insert_of_notMem hNotMem]

/-- Event-level occurrence reconstructed from the exact zero-source channel. -/
noncomputable def nHeightEventMZOccurrence (e : TZeroHeightEvent) : ℕ :=
  (fnReconstructGrammar rPsiZeroChannel).primeAt (nZeroHeightEventIndex e)

noncomputable def nHeightEventCanonicalPrime (e : TZeroHeightEvent) : ℕ :=
  fnPrimeAtRank (nZeroHeightEventIndex e)

theorem thm_heightEventMZOccurrence_eq_canonicalPrime_unconditional
    (e : TZeroHeightEvent) :
    nHeightEventMZOccurrence e = nHeightEventCanonicalPrime e := by
  unfold nHeightEventMZOccurrence nHeightEventCanonicalPrime
  rw [thm_M9a_M9b_components_unconditional.2.1]

theorem thm_sameHeight_sameReconstructedPrime
    {z₁ z₂ : TUpperNonTrivialZetaZero}
    (h : rZeroHeight z₁.1 = rZeroHeight z₂.1) :
    nHeightEventMZOccurrence (tZeroHeightEvent z₁) =
      nHeightEventMZOccurrence (tZeroHeightEvent z₂) := by
  rw [thm_sameHeight_sameHeightEvent h]

theorem thm_beta_does_not_increment_primeEvent
    {z₁ z₂ : TUpperNonTrivialZetaZero}
    (h : rZeroHeight z₁.1 = rZeroHeight z₂.1) :
    tZeroHeightEvent z₁ = tZeroHeightEvent z₂ ∧
      nZeroHeightEventIndex (tZeroHeightEvent z₁) =
        nZeroHeightEventIndex (tZeroHeightEvent z₂) ∧
      nHeightEventCanonicalPrime (tZeroHeightEvent z₁) =
        nHeightEventCanonicalPrime (tZeroHeightEvent z₂) := by
  have he := thm_sameHeight_sameHeightEvent h
  exact ⟨he, congrArg nZeroHeightEventIndex he,
    congrArg nHeightEventCanonicalPrime he⟩

theorem thm_heightGap_entryPrime (g : TZeroHeightGap) :
    nHeightEventMZOccurrence g.earlier =
      fnPrimeAtRank (nZeroHeightEventIndex g.earlier) := by
  exact thm_heightEventMZOccurrence_eq_canonicalPrime_unconditional g.earlier

theorem thm_heightGap_exitPrime_is_successor (g : TZeroHeightGap) :
    nHeightEventMZOccurrence g.later =
      fnPrimeSuccessor (nZeroHeightEventIndex g.earlier) := by
  rw [thm_heightEventMZOccurrence_eq_canonicalPrime_unconditional,
    nHeightEventCanonicalPrime, thm_consecutiveHeightEvents_index_succ,
    fnPrimeSuccessor]

/-- The strong T2 package.  The analytic chain is retained as proof data in
the conclusion, while both endpoints are computed from the same height gap. -/
theorem thm_T2_heightGap_maps_to_exact_primeGap (g : TZeroHeightGap) :
    nHeightEventMZOccurrence g.earlier =
        fnPrimeAtRank (nZeroHeightEventIndex g.earlier) ∧
      nHeightEventMZOccurrence g.later =
        fnPrimeSuccessor (nZeroHeightEventIndex g.earlier) ∧
      PM9aChannelIdentityOnNaturals ∧
      (fnReconstructGrammar rPsiZeroChannel).primeAt = fnPrimeAtRank ∧
      (∀ x : ℝ, 2 ≤ x → psiRecoveredFromZeros x = (Chebyshev.psi x : ℂ)) := by
  refine ⟨thm_heightGap_entryPrime g, thm_heightGap_exitPrime_is_successor g,
    thm_M9aChannelIdentityOnNaturals_proved,
    thm_M9a_M9b_components_unconditional.2.1, ?_⟩
  intro x hx
  exact psiRecoveredFromZeros_eq_psi hx

theorem thm_heightGap_primeGap_exact (g : TZeroHeightGap) :
    (nHeightEventMZOccurrence g.earlier,
      nHeightEventMZOccurrence g.later) =
    (fnPrimeAtRank (nZeroHeightEventIndex g.earlier),
      fnPrimeSuccessor (nZeroHeightEventIndex g.earlier)) := by
  exact Prod.ext (thm_heightGap_entryPrime g) (thm_heightGap_exitPrime_is_successor g)

/-- Computed correspondence object.  It stores only the source grammatical
event; its two prime endpoints are functions, never certificates stored as
fields. -/
structure THeightGapPrimeGapCorrespondence where
  heightEvent : TZeroHeightGrammarEvent

noncomputable def THeightGapPrimeGapCorrespondence.entryPrime
    (c : THeightGapPrimeGapCorrespondence) : ℕ :=
  nHeightEventMZOccurrence c.heightEvent.earlier

noncomputable def THeightGapPrimeGapCorrespondence.exitPrime
    (c : THeightGapPrimeGapCorrespondence) : ℕ :=
  nHeightEventMZOccurrence c.heightEvent.later

noncomputable def THeightGapPrimeGapCorrespondence.primeEvent
    (c : THeightGapPrimeGapCorrespondence) : ℕ × ℕ :=
  (c.entryPrime, c.exitPrime)

theorem thm_heightGrammarEvent_is_exact_primePair
    (c : THeightGapPrimeGapCorrespondence) :
    c.primeEvent =
      (fnPrimeAtRank (nZeroHeightEventIndex c.heightEvent.earlier),
        fnPrimeSuccessor (nZeroHeightEventIndex c.heightEvent.earlier)) :=
  thm_heightGap_primeGap_exact c.heightEvent

/-! The authentic mirror specialization is stated directly on an upper zero,
so this event-level module does not import or revive `PMirrorCollision`. -/
theorem thm_offMirror_sameHeightEvent
    (z : TUpperNonTrivialZetaZero) (_hOff : PIsOffCriticalLine z.1) :
    tZeroHeightEvent (zUpperMirrorZero z) = tZeroHeightEvent z := by
  exact thm_sameHeight_sameHeightEvent (thm_mirror_sameHeight z.1)

theorem thm_offMirror_sameHeightEvent_samePrime
    (z : TUpperNonTrivialZetaZero) (hOff : PIsOffCriticalLine z.1) :
    nHeightEventMZOccurrence (tZeroHeightEvent (zUpperMirrorZero z)) =
      nHeightEventMZOccurrence (tZeroHeightEvent z) := by
  rw [thm_offMirror_sameHeightEvent z hOff]

/-- An OFF mirror pair cannot itself be the endpoints of a height gap. -/
theorem thm_offMirror_cannot_consume_primeGap
    (z : TUpperNonTrivialZetaZero) (hOff : PIsOffCriticalLine z.1) :
    ¬ ∃ g : TZeroHeightGap,
      g.earlier = tZeroHeightEvent z ∧
      g.later = tZeroHeightEvent (zUpperMirrorZero z) := by
  rintro ⟨g, hEarlier, hLater⟩
  have hSame := thm_offMirror_sameHeightEvent z hOff
  have hEq : g.earlier = g.later := hEarlier.trans (hSame.symm.trans hLater.symm)
  exact (lt_irrefl g.earlier.height) (by simpa [hEq] using g.height_lt)

#check thm_sameHeight_sameHeightEvent
#check thm_consecutiveHeightEvents_index_succ
#check thm_beta_does_not_increment_primeEvent
#check thm_T2_heightGap_maps_to_exact_primeGap
#print axioms thm_heightGrammarEvent_is_exact_primePair
#print axioms thm_offMirror_cannot_consume_primeGap

end RHV3Lean
