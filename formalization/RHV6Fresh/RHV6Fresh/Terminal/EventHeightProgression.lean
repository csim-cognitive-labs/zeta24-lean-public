/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ReadingArithmetic
import RHV3Lean.Objects.HeightEventPrimeGap

/-!
# RHV6Fresh — « EV = EV + 1 » et la progression de la hauteur

Code d'abord (auteur, 2026-09-25).  Ce fichier déplie ce que le code compilé dit déjà de la relation
entre l'événement (l'index zéro-source `nZeroSourceIndex`, qui avance de un sur tout passage) et la
hauteur `T`, puis compare les deux grammaires de zéros présentes dans la base :

* la grammaire des **membres** (`nZeroSourceIndex`, ordre lexicographique hauteur puis position
  radiale, `ZeroGapGrammar.lean`, `MemberZeroSourceOccurrence.lean`) : chaque passage consécutif
  incrémente l'événement et fait avancer l'occurrence de `p_n` à `p_{n+1}`, que la hauteur avance ou
  non ;
* la grammaire des **hauteurs** (`nZeroHeightEventIndex`, `HeightEventPrimeGap.lean`) : une hauteur
  est un événement, deux membres de même hauteur portent le même événement et le même premier.

Les deux grammaires sont liées rigidement au même canal premier (`primeAt = fnPrimeAtRank`,
`thm_M9a_M9b_components_unconditional`).  Elles coïncident sur tout zéro si et seulement si RH
(`grammarsAgree_iff_riemannHypothesis`, `occurrences_agree_iff_riemannHypothesis`).

Sur la ligne, « EV = EV + 1 » force bien la progression de `T`
(`passage_height_lt_of_onLine`).  Hors ligne, un passage avec « EV = EV + 1 », occurrence qui avance
et hauteur qui n'avance pas existe (`off_event_increment_without_height`) ; exiger la progression de
`T` sur tout passage, ou seulement sur les passages ayant une extrémité hors ligne, est RH
(`heightProgression_iff_riemannHypothesis`, `offPassages_heightProgression_iff_riemannHypothesis`).
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Ce que tout passage compile : événement + 1, occurrence + 1 -/

/-- Sur tout passage consécutif de membres supérieurs : l'index avance de un, l'occurrence de sortie
est le premier minimal attendu de l'entrée, et l'occurrence progresse strictement. -/
theorem passage_event_increment (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
      occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
      occurrence ⟨p.zEarlierMember, hE⟩ < occurrence ⟨p.zLaterMember, hL⟩ :=
  ⟨thm_zeroSourceIndex_succ_of_passage p hE,
    (expectedMinimumPrime_eq_laterOccurrence p hE hL).symm,
    occurrence_strict_of_passage p hE hL⟩

/-! ## 2. Sur la ligne, l'événement force la hauteur -/

/-- Deux membres consécutifs situés sur la ligne ont des hauteurs strictement croissantes : l'ordre
est lexicographique (hauteur, position radiale), et les positions radiales coïncident. -/
theorem passage_height_lt_of_onLine (p : TZeroPassage)
    (hE : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hL : rZeroRadialPosition p.zLaterMember = 1 / 2) :
    rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember := by
  rcases (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mp p.precedes with h | ⟨_, h⟩
  · exact h
  · rw [hE, hL] at h
    exact absurd h (lt_irrefl _)

/-- Sous RH, tout passage fait progresser la hauteur. -/
theorem passage_height_lt_of_riemannHypothesis (hRH : RiemannHypothesis) (p : TZeroPassage) :
    rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember :=
  passage_height_lt_of_onLine p
    (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _)
    (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _)

/-- Un passage nul (même hauteur) a une extrémité hors ligne. -/
theorem nullPassage_offLine (p : TZeroPassage)
    (h : rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember) :
    PIsOffCriticalLine p.zEarlierMember ∨ PIsOffCriticalLine p.zLaterMember := by
  by_contra hcon
  have hE : rZeroRadialPosition p.zEarlierMember = 1 / 2 := by
    by_contra hne
    exact hcon (Or.inl hne)
  have hL : rZeroRadialPosition p.zLaterMember = 1 / 2 := by
    by_contra hne
    exact hcon (Or.inr hne)
  have hlt := passage_height_lt_of_onLine p hE hL
  rw [h] at hlt
  exact lt_irrefl _ hlt

/-! ## 3. Hors ligne : « EV = EV + 1 » sans progression de la hauteur -/

/-- Un zéro hors ligne produit un passage réel dont l'index avance de un, dont l'occurrence avance
au premier minimal attendu, et dont la hauteur n'avance pas (`thm_offCriticalLine_existsNullPassage`
dans la fibre finie de la hauteur). -/
theorem off_event_increment_without_height {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    ∃ p : TZeroPassage, ∃ hE : 0 < rZeroHeight p.zEarlierMember,
      ∃ hL : 0 < rZeroHeight p.zLaterMember,
        rZeroHeight p.zEarlierMember = rZeroHeight z.1 ∧
        rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember ∧
        nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
        occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
        occurrence ⟨p.zEarlierMember, hE⟩ < occurrence ⟨p.zLaterMember, hL⟩ := by
  obtain ⟨p, hGap, hHeight⟩ := thm_offCriticalLine_existsNullPassage hOff
  have hSame : rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember :=
    (thm_zeroPassage_null_iff_sameHeight p).mp hGap
  have hE : 0 < rZeroHeight p.zEarlierMember := by
    rw [hHeight]
    exact z.2
  have hL : 0 < rZeroHeight p.zLaterMember := by
    rw [← hSame]
    exact hE
  obtain ⟨hSucc, hOcc, hLt⟩ := passage_event_increment p hE hL
  exact ⟨p, hE, hL, hHeight, hSame, hSucc, hOcc, hLt⟩

/-! ## 4. Les deux grammaires de zéros : membres contre hauteurs -/

/-- L'index par hauteurs est majoré par l'index par membres : les hauteurs strictement inférieures
sont les images des membres qui précèdent. -/
theorem heightEventIndex_le_sourceIndex (z : TrueZero) :
    nZeroHeightEventIndex (tZeroHeightEvent z) ≤ nZeroSourceIndex z.1 := by
  classical
  unfold nZeroHeightEventIndex nZeroSourceIndex
  have hsub : (thm_zeroHeightsBelow_finite (tZeroHeightEvent z)).toFinset ⊆
      (thm_upperZerosBelow_finite z.1).toFinset.image rZeroHeight := by
    intro T hT
    rw [Set.Finite.mem_toFinset] at hT
    obtain ⟨⟨w, hw⟩, hlt⟩ := hT
    rw [Finset.mem_image]
    refine ⟨w.1, ?_, hw⟩
    rw [Set.Finite.mem_toFinset]
    refine ⟨w.2, ?_⟩
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    left
    rw [hw]
    exact hlt
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Sous RH les deux index coïncident : la hauteur détermine le membre. -/
theorem sourceIndex_eq_heightEventIndex_of_riemannHypothesis
    (hRH : RiemannHypothesis) (z : TrueZero) :
    nZeroSourceIndex z.1 = nZeroHeightEventIndex (tZeroHeightEvent z) := by
  classical
  unfold nZeroHeightEventIndex nZeroSourceIndex
  have himg : (thm_upperZerosBelow_finite z.1).toFinset.image rZeroHeight =
      (thm_zeroHeightsBelow_finite (tZeroHeightEvent z)).toFinset := by
    ext T
    constructor
    · intro hT
      rw [Finset.mem_image] at hT
      obtain ⟨w, hw, rfl⟩ := hT
      rw [Set.Finite.mem_toFinset] at hw ⊢
      obtain ⟨hpos, hprec⟩ := hw
      refine ⟨⟨⟨w, hpos⟩, rfl⟩, ?_⟩
      rcases (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mp hprec with h | ⟨_, h⟩
      · exact h
      · exfalso
        rw [thm_zeroRadialPosition_half_of_riemannHypothesis hRH,
          thm_zeroRadialPosition_half_of_riemannHypothesis hRH] at h
        exact lt_irrefl _ h
    · intro hT
      rw [Set.Finite.mem_toFinset] at hT
      obtain ⟨⟨w, hw⟩, hlt⟩ := hT
      rw [Finset.mem_image]
      refine ⟨w.1, ?_, hw⟩
      rw [Set.Finite.mem_toFinset]
      refine ⟨w.2, ?_⟩
      rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
      left
      rw [hw]
      exact hlt
  rw [← himg]
  symm
  apply Finset.card_image_of_injOn
  intro a _ b _ hab
  apply thm_zeroOrderKey_injective
  unfold fnZeroOrderKey
  rw [hab, thm_zeroRadialPosition_half_of_riemannHypothesis hRH a,
    thm_zeroRadialPosition_half_of_riemannHypothesis hRH b]

/-- Hors ligne, la sortie du passage nul a un index par membres strictement plus grand que son
index par hauteurs : l'événement des membres a avancé, celui des hauteurs non. -/
theorem off_heightEventIndex_lt_sourceIndex {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    ∃ w : TrueZero, nZeroHeightEventIndex (tZeroHeightEvent w) < nZeroSourceIndex w.1 := by
  obtain ⟨p, hE, hL, _, hSame, hSucc, _, _⟩ := off_event_increment_without_height hOff
  refine ⟨⟨p.zLaterMember, hL⟩, ?_⟩
  have h1 : nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zLaterMember, hL⟩) =
      nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zEarlierMember, hE⟩) :=
    thm_heightEventIndex_eq_of_sameHeight hSame.symm
  have h2 := heightEventIndex_le_sourceIndex ⟨p.zEarlierMember, hE⟩
  change nZeroHeightEventIndex (tZeroHeightEvent ⟨p.zLaterMember, hL⟩) <
    nZeroSourceIndex p.zLaterMember
  rw [h1, hSucc]
  exact Nat.lt_succ_of_le h2

/-- Le miroir d'un zéro hors ligne : même événement de hauteur et même premier par hauteurs
(`thm_offMirror_sameHeightEvent_samePrime`), mais occurrence par membres distincte. -/
theorem off_mirror_two_grammars {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    nHeightEventMZOccurrence (tZeroHeightEvent (mirrorMember z)) =
        nHeightEventMZOccurrence (tZeroHeightEvent z) ∧
      occurrence (mirrorMember z) ≠ occurrence z := by
  refine ⟨thm_offMirror_sameHeightEvent_samePrime z hOff, ?_⟩
  intro hEq
  rw [occurrence_eq_canonicalAnchor, occurrence_eq_canonicalAnchor] at hEq
  unfold nMemberCanonicalAnchor at hEq
  have hIdx := thm_primeAtRank_injective hEq
  have hMem : mirrorMember z = z := thm_zeroSourceIndex_injective hIdx
  exact thm_offCriticalLine_mirror_distinct hOff (congrArg Subtype.val hMem)

end RHV6Fresh
