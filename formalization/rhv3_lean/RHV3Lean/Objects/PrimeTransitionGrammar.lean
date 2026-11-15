/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.PrimeGapGrammar

/-!
# RHV3Lean — grammaire complète des transitions premières

    TRACE_ID              : RHV3-PRIME-TRANSITION-GRAMMAR
    SEMANTIC_OBJECT       : transitions de l'unique histoire première
    SEMANTIC_STATEMENT    : au-delà de 3, toute place porte exactement l'une
                            des quatre transitions modulo 6 et sa classe.
    MATHEMATICAL_STATEMENT: états 1/5, transitions 11/15/51/55, classes
                            0/4/2/0, chemins finis et alternance des changements.
    MATHEMATICAL_PARENT   : O6 — histoire première canonique.
    PROOF_STRATEGY        : éliminer les divisibilités par 2 et 3, calculer les
                            quatre couples puis raisonner sur les chemins finis.
    REQUIRED_LEMMAS       : thm_primeAtRank_isPrime,
                            thm_primeAtRank_lt_successor
    WHY_EACH_LEMMA_EXISTS : primalité pour exclure 0/2/3/4 modulo 6 ; ordre
                            strict pour calculer le gap par soustraction Nat.
    LEAN_DEFINITION       : TPrimeTransition, PPrimeTransitionAtRank
    LEAN_THEOREM          : thm_transition_exhaustive, thm_transition_unique,
                            thm_class_projection_complete,
                            thm_gap_mod6_exhaustive,
                            thm_state_preserved_of_maintenance_run,
                            thm_change_skeleton_alternates
    SAME_MEMBER_CHECK     : sans objet, aucune donnée zêta.
    SAME_PASSAGE_CHECK    : chaque transition est indexée par une seule place.
    SAME_MIDDLE_CHECK     : deux rangs adjacents partagent définitionnellement
                            le premier médian de l'histoire.
    SAME_HISTORY_CHECK    : toutes les définitions utilisent `fnPrimeAtRank`.
    FORBIDDEN_PREMISES    : zéro, Tour, phase expérimentale, transition choisie.
    NEXT_CONSUMER         : projection grammaticale des places produites par T2.
    AXIOMS                : propext, Classical.choice, Quot.sound au plus.
    LEAN_STATUS           : CERTIFIED_ON_ROUTE

Ce module redémontre dans RHV3, sans importer le corpus historique, la grammaire
arithmétique des premiers successifs au-delà de 3 :

* chaque premier considéré a pour état modulo 6 `1` ou `5` ;
* les quatre transitions `1→1`, `1→5`, `5→1`, `5→5` sont exhaustives ;
* elles se projettent exactement sur les classes de gaps `0`, `4`, `2`, `0` modulo 6 ;
* tout bloc fini de gaps est un chemin de cette grammaire ;
* les transitions de maintenance (classe `0`) conservent l'état ;
* dans le squelette des changements, les classes `2` et `4` alternent.

Aucun zéro de zêta, aucune Tour, aucun contact, aucun comptage de cellule n'intervient.
-/

namespace RHV3Lean

/-- Les quatre transitions primitives de la grammaire modulo 6. -/
inductive TPrimeTransition where
  | keep11
  | switch15
  | switch51
  | keep55
  deriving DecidableEq, Repr

/-- Relation exacte entre une occurrence de rang et son type de transition. -/
def PPrimeTransitionAtRank (tTransition : TPrimeTransition) (nRank : ℕ) : Prop :=
  match tTransition with
  | .keep11 =>
      fnPrimeAtRank nRank % 6 = 1 ∧ fnPrimeSuccessor nRank % 6 = 1
  | .switch15 =>
      fnPrimeAtRank nRank % 6 = 1 ∧ fnPrimeSuccessor nRank % 6 = 5
  | .switch51 =>
      fnPrimeAtRank nRank % 6 = 5 ∧ fnPrimeSuccessor nRank % 6 = 1
  | .keep55 =>
      fnPrimeAtRank nRank % 6 = 5 ∧ fnPrimeSuccessor nRank % 6 = 5

/-- Tout premier strictement supérieur à `3` est congru à `1` ou `5` modulo `6`. -/
theorem thm_prime_gt_three_mod6_state
    {nPrime : ℕ} (hPrime : Nat.Prime nPrime) (hGtThree : 3 < nPrime) :
    nPrime % 6 = 1 ∨ nPrime % 6 = 5 := by
  have hNotDivTwo : nPrime % 2 ≠ 0 := by
    intro hEven
    have hDiv : 2 ∣ nPrime := Nat.dvd_of_mod_eq_zero hEven
    have hEq : 2 = nPrime := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hPrime).mp hDiv
    omega
  have hNotDivThree : nPrime % 3 ≠ 0 := by
    intro hThree
    have hDiv : 3 ∣ nPrime := Nat.dvd_of_mod_eq_zero hThree
    have hEq : 3 = nPrime :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three hPrime).mp hDiv
    omega
  omega

/-- Version sur l'histoire première canonique. -/
theorem thm_primeAtRank_mod6_state
    {nRank : ℕ} (hGtThree : 3 < fnPrimeAtRank nRank) :
    fnPrimeAtRank nRank % 6 = 1 ∨ fnPrimeAtRank nRank % 6 = 5 :=
  thm_prime_gt_three_mod6_state (thm_primeAtRank_isPrime nRank) hGtThree

/-- Si `p_n > 3`, son successeur est lui aussi `> 3`. -/
theorem thm_primeSuccessor_gt_three
    {nRank : ℕ} (hGtThree : 3 < fnPrimeAtRank nRank) :
    3 < fnPrimeSuccessor nRank :=
  lt_trans hGtThree (thm_primeAtRank_lt_successor nRank)

/-- Les quatre transitions épuisent toutes les occurrences au-delà de `3`. -/
theorem thm_transition_exhaustive
    {nRank : ℕ} (hGtThree : 3 < fnPrimeAtRank nRank) :
    PPrimeTransitionAtRank .keep11 nRank ∨
      PPrimeTransitionAtRank .switch15 nRank ∨
      PPrimeTransitionAtRank .switch51 nRank ∨
      PPrimeTransitionAtRank .keep55 nRank := by
  have hLeft := thm_primeAtRank_mod6_state hGtThree
  have hRight := thm_primeAtRank_mod6_state (thm_primeSuccessor_gt_three hGtThree)
  unfold PPrimeTransitionAtRank
  rcases hLeft with hL | hL <;> rcases hRight with hR | hR
  · exact Or.inl ⟨hL, hR⟩
  · exact Or.inr (Or.inl ⟨hL, hR⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hL, hR⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hL, hR⟩))

/-- Une occurrence de rang ne peut porter deux types de transition différents. -/
theorem thm_transition_unique
    {nRank : ℕ} {tLeft tRight : TPrimeTransition}
    (hLeft : PPrimeTransitionAtRank tLeft nRank)
    (hRight : PPrimeTransitionAtRank tRight nRank) :
    tLeft = tRight := by
  cases tLeft <;> cases tRight <;>
    simp only [PPrimeTransitionAtRank] at hLeft hRight ⊢ <;> omega

/-- La classe modulo 6 du gap et la transition se déterminent exactement. -/
theorem thm_class_projection_complete
    {nRank : ℕ} (hGtThree : 3 < fnPrimeAtRank nRank) :
    (nPrimeGap nRank % 6 = 0 ↔
      fnPrimeSuccessor nRank % 6 = fnPrimeAtRank nRank % 6) ∧
    (nPrimeGap nRank % 6 = 2 ↔
      (fnPrimeAtRank nRank % 6 = 5 ∧ fnPrimeSuccessor nRank % 6 = 1)) ∧
    (nPrimeGap nRank % 6 = 4 ↔
      (fnPrimeAtRank nRank % 6 = 1 ∧ fnPrimeSuccessor nRank % 6 = 5)) := by
  have hLeft := thm_primeAtRank_mod6_state hGtThree
  have hRight := thm_primeAtRank_mod6_state (thm_primeSuccessor_gt_three hGtThree)
  have hLt := thm_primeAtRank_lt_successor nRank
  let a := fnPrimeAtRank nRank
  let b := fnPrimeSuccessor nRank
  change
    ((b - a) % 6 = 0 ↔ b % 6 = a % 6) ∧
      ((b - a) % 6 = 2 ↔ (a % 6 = 5 ∧ b % 6 = 1)) ∧
      ((b - a) % 6 = 4 ↔ (a % 6 = 1 ∧ b % 6 = 5))
  change a % 6 = 1 ∨ a % 6 = 5 at hLeft
  change b % 6 = 1 ∨ b % 6 = 5 at hRight
  change a < b at hLt
  omega

/-- Les seules classes primitives de gaps au-delà de `3` sont `0`, `2`, `4`. -/
theorem thm_gap_mod6_exhaustive
    {nRank : ℕ} (hGtThree : 3 < fnPrimeAtRank nRank) :
    nPrimeGap nRank % 6 = 0 ∨
      nPrimeGap nRank % 6 = 2 ∨
      nPrimeGap nRank % 6 = 4 := by
  have hProjection := thm_class_projection_complete hGtThree
  rcases thm_transition_exhaustive hGtThree with h11 | h15 | h51 | h55
  · left
    apply hProjection.1.mpr
    simpa [PPrimeTransitionAtRank] using h11.2.trans h11.1.symm
  · right; right
    exact hProjection.2.2.mpr (by simpa [PPrimeTransitionAtRank] using h15)
  · right; left
    exact hProjection.2.1.mpr (by simpa [PPrimeTransitionAtRank] using h51)
  · left
    apply hProjection.1.mpr
    simpa [PPrimeTransitionAtRank] using h55.2.trans h55.1.symm

/-- La classe primitive du gap est unique. -/
theorem thm_gap_class_unique
    {nRank : ℕ} (hGtThree : 3 < fnPrimeAtRank nRank) :
    ∃! nClass : ℕ,
      nClass ∈ ({0, 2, 4} : Finset ℕ) ∧ nPrimeGap nRank % 6 = nClass := by
  refine ⟨nPrimeGap nRank % 6, ?_, ?_⟩
  · rcases thm_gap_mod6_exhaustive hGtThree with h0 | h2 | h4
    · simp [h0]
    · simp [h2]
    · simp [h4]
  · intro nClass hClass
    exact hClass.2.symm

/-- Chaque étape d'un bloc fini est un chemin de la même grammaire modulo 6. -/
theorem thm_pattern_is_grammar_path
    {nRank : ℕ} (hGtThree : 3 < fnPrimeAtRank nRank) (nLength : ℕ) :
    ∀ nOffset < nLength,
      (fnPrimeAtRank (nRank + nOffset) % 6 = 1 ∨
        fnPrimeAtRank (nRank + nOffset) % 6 = 5) ∧
      (fnPrimeSuccessor (nRank + nOffset) % 6 = 1 ∨
        fnPrimeSuccessor (nRank + nOffset) % 6 = 5) ∧
      ((nPrimeGap (nRank + nOffset) % 6 = 0 ↔
          fnPrimeSuccessor (nRank + nOffset) % 6 =
            fnPrimeAtRank (nRank + nOffset) % 6) ∧
       (nPrimeGap (nRank + nOffset) % 6 = 2 ↔
          (fnPrimeAtRank (nRank + nOffset) % 6 = 5 ∧
            fnPrimeSuccessor (nRank + nOffset) % 6 = 1)) ∧
       (nPrimeGap (nRank + nOffset) % 6 = 4 ↔
          (fnPrimeAtRank (nRank + nOffset) % 6 = 1 ∧
            fnPrimeSuccessor (nRank + nOffset) % 6 = 5))) := by
  intro nOffset _
  have hMono : fnPrimeAtRank nRank ≤ fnPrimeAtRank (nRank + nOffset) :=
    thm_primeAtRank_strictMono.monotone (Nat.le_add_right nRank nOffset)
  have hGtOffset : 3 < fnPrimeAtRank (nRank + nOffset) := lt_of_lt_of_le hGtThree hMono
  exact ⟨thm_primeAtRank_mod6_state hGtOffset,
    thm_primeAtRank_mod6_state (thm_primeSuccessor_gt_three hGtOffset),
    thm_class_projection_complete hGtOffset⟩

/-- Une suite de transitions de maintenance (classe `0`) conserve l'état modulo 6. -/
theorem thm_state_preserved_of_maintenance_run
    {nRank : ℕ} (hGtThree : 3 < fnPrimeAtRank nRank)
    (nStart nStop : ℕ) (hStartStop : nStart ≤ nStop)
    (hMaintenance : ∀ nOffset,
      nStart ≤ nOffset → nOffset < nStop →
        nPrimeGap (nRank + nOffset) % 6 = 0) :
    fnPrimeAtRank (nRank + nStop) % 6 =
      fnPrimeAtRank (nRank + nStart) % 6 := by
  induction nStop, hStartStop using Nat.le_induction with
  | base => rfl
  | succ nStop hStartStop hInduction =>
      have hGapZero : nPrimeGap (nRank + nStop) % 6 = 0 :=
        hMaintenance nStop hStartStop (Nat.lt_succ_self nStop)
      have hMono : fnPrimeAtRank nRank ≤ fnPrimeAtRank (nRank + nStop) :=
        thm_primeAtRank_strictMono.monotone (Nat.le_add_right nRank nStop)
      have hGtStep : 3 < fnPrimeAtRank (nRank + nStop) := lt_of_lt_of_le hGtThree hMono
      have hPreserved :
          fnPrimeSuccessor (nRank + nStop) % 6 =
            fnPrimeAtRank (nRank + nStop) % 6 :=
        (thm_class_projection_complete hGtStep).1.mp hGapZero
      have hSuccIndex : nRank + (nStop + 1) = nRank + nStop + 1 := by omega
      unfold fnPrimeSuccessor at hPreserved
      rw [hSuccIndex, hPreserved, hInduction]
      intro nOffset hLower hUpper
      exact hMaintenance nOffset hLower (by omega)

/-- Dans le squelette des changements, les classes `2` et `4` alternent. -/
theorem thm_change_skeleton_alternates
    {nRank : ℕ} (hGtThree : 3 < fnPrimeAtRank nRank)
    {nFirst nSecond : ℕ} (hFirstSecond : nFirst < nSecond)
    (hFirstChange : nPrimeGap (nRank + nFirst) % 6 ≠ 0)
    (hSecondChange : nPrimeGap (nRank + nSecond) % 6 ≠ 0)
    (hBetweenMaintenance : ∀ nOffset,
      nFirst < nOffset → nOffset < nSecond →
        nPrimeGap (nRank + nOffset) % 6 = 0) :
    (nPrimeGap (nRank + nFirst) % 6 = 2 ∧
      nPrimeGap (nRank + nSecond) % 6 = 4) ∨
    (nPrimeGap (nRank + nFirst) % 6 = 4 ∧
      nPrimeGap (nRank + nSecond) % 6 = 2) := by
  have hStateBridge :
      fnPrimeAtRank (nRank + nSecond) % 6 =
        fnPrimeAtRank (nRank + (nFirst + 1)) % 6 := by
    apply thm_state_preserved_of_maintenance_run hGtThree (nFirst + 1) nSecond (by omega)
    intro nOffset hLower hUpper
    exact hBetweenMaintenance nOffset (by omega) hUpper
  have hMonoFirst : fnPrimeAtRank nRank ≤ fnPrimeAtRank (nRank + nFirst) :=
    thm_primeAtRank_strictMono.monotone (Nat.le_add_right nRank nFirst)
  have hGtFirst : 3 < fnPrimeAtRank (nRank + nFirst) := lt_of_lt_of_le hGtThree hMonoFirst
  have hMonoSecond : fnPrimeAtRank nRank ≤ fnPrimeAtRank (nRank + nSecond) :=
    thm_primeAtRank_strictMono.monotone (Nat.le_add_right nRank nSecond)
  have hGtSecond : 3 < fnPrimeAtRank (nRank + nSecond) := lt_of_lt_of_le hGtThree hMonoSecond
  have hClassFirst := thm_gap_mod6_exhaustive hGtFirst
  have hClassSecond := thm_gap_mod6_exhaustive hGtSecond
  have hProjFirst := thm_class_projection_complete hGtFirst
  have hProjSecond := thm_class_projection_complete hGtSecond
  have hShift : nRank + (nFirst + 1) = nRank + nFirst + 1 := by omega
  rw [hShift] at hStateBridge
  unfold fnPrimeSuccessor at hProjFirst hProjSecond
  rcases hClassFirst with hFirst0 | hFirst2 | hFirst4
  · exact absurd hFirst0 hFirstChange
  · left
    refine ⟨hFirst2, ?_⟩
    have h51 := hProjFirst.2.1.mp hFirst2
    have hStateSecond : fnPrimeAtRank (nRank + nSecond) % 6 = 1 := by
      rw [hStateBridge, h51.2]
    rcases hClassSecond with hSecond0 | hSecond2 | hSecond4
    · exact absurd hSecond0 hSecondChange
    · have hImpossible := (hProjSecond.2.1.mp hSecond2).1
      omega
    · exact hSecond4
  · right
    refine ⟨hFirst4, ?_⟩
    have h15 := hProjFirst.2.2.mp hFirst4
    have hStateSecond : fnPrimeAtRank (nRank + nSecond) % 6 = 5 := by
      rw [hStateBridge, h15.2]
    rcases hClassSecond with hSecond0 | hSecond2 | hSecond4
    · exact absurd hSecond0 hSecondChange
    · exact hSecond2
    · have hImpossible := (hProjSecond.2.2.mp hSecond4).1
      omega

/-- Résumé machine de la grammaire première sur toute occurrence dont le premier d'entrée est `> 3`. -/
theorem thm_prime_transition_grammar_complete
    {nRank : ℕ} (hGtThree : 3 < fnPrimeAtRank nRank) :
    (PPrimeTransitionAtRank .keep11 nRank ∨
      PPrimeTransitionAtRank .switch15 nRank ∨
      PPrimeTransitionAtRank .switch51 nRank ∨
      PPrimeTransitionAtRank .keep55 nRank) ∧
    (nPrimeGap nRank % 6 = 0 ∨
      nPrimeGap nRank % 6 = 2 ∨
      nPrimeGap nRank % 6 = 4) ∧
    ((nPrimeGap nRank % 6 = 0 ↔
        fnPrimeSuccessor nRank % 6 = fnPrimeAtRank nRank % 6) ∧
      (nPrimeGap nRank % 6 = 2 ↔
        (fnPrimeAtRank nRank % 6 = 5 ∧ fnPrimeSuccessor nRank % 6 = 1)) ∧
      (nPrimeGap nRank % 6 = 4 ↔
        (fnPrimeAtRank nRank % 6 = 1 ∧ fnPrimeSuccessor nRank % 6 = 5))) :=
  ⟨thm_transition_exhaustive hGtThree,
    thm_gap_mod6_exhaustive hGtThree,
    thm_class_projection_complete hGtThree⟩

end RHV3Lean
