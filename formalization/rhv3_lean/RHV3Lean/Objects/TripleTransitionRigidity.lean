/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.Triple
import RHV3Lean.Objects.PlaceAndLocalLaw
import RHV3Lean.Objects.OffFibreAndPassage

/-!
# RHV3Lean — rigidité des TRANSITIONS du triple

Correction de fidélité du tour T06 : l'événement rigide est la TRANSITION
complète. Une transition zéro n'est jamais réduite à son gap ni à une paire de
hauteurs ; elle conserve le passage source et ses deux membres. Les hauteurs ne
sont qu'un observable de cet événement.

Cette couche matérialise :

* les deux transitions zéro du même triple `Z0 -> Z1 -> Z2` ;
* les trois premiers `p_r,p_(r+1),p_(r+2)` et leurs deux transitions ;
* SAME-MIDDLE des deux côtés ;
* la stricte non-diagonalité des transitions premières ;
* l'existence sous OFF d'une vraie transition zéro dont l'observable hauteur
  est diagonal.

Le raccord T2 entre la transition source et une occurrence première n'est pas
une conséquence de `M^Z = M`, qui porte seulement sur les suites premières
reconstruites. L'égalité isolée de deux C3 n'est pas une cible active. Voir
`TerminalCoreStrength` pour la mesure formelle de la force du raccord demandé.

Aucun `sorry`, aucun `admit`, aucun nouvel axiome.

    TRACE_ID              : RHV3-TRIPLE-TRANSITION-RIGIDITY
    SEMANTIC_OBJECT       : deux transitions complètes du même vrai triple et
                            deux transitions de trois premiers successifs
    SEMANTIC_STATEMENT    : la transition zéro conserve son passage complet ;
                            sa hauteur n'est qu'un observable, et SAME-MIDDLE
                            est définitionnel des deux côtés
    MATHEMATICAL_STATEMENT: (Z0,Z1),(Z1,Z2) et
                            (p_r,p_(r+1)),(p_(r+1),p_(r+2)), avec stricte
                            croissance des trois premiers
    MATHEMATICAL_PARENT   : O9 triple, O8 passage, O6 histoire première
    PROOF_STRATEGY        : projections des structures du triple et stricte
                            monotonie de la suite canonique des premiers
    REQUIRED_LEMMAS       : thm_primeAtRank_strictMono,
                            thm_offCriticalLine_existsNullPassage
    WHY_EACH_LEMMA_EXISTS : le premier interdit toute transition première
                            diagonale ; le second produit une vraie transition
                            source à gap de hauteur nul sous OFF
    LEAN_DEFINITION       : TZeroTransitionEvent, TPrimeTransitionEvent,
                            tZeroTripleTransitions, tPrimeTripleTransitions
    LEAN_THEOREM          : thm_zeroTransition_heightDegenerate_iff_sameHeight,
                            thm_threeCanonicalPrimes_strict,
                            thm_primeTripleTransitions_notDiagonal,
                            thm_off_existsHeightDegenerateZeroTransition
    SAME_MEMBER_CHECK     : chaque transition zéro projette les membres de son
                            propre passage
    SAME_PASSAGE_CHECK    : la dégénérescence est projetée du même passage OFF
    SAME_MIDDLE_CHECK     : les deux égalités SAME-MIDDLE sont des `rfl`
    SAME_HISTORY_CHECK    : les deux transitions premières utilisent les rangs
                            adjacents r et r+1 de l'histoire canonique
    FORBIDDEN_PREMISES    : RH, collision C3, conversion gap-vers-diagonale,
                            nullité stockée comme conclusion
    NEXT_CONSUMER         : attachement T2 concret puis conversion éventuelle
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : STRUCTURAL_BODIES_PRODUCED_NO_T2_CONVERSION
-/

namespace RHV3Lean

/-! ## 1. Transition source-sensible côté zéro -/

/-- Une transition zéro EST le passage réel complet qui la porte. -/
structure TZeroTransitionEvent where
  passage : TZeroPassage

/-- Construction canonique de l'événement depuis le passage lui-même. -/
def tZeroTransitionEvent (E : TZeroPassage) : TZeroTransitionEvent := ⟨E⟩

namespace TZeroTransitionEvent

variable (E : TZeroTransitionEvent)

/-- Membre d'entrée de la transition. -/
def entryMember : TNonTrivialZetaZero := E.passage.zEarlierMember

/-- Membre de sortie de la transition. -/
def exitMember : TNonTrivialZetaZero := E.passage.zLaterMember

/-- Observable hauteur à l'entrée. -/
def entryHeight : ℝ := rZeroHeight E.entryMember

/-- Observable hauteur à la sortie. -/
def exitHeight : ℝ := rZeroHeight E.exitMember

/-- Dégénérescence de l'observable hauteur de CETTE transition. -/
def PHeightDegenerate : Prop := E.entryHeight = E.exitHeight

end TZeroTransitionEvent

/-- Les deux événements de transition du même triple. -/
def tZeroTripleTransitions (three : TThreeConsecutiveZeros) :
    TZeroTransitionEvent × TZeroTransitionEvent :=
  (tZeroTransitionEvent (tEarlierPassage three),
    tZeroTransitionEvent (tLaterPassage three))

/-- SAME-MIDDLE côté zéro : le même membre est sortie de la première transition
et entrée de la seconde. -/
@[simp] theorem thm_zeroTripleTransitions_sharedMiddle
    (three : TThreeConsecutiveZeros) :
    (tZeroTripleTransitions three).1.exitMember =
      (tZeroTripleTransitions three).2.entryMember :=
  rfl

/-- La dégénérescence en hauteur est exactement l'égalité des hauteurs des deux
membres propres de la transition ; elle n'est pas stockée comme hypothèse. -/
theorem thm_zeroTransition_heightDegenerate_iff_sameHeight
    (E : TZeroTransitionEvent) :
    E.PHeightDegenerate ↔
      rZeroHeight E.passage.zEarlierMember =
        rZeroHeight E.passage.zLaterMember :=
  Iff.rfl

/-! ## 2. Trois premiers et leurs deux événements de transition -/

/-- Une transition de l'histoire première est identifiée par son rang d'entrée. -/
structure TPrimeTransitionEvent where
  rank : ℕ

namespace TPrimeTransitionEvent

variable (E : TPrimeTransitionEvent)

/-- Premier d'entrée. -/
noncomputable def entryPrime : ℕ := fnPrimeAtRank E.rank

/-- Premier de sortie, successeur canonique. -/
noncomputable def exitPrime : ℕ := fnPrimeAtRank (E.rank + 1)

/-- Une transition première serait diagonale si ses deux premiers coïncidaient. -/
def PDiagonal : Prop := E.entryPrime = E.exitPrime

end TPrimeTransitionEvent

/-- Première transition d'un triple premier commençant au rang `r`. -/
def tPrimeTransitionAt (r : ℕ) : TPrimeTransitionEvent := ⟨r⟩

/-- Les deux transitions adjacentes portées par trois premiers successifs. -/
def tPrimeTripleTransitions (r : ℕ) :
    TPrimeTransitionEvent × TPrimeTransitionEvent :=
  (tPrimeTransitionAt r, tPrimeTransitionAt (r + 1))

/-- Les trois sommets premiers explicites. -/
noncomputable def nTriplePrime0 (r : ℕ) : ℕ := (tPrimeTransitionAt r).entryPrime
noncomputable def nTriplePrime1 (r : ℕ) : ℕ := (tPrimeTransitionAt r).exitPrime
noncomputable def nTriplePrime2 (r : ℕ) : ℕ := (tPrimeTransitionAt (r + 1)).exitPrime

/-- SAME-MIDDLE côté premier. -/
@[simp] theorem thm_primeTripleTransitions_sharedMiddle (r : ℕ) :
    (tPrimeTripleTransitions r).1.exitPrime =
      (tPrimeTripleTransitions r).2.entryPrime :=
  rfl

/-- Les trois premiers progressent strictement. -/
theorem thm_threeCanonicalPrimes_strict (r : ℕ) :
    nTriplePrime0 r < nTriplePrime1 r ∧
      nTriplePrime1 r < nTriplePrime2 r := by
  constructor
  · exact thm_primeAtRank_strictMono (Nat.lt_succ_self r)
  · exact thm_primeAtRank_strictMono (Nat.lt_succ_self (r + 1))

/-- Aucune transition première canonique n'est diagonale. -/
theorem thm_primeTransition_notDiagonal (E : TPrimeTransitionEvent) :
    ¬ E.PDiagonal := by
  exact ne_of_lt (thm_primeAtRank_strictMono (Nat.lt_succ_self E.rank))

/-- Les deux transitions du triple premier sont simultanément non diagonales. -/
theorem thm_primeTripleTransitions_notDiagonal (r : ℕ) :
    ¬ (tPrimeTripleTransitions r).1.PDiagonal ∧
      ¬ (tPrimeTripleTransitions r).2.PDiagonal :=
  ⟨thm_primeTransition_notDiagonal _, thm_primeTransition_notDiagonal _⟩

/-! ## 3. OFF détruit l'observable hauteur d'une vraie transition zéro -/

/-- OFF produit une vraie transition zéro consécutive dont l'entrée et la sortie
ont la même hauteur. L'événement reste le passage complet ; seule cette
projection est diagonale. -/
theorem thm_off_existsHeightDegenerateZeroTransition
    {zZero : TNonTrivialZetaZero} (hOff : PIsOffCriticalLine zZero) :
    ∃ E : TZeroTransitionEvent, E.PHeightDegenerate := by
  obtain ⟨P, hGapZero, _⟩ := thm_offCriticalLine_existsNullPassage hOff
  refine ⟨tZeroTransitionEvent P, ?_⟩
  have hNull : PZeroPassageRelationNull P := hGapZero
  exact (thm_zeroPassage_null_iff_sameHeight P).mp hNull

/-! ## 4. Consumer logique conditionnel, hors du cône terminal -/

/-- Si une loi externe transportait la dégénérescence de chaque événement vers
une transition première, OFF serait impossible. Cette signature mesure la
force de cette loi ; elle n'est ni un producteur T2 ni une conséquence de
`M^Z=M`. -/
theorem thm_off_impossible_of_transitionDegeneracyTransport
    {zZero : TNonTrivialZetaZero} (hOff : PIsOffCriticalLine zZero)
    (hTransitionTransport :
      ∀ E : TZeroTransitionEvent,
        E.PHeightDegenerate →
          ∃ P : TPrimeTransitionEvent, P.PDiagonal) : False := by
  obtain ⟨E, hDegenerate⟩ := thm_off_existsHeightDegenerateZeroTransition hOff
  obtain ⟨P, hDiagonal⟩ := hTransitionTransport E hDegenerate
  exact thm_primeTransition_notDiagonal P hDiagonal

end RHV3Lean
