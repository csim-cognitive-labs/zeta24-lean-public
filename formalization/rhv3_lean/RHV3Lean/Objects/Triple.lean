/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.Passage

/-!
# RHV3Lean — O9, le triple

    TRACE_ID              : RHV3-O9
    SEMANTIC_OBJECT       : O9 — le triple
    SEMANTIC_STATEMENT    : trois vrais zéros consécutifs forment l'objet
                            unitaire minimal de composition, porteur de deux
                            passages liés par un seul membre médian partagé,
                            strictement identique dans les deux passages.
    MATHEMATICAL_STATEMENT: Z0, Z1, Z2 consécutifs portant E0 = (Z0, Z1) et
                            E1 = (Z1, Z2), avec Z1 le même objet dans E0 et E1,
                            et aucune moyenne de d0, d1 ne remplaçant le couple
                            (d0, d1).
    MATHEMATICAL_PARENT   : O8 — le passage.
    PROOF_STRATEGY        : le triple stocke ses trois membres et ses deux
                            consécutivités ; les deux passages sont construits
                            sur le MÊME champ médian, de sorte que le partage du
                            membre médian est définitionnel et non un énoncé à
                            vérifier ; les deux écarts sont lus séparément sur
                            les deux passages.
    REQUIRED_LEMMAS       : thm_zeroPassage_heightGap_nonnegative
    WHY_EACH_LEMMA_EXISTS : ce lemme donne la non-négativité des deux écarts,
                            acquise en O7.
    LEAN_DEFINITION       : TThreeConsecutiveZeros, tEarlierPassage,
                            tLaterPassage, rEarlierZeroHeightGap,
                            rLaterZeroHeightGap
    LEAN_THEOREM          : thm_triple_sameMiddleMember,
                            thm_triple_twoHeightGaps_nonnegative,
                            thm_triple_members_pairwiseDistinct,
                            thm_triple_mean_does_not_determine_pair
    SAME_MEMBER_CHECK     : les trois membres du triple sont ses propres champs.
    SAME_PASSAGE_CHECK    : chaque écart est lu sur son propre passage, jamais
                            par comparaison entre les deux.
    SAME_MIDDLE_CHECK     : thm_triple_sameMiddleMember est vrai par `rfl` : le
                            membre médian est littéralement le même champ dans
                            les deux passages, il n'est pas recollé après coup.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre ici ; le type des
                            images du transport reste abstrait.
    FORBIDDEN_PREMISES    : remplacer le couple des deux écarts par leur moyenne
                            ou leur somme ; reconstruire le membre médian par
                            une égalité prouvée au lieu de le partager ; poser
                            la positivité d'un écart comme prémisse.
    NEXT_CONSUMER         : la Tour harmonique et, plus loin, la loi locale du
                            transport puis la contradiction OFF.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

/-! ## 1. Le triple, et ses deux passages -/

/-- **Trois vrais zéros consécutifs**, l'objet unitaire minimal de
composition. -/
structure TThreeConsecutiveZeros where
  /-- Le membre antérieur. -/
  zEarlierZero : TNonTrivialZetaZero
  /-- Le membre médian, partagé par les deux passages. -/
  zMiddleZero : TNonTrivialZetaZero
  /-- Le membre tardif. -/
  zLaterZero : TNonTrivialZetaZero
  /-- Premier voisinage. -/
  hEarlierMiddleConsecutive : PZeroMembersConsecutive zEarlierZero zMiddleZero
  /-- Second voisinage. -/
  hMiddleLaterConsecutive : PZeroMembersConsecutive zMiddleZero zLaterZero

/-- Le passage du membre antérieur vers le membre médian. -/
def tEarlierPassage (tThree : TThreeConsecutiveZeros) : TZeroPassage :=
  ⟨tThree.zEarlierZero, tThree.zMiddleZero, tThree.hEarlierMiddleConsecutive⟩

/-- Le passage du MÊME membre médian vers le membre tardif. -/
def tLaterPassage (tThree : TThreeConsecutiveZeros) : TZeroPassage :=
  ⟨tThree.zMiddleZero, tThree.zLaterZero, tThree.hMiddleLaterConsecutive⟩

/-! ## 2. Rigidité — le membre médian est le même objet dans les deux passages -/

/-- **RIGIDITE — SAME-MIDDLE, définitionnel.**

L'extrémité de sortie du premier passage et l'extrémité d'entrée du second sont
littéralement le même champ du même triple.  Ce n'est pas une égalité obtenue
après coup entre deux membres qui se ressembleraient : c'est le même objet, et
aucune étape en aval ne peut les disjoindre. -/
theorem thm_triple_sameMiddleMember (tThree : TThreeConsecutiveZeros) :
    (tEarlierPassage tThree).zLaterMember =
        (tLaterPassage tThree).zEarlierMember ∧
      (tEarlierPassage tThree).zLaterMember = tThree.zMiddleZero :=
  ⟨rfl, rfl⟩

/-- Les extrémités des deux passages sont exactement les trois membres du
triple, dans l'ordre. -/
theorem thm_triple_passages_endpoints (tThree : TThreeConsecutiveZeros) :
    (tEarlierPassage tThree).zEarlierMember = tThree.zEarlierZero ∧
      (tLaterPassage tThree).zLaterMember = tThree.zLaterZero :=
  ⟨rfl, rfl⟩

/-- Les trois membres d'un triple sont deux à deux distincts. -/
theorem thm_triple_members_pairwiseDistinct (tThree : TThreeConsecutiveZeros) :
    tThree.zEarlierZero ≠ tThree.zMiddleZero ∧
      tThree.zMiddleZero ≠ tThree.zLaterZero ∧
        tThree.zEarlierZero ≠ tThree.zLaterZero := by
  refine ⟨thm_consecutive_members_distinct tThree.hEarlierMiddleConsecutive,
    thm_consecutive_members_distinct tThree.hMiddleLaterConsecutive, ?_⟩
  intro hSame
  have hChain : PZeroMemberPrecedes tThree.zEarlierZero tThree.zLaterZero :=
    thm_zeroMemberPrecedes_transitive tThree.hEarlierMiddleConsecutive.1
      tThree.hMiddleLaterConsecutive.1
  exact thm_zeroMemberPrecedes_irreflexive tThree.zLaterZero (hSame ▸ hChain)

/-! ## 3. Les deux écarts, pris séparément -/

/-- L'écart du premier passage. -/
def rEarlierZeroHeightGap (tThree : TThreeConsecutiveZeros) : ℝ :=
  rZeroPassageHeightGap (tEarlierPassage tThree)

/-- L'écart du second passage. -/
def rLaterZeroHeightGap (tThree : TThreeConsecutiveZeros) : ℝ :=
  rZeroPassageHeightGap (tLaterPassage tThree)

/-- **Les deux écarts du triple sont non négatifs.**  Acquis en O7, lu
séparément sur chacun des deux passages. -/
theorem thm_triple_twoHeightGaps_nonnegative (tThree : TThreeConsecutiveZeros) :
    0 ≤ rEarlierZeroHeightGap tThree ∧ 0 ≤ rLaterZeroHeightGap tThree :=
  ⟨thm_zeroPassage_heightGap_nonnegative _,
    thm_zeroPassage_heightGap_nonnegative _⟩

/-- **RIGIDITE — aucune moyenne ne remplace le couple.**

Contrôle explicite : la moyenne de deux écarts ne détermine pas le couple.  Deux
couples distincts partagent la même moyenne, donc toute étape qui remplacerait
`(d0, d1)` par leur moyenne perdrait de l'information sur le triple.  Le couple
est donc conservé partout, et les deux écarts sont toujours conclus séparément. -/
theorem thm_triple_mean_does_not_determine_pair (rMean : ℝ) :
    ∃ pLeftPair pRightPair : ℝ × ℝ,
      pLeftPair ≠ pRightPair ∧
        (pLeftPair.1 + pLeftPair.2) / 2 = rMean ∧
          (pRightPair.1 + pRightPair.2) / 2 = rMean := by
  refine ⟨(rMean, rMean), (rMean - 1, rMean + 1), ?_, by ring, by ring⟩
  intro hEqual
  have hFirst : rMean = rMean - 1 := congrArg Prod.fst hEqual
  linarith

end RHV3Lean
