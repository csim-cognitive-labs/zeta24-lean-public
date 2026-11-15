/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.ZeroGapGrammar
import RHV3Lean.Objects.ZeroSourceReconstruction
import RHV3Lean.Objects.Passage

/-!
# RHV3Lean — l'identité d'un membre dans la source complète des zéros

    TRACE_ID              : RHV3-ZERO-SOURCE-OCCURRENCE
    SEMANTIC_OBJECT       : l'index zéro-source d'un membre — combien de
                            membres supérieurs le précèdent dans l'ordre
                            membre-sensible.
    SEMANTIC_STATEMENT    : un membre porte, depuis le seul côté zéro, sans
                            aucun premier, aucune cellule, aucun comptage
                            arithmétique, sa propre place dans l'ordre des
                            vrais zéros. C'est la première moitié — côté
                            source — de tout raccord membre-sensible ; elle ne
                            lit ni `nCellCentralPrime` ni `nCellCentralRank`.
    MATHEMATICAL_STATEMENT: nZeroSourceIndex(z) = card{w upper | w précède z} ;
                            fini par plongement dans la fenêtre symétrique de
                            L15 ; avance exactement de un sur un passage
                            consécutif authentique ; strictement monotone et
                            injectif sur la branche supérieure.
    MATHEMATICAL_PARENT   : O7 (la grammaire des écarts de zéros), L15 (la
                            fenêtre symétrique finie de la source complète).
    PROOF_STRATEGY        : le sous-ensemble des membres précédant `z` se
                            plonge, par le support complexe, dans la fenêtre
                            symétrique déjà prouvée finie en L15 ; l'avance de
                            un sur un passage consécutif vient de l'égalité
                            explicite `sUpperZerosBelow zLater = insert
                            zEarlier (sUpperZerosBelow zEarlier)` ; monotonie
                            et injectivité viennent de l'inclusion stricte des
                            mêmes ensembles.
    REQUIRED_LEMMAS       : thm_symmetricZeroWindow_finite (L15),
                            thm_zeroMemberPrecedes_iff_height_radial_lex,
                            thm_distinctZeroMembers_comparable,
                            thm_zeroMemberPrecedes_transitive,
                            thm_zeroMemberPrecedes_irreflexive
    WHY_EACH_LEMMA_EXISTS : le premier donne la finitude par plongement dans
                            un compact déjà traité ; les quatre suivants
                            donnent la trichotomie, la transitivité et
                            l'irréflexivité de l'ordre membre-sensible, sans
                            lesquelles ni l'avance de un ni la stricte
                            monotonie ne se prouvent.
    LEAN_DEFINITION       : sUpperZerosBelow, nZeroSourceIndex
    LEAN_THEOREM          : thm_upperZerosBelow_finite,
                            thm_upperZerosBelow_of_consecutive,
                            thm_zeroSourceIndex_succ_of_consecutive,
                            thm_upperZerosBelow_subset_of_precedes,
                            thm_upperZerosBelow_ssubset_of_precedes,
                            thm_zeroSourceIndex_strictMono,
                            thm_zeroSourceIndex_injective
    SAME_MEMBER_CHECK     : l'index est une fonction du seul membre, jamais
                            d'une cellule ou d'un premier.
    SAME_PASSAGE_CHECK    : l'avance de un est lue sur le passage réel complet
                            (`PZeroMembersConsecutive`), jamais sur un simple
                            écart de hauteur.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre ici, par
                            construction.
    FORBIDDEN_PREMISES    : lire `nCellCentralPrime`, `nCellCentralRank`,
                            `nCellFoundCount`, ou toute quantité de comptage
                            arithmétique dans la définition de cet index ;
                            poser `nZeroSourceIndex z = rang premier` comme
                            hypothèse.
    NEXT_CONSUMER         : `MemberSensitiveMZCorrespondence`, qui lit ce seul
                            index pour construire l'occurrence reconstruite
                            d'un membre dans M^Z.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau. Ce module ne construit
JAMAIS l'objet `TPrimeOccurrence` de l'ancien module `PrimeOccurrence.lean` :
il ne le réutilise pas, il ne l'étend pas, il reconstruit depuis zéro le seul
côté zéro-source du raccord.
-/

namespace RHV3Lean

/-! ## 1. Le sous-ensemble zéro-source qui précède strictement un membre -/

/-- Les membres supérieurs qui précèdent strictement `z`, dans l'ordre
membre-sensible du côté zéro seul. -/
def sUpperZerosBelow (z : TNonTrivialZetaZero) : Set TNonTrivialZetaZero :=
  {w | 0 < rZeroHeight w ∧ PZeroMemberPrecedes w z}

/-- **Finitude par plongement dans la fenêtre symétrique de L15.**  Tout membre
qui précède `z` et qui est supérieur a une hauteur strictement positive et
inférieure ou égale à celle de `z` — donc son support tombe dans la fenêtre
symétrique de cutoff `rZeroHeight z`, déjà prouvée finie sans aucune hypothèse
supplémentaire. -/
theorem thm_upperZerosBelow_finite (z : TNonTrivialZetaZero) :
    (sUpperZerosBelow z).Finite := by
  have hSubset :
      cZeroSupport '' sUpperZerosBelow z ⊆
        (finsetSymmetricZeroWindow (rZeroHeight z) : Set ℂ) := by
    rintro cPoint ⟨w, ⟨hPos, hPrec⟩, rfl⟩
    rw [Finset.mem_coe, thm_mem_finsetSymmetricZeroWindow]
    refine ⟨w.2, ?_⟩
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex] at hPrec
    have hLe : rZeroHeight w ≤ rZeroHeight z := by
      rcases hPrec with hStrict | hEqual
      · exact le_of_lt hStrict
      · exact le_of_eq hEqual.1
    show |(cZeroSupport w).im| ≤ rZeroHeight z
    have hPos' : (0 : ℝ) < (cZeroSupport w).im := hPos
    rw [abs_of_pos hPos']
    exact hLe
  have hInjective : Function.Injective cZeroSupport := fun a b h => Subtype.ext h
  exact Set.Finite.of_finite_image
    ((finsetSymmetricZeroWindow (rZeroHeight z)).finite_toSet.subset hSubset)
    hInjective.injOn

/-- **L'index zéro-source du membre** : combien de membres supérieurs le
précèdent. Aucun premier, aucune cellule, aucun rang arithmétique n'entre dans
cette définition. -/
noncomputable def nZeroSourceIndex (z : TNonTrivialZetaZero) : ℕ :=
  (thm_upperZerosBelow_finite z).toFinset.card

/-! ## 2. Un passage consécutif authentique avance l'index de un -/

theorem thm_upperZerosBelow_of_consecutive
    {zEarlier zLater : TNonTrivialZetaZero}
    (hEarlierUpper : 0 < rZeroHeight zEarlier)
    (hConsecutive : PZeroMembersConsecutive zEarlier zLater) :
    sUpperZerosBelow zLater = insert zEarlier (sUpperZerosBelow zEarlier) := by
  ext w
  constructor
  · rintro ⟨hUpper, hLt⟩
    by_cases hEq : w = zEarlier
    · exact hEq ▸ Set.mem_insert _ _
    · rcases thm_distinctZeroMembers_comparable hEq with hBefore | hAfter
      · exact Set.mem_insert_of_mem _ ⟨hUpper, hBefore⟩
      · exact absurd ⟨w, hAfter, hLt⟩ hConsecutive.2
  · intro hMem
    rcases Set.mem_insert_iff.mp hMem with hEq | ⟨hUpper, hBefore⟩
    · exact hEq ▸ ⟨hEarlierUpper, hConsecutive.1⟩
    · exact ⟨hUpper, thm_zeroMemberPrecedes_transitive hBefore hConsecutive.1⟩

/-- **L'index avance exactement de un sur un passage consécutif authentique.**
Théorème, jamais hypothèse : la donnée d'un vrai passage consécutif suffit. -/
theorem thm_zeroSourceIndex_succ_of_consecutive
    {zEarlier zLater : TNonTrivialZetaZero}
    (hEarlierUpper : 0 < rZeroHeight zEarlier)
    (hConsecutive : PZeroMembersConsecutive zEarlier zLater) :
    nZeroSourceIndex zLater = nZeroSourceIndex zEarlier + 1 := by
  classical
  have hSet := thm_upperZerosBelow_of_consecutive hEarlierUpper hConsecutive
  have hNotMem : zEarlier ∉ (thm_upperZerosBelow_finite zEarlier).toFinset := by
    simp only [Set.Finite.mem_toFinset, sUpperZerosBelow, Set.mem_setOf_eq]
    intro h
    exact thm_zeroMemberPrecedes_irreflexive zEarlier h.2
  have hFinsetEq :
      (thm_upperZerosBelow_finite zLater).toFinset =
        insert zEarlier (thm_upperZerosBelow_finite zEarlier).toFinset := by
    ext w
    simp [Set.Finite.mem_toFinset, hSet]
  rw [nZeroSourceIndex, nZeroSourceIndex, hFinsetEq,
    Finset.card_insert_of_notMem hNotMem]

/-- Passage form of the same transport law. -/
theorem thm_zeroSourceIndex_succ_of_passage
    (tPassage : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight tPassage.zEarlierMember) :
    nZeroSourceIndex tPassage.zLaterMember =
      nZeroSourceIndex tPassage.zEarlierMember + 1 :=
  thm_zeroSourceIndex_succ_of_consecutive hEarlierUpper tPassage.hConsecutive

/-! ## 3. Stricte monotonie et injectivité sur la branche supérieure -/

theorem thm_upperZerosBelow_subset_of_precedes
    {z1 z2 : TNonTrivialZetaZero}
    (h1 : 0 < rZeroHeight z1) (hLt : PZeroMemberPrecedes z1 z2) :
    sUpperZerosBelow z1 ⊆ sUpperZerosBelow z2 := by
  intro w hw
  exact ⟨hw.1, thm_zeroMemberPrecedes_transitive hw.2 hLt⟩

theorem thm_upperZerosBelow_ssubset_of_precedes
    {z1 z2 : TNonTrivialZetaZero}
    (h1 : 0 < rZeroHeight z1) (hLt : PZeroMemberPrecedes z1 z2) :
    sUpperZerosBelow z1 ⊂ sUpperZerosBelow z2 := by
  rw [Set.ssubset_iff_of_subset (thm_upperZerosBelow_subset_of_precedes h1 hLt)]
  exact ⟨z1, ⟨h1, hLt⟩, fun hSelf => thm_zeroMemberPrecedes_irreflexive z1 hSelf.2⟩

theorem thm_zeroSourceIndex_strictMono
    {z1 z2 : TNonTrivialZetaZero}
    (h1 : 0 < rZeroHeight z1) (hLt : PZeroMemberPrecedes z1 z2) :
    nZeroSourceIndex z1 < nZeroSourceIndex z2 := by
  have hSSubset := thm_upperZerosBelow_ssubset_of_precedes h1 hLt
  have hFinsetSSubset :
      (thm_upperZerosBelow_finite z1).toFinset ⊂
        (thm_upperZerosBelow_finite z2).toFinset :=
    Set.Finite.toFinset_ssubset_toFinset.mpr hSSubset
  exact Finset.card_lt_card hFinsetSSubset

theorem thm_zeroSourceIndex_injective
    {z1 z2 : TUpperNonTrivialZetaZero}
    (h : nZeroSourceIndex z1.1 = nZeroSourceIndex z2.1) : z1 = z2 := by
  by_cases hEq : z1.1 = z2.1
  · exact Subtype.ext hEq
  · rcases thm_distinctZeroMembers_comparable hEq with hLt | hGt
    · exact absurd h (ne_of_lt (thm_zeroSourceIndex_strictMono z1.2 hLt))
    · exact absurd h.symm (ne_of_lt (thm_zeroSourceIndex_strictMono z2.2 hGt))

#check thm_upperZerosBelow_finite
#check thm_zeroSourceIndex_succ_of_consecutive
#check thm_zeroSourceIndex_succ_of_passage
#check thm_zeroSourceIndex_strictMono
#check thm_zeroSourceIndex_injective

end RHV3Lean
