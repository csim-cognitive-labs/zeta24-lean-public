/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.CanonicalT2
import RHV3Lean.Objects.SamePrimeCollision
import RHV3Lean.Objects.OffFibreAndPassage

/-!
# RHV3Lean — T2 étendu à toute la fibre finie contredit la collision miroir

    TRACE_ID              : RHV3-OFF-T2-CHAIN-VS-MIRROR-COLLISION
    SEMANTIC_OBJECT       : la contradiction entre `PCanonicalSuccession` (T2,
                            sur tout `TZeroPassage` réel) étendu le long de la
                            fibre finie de hauteur, et `PMirrorCollision` --
                            sans jamais construire de passage non consécutif
                            entre l'original et son miroir.
    SEMANTIC_STATEMENT    : dans la fibre finie de hauteur de la paire miroir
                            (`OffFibreAndPassage.lean`), l'original et le
                            miroir sont deux membres distincts, donc comparables
                            par l'ordre membre-sensible. Si l'un précède
                            l'autre à travers zéro, un ou plusieurs membres
                            intermédiaires réels de la MÊME fibre, chaque
                            passage entre deux membres immédiatement consécutifs
                            de cette chaîne finie est un vrai `TZeroPassage`,
                            auquel T2 s'applique déjà tel quel. La composition
                            de ces inégalités strictes donne le premier central
                            de l'un STRICTEMENT plus grand que celui de l'autre
                            -- jamais une égalité. `PMirrorCollision` affirme
                            l'égalité : contradiction. Un ou plusieurs membres
                            intermédiaires ne rendent la contradiction que PLUS
                            forte, jamais plus faible.
    MATHEMATICAL_STATEMENT: (PCanonicalSuccession) ET (PMirrorCollision)
                            impliquent, pour tout `zOff`,
                            C3(original) < C3(miroir) ET C3(original) =
                            C3(miroir) -- faux.
    MATHEMATICAL_PARENT   : `CanonicalT2.lean` (`thm_T2_order`, sur `TZeroPassage`
                            SEUL, jamais un `TTowerMemberTransition` non
                            consécutif) ; `OffFibreAndPassage.lean` (finitude de
                            la fibre, extraction de voisin immédiat) ;
                            `SamePrimeCollision.lean` (`PMirrorCollision`,
                            `thm_offMirror_distinct`, `thm_offMirror_sameHeight`).
    PROOF_STRATEGY        : récursion forte sur le cardinal (fini) de l'ensemble
                            des membres strictement compris entre le membre
                            courant et la cible, dans la fibre. À chaque étape,
                            le voisin immédiat du membre courant (extrait comme
                            dans `thm_existsConsecutiveInFiber`, mais borné par
                            la cible) donne un vrai passage consécutif, auquel
                            T2 s'applique ; la récursion avance strictement vers
                            la cible, ou l'atteint directement.
    REQUIRED_LEMMAS       : thm_zeroHeightFiber_finite, thm_sameFiberInterposition,
                            thm_distinctZeroMembers_comparable,
                            thm_zeroOrderKey_injective, thm_T2_order,
                            thm_offMirror_distinct, thm_offMirror_sameHeight,
                            thm_upperRepresentativeMember_of_positiveHeight
    WHY_EACH_LEMMA_EXISTS : les trois premiers construisent et bornent le
                            voisin immédiat à chaque étape de la récursion ;
                            le quatrième distingue l'égalité de clé de l'atteinte
                            de la cible ; le cinquième est T2 lui-même, appliqué
                            au SEUL passage réel produit à chaque étape ; les deux
                            derniers relient l'original/le miroir (branche
                            supérieure) à la forme générale sur `TNonTrivialZetaZero`
                            que T2 consomme.
    SAME_MEMBER_CHECK     : chaque application de T2 porte sur un unique passage
                            réel dont les deux extrémités sont ses propres
                            membres consécutifs -- jamais l'original et le
                            miroir directement s'il existe un intermédiaire.
    SAME_PASSAGE_CHECK    : à chaque étape, l'inégalité stricte vient du MÊME
                            passage consécutif que celui construit à cette étape.
    SAME_MIDDLE_CHECK      : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : l'unique histoire première de O6, comme partout
                            ailleurs.
    FORBIDDEN_PREMISES    : toute hypothèse d'unicité de la paire à cette
                            hauteur ; `PT2AppliesToOffTransition` sur le
                            `TTowerMemberTransition` non consécutif
                            original->miroir ; RH ou sa négation comme prémisse.
    NEXT_CONSUMER         : `riemannHypothesis_of_T1_T2_mirrorCollision`, la
                            fermeture terminale sur exactement les trois
                            prémisses nommées T1/T2/PMirrorCollision.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-! ## 1. Le voisin immédiat, borné par une cible dans la même fibre -/

/-- **Le voisin immédiat de `zLeft`, borné par `zRight`.**  Comme
`thm_existsConsecutiveInFiber`, mais avec la garantie supplémentaire que ce
voisin ne dépasse jamais `zRight` : soit il L'ATTEINT exactement, soit il lui
reste strictement antérieur. -/
private theorem exists_bounded_immediate_successor
    {zLeft zRight : TNonTrivialZetaZero}
    (hPrecedes : PZeroMemberPrecedes zLeft zRight)
    (hSameHeight : rZeroHeight zLeft = rZeroHeight zRight) :
    ∃ zMid : TNonTrivialZetaZero,
      rZeroHeight zMid = rZeroHeight zLeft ∧
        PZeroMembersConsecutive zLeft zMid ∧
          (zMid = zRight ∨ PZeroMemberPrecedes zMid zRight) := by
  classical
  set rHeight := rZeroHeight zLeft with hHeightDef
  set sLater : Set TNonTrivialZetaZero :=
    {zCandidate | rZeroHeight zCandidate = rHeight ∧
      PZeroMemberPrecedes zLeft zCandidate} with hLaterDef
  have hFinite : sLater.Finite := by
    refine Set.Finite.subset (thm_zeroHeightFiber_finite rHeight) ?_
    intro zCandidate hCandidate
    exact hCandidate.1
  have hRightMem : zRight ∈ sLater := ⟨hHeightDef ▸ hSameHeight.symm, hPrecedes⟩
  have hNonempty : sLater.Nonempty := ⟨zRight, hRightMem⟩
  obtain ⟨zNeighbour, hNeighbourMember, hMinimal⟩ :=
    Set.exists_min_image sLater fnZeroOrderKey hFinite hNonempty
  have hSameH2 : rZeroHeight zLeft = rZeroHeight zNeighbour :=
    (hNeighbourMember.1.trans hHeightDef).symm
  refine ⟨zNeighbour, hSameH2.symm, ⟨hNeighbourMember.2, ?_⟩, ?_⟩
  · rintro ⟨zBetween, hAfter, hBefore⟩
    have hBetweenHeight : rZeroHeight zBetween = rHeight :=
      (thm_sameFiberInterposition hSameH2 hAfter hBefore).trans hHeightDef
    have hBetweenMember : zBetween ∈ sLater := ⟨hBetweenHeight, hAfter⟩
    exact absurd (hMinimal zBetween hBetweenMember) (not_le.mpr hBefore)
  · rcases eq_or_ne zNeighbour zRight with hEq | hNe
    · exact Or.inl hEq
    · have hLe : fnZeroOrderKey zNeighbour ≤ fnZeroOrderKey zRight :=
        hMinimal zRight hRightMem
      exact Or.inr (lt_of_le_of_ne hLe (fun hKeyEq => hNe (thm_zeroOrderKey_injective hKeyEq)))

/-! ## 2. La récursion : T2 le long de toute la fibre finie -/

private def sFiberBetween (zRight zLeft : TNonTrivialZetaZero) : Set TNonTrivialZetaZero :=
  {zBetween | rZeroHeight zBetween = rZeroHeight zRight ∧
    PZeroMemberPrecedes zLeft zBetween ∧ PZeroMemberPrecedes zBetween zRight}

private theorem sFiberBetween_finite (zRight zLeft : TNonTrivialZetaZero) :
    (sFiberBetween zRight zLeft).Finite := by
  refine Set.Finite.subset (thm_zeroHeightFiber_finite (rZeroHeight zRight)) ?_
  intro zBetween hBetween
  exact hBetween.1

/-- **T2 le long de la fibre finie.**  Le premier central est strictement
croissant le long de tout couple comparable de la même fibre de hauteur -- via
une chaîne finie de vrais passages consécutifs, jamais via un passage direct
non consécutif entre les deux extrémités. -/
theorem thm_centralPrime_strict_of_sameFiber_precedes
    (hT2 : tCarrier.PCanonicalSuccession)
    {zLeft zRight : TNonTrivialZetaZero}
    (hSameHeight : rZeroHeight zLeft = rZeroHeight zRight)
    (hPrecedes : PZeroMemberPrecedes zLeft zRight) :
    tCarrier.fnCarrierMemberCentralPrime zLeft <
      tCarrier.fnCarrierMemberCentralPrime zRight := by
  classical
  have main : ∀ n : ℕ, ∀ zLeft : TNonTrivialZetaZero,
      rZeroHeight zLeft = rZeroHeight zRight →
      PZeroMemberPrecedes zLeft zRight →
      (sFiberBetween zRight zLeft).ncard ≤ n →
      tCarrier.fnCarrierMemberCentralPrime zLeft <
        tCarrier.fnCarrierMemberCentralPrime zRight := by
    intro n
    induction n with
    | zero =>
      intro zLeft hSameHeight hPrecedes hCard
      have hEmpty : sFiberBetween zRight zLeft = ∅ :=
        (Set.ncard_eq_zero (sFiberBetween_finite zRight zLeft)).mp
          (Nat.le_zero.mp hCard)
      obtain ⟨zMid, zMidHeightEq, hConsecutive, hReached⟩ :=
        exists_bounded_immediate_successor hPrecedes hSameHeight
      rcases hReached with hEq | hLt
      · exact hEq ▸ tCarrier.thm_T2_order hT2 ⟨zLeft, zMid, hConsecutive⟩
      · exfalso
        have hMidHeight : rZeroHeight zMid = rZeroHeight zRight :=
          zMidHeightEq.trans hSameHeight
        have : zMid ∈ sFiberBetween zRight zLeft := ⟨hMidHeight, hConsecutive.1, hLt⟩
        rw [hEmpty] at this
        exact this
    | succ n ih =>
      intro zLeft hSameHeight hPrecedes hCard
      obtain ⟨zMid, zMidHeightEq, hConsecutive, hReached⟩ :=
        exists_bounded_immediate_successor hPrecedes hSameHeight
      have hStepLt :
          tCarrier.fnCarrierMemberCentralPrime zLeft <
            tCarrier.fnCarrierMemberCentralPrime zMid :=
        tCarrier.thm_T2_order hT2 ⟨zLeft, zMid, hConsecutive⟩
      rcases hReached with hEq | hLt
      · exact hEq ▸ hStepLt
      · have hMidHeight : rZeroHeight zMid = rZeroHeight zRight :=
          zMidHeightEq.trans hSameHeight
        have hSubset : sFiberBetween zRight zMid ⊂ sFiberBetween zRight zLeft := by
          constructor
          · intro zCandidate hCandidate
            exact ⟨hCandidate.1,
              thm_zeroMemberPrecedes_transitive hConsecutive.1 hCandidate.2.1,
              hCandidate.2.2⟩
          · intro hSub
            have hMidMem : zMid ∈ sFiberBetween zRight zLeft :=
              ⟨hMidHeight, hConsecutive.1, hLt⟩
            have := hSub hMidMem
            exact absurd this.2.1 (thm_zeroMemberPrecedes_irreflexive zMid)
        have hCardLt :
            (sFiberBetween zRight zMid).ncard < (sFiberBetween zRight zLeft).ncard :=
          Set.ncard_lt_ncard hSubset (sFiberBetween_finite zRight zLeft)
        have hCardLe : (sFiberBetween zRight zMid).ncard ≤ n := by omega
        exact lt_trans hStepLt (ih zMid hMidHeight hLt hCardLe)
  exact main (sFiberBetween zRight zLeft).ncard zLeft hSameHeight hPrecedes le_rfl

end TTrueTowerCarrier

/-! ## 3. La contradiction sur la paire miroir OFF -/

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-- **T2 étendu à la fibre et `PMirrorCollision` sont mutuellement exclusifs.**
Aucune hypothèse d'unicité de la paire à cette hauteur : s'il existe des
membres intermédiaires réels, la chaîne de T2 ne fait que s'allonger, jamais
s'affaiblir. -/
theorem thm_off_impossible_of_T2_and_mirrorCollision
    (hT2 : tCarrier.PCanonicalSuccession)
    (hCollision : tCarrier.PMirrorCollision)
    (zOff : TOffCriticalLineUpperZero) : False := by
  have hDistinct : (offOriginalUpperMember zOff).1 ≠ (offMirrorUpperMember zOff).1 :=
    fun hEq => thm_offMirror_distinct zOff (Subtype.ext hEq)
  have hSameHeight : rZeroHeight (offOriginalUpperMember zOff).1 =
      rZeroHeight (offMirrorUpperMember zOff).1 :=
    (thm_offMirror_sameHeight zOff).symm
  have hReprOriginal :
      tCarrier.fnCarrierMemberCentralPrime (offOriginalUpperMember zOff).1 =
        tCarrier.nCarrierCentralPrime (offOriginalUpperMember zOff) := by
    unfold fnCarrierMemberCentralPrime
    exact congrArg tCarrier.nCarrierCentralPrime
      (Subtype.ext (thm_upperRepresentativeMember_of_positiveHeight
        (offOriginalUpperMember zOff).2))
  have hReprMirror :
      tCarrier.fnCarrierMemberCentralPrime (offMirrorUpperMember zOff).1 =
        tCarrier.nCarrierCentralPrime (offMirrorUpperMember zOff) := by
    unfold fnCarrierMemberCentralPrime
    exact congrArg tCarrier.nCarrierCentralPrime
      (Subtype.ext (thm_upperRepresentativeMember_of_positiveHeight
        (offMirrorUpperMember zOff).2))
  have hEq := hCollision zOff
  rcases thm_distinctZeroMembers_comparable hDistinct with hOrder | hOrder
  · have hLt := tCarrier.thm_centralPrime_strict_of_sameFiber_precedes hT2 hSameHeight hOrder
    rw [hReprOriginal, hReprMirror] at hLt
    exact absurd hEq (Nat.ne_of_lt hLt)
  · have hLt := tCarrier.thm_centralPrime_strict_of_sameFiber_precedes hT2
      hSameHeight.symm hOrder
    rw [hReprMirror, hReprOriginal] at hLt
    exact absurd hEq.symm (Nat.ne_of_lt hLt)

end TTrueTowerCarrier

/-! ## 4. Fermeture terminale : exactement T1, T2, `PMirrorCollision` -/

/-- **RH, sur exactement les trois prémisses nommées.** Aucune quatrième :
`PMirrorPairIsOnlyMembersAtHeight` n'est jamais introduite -- s'il existe des
membres intermédiaires réels dans la fibre, T2 en tire une chaîne plus longue,
donc une contradiction plus forte, jamais un obstacle. -/
theorem thm_riemannHypothesis_of_T1_T2_mirrorCollision
    (tCarrier : TTrueTowerCarrier)
    (hT1 : tCarrier.PUniqueCenterRegime)
    (hT2 : tCarrier.PCanonicalSuccession)
    (hCollision : tCarrier.PMirrorCollision) :
    RiemannHypothesis := by
  refine thm_riemannHypothesis_of_allUpperOnCriticalLine ?_
  intro z
  by_contra hOff
  exact tCarrier.thm_off_impossible_of_T2_and_mirrorCollision hT2 hCollision ⟨z, hOff⟩

/-! Surface audit. -/

#check @TTrueTowerCarrier.thm_centralPrime_strict_of_sameFiber_precedes
#check @TTrueTowerCarrier.thm_off_impossible_of_T2_and_mirrorCollision
#check @thm_riemannHypothesis_of_T1_T2_mirrorCollision

end RHV3Lean
