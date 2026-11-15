/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.SamePrimeCollision
import RHV3Lean.Objects.OffFibreAndPassage

/-!
# RHV3Lean — le passage nul produit par OFF ne peut jamais partager son
contact gauche vrai

    TRACE_ID              : RHV3-OFF-NULL-PASSAGE-CONTACT-SEPARATION
    SEMANTIC_OBJECT       : le couple d'états propres de Tour porté par les
                            deux extrémités d'un vrai passage d'écart nul.
    SEMANTIC_STATEMENT    : deux membres distincts à la même hauteur ont
                            nécessairement des positions radiales distinctes
                            (sinon ils seraient le même zéro, par l'injectivité
                            du support). La loi tangentielle de chaque état
                            propre lie son contact gauche à sa PROPRE position
                            radiale, à hauteur commune. Deux positions
                            radiales distinctes ne peuvent jamais produire la
                            même valeur de tangente au même contact : donc les
                            deux contacts gauches vrais sont eux-mêmes
                            distincts.
    MATHEMATICAL_STATEMENT: si beta_1*tan(T*log C) = T et beta_2*tan(T*log C) = T
                            avec T>0 et beta_1 != beta_2, alors une contradiction
                            (le même tan ne peut satisfaire les deux équations) ;
                            donc C_1 != C_2 pour deux vrais contacts gauches
                            portés à la même hauteur par deux membres distincts.
    MATHEMATICAL_PARENT   : `TrueTowerState.lean` (la loi tangentielle,
                            ACQUISE, jamais dérivée ici) ; `OffFibreAndPassage.lean`
                            (le passage nul produit par OFF, déjà inconditionnel) ;
                            `SamePrimeCollision.lean` (le couple OFF supérieur).
    PROOF_STRATEGY        : pur calcul algébrique sur les deux lois
                            tangentielles déjà acquises, sans aucune nouvelle
                            hypothèse, sans comptage, sans fonction de
                            comptage, sans adresse (kappa,m). Le passage nul
                            fournit les deux membres distincts de même hauteur ;
                            l'injectivité du support en tire la distinction des
                            positions radiales ; la loi tangentielle fait le
                            reste par annulation algébrique.
    REQUIRED_LEMMAS       : TTrueHarmonicTowerState.tangent_law,
                            thm_zero_identity_of_sameSupport,
                            thm_offCriticalLine_existsNullPassage,
                            thm_zeroPassage_null_iff_sameHeight,
                            TZeroPassage.members_distinct,
                            tPassageUpperEndpoints, thm_passageEndpoints_upperBranch
    WHY_EACH_LEMMA_EXISTS : la loi tangentielle est la seule loi de tout ce
                            corpus qui voit réellement la position radiale
                            (bêta) — ni la grammaire première, ni M^Z, ni le
                            comptage ne la voient ; c'est pourquoi elle est le
                            seul endroit où une séparation analytique du
                            couple OFF peut apparaître.
    LEAN_DEFINITION       : aucune nouvelle définition
    LEAN_THEOREM          : thm_contactMinus_distinct_of_sameHeight_diffRadial,
                            thm_offNullPassage_contacts_distinct
    SAME_MEMBER_CHECK     : les deux états lus sont ceux des deux extrémités
                            PROPRES du passage, jamais d'un membre étranger.
    SAME_PASSAGE_CHECK    : c'est le MÊME passage nul, produit par
                            `thm_offCriticalLine_existsNullPassage`, dont les
                            deux extrémités sont relues ici.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre dans ce fichier.
    FORBIDDEN_PREMISES    : compter des premiers dans une cellule ; comparer
                            une largeur de cellule à un écart de premiers ;
                            choisir une branche (kappa, m) pour fixer la valeur
                            réelle du contact ; utiliser `nCarrierCentralPrime`
                            ou toute donnée première dans ce fichier.
    NEXT_CONSUMER         : aucun encore. Ce théorème établit une séparation
                            RÉELLE (les deux contacts gauches diffèrent) mais
                            NE FERME NI `PMirrorCollision` NI
                            `PNullPassageForcesNullPlace` : `PMirrorCollision`
                            autorise déjà explicitement des contacts distincts
                            (`SamePrimeCollision.lean`, définition, « même si
                            elles atterrissent sur l'axe algébrique en des
                            points généralement distincts ») ; ce théorème ne
                            contredit donc pas cette prémisse, il ne fait que
                            confirmer, par un calcul réel indépendant, que la
                            séparation géométrique qu'elle autorise a
                            effectivement lieu. La question encore ouverte —
                            la seule prémisse restante — porte sur ce que
                            `nCarrierCentralPrime` fait de deux cellules ainsi
                            séparées, pas sur leur position.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED — fait réel, vérifié, mais
                            explicitement insuffisant à lui seul pour clore la
                            dernière prémisse. Aucun `sorry`, aucun `admit`,
                            aucun axiome nouveau.
-/

namespace RHV3Lean

/-! ## 1. Le fait réel, sur deux états propres quelconques -/

/-- **Deux vrais contacts gauches, à la même hauteur, portés par deux membres
de positions radiales distinctes, sont eux-mêmes distincts.**  Pur calcul
depuis la loi tangentielle des deux états — jamais un choix de branche, jamais
un comptage. -/
theorem thm_contactMinus_distinct_of_sameHeight_diffRadial
    {z1 z2 : TUpperNonTrivialZetaZero}
    (S1 : TTrueHarmonicTowerState z1) (S2 : TTrueHarmonicTowerState z2)
    (hHeight : rZeroHeight z1.1 = rZeroHeight z2.1)
    (hRadial : rZeroRadialPosition z1.1 ≠ rZeroRadialPosition z2.1) :
    S1.contactMinus ≠ S2.contactMinus := by
  intro hEq
  have hT1 := S1.tangent_law
  have hT2 := S2.tangent_law
  rw [hEq, hHeight] at hT1
  have hτ : Real.tan (rZeroHeight z2.1 * Real.log S2.contactMinus) ≠ 0 := by
    intro hτ0
    rw [hτ0, mul_zero] at hT1
    exact (ne_of_gt z2.2) hT1.symm
  exact hRadial (mul_right_cancel₀ hτ (hT1.trans hT2.symm))

/-! ## 2. Instancié sur le passage nul produit par OFF -/

/-- **Le passage nul produit par un vrai zéro hors ligne porte deux contacts
gauches vrais qui sont eux-mêmes distincts.**  Ni comptage, ni adresse, ni
choix de branche : seule la loi tangentielle des deux membres, appliquée au
passage nul déjà produit par `thm_offCriticalLine_existsNullPassage`. -/
theorem thm_offNullPassage_contacts_distinct
    (tCarrier : TTrueTowerCarrier) (zOff : TOffCriticalLineUpperZero) :
    ∃ (tPassage : TZeroPassage) (hEarlierPositive : 0 < rZeroHeight tPassage.zEarlierMember),
      rZeroPassageHeightGap tPassage = 0 ∧
      (tCarrier.fnState (tPassageUpperEndpoints tPassage hEarlierPositive).1).contactMinus ≠
        (tCarrier.fnState (tPassageUpperEndpoints tPassage hEarlierPositive).2).contactMinus := by
  obtain ⟨tPassage, hGapZero, hHeightEq⟩ := thm_offCriticalLine_existsNullPassage zOff.2
  have hEarlierPositive : 0 < rZeroHeight tPassage.zEarlierMember := hHeightEq ▸ zOff.1.2
  refine ⟨tPassage, hEarlierPositive, hGapZero, ?_⟩
  set zE := (tPassageUpperEndpoints tPassage hEarlierPositive).1 with hzEDef
  set zL := (tPassageUpperEndpoints tPassage hEarlierPositive).2 with hzLDef
  have hzE : zE.1 = tPassage.zEarlierMember :=
    (thm_passageEndpoints_upperBranch tPassage hEarlierPositive).1
  have hzL : zL.1 = tPassage.zLaterMember :=
    (thm_passageEndpoints_upperBranch tPassage hEarlierPositive).2
  have hSameHeight : rZeroHeight zE.1 = rZeroHeight zL.1 := by
    rw [hzE, hzL]
    exact (thm_zeroPassage_null_iff_sameHeight tPassage).mp hGapZero
  have hDistinctMembers : zE.1 ≠ zL.1 := by
    rw [hzE, hzL]; exact tPassage.members_distinct
  have hRadialNe : rZeroRadialPosition zE.1 ≠ rZeroRadialPosition zL.1 := by
    intro hRadEq
    exact hDistinctMembers (thm_zero_identity_of_sameSupport (Complex.ext hRadEq hSameHeight))
  exact thm_contactMinus_distinct_of_sameHeight_diffRadial
    (tCarrier.fnState zE) (tCarrier.fnState zL) hSameHeight hRadialNe

#check @thm_contactMinus_distinct_of_sameHeight_diffRadial
#check @thm_offNullPassage_contacts_distinct

end RHV3Lean
