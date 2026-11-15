/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.OffMirrorDifferenceBands
import RHV3Lean.Objects.CanonicalT1

/-!
# RHV3Lean — Piste C, resserrée par T1 : un seul bit décide tout

    TRACE_ID              : RHV3-OFF-MIRROR-OVERLAP-REDUCTION
    SEMANTIC_OBJECT       : la collision miroir OFF, réduite -- sous le régime
                            de centre unique (T1) -- d'une conjonction de deux
                            faits de comptage à un seul fait de comptage,
                            nécessaire ET suffisant, jamais seulement
                            suffisant.
    SEMANTIC_STATEMENT    : chaque cellule du couple miroir contient, par le
                            régime de centre unique, exactement un premier --
                            ni plus, ni moins. Cette seule contrainte, combinée
                            à la structure déjà produite des deux bandes de
                            différence, force les deux bandes à avoir
                            exactement le même cardinal, et ce cardinal commun
                            ne peut valoir que zéro ou un. La collision miroir
                            équivaut alors très exactement à la nullité de ce
                            cardinal commun -- une seule lecture de la fonction
                            de comptage de Von Mangoldt/Chebyshev, sur une
                            seule bande, décide tout, dans les deux sens.
    MATHEMATICAL_STATEMENT: soit A = pi(c1-), B = pi(c1+), C = pi(c2-),
                            D = pi(c2+) les quatre rangs de comptage. T1 donne
                            B=A+1 et D=C+1. Le cardinal de la bande gauche est
                            max(A,C)-min(A,C), celui de la bande droite
                            max(B,D)-min(B,D) = max(A,C)-min(A,C) : les deux
                            coïncident toujours. La collision miroir équivaut
                            à A=C (injectivité de l'énumération première), donc
                            à ce cardinal commun nul.
    MATHEMATICAL_PARENT   : maître sémantique §9/§13.1 (régime de centre
                            unique, ACQUIS) ; maître Lean §35/§36 (Piste C) ;
                            OffMirrorDifferenceBands.lean (bandes, borne) ;
                            CanonicalT1.lean (T1, PUniqueCenterRegime).
    PROOF_STRATEGY        : exprimer les deux cardinaux de bande comme un
                            max/min des quatre rangs de comptage ; utiliser T1
                            pour fixer B et D en fonction de A et C ; en
                            déduire l'égalité des deux bandes par arithmétique
                            entière pure ; relier le cardinal nul à l'égalité
                            A=C, puis à l'égalité des premiers centraux par
                            l'injectivité déjà produite de l'énumération.
    REQUIRED_LEMMAS       : thm_nEdgePrimeRank_mono, thm_cellFoundCount_eq_
                            edgeRankDifference, thm_primeAtRank_injective
    WHY_EACH_LEMMA_EXISTS : la première donne min/max de rang depuis min/max de
                            point ; la deuxième relit chaque cardinal comme une
                            différence de rangs ; la troisième transporte
                            l'égalité de rang en égalité de premier.
    LEAN_DEFINITION       : (aucune nouvelle -- recompose les objets déjà
                            nommés)
    LEAN_THEOREM          : thm_edgeRank_min_eq, thm_edgeRank_max_eq,
                            thm_mirrorBands_sameCount_of_T1,
                            thm_mirrorCollision_iff_leftBandEmpty_of_T1
    SAME_MEMBER_CHECK     : toutes les lectures restent fonctions du seul
                            membre reçu (contacts, cellule, bande).
    SAME_PASSAGE_CHECK    : sans objet -- aucun passage n'est construit ici.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : l'énumération première utilisée est celle de O6,
                            unique, lue par O10 seul.
    FORBIDDEN_PREMISES    : choisir une adresse kappa ; supposer une relation
                            entre T et l'ordre de grandeur absolu des contacts ;
                            recevoir un premier, un rang ou une position cible.
    NEXT_CONSUMER         : la route miroir (`PMirrorCollision`), désormais
                            réductible à la lecture d'une seule bande sous T1,
                            au lieu de deux.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS            : BODY_PRODUCED. `PUniqueCenterRegime` et
                             `PMirrorSameStageLogGap` restent des `Prop`
                             nommées, non prouvées ici, exactement à leur
                             statut déjà enregistré. Ce module ne reçoit
                             aucune hypothèse nouvelle : il recompose
                             uniquement des faits déjà acquis ou déjà produits.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

/-! ## 1. Le rang de comptage au bord commute avec min/max -/

theorem thm_edgeRank_min_eq (a b : ℝ) :
    nEdgePrimeRank (min a b) = min (nEdgePrimeRank a) (nEdgePrimeRank b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (thm_nEdgePrimeRank_mono h)]
  · rw [min_eq_right h, min_eq_right (thm_nEdgePrimeRank_mono h)]

theorem thm_edgeRank_max_eq (a b : ℝ) :
    nEdgePrimeRank (max a b) = max (nEdgePrimeRank a) (nEdgePrimeRank b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (thm_nEdgePrimeRank_mono h)]
  · rw [max_eq_left h, max_eq_left (thm_nEdgePrimeRank_mono h)]

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-! ## 2. Sous T1, les deux bandes ont toujours le même cardinal -/

/-- **Les deux bandes de différence ont exactement le même cardinal**, dès que
le régime de centre unique tient sur les deux membres. Plus besoin de tester
les deux bandes séparément : une seule lecture suffit désormais. -/
theorem thm_mirrorBands_sameCount_of_T1
    (hStage : tCarrier.PMirrorSameStageLogGap)
    (hT1 : tCarrier.PUniqueCenterRegime)
    (zOff : TOffCriticalLineUpperZero) :
    nCellFoundCount (tCarrier.tLeftDifferenceBand hStage zOff) =
      nCellFoundCount (tCarrier.tRightDifferenceBand hStage zOff) := by
  have hCountOrig := hT1 (offOriginalUpperMember zOff)
  have hCountMirror := hT1 (offMirrorUpperMember zOff)
  have hDiffOrig : nCellFoundCount (tCarrier.tCarrierCell (offOriginalUpperMember zOff)) =
      nEdgePrimeRank (tCarrier.rCarrierContactPlus (offOriginalUpperMember zOff)) -
        nEdgePrimeRank (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff)) :=
    thm_cellFoundCount_eq_edgeRankDifference (tCarrier.tCarrierCell (offOriginalUpperMember zOff))
  have hDiffMirror : nCellFoundCount (tCarrier.tCarrierCell (offMirrorUpperMember zOff)) =
      nEdgePrimeRank (tCarrier.rCarrierContactPlus (offMirrorUpperMember zOff)) -
        nEdgePrimeRank (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff)) :=
    thm_cellFoundCount_eq_edgeRankDifference (tCarrier.tCarrierCell (offMirrorUpperMember zOff))
  rw [hCountOrig] at hDiffOrig
  rw [hCountMirror] at hDiffMirror
  have hOrderedOrig : tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff) <
      tCarrier.rCarrierContactPlus (offOriginalUpperMember zOff) :=
    (tCarrier.tCarrierCell (offOriginalUpperMember zOff)).hOrdered
  have hOrderedMirror : tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff) <
      tCarrier.rCarrierContactPlus (offMirrorUpperMember zOff) :=
    (tCarrier.tCarrierCell (offMirrorUpperMember zOff)).hOrdered
  have hMonoOrig := thm_nEdgePrimeRank_mono (le_of_lt hOrderedOrig)
  have hMonoMirror := thm_nEdgePrimeRank_mono (le_of_lt hOrderedMirror)
  have hB : nEdgePrimeRank (tCarrier.rCarrierContactPlus (offOriginalUpperMember zOff)) =
      nEdgePrimeRank (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff)) + 1 := by omega
  have hD : nEdgePrimeRank (tCarrier.rCarrierContactPlus (offMirrorUpperMember zOff)) =
      nEdgePrimeRank (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff)) + 1 := by omega
  have hLeft : nCellFoundCount (tCarrier.tLeftDifferenceBand hStage zOff) =
      max (nEdgePrimeRank (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff)))
          (nEdgePrimeRank (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff))) -
        min (nEdgePrimeRank (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff)))
          (nEdgePrimeRank (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff))) := by
    rw [thm_cellFoundCount_eq_edgeRankDifference]
    unfold nCellLeftEdgeRank nCellRightEdgeRank tLeftDifferenceBand
    rw [thm_edgeRank_min_eq, thm_edgeRank_max_eq]
  have hRight : nCellFoundCount (tCarrier.tRightDifferenceBand hStage zOff) =
      max (nEdgePrimeRank (tCarrier.rCarrierContactPlus (offOriginalUpperMember zOff)))
          (nEdgePrimeRank (tCarrier.rCarrierContactPlus (offMirrorUpperMember zOff))) -
        min (nEdgePrimeRank (tCarrier.rCarrierContactPlus (offOriginalUpperMember zOff)))
          (nEdgePrimeRank (tCarrier.rCarrierContactPlus (offMirrorUpperMember zOff))) := by
    rw [thm_cellFoundCount_eq_edgeRankDifference]
    unfold nCellLeftEdgeRank nCellRightEdgeRank tRightDifferenceBand
    rw [thm_edgeRank_min_eq, thm_edgeRank_max_eq]
  rw [hLeft, hRight, hB, hD]
  omega

/-! ## 3. La collision miroir équivaut, sous T1, à la bande gauche vide -/

/-- **Le théorème central de cette réduction.** Sous le régime de centre
unique sur les deux membres, la collision miroir OFF, pour une paire donnée,
équivaut EXACTEMENT à la nullité du cardinal de la bande gauche -- jamais
seulement impliquée par elle. Une seule lecture de la fonction de comptage de
Von Mangoldt/Chebyshev, sur une seule bande étroite, décide tout : ni plus
faible, ni plus forte que ce qu'il faut. -/
theorem thm_mirrorCollision_iff_leftBandEmpty_of_T1
    (hStage : tCarrier.PMirrorSameStageLogGap)
    (hT1 : tCarrier.PUniqueCenterRegime)
    (zOff : TOffCriticalLineUpperZero) :
    tCarrier.nCarrierCentralPrime (offOriginalUpperMember zOff) =
        tCarrier.nCarrierCentralPrime (offMirrorUpperMember zOff) ↔
      nCellFoundCount (tCarrier.tLeftDifferenceBand hStage zOff) = 0 := by
  have hCountOrig := hT1 (offOriginalUpperMember zOff)
  have hCountMirror := hT1 (offMirrorUpperMember zOff)
  have hLeft : nCellFoundCount (tCarrier.tLeftDifferenceBand hStage zOff) =
      max (nEdgePrimeRank (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff)))
          (nEdgePrimeRank (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff))) -
        min (nEdgePrimeRank (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff)))
          (nEdgePrimeRank (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff))) := by
    rw [thm_cellFoundCount_eq_edgeRankDifference]
    unfold nCellLeftEdgeRank nCellRightEdgeRank tLeftDifferenceBand
    rw [thm_edgeRank_min_eq, thm_edgeRank_max_eq]
  have hCentralOrig :
      tCarrier.nCarrierCentralPrime (offOriginalUpperMember zOff) =
        fnPrimeAtRank
          (nEdgePrimeRank (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff))) := by
    unfold nCarrierCentralPrime nCellCentralPrime nCellCentralRank nCellLeftEdgeRank
    rw [hCountOrig, show (tCarrier.tCarrierCell (offOriginalUpperMember zOff)).rLeftEndpoint =
      tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff) from rfl,
      show (1 + 1) / 2 = 1 from rfl, Nat.add_sub_cancel]
  have hCentralMirror :
      tCarrier.nCarrierCentralPrime (offMirrorUpperMember zOff) =
        fnPrimeAtRank
          (nEdgePrimeRank (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff))) := by
    unfold nCarrierCentralPrime nCellCentralPrime nCellCentralRank nCellLeftEdgeRank
    rw [hCountMirror, show (tCarrier.tCarrierCell (offMirrorUpperMember zOff)).rLeftEndpoint =
      tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff) from rfl,
      show (1 + 1) / 2 = 1 from rfl, Nat.add_sub_cancel]
  rw [hCentralOrig, hCentralMirror]
  constructor
  · intro hEq
    have hRankEq := thm_primeAtRank_injective hEq
    rw [hLeft]
    omega
  · intro hEq
    rw [hLeft] at hEq
    congr 1
    omega

end TTrueTowerCarrier

end RHV3Lean
