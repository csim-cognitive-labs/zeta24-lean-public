/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.CountingRigidity
import RHV3Lean.Objects.TrueTowerState

/-!
# RHV3Lean — O5, l'occurrence première, et R-ATT

    TRACE_ID              : RHV3-O5
    SEMANTIC_OBJECT       : O5 — l'occurrence première ; R-ATT — sa rigidité
                            d'attachement
    SEMANTIC_STATEMENT    : une occurrence première n'est pas un nombre premier
                            nu mais le nombre premier muni de sa position
                            complète dans l'histoire première telle qu'elle a
                            été effectivement lue, à une cellule donnée — sa
                            provenance de lecture ; deux membres distincts ont
                            toujours deux occurrences distinctes, mais cela ne
                            donne JAMAIS la distinction des nombres premiers
                            portés.
    MATHEMATICAL_STATEMENT: Occ(rho) = (P(rho), r, e_(r-1), e_r, orientation,
                            gap, I_C(rho)) ; rho_A != rho_B => Occ(rho_A) !=
                            Occ(rho_B) par la composante de provenance ; mais
                            rho_A != rho_B n'implique jamais P(rho_A) != P(rho_B)
                            par R-ATT seule.
    MATHEMATICAL_PARENT   : O10 — la rigidité de comptage ; O4 — les contacts et
                            la cellule ; O6 — la grammaire des écarts premiers.
    PROOF_STRATEGY        : l'occurrence stocke le premier, son rang, sa
                            provenance de lecture — les deux vrais contacts et
                            leur cellule, que l'inversion de O4 rend
                            membre-sensibles — et la preuve que
                            le premier est bien celui de ce rang ; R-ATT est
                            alors la contraposée de l'inversion ; la limite de
                            R-ATT est exhibée par deux occurrences de même
                            premier et de provenances distinctes.
    REQUIRED_LEMMAS       : thm_sameContactData_sameMember,
                            thm_primeAtRank_surjective_onPrimes,
                            thm_primeGap_positive
    WHY_EACH_LEMMA_EXISTS : le premier donne R-ATT par contraposition ; le
                            deuxième attache à chaque premier son rang unique ;
                            le troisième donne l'écart strictement positif porté
                            par l'occurrence.
    LEAN_DEFINITION       : TReadingProvenance, TPrimeOccurrence,
                            tMemberProvenance, tMemberPrimeOccurrence
    LEAN_THEOREM          : thm_rATT_sameProvenance_sameMember,
                            thm_rATT_distinctMembers_distinctOccurrences,
                            thm_rATT_doesNotSeparatePrimes,
                            thm_occurrence_nextGap_positive
    SAME_MEMBER_CHECK     : la provenance de lecture d'une occurrence de membre
                            est la donnée complète de contacts de la Tour de CE
                            membre, jamais d'un autre.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : le rang et les arêtes sont lus dans l'unique
                            histoire première de O6.
    FORBIDDEN_PREMISES    : réduire l'occurrence au nombre premier nu ; utiliser
                            R-ATT pour obtenir deux premiers distincts — toute
                            étape qui a besoin de deux premiers distincts
                            s'appuie sur la loi locale, jamais sur R-ATT.
    NEXT_CONSUMER         : la loi locale du transport, qui seule sépare les
                            nombres premiers de deux extrémités d'un passage.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

/-! ## 1. La provenance de lecture -/

/-- **La provenance de lecture** : la paire complète de vrais contacts qui a
produit l'occurrence et la cellule dont ils sont exactement les deux bords.
L'inversion contacts-only de O4 renvoie le membre depuis cette paire. -/
structure TReadingProvenance where
  /-- La cellule terminale qui a produit la lecture. -/
  tCell : TAlgebraicInterval
  /-- Le vrai contact inférieur qui a produit la cellule. -/
  contactMinus : ℝ
  /-- Le vrai contact supérieur consécutif. -/
  contactPlus : ℝ
  /-- Le bord gauche est exactement le contact inférieur. -/
  cell_left : tCell.rLeftEndpoint = contactMinus
  /-- Le bord droit est exactement le contact supérieur. -/
  cell_right : tCell.rRightEndpoint = contactPlus

/-! ## 2. L'occurrence première -/

/-- **L'occurrence première** : le premier, son rang dans l'unique histoire
première, et sa provenance de lecture.  Le premier nu n'est jamais l'objet. -/
structure TPrimeOccurrence where
  /-- Le nombre premier porté. -/
  nPrime : ℕ
  /-- Son rang dans l'unique histoire première, zéro-basé. -/
  nRank : ℕ
  /-- La cellule qui a produit cette occurrence. -/
  tProvenance : TReadingProvenance
  /-- Le premier porté est bien celui de ce rang. -/
  hPrimeAtRank : nPrime = fnPrimeAtRank nRank

namespace TPrimeOccurrence

variable (tOccurrence : TPrimeOccurrence)

theorem isPrime : Nat.Prime tOccurrence.nPrime :=
  tOccurrence.hPrimeAtRank ▸ thm_primeAtRank_isPrime tOccurrence.nRank

/-- **L'arête suivante** de l'occurrence : la place entre son premier et le
suivant. -/
noncomputable def nNextEdgeEnd : ℕ := fnPrimeSuccessor tOccurrence.nRank

/-- **L'arête précédente** de l'occurrence. -/
noncomputable def nPreviousEdgeStart : ℕ := fnPrimeAtRank (tOccurrence.nRank - 1)

/-- **L'écart porté par l'arête suivante.** -/
noncomputable def nNextGap : ℕ := nPrimeGap tOccurrence.nRank

/-- **L'orientation** : le premier porté précède strictement l'extrémité de son
arête suivante. -/
theorem orientation :
    tOccurrence.nPrime < tOccurrence.nNextEdgeEnd := by
  rw [tOccurrence.hPrimeAtRank]
  exact thm_primeAtRank_lt_successor _

/-- **La composition arithmétique complète de l'arête suivante.**  Le premier
porté, augmenté de son écart suivant, EST exactement l'extrémité de son arête
suivante — purement arithmétique, inconditionnel, ni RH, ni T1, ni T2 : la
définition complète de l'occurrence première que porte déjà `TPrimeOccurrence`. -/
theorem central_add_nextGap_eq_nextEdgeEnd :
    tOccurrence.nPrime + tOccurrence.nNextGap = tOccurrence.nNextEdgeEnd := by
  have hlt := thm_primeAtRank_lt_successor tOccurrence.nRank
  unfold nNextGap nNextEdgeEnd nPrimeGap
  rw [tOccurrence.hPrimeAtRank]
  omega

/-- **La composition arithmétique symétrique de l'arête précédente**, pour tout
rang strictement positif.  Au rang zéro, il n'existe aucun premier précédent :
`nPreviousEdgeStart` retombe alors, par la soustraction tronquée de sa
définition, sur le rang zéro lui-même, sans qu'aucun énoncé faux n'en résulte —
c'est pourquoi cette composition exige `0 < nRank`, séparément du cas zéro. -/
theorem previousEdgeStart_add_gap_eq_central (hRank : 0 < tOccurrence.nRank) :
    tOccurrence.nPreviousEdgeStart + nPrimeGap (tOccurrence.nRank - 1) =
      tOccurrence.nPrime := by
  have hSucc : tOccurrence.nRank - 1 + 1 = tOccurrence.nRank := by omega
  have hltRank : tOccurrence.nRank - 1 < tOccurrence.nRank := by omega
  have hlt := thm_primeAtRank_strictMono hltRank
  have hGapEq :
      nPrimeGap (tOccurrence.nRank - 1) =
        fnPrimeAtRank tOccurrence.nRank - fnPrimeAtRank (tOccurrence.nRank - 1) := by
    unfold nPrimeGap fnPrimeSuccessor
    rw [hSucc]
  unfold nPreviousEdgeStart
  rw [hGapEq, tOccurrence.hPrimeAtRank]
  omega

end TPrimeOccurrence

/-- **L'écart porté par une occurrence est strictement positif.**  Il vient de
O6, et de nulle part ailleurs : aucune place de la grammaire n'est nulle. -/
theorem thm_occurrence_nextGap_positive (tOccurrence : TPrimeOccurrence) :
    0 < tOccurrence.nNextGap := thm_primeGap_positive _

/-! ## 3. L'occurrence d'un membre, lue sur sa propre cellule -/

variable (zUpperZero : TUpperNonTrivialZetaZero)
  (tState : TTrueHarmonicTowerState zUpperZero)

/-- Compatibilité de surface : l'occurrence lit désormais la cellule déjà
produite directement par l'état de Tour, sans la reconstruire. -/
noncomputable abbrev tTrueStateCell : TAlgebraicInterval :=
  tState.terminalCell

/-- **La provenance de lecture d'un membre** : la donnée complète de contacts de
sa propre Tour. -/
noncomputable def tMemberProvenance : TReadingProvenance where
  tCell := tTrueStateCell zUpperZero tState
  contactMinus := tState.contactMinus
  contactPlus := tState.contactPlus
  cell_left := rfl
  cell_right := rfl

/-- **L'occurrence première d'un membre** : son premier central, le rang que le
comptage confirme, et sa propre provenance de lecture. -/
noncomputable def tMemberPrimeOccurrence : TPrimeOccurrence where
  nPrime := nCellCentralPrime (tTrueStateCell zUpperZero tState)
  nRank := nCellCentralRank (tTrueStateCell zUpperZero tState) - 1
  tProvenance := tMemberProvenance zUpperZero tState
  hPrimeAtRank := rfl

/-! ## 4. R-ATT -/

/-- **R-ATT — même provenance de lecture, même membre.**

C'est l'inversion de O4 relue sur l'occurrence : la provenance porte la donnée
complète de contacts, donc elle rend la hauteur, la position radiale, et donc le
membre. -/
theorem thm_rATT_sameProvenance_sameMember
    {zLeftZero zRightZero : TUpperNonTrivialZetaZero}
    {tLeftState : TTrueHarmonicTowerState zLeftZero}
    {tRightState : TTrueHarmonicTowerState zRightZero}
    (hSameProvenance :
      tMemberProvenance zLeftZero tLeftState =
        tMemberProvenance zRightZero tRightState) :
    zLeftZero = zRightZero := by
  have hContactMinus :
      tLeftState.contactMinus = tRightState.contactMinus :=
    congrArg TReadingProvenance.contactMinus hSameProvenance
  have hContactPlus :
      tLeftState.contactPlus = tRightState.contactPlus :=
    congrArg TReadingProvenance.contactPlus hSameProvenance
  exact TTrueHarmonicTowerState.thm_same_true_contacts_same_member
    tLeftState tRightState hContactMinus hContactPlus

/-- **R-ATT — deux membres distincts ont deux occurrences distinctes.**

La distinction passe par la composante de provenance, jamais par le nombre
premier porté. -/
theorem thm_rATT_distinctMembers_distinctOccurrences
    {zLeftZero zRightZero : TUpperNonTrivialZetaZero}
    {tLeftState : TTrueHarmonicTowerState zLeftZero}
    {tRightState : TTrueHarmonicTowerState zRightZero}
    (hDistinct : zLeftZero ≠ zRightZero) :
    tMemberPrimeOccurrence zLeftZero tLeftState ≠
      tMemberPrimeOccurrence zRightZero tRightState := by
  intro hSameOccurrence
  exact hDistinct (thm_rATT_sameProvenance_sameMember
    (congrArg TPrimeOccurrence.tProvenance hSameOccurrence))

/-- **LA LIMITE EXACTE DE R-ATT — elle ne sépare jamais les nombres premiers.**

Deux occurrences peuvent porter le MÊME premier, au même rang, et différer par
la seule provenance de lecture.  Toute étape qui a besoin de deux nombres
premiers distincts doit donc s'appuyer sur la loi locale du transport, et jamais
sur R-ATT.

Le témoin est explicite : deux provenances de cellules distinctes portant la
même occurrence de rang zéro. -/
theorem thm_rATT_doesNotSeparatePrimes :
    ∃ tLeftOccurrence tRightOccurrence : TPrimeOccurrence,
      tLeftOccurrence ≠ tRightOccurrence ∧
        tLeftOccurrence.nPrime = tRightOccurrence.nPrime := by
  classical
  refine ⟨⟨fnPrimeAtRank 0, 0, ⟨tWitnessInterval, 1, 4, rfl, rfl⟩, rfl⟩,
    ⟨fnPrimeAtRank 0, 0, ⟨tWitnessSecondInterval, 1, 8, rfl, rfl⟩, rfl⟩, ?_, rfl⟩
  intro hSame
  have hProvenance :
      (⟨tWitnessInterval, 1, 4, rfl, rfl⟩ : TReadingProvenance) =
        ⟨tWitnessSecondInterval, 1, 8, rfl, rfl⟩ :=
    congrArg TPrimeOccurrence.tProvenance hSame
  have hCell : tWitnessInterval = tWitnessSecondInterval :=
    congrArg TReadingProvenance.tCell hProvenance
  have hRight : (4 : ℝ) = 8 :=
    congrArg TAlgebraicInterval.rRightEndpoint hCell
  norm_num at hRight

end RHV3Lean
