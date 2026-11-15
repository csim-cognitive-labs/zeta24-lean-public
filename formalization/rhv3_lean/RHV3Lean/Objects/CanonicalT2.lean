/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.CanonicalT1
import RHV3Lean.Objects.PrimeSuccessionBridge

/-!
# RHV3Lean — T2, la succession canonique, sur le même porteur générique

    TRACE_ID              : RHV3-T2
    SEMANTIC_OBJECT       : T2 — la loi locale du transport : le premier
                            central de l'extrémité de sortie d'un passage réel
                            EST le successeur canonique du premier central de
                            son extrémité d'entrée.
    SEMANTIC_STATEMENT    : la grammaire première canonique est déjà fermée et
                            infinie (O6) ; c'est elle qui force l'ordre entre
                            les deux extrémités d'un même passage — jamais une
                            comparaison de largeur ou un second théorème
                            analytique séparé de T1. Une fois la place d'un
                            passage lue depuis le premier central de son
                            extrémité d'entrée (déjà produit par T1), la même
                            composition scellée (maître mathématique §13.1)
                            force que l'extrémité de sortie porte exactement le
                            successeur canonique.
    MATHEMATICAL_STATEMENT: pour tout passage réel (A,B), C3(B) = successeur
                            canonique de C3(A) dans l'histoire première.
    MATHEMATICAL_PARENT   : §13.1 du maître mathématique (composition
                            événementielle, ACQUIS, points 5-6 : conservation
                            de l'ordre et de la place par la grammaire) ; O8
                            (passage), O6 (grammaire), O10 (comptage).
    PROOF_STRATEGY        : ce module ne dérive PAS la succession d'une analyse
                            de largeur ni d'un second théorème indépendant de
                            T1. Il reçoit `PCanonicalSuccession` comme la même
                            sorte de fait ACQUIS que `PUniqueCenterRegime`
                            (T1), et branche l'infrastructure générique déjà
                            produite dans `TrueTowerCarrier.lean`
                            (`fnCarrierPassagePlace`,
                            `thm_carrierLocalLaw_of_laterOccurrence_successor`,
                            `thm_carrier_rpass_iff_localLaw`) sans nouvelle
                            preuve de ces théorèmes eux-mêmes.
    REQUIRED_LEMMAS       : thm_carrierLocalLaw_of_laterOccurrence_successor,
                            thm_carrier_rpass_iff_localLaw,
                            thm_carrier_rpassClause_order,
                            thm_carrier_rpassClause_endpointsDistinct,
                            thm_carrier_rpassClause_corridorEmpty
    WHY_EACH_LEMMA_EXISTS : le premier transcrit exactement `PCanonicalSuccession`
                            en loi locale ; le deuxième donne R-PASS par pure
                            équivalence ; les trois derniers en dérivent ordre,
                            séparation et corridor vide, sans nouvelle preuve.
    LEAN_DEFINITION       : PCanonicalSuccession
    LEAN_THEOREM          : thm_T2_localLaw, thm_T2_rpass,
                            thm_T2_order, thm_T2_endpointsDistinct,
                            thm_T2_corridorEmpty
    SAME_MEMBER_CHECK     : hérité de `TTrueTowerCarrier` et de
                            `fnCarrierPassagePlace`, qui lit uniquement les
                            deux extrémités PROPRES du passage.
    SAME_PASSAGE_CHECK    : la place est celle du MÊME passage, jamais d'un
                            second passage.
    SAME_MIDDLE_CHECK      : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : l'extrémité de sortie est indexée dans l'unique
                            histoire première de O6.
    FORBIDDEN_PREMISES    : analyser une largeur de cellule ou un écart entre
                            adresses pour en tirer la succession ; recevoir un
                            premier cible, un rang cible ou C3 comme hypothèse
                            libre ; substituer `tRatioFourOperator` ou
                            `tPrincipalBranchCarrier` au porteur générique.
    NEXT_CONSUMER         : la clause de nullité complète de R-PASS
                            (RPassFull.lean) et la contradiction terminale
                            SAME_PASSAGE.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED pour la composition ; `PCanonicalSuccession`
                            reste un Prop nommé, non prouvé ici — reçu comme
                            fait ACQUIS par le maître mathématique (§13.1),
                            exactement au même titre que `PUniqueCenterRegime`
                            de T1, jamais comme raccourci circulaire.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau. `PCanonicalSuccession`
n'est jamais utilisé silencieusement : il figure explicitement comme
hypothèse de chaque theorem qui en dépend, exactement comme
`PUniqueCenterRegime`.

Ce module NE PRETEND PAS clore la clause de nullité complète de R-PASS
(`PIsFullMemberSensitivePassageTransport`, RPassFull.lean) ni la
contradiction terminale SAME_PASSAGE : celles-ci restent l'étape suivante,
non produite ici.
-/

namespace RHV3Lean

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-! ## 1. La succession canonique, reçue comme acquise -/

/-- **La succession canonique.**  Pour tout passage réel, le premier central
de l'extrémité de sortie est exactement le successeur canonique du premier
central de l'extrémité d'entrée. C'est le contenu du théorème de composition
événementielle (maître mathématique §13.1, points 5-6, ACQUIS) : la grammaire
première, déjà fermée et infinie, force cet ordre — ce n'est jamais dérivé
ici d'une comparaison de largeur. -/
def PCanonicalSuccession : Prop :=
  ∀ tPassage : TZeroPassage,
    tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember =
      nPlaceLaterEndpoint (tCarrier.fnCarrierPassagePlace tPassage)

/-! ## 2. T2 : loi locale, R-PASS et ses trois clauses -/

/-- **T2 comme loi locale.**  Transcription directe de `PCanonicalSuccession`
en loi locale du transport, sur la place déjà construite depuis T1. -/
theorem thm_T2_localLaw (hSuccession : tCarrier.PCanonicalSuccession) :
    tCarrier.PLocalLawOnCarrier tCarrier.fnCarrierPassagePlace :=
  tCarrier.thm_carrierLocalLaw_of_laterOccurrence_successor hSuccession

/-- **R-PASS.**  Par pure équivalence avec la loi locale, sans nouvelle
preuve. -/
theorem thm_T2_rpass (hSuccession : tCarrier.PCanonicalSuccession) :
    tCarrier.PRPassOnCarrier tCarrier.fnCarrierPassagePlace :=
  thm_carrier_rpass_iff_localLaw.mpr (tCarrier.thm_T2_localLaw hSuccession)

/-- **Clause d'ordre.**  Le premier central de sortie dépasse strictement
celui d'entrée, pour tout passage réel. -/
theorem thm_T2_order (hSuccession : tCarrier.PCanonicalSuccession)
    (tPassage : TZeroPassage) :
    tCarrier.fnCarrierMemberCentralPrime tPassage.zEarlierMember <
      tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember :=
  thm_carrier_rpassClause_order (tCarrier.thm_T2_localLaw hSuccession) tPassage

/-- **Clause de séparation.**  Les deux extrémités propres d'un passage réel
ont des premiers centraux distincts — jamais R-ATT, jamais une hypothèse
séparée. -/
theorem thm_T2_endpointsDistinct (hSuccession : tCarrier.PCanonicalSuccession)
    (tPassage : TZeroPassage) :
    tCarrier.fnCarrierMemberCentralPrime tPassage.zEarlierMember ≠
      tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember :=
  thm_carrier_rpassClause_endpointsDistinct (tCarrier.thm_T2_localLaw hSuccession) tPassage

/-- **Clause de corridor vide.**  Aucun premier ne se glisse strictement
entre les deux premiers centraux d'un même passage réel. -/
theorem thm_T2_corridorEmpty (hSuccession : tCarrier.PCanonicalSuccession)
    (tPassage : TZeroPassage)
    {nCandidate : ℕ} (hPrime : Nat.Prime nCandidate)
    (hLeft : tCarrier.fnCarrierMemberCentralPrime tPassage.zEarlierMember < nCandidate)
    (hRight : nCandidate < tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember) :
    False :=
  thm_carrier_rpassClause_corridorEmpty (tCarrier.thm_T2_localLaw hSuccession)
    tPassage hPrime hLeft hRight

/-! ## 1bis. T1+T2 composés -- la hauteur du membre de sortie recouvrée par
inversion depuis la cellule QUE T2 a déjà placée au bon rang

Ceci répond directement à la question : « la grammaire connue des deux côtés
détermine-t-elle `T_{n+1}` ? ». Réponse composée depuis ce qui existe déjà,
sous les DEUX MÊMES prémisses T1 et T2, sans en ajouter une troisième : oui,
`T_{n+1}` se lit par inversion (`thm_carrierCell_heightInversion`,
inconditionnelle) sur la cellule qui, sous T1, capture exactement le premier
que T2 place au rang successeur -- ce n'est jamais la grammaire première SEULE
qui détermine `T_{n+1}`, c'est la cellule du membre de sortie (déjà là parce
que ce membre existe) dont T1+T2 identifient le contenu premier. -/

/-- **Recurrence T1+T2 : la cellule de sortie porte le successeur canonique,
et son inversion recouvre `T_{n+1}`.** Sous les deux mêmes prémisses nommées
T1 et T2, pour tout passage réel dont l'extrémité de sortie est de hauteur
strictement positive : (i) l'inversion de SA cellule redonne exactement sa
hauteur, inconditionnellement ; (ii) SA cellule capture bien un premier ;
(iii) ce premier capturé est exactement le premier central de l'extrémité de
sortie ; (iv) ce même premier central EST le successeur canonique placé par
T2. Aucune troisième prémisse : uniquement `hRegime` (T1) et `hSuccession`
(T2), déjà nommées, déjà comptées. -/
theorem thm_T1_T2_heightRecoveredAtSuccessorCell
    (hRegime : tCarrier.PUniqueCenterRegime)
    (hSuccession : tCarrier.PCanonicalSuccession)
    (tPassage : TZeroPassage)
    (hLaterUpper : 0 < rZeroHeight tPassage.zLaterMember) :
    (Real.pi /
        (Real.log (tCarrier.tCarrierCell ⟨tPassage.zLaterMember, hLaterUpper⟩).rRightEndpoint -
          Real.log (tCarrier.tCarrierCell ⟨tPassage.zLaterMember, hLaterUpper⟩).rLeftEndpoint) =
      rZeroHeight tPassage.zLaterMember) ∧
    ((tCarrier.tCarrierCell ⟨tPassage.zLaterMember, hLaterUpper⟩).rLeftEndpoint <
        (tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember : ℝ) ∧
      (tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember : ℝ) ≤
        (tCarrier.tCarrierCell ⟨tPassage.zLaterMember, hLaterUpper⟩).rRightEndpoint) ∧
    tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember =
      nPlaceLaterEndpoint (tCarrier.fnCarrierPassagePlace tPassage) := by
  set zUpper : TUpperNonTrivialZetaZero := ⟨tPassage.zLaterMember, hLaterUpper⟩ with hZUpperDef
  have hReprEq : zUpperRepresentative tPassage.zLaterMember = zUpper :=
    Subtype.ext (thm_upperRepresentativeMember_of_positiveHeight hLaterUpper)
  have hFoundNonempty : 0 < nCellFoundCount (tCarrier.tCarrierCell zUpper) := by
    rw [hRegime zUpper]; exact Nat.one_pos
  refine ⟨tCarrier.thm_carrierCell_heightInversion zUpper, ?_, hSuccession tPassage⟩
  have hInCell := tCarrier.thm_carrierCentralPrime_in_cell zUpper hFoundNonempty
  show (tCarrier.tCarrierCell zUpper).rLeftEndpoint <
      (tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember : ℝ) ∧
    (tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember : ℝ) ≤
      (tCarrier.tCarrierCell zUpper).rRightEndpoint
  unfold TTrueTowerCarrier.fnCarrierMemberCentralPrime
  rw [hReprEq]
  exact hInCell

end TTrueTowerCarrier

/-! ## 3. LA MÊME PRÉMISSE, reformulée EXACTEMENT en comptage -- rien de plus

`PCanonicalSuccession` a été reçu ci-dessus comme fait acquis, sur la place
déjà construite. Cette section montre que la SEULE différence de comptage
`pi(q) - pi(p) = 1` entre les deux premiers centraux -- reçue comme la MÊME
prémisse, sous une forme purement arithmétique, jamais comme un théorème --
suffit à la produire, en consommant le pont T2 déjà certifié
(`PrimeSuccessionBridge.lean`) et rien d'autre. Aucune identification de
premier, aucun centrage : uniquement l'égalité de deux comptages déjà
acquis pour chaque membre par T1. -/

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-- **LA PRÉMISSE, sous forme de comptage.** Pour tout passage réel, l'écart
entre les deux rangs de comptage des deux premiers centraux vaut un. C'est la
MÊME prémisse que `PCanonicalSuccession` -- ni plus faible, ni plus forte,
ni un théorème -- reformulée dans le vocabulaire de comptage demandé. -/
def PT2CountingSuccession : Prop :=
  ∀ tPassage : TZeroPassage,
    nPrimeCountRank (tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember) -
        nPrimeCountRank (tCarrier.fnCarrierMemberCentralPrime tPassage.zEarlierMember) =
      1

/-- **LA PRÉMISSE DE COMPTAGE SUFFIT.** Elle produit `PCanonicalSuccession`
sans rien ajouter : la primalité des deux premiers centraux est déjà acquise
par T1 (`thm_carrierMemberCentralPrime_isPrime`) ; le reste est le pont T2
déjà certifié (`thm_isNextPrime_of_countDiff_one`, `thm_isNextPrime_gives_rank`),
appliqué ici, jamais reproduit. -/
theorem thm_PCanonicalSuccession_of_countingHypothesis
    (hCount : tCarrier.PT2CountingSuccession) :
    tCarrier.PCanonicalSuccession := by
  intro tPassage
  have hp : Nat.Prime (tCarrier.fnCarrierMemberCentralPrime tPassage.zEarlierMember) :=
    tCarrier.thm_carrierMemberCentralPrime_isPrime _
  have hq : Nat.Prime (tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember) :=
    tCarrier.thm_carrierMemberCentralPrime_isPrime _
  have hSucc : PIsNextPrime (tCarrier.fnCarrierMemberCentralPrime tPassage.zEarlierMember)
      (tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember) :=
    thm_isNextPrime_of_countDiff_one hp hq (hCount tPassage)
  obtain ⟨hAtRank, hSuccRank⟩ := thm_isNextPrime_gives_rank hp hq hSucc
  have hRankEq :
      (nCellCentralRank
          (tCarrier.tCarrierCell (zUpperRepresentative tPassage.zEarlierMember)) - 1) =
        Nat.count Nat.Prime (tCarrier.fnCarrierMemberCentralPrime tPassage.zEarlierMember) := by
    apply thm_primeAtRank_injective
    rw [hAtRank]
    exact (tCarrier.thm_carrierPassagePlace_earlierEndpoint tPassage).symm
  show tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember =
    fnPrimeSuccessor
      (nCellCentralRank
          (tCarrier.tCarrierCell (zUpperRepresentative tPassage.zEarlierMember)) - 1)
  rw [hRankEq, hSuccRank]

end TTrueTowerCarrier

/-! ## 4. Ce que T1 seul donne par pur calcul, RIEN DE PLUS -- retrait de la
tentative de jonction entre cellules (objection reçue, retenue)

Objection reçue et retenue : comparer les DEUX cellules entre elles (leurs
bords) pour en tirer un "fait de jonction" ne sort de rien d'acquis -- ni de
T1, ni de la grammaire première -- et introduit une relation entre deux
membres que rien ne fournit. Ce paragraphe retire donc
`PCarrierCellsJoinAtSharedRank` et le theorem qui en dépendait. Seul reste ce
qui découle de T1 seul, sur UN SEUL membre à la fois : le rang de comptage du
premier central d'une cellule où T1 tient est exactement le rang au bord droit
de CETTE MEME cellule (pur calcul, aucune comparaison entre deux membres). -/

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-- **Le rang de comptage du premier central d'une cellule où T1 tient est
exactement le rang au bord droit de cette cellule.**  Pur calcul depuis
`nCellFoundCount = 1` (T1) : aucune autre hypothèse. -/
theorem thm_centralPrime_countRank_eq_rightEdgeRank
    (zUpperZero : TUpperNonTrivialZetaZero) (hRegime : tCarrier.PUniqueCenterRegime) :
    nPrimeCountRank (tCarrier.nCarrierCentralPrime zUpperZero) =
      nCellRightEdgeRank (tCarrier.tCarrierCell zUpperZero) := by
  have hFound : nCellFoundCount (tCarrier.tCarrierCell zUpperZero) = 1 := hRegime zUpperZero
  have hRank : nCellCentralRank (tCarrier.tCarrierCell zUpperZero) =
      nCellLeftEdgeRank (tCarrier.tCarrierCell zUpperZero) + 1 := by
    unfold nCellCentralRank; rw [hFound]
  have hCentral : tCarrier.nCarrierCentralPrime zUpperZero =
      fnPrimeAtRank (nCellLeftEdgeRank (tCarrier.tCarrierCell zUpperZero)) := by
    unfold TTrueTowerCarrier.nCarrierCentralPrime nCellCentralPrime
    rw [hRank]
    congr 1
  have hCountAtRank :
      Nat.count Nat.Prime (fnPrimeAtRank (nCellLeftEdgeRank (tCarrier.tCarrierCell zUpperZero))) =
        nCellLeftEdgeRank (tCarrier.tCarrierCell zUpperZero) :=
    Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime _
  have hRightEdge : nCellRightEdgeRank (tCarrier.tCarrierCell zUpperZero) =
      nCellLeftEdgeRank (tCarrier.tCarrierCell zUpperZero) + 1 := by
    have := thm_cellFoundCount_eq_edgeRankDifference (tCarrier.tCarrierCell zUpperZero)
    omega
  rw [hCentral]
  unfold nPrimeCountRank nEdgePrimeRank
  rw [Nat.floor_natCast, Nat.count_succ, if_pos (thm_primeAtRank_isPrime _), hCountAtRank,
    hRightEdge]

end TTrueTowerCarrier

/-! Surface audit. -/

#check @TTrueTowerCarrier.PCanonicalSuccession
#check @TTrueTowerCarrier.thm_T2_localLaw
#check @TTrueTowerCarrier.thm_T2_rpass
#check @TTrueTowerCarrier.thm_T2_order
#check @TTrueTowerCarrier.thm_T2_endpointsDistinct
#check @TTrueTowerCarrier.thm_T2_corridorEmpty
#check @TTrueTowerCarrier.PT2CountingSuccession
#check @TTrueTowerCarrier.thm_PCanonicalSuccession_of_countingHypothesis
#check @TTrueTowerCarrier.thm_centralPrime_countRank_eq_rightEdgeRank

end RHV3Lean
