/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TowerTransition
import RHV3Lean.Objects.CountingRigidity
import RHV3Lean.Objects.PlaceAndLocalLaw
import RHV3Lean.Objects.PrimeTransitionGrammar

/-!
# RHV3Lean — le morphisme grammatical : passage de Tour vers transition première

    TRACE_ID              : RHV3-TOWER-GRAMMAR-MORPHISM
    SEMANTIC_OBJECT       : le morphisme qui envoie un passage entre deux Tours
                            propres sur une transition première canonique de
                            l'unique histoire première — sans recevoir de rang,
                            de premier cible, ni aucune des `Prop` fermées T1,
                            T2, R-PASS, `PNullPassageForcesNullPlace`,
                            `PCanonicalSuccession`, `PUniqueCenterRegime`.
    SEMANTIC_STATEMENT    : le rang `n` n'est jamais un entier libre choisi
                            pour faire fonctionner une formule.  Il est PRODUIT
                            par la cellule propre de l'extrémité d'entrée du
                            passage, via le comptage O10 déjà inconditionnel
                            (`nCellCentralRank`/`nCellCentralPrime`), lui-même
                            lu sur la cellule que la vraie Tour a construite
                            (O4).  Aucune adresse choisie depuis un premier,
                            aucune réinitialisation au seuil `2` : les contacts
                            reçus par `TTrueHarmonicTowerState` sont abstraits,
                            contraints par les deux seules lois exactes de la
                            Tour, jamais par une recherche d'adresse.
    MATHEMATICAL_STATEMENT: n(E) := nCellCentralRank(S_gauche.terminalCell) - 1 ;
                            ZeroPassageGrammarPlace(E) := ⟨n(E)⟩ ;
                            GrammarImageEarlier(E) = p_(n(E))
                              = nCellCentralPrime(S_gauche.terminalCell) — PAR
                              CONSTRUCTION, sans hypothèse ;
                            GrammarImageLater(E) = p_(n(E)+1) ;
                            GrammarImageEarlier(E) < GrammarImageLater(E).
                            CE QUI N'EST PAS PRODUIT ICI, nommé mais non
                            démontré, non reçu comme hypothèse nulle part :
                            GrammarImageLater(E) = nCellCentralPrime
                              (S_droite.terminalCell) — l'égalité du premier
                              successeur arithmétique avec le premier central
                              PROPRE du membre de sortie.  C'est exactement le
                              contenu de T2, jamais posé.
    MATHEMATICAL_PARENT   : O4/O10 — la cellule propre et son comptage
                            (`ContactsAndCell.lean`, `CountingRigidity.lean`) ;
                            O5 — l'occurrence première (`PrimeOccurrence.lean`,
                            `tMemberPrimeOccurrence`) ; la place et sa loi
                            locale (`PlaceAndLocalLaw.lean`) ; O6/grammaire
                            (`PrimeTransitionGrammar.lean`).
    PROOF_STRATEGY        : `ZeroPassageGrammarPlace` ne fait qu'assembler des
                            objets déjà totalement définis (`nCellCentralRank`
                            n'a besoin d'aucune hypothèse de non-vacuité ou de
                            singleton pour exister) ; `GrammarImageEarlier`
                            coïncide avec le premier central du membre gauche
                            par dépliage pur (`rfl`) ; la stricte positivité de
                            l'écart vient directement de O6
                            (`thm_place_gap_positive`) ; la lettre
                            grammaticale du rang produit est celle, déjà
                            certifiée, de `PrimeTransitionGrammar.lean`.
    REQUIRED_LEMMAS       : nCellCentralRank, nCellCentralPrime,
                            nPlaceEarlierEndpoint, nPlaceLaterEndpoint,
                            thm_place_gap_positive, thm_transition_exhaustive
    WHY_EACH_LEMMA_EXISTS : les deux premiers produisent le rang et le premier
                            central sans aucune hypothèse ; les deux suivants
                            relisent ce rang comme place de l'histoire première ;
                            le cinquième donne la séparation stricte des deux
                            extrémités ; le dernier donne la lettre
                            grammaticale certifiée du rang produit.
    LEAN_DEFINITION       : nPassageGrammarRank, ZeroPassageGrammarPlace,
                            GrammarImageEarlier, GrammarImageLater
    LEAN_THEOREM          : thm_grammarImageEarlier_eq_leftCentralPrime,
                            thm_grammarImage_gap_positive,
                            thm_grammarImage_transition_exhaustive
    LEAN_PROP_TARGET      : PPassageReachesOwnLaterMember — NOMME la cible non
                            produite (§ ci-dessus), n'est reçue en hypothèse
                            par AUCUN théorème de ce module.
    SAME_MEMBER_CHECK     : `nPassageGrammarRank` lit exclusivement la cellule
                            propre de `Tr.SLeft`, jamais une cellule
                            synthétique ni celle d'un autre membre.
    SAME_PASSAGE_CHECK    : toutes les quantités de ce module sont fonctions du
                            MÊME `Tr : TTowerMemberTransition`.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau — c'est exactement l'objet
                            du module suivant (`TripleGrammarEvolution.lean`),
                            qui applique ce morphisme aux deux passages d'un
                            triple et teste si les deux places produites
                            partagent leur extrémité médiane.
    SAME_HISTORY_CHECK    : la place produite est indexée dans l'unique
                            histoire première de O6 (`fnPrimeAtRank`).
    FORBIDDEN_PREMISES    : T1, T2, R-PASS, `PNullPassageForcesNullPlace`,
                            `PCanonicalSuccession`, `PUniqueCenterRegime`, un
                            rang cible, un premier cible, une adresse choisie
                            depuis un premier ; stocker
                            `PPassageReachesOwnLaterMember` comme un champ de
                            structure destiné à être reçu ailleurs.
    NEXT_CONSUMER         : `TripleGrammarEvolution.lean` (structure à trois
                            membres, test de l'adjacence des deux places),
                            `OffGrammarDetection.lean` (insertion du passage
                            OFF dans ce même morphisme).
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED — la cible `T2` nommée en
                            `PPassageReachesOwnLaterMember` reste NON prouvée et
                            n'est reçue nulle part.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

/-! ## 0. Le rang produit par un MEMBRE — avant tout passage -/

/-- **Le rang premier canonique d'un membre.**  Fonction du seul état propre
`S` du membre — jamais d'un passage entier, jamais d'une paire.  C'est
l'objet que réclame T14/§4 : un `memberPrimeRank : Membre -> Nat`, dont
`nPassageGrammarRank` ci-dessous n'est plus qu'une LECTURE à l'extrémité
gauche d'un passage donné, et jamais une construction indépendante. -/
noncomputable def memberPrimeRank {z : TUpperNonTrivialZetaZero}
    (S : TTrueHarmonicTowerState z) : ℕ :=
  nCellCentralRank S.terminalCell - 1

/-! ## 1. Le rang produit par un passage -/

/-- **Le rang grammatical produit par un passage.**  Il n'est jamais choisi :
c'est le rang du premier central de la cellule PROPRE de l'extrémité d'entrée,
déjà totalement défini par O10, sans aucune hypothèse de non-vacuité ni de
singleton. -/
noncomputable def nPassageGrammarRank (Tr : TTowerMemberTransition) : ℕ :=
  nCellCentralRank Tr.SLeft.terminalCell - 1

/-- **`nPassageGrammarRank` EST `memberPrimeRank` lu à l'extrémité gauche.**
Le rang du passage n'est pas un objet indépendant du rang du membre : c'est
littéralement la même définition, appliquée au seul état `Tr.SLeft`. -/
theorem thm_nPassageGrammarRank_eq_memberPrimeRank_left (Tr : TTowerMemberTransition) :
    nPassageGrammarRank Tr = memberPrimeRank Tr.SLeft := rfl

/-- **La place grammaticale produite par le passage.** -/
noncomputable def ZeroPassageGrammarPlace (Tr : TTowerMemberTransition) :
    TPrimeHistoryPlace :=
  ⟨nPassageGrammarRank Tr⟩

/-- **L'extrémité d'entrée de l'image grammaticale**, `p_(n(E))`. -/
noncomputable def GrammarImageEarlier (Tr : TTowerMemberTransition) : ℕ :=
  nPlaceEarlierEndpoint (ZeroPassageGrammarPlace Tr)

/-- **L'extrémité de sortie de l'image grammaticale**, `p_(n(E)+1)`. -/
noncomputable def GrammarImageLater (Tr : TTowerMemberTransition) : ℕ :=
  nPlaceLaterEndpoint (ZeroPassageGrammarPlace Tr)

/-! ## 2. L'entrée est produite, PAR CONSTRUCTION, sans hypothèse -/

/-- **L'extrémité d'entrée de l'image grammaticale EST le premier central de la
cellule propre du membre d'entrée.**  Ce n'est ni supposé ni reconstruit après
coup : c'est un dépliage pur des définitions — `nPlaceEarlierEndpoint` et
`nCellCentralPrime` sont, à un renommage près, la même application de
`fnPrimeAtRank` au même rang. -/
theorem thm_grammarImageEarlier_eq_leftCentralPrime (Tr : TTowerMemberTransition) :
    GrammarImageEarlier Tr = nCellCentralPrime Tr.SLeft.terminalCell := rfl

/-! ## 3. La séparation stricte des deux extrémités, héritée de O6 -/

/-- **L'image grammaticale a deux extrémités strictement ordonnées.**  Elle
vient de la positivité primitive de l'écart premier (O6), jamais d'une
hypothèse sur le passage lui-même. -/
theorem thm_grammarImage_gap_positive (Tr : TTowerMemberTransition) :
    GrammarImageEarlier Tr < GrammarImageLater Tr :=
  thm_place_gap_positive (ZeroPassageGrammarPlace Tr)

/-! ## 4. La lettre grammaticale de la place produite -/

/-- **La place produite par le passage porte l'une des quatre lettres
certifiées de la grammaire**, dès que son premier d'entrée dépasse `3`.
Corollaire direct de `thm_transition_exhaustive`, appliqué au SEUL rang produit
par CE passage. -/
theorem thm_grammarImage_transition_exhaustive (Tr : TTowerMemberTransition)
    (hGtThree : 3 < GrammarImageEarlier Tr) :
    PPrimeTransitionAtRank .keep11 (nPassageGrammarRank Tr) ∨
      PPrimeTransitionAtRank .switch15 (nPassageGrammarRank Tr) ∨
      PPrimeTransitionAtRank .switch51 (nPassageGrammarRank Tr) ∨
      PPrimeTransitionAtRank .keep55 (nPassageGrammarRank Tr) :=
  thm_transition_exhaustive hGtThree

/-! ## 5. La cible NON produite — nommée, jamais reçue -/

/-- **LA CIBLE NON PRODUITE.**

Ce `Prop` nomme exactement ce qu'il faudrait démontrer pour que l'extrémité de
sortie de l'image grammaticale soit le premier central PROPRE du membre de
sortie du passage, et non seulement le successeur arithmétique du premier
central du membre d'entrée.  C'est le contenu exact de T2 (succession
canonique), relu comme fidélité du morphisme.

AUCUN théorème de ce fichier ne reçoit ce `Prop` en hypothèse : il n'est pas
stocké comme champ de `TTowerMemberTransition`, il n'est composé nulle part
ci-dessus.  Il est seulement nommé, pour qu'aucune étape ultérieure ne puisse
le recevoir silencieusement comme prémisse. -/
def PPassageReachesOwnLaterMember (Tr : TTowerMemberTransition) : Prop :=
  GrammarImageLater Tr = nCellCentralPrime Tr.SRight.terminalCell

/-! ## 6. La cible NON produite, relue comme succession de RANGS -/

/-- **`PPassageReachesOwnLaterMember` EST exactement la succession des deux
rangs de membre, `memberPrimeRank` à droite = `memberPrimeRank` à gauche + 1.**

Ce théorème ne prouve rien de nouveau sur la cible : il en donne la forme la
plus dépouillée possible, au niveau des RANGS (des `ℕ`) plutôt que des
PREMIERS eux-mêmes, en utilisant l'injectivité de `fnPrimeAtRank` (O6).  C'est
la forme demandée par T14/§4/§12 : « le rang du membre de sortie est le
successeur du rang du membre d'entrée » — un fait de succession de rang, pas
un fait de coïncidence de premier. Il reste, comme `PPassageReachesOwnLaterMember`
lui-même, NON prouvé pour un passage quelconque : aucune hypothèse
supplémentaire n'est introduite ici, seule la forme change. -/
theorem thm_reachesOwnLaterMember_iff_rank_succ (Tr : TTowerMemberTransition) :
    PPassageReachesOwnLaterMember Tr ↔
      nPassageGrammarRank Tr + 1 = memberPrimeRank Tr.SRight := by
  unfold PPassageReachesOwnLaterMember GrammarImageLater ZeroPassageGrammarPlace
    nPlaceLaterEndpoint fnPrimeSuccessor nCellCentralPrime memberPrimeRank
  exact ⟨fun h => thm_primeAtRank_injective h, fun h => congrArg fnPrimeAtRank h⟩

/-! Surface audit. -/

#check memberPrimeRank
#check nPassageGrammarRank
#check thm_nPassageGrammarRank_eq_memberPrimeRank_left
#check ZeroPassageGrammarPlace
#check GrammarImageEarlier
#check GrammarImageLater
#check thm_grammarImageEarlier_eq_leftCentralPrime
#check thm_grammarImage_gap_positive
#check thm_grammarImage_transition_exhaustive
#check PPassageReachesOwnLaterMember
#check thm_reachesOwnLaterMember_iff_rank_succ

end RHV3Lean
