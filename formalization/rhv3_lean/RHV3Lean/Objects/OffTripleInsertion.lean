/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TowerGrammarMorphism
import RHV3Lean.Objects.TowerTransitionOffSignature
import RHV3Lean.Objects.TowerPrimeGapSpan
import RHV3Lean.Objects.OffGrammarDetection

/-!
# RHV3Lean — insertion du couple miroir OFF entre deux voisins réels

    TRACE_ID              : RHV3-OFF-TRIPLE-INSERTION
    SEMANTIC_OBJECT       : quatre membres localement ordonnés
                            `zPrev -> zA -> zB -> zNext`, où `zA` et `zB` sont
                            EXACTEMENT l'original et le miroir d'un couple hors
                            ligne, portant trois passages membre-sensibles ;
                            et la métrique `D` (`TowerPrimeGapSpan`) lue sur le
                            passage central, dont l'écart de hauteur est nul.
    SEMANTIC_STATEMENT    : le passage central `zA -> zB` a, par construction
                            déjà produite, un écart de hauteur nul. Ce module
                            en tire la conséquence EXACTE, et rien de plus :
                            sur l'arête que CE PASSAGE LUI-MÊME produit (celle
                            dont l'entrée est le premier central de `zA`), la
                            lecture de portée par `zB` coïncide EXACTEMENT avec
                            la lecture de portée par `zA` — même lecture
                            métrique du passage premier, alors que les deux
                            membres restent des états de Tour distincts (`beta`
                            et `phi` différents, `TowerTransitionOffSignature`).
                            Ce module NE CONCLUT PAS que les deux membres
                            produisent le même rang canonique : cette question
                            plus forte reste, sans changement, exactement
                            `PMirrorCollision` (`OffGrammarDetection.lean`).
                            La question de cardinalité (§11 de la mission :
                            trois passages membre-sensibles ne peuvent pas
                            s'injecter fidèlement dans seulement deux
                            transitions premières adjacentes) est nommée ici,
                            PRÉCISÉMENT, et montrée dépendre de trois faits de
                            succession de rang non produits — jamais posée
                            comme hypothèse ni comme axiome.
    MATHEMATICAL_STATEMENT: Q := (tCarrier, zPrev, zOff, zNext, SPrev, SNext) ;
                            zA := original(zOff), zB := mirror(zOff) ;
                            T1 := zPrev -> zA, T2 := zA -> zB (= tOffTransition),
                            T3 := zB -> zNext ;
                            T2.heightGap = 0 (déjà produit) ⟹, pour TOUT rang
                            `n`, TowerPrimeGapSpan zB n = TowerPrimeGapSpan zA n
                            (`thm_towerPrimeGapSpan_eq_of_heightGap_zero`) ; en
                            particulier pour `n = nPassageGrammarRank T2` ;
                            POffChainPreservesCardinality Q :=
                              PPassageReachesOwnLaterMember T1 ∧
                              PPassageReachesOwnLaterMember T2 ∧
                              PPassageReachesOwnLaterMember T3
                            — nommé, jamais reçu en hypothèse, jamais prouvé.
    MATHEMATICAL_PARENT   : `TowerGrammarMorphism.lean` (le morphisme et sa
                            cible non produite), `TowerTransitionOffSignature.lean`
                            (heightGap=0 du passage OFF), `TowerPrimeGapSpan.lean`
                            (`thm_towerPrimeGapSpan_eq_of_heightGap_zero`, ajouté
                            ce tour), `OffGrammarDetection.lean` (`PMirrorCollision`
                            relu comme entrée de l'image grammaticale).
    PROOF_STRATEGY        : aucune construction analytique nouvelle. Le seul
                            fait mobilisé est l'écart de hauteur nul du passage
                            OFF déjà produit, transporté par la loi de portée
                            déjà produite ce tour ; la cardinalité n'est ni
                            prouvée ni contournée, seulement isolée dans un
                            `Prop` nommé qui rend explicites SES TROIS
                            composantes exactes.
    REQUIRED_LEMMAS       : TTrueTowerCarrier.thm_offTransition_heightGap_zero,
                            thm_towerPrimeGapSpan_eq_of_heightGap_zero,
                            PPassageReachesOwnLaterMember
    WHY_EACH_LEMMA_EXISTS : le premier donne la nullité de hauteur du passage
                            central ; le second la transporte en égalité de
                            portée sur une arête quelconque ; le troisième nomme
                            exactement ce que chacun des trois maillons de la
                            chaîne devrait satisfaire pour que la chaîne se
                            recolle fidèlement sur seulement deux transitions
                            premières adjacentes.
    LEAN_DEFINITION       : TOffQuadrupleInsertion, zAOf, zBOf, SAOf, SBOf,
                            tFirstInsertionTransition, tCentralInsertionTransition,
                            tLastInsertionTransition
    LEAN_THEOREM          : thm_offCentral_sameArete_sameSpan_atOwnRank
    LEAN_PROP_TARGET      : POffChainPreservesCardinality — nomme le contenu
                            exact du §11 de la mission, jamais reçu en
                            hypothèse par aucun théorème de ce module.
    SAME_MEMBER_CHECK     : `zAOf`/`zBOf`/`SAOf`/`SBOf` lisent exclusivement
                            `Q.zOff` et `Q.tCarrier` ; aucune substitution.
    SAME_PASSAGE_CHECK    : chaque transition de la chaîne porte sur SON SEUL
                            couple d'extrémités ; `tCentralInsertionTransition`
                            EST, par construction, `Q.tCarrier.tOffTransition
                            Q.zOff`, jamais un passage synthétique distinct.
    SAME_MIDDLE_CHECK     : sans objet — ce module ne prétend à aucun membre
                            médian partagé entre `T1`/`T2`/`T3` ; c'est
                            précisément la question ouverte (les trois maillons
                            sont a priori sur trois membres deux à deux
                            distincts).
    SAME_HISTORY_CHECK    : chaque image grammaticale est indexée dans l'unique
                            histoire première de O6, comme dans
                            `TowerGrammarMorphism.lean`.
    FORBIDDEN_PREMISES    : un ordre supposé entre `zA` et `zB` non produit par
                            ailleurs ; `PMirrorCollision`, `PCentralPrimeInjective`,
                            `PPassageReachesOwnLaterMember` reçus en hypothèse ;
                            T1, T2, R-PASS, `PNullPassageForcesNullPlace`,
                            `PCanonicalSuccession`, `PUniqueCenterRegime` ;
                            l'hypothèse de Riemann ou sa négation ; conclure une
                            contradiction de cardinalité sans l'avoir produite.
    NEXT_CONSUMER         : aucun — ce module s'arrête au premier `Prop` exact
                            qui isole la question de cardinalité, conformément
                            à la consigne de ne jamais la poser comme prémisse.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED — DIAGNOSTIC SEUL, comme
                            `OffGrammarDetection.lean`. La question de
                            cardinalité (§11) reste ouverte ; ce module en donne
                            la forme exacte, en trois maillons nommés, sans
                            jamais la recevoir comme hypothèse.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

open TTrueTowerCarrier

/-! ## 1. Le quadruple, membre-sensible, sans ordre supposé -/

/-- **Les quatre membres localement ordonnés**, avec le couple miroir OFF
inséré au centre. -/
structure TOffQuadrupleInsertion where
  /-- Le porteur de Tour sous lequel le couple OFF est lu. -/
  tCarrier : TTrueTowerCarrier
  /-- Le membre antérieur au couple. -/
  zPrev : TUpperNonTrivialZetaZero
  /-- Le couple miroir hors ligne. -/
  zOff : TOffCriticalLineUpperZero
  /-- Le membre postérieur au couple. -/
  zNext : TUpperNonTrivialZetaZero
  /-- L'état propre du membre antérieur. -/
  SPrev : TTrueHarmonicTowerState zPrev
  /-- L'état propre du membre postérieur. -/
  SNext : TTrueHarmonicTowerState zNext

/-- Le membre original du couple OFF. -/
noncomputable def zAOf (Q : TOffQuadrupleInsertion) : TUpperNonTrivialZetaZero :=
  offOriginalUpperMember Q.zOff

/-- Le membre miroir du couple OFF. -/
noncomputable def zBOf (Q : TOffQuadrupleInsertion) : TUpperNonTrivialZetaZero :=
  offMirrorUpperMember Q.zOff

/-- L'état propre du membre original, sous le porteur de `Q`. -/
noncomputable def SAOf (Q : TOffQuadrupleInsertion) : TTrueHarmonicTowerState (zAOf Q) :=
  Q.tCarrier.fnState (zAOf Q)

/-- L'état propre du membre miroir, sous le porteur de `Q`. -/
noncomputable def SBOf (Q : TOffQuadrupleInsertion) : TTrueHarmonicTowerState (zBOf Q) :=
  Q.tCarrier.fnState (zBOf Q)

/-! ## 2. Les trois passages membre-sensibles -/

/-- Le premier passage : du membre antérieur vers l'original OFF. -/
noncomputable def tFirstInsertionTransition (Q : TOffQuadrupleInsertion) :
    TTowerMemberTransition where
  zLeft := Q.zPrev
  zRight := zAOf Q
  SLeft := Q.SPrev
  SRight := SAOf Q

/-- Le passage central : EXACTEMENT le passage OFF déjà produit, sans aucune
construction supplémentaire. -/
noncomputable def tCentralInsertionTransition (Q : TOffQuadrupleInsertion) :
    TTowerMemberTransition :=
  Q.tCarrier.tOffTransition Q.zOff

/-- Le dernier passage : du miroir OFF vers le membre postérieur. -/
noncomputable def tLastInsertionTransition (Q : TOffQuadrupleInsertion) :
    TTowerMemberTransition where
  zLeft := zBOf Q
  zRight := Q.zNext
  SLeft := SBOf Q
  SRight := Q.SNext

/-! ## 3. Ce que la nullité de hauteur centrale produit réellement -/

/-- **Sur l'arête que le passage central produit lui-même, les deux membres
du couple OFF lisent EXACTEMENT la même portée première.**  Conséquence
directe et SEULE conséquence tirée ici de `heightGap = 0` : aucune coïncidence
de rang canonique n'est affirmée, seulement l'égalité de la lecture métrique
`D`, sur cette arête précise, entre le membre original et son miroir. -/
theorem thm_offCentral_sameArete_sameSpan_atOwnRank (Q : TOffQuadrupleInsertion) :
    TowerPrimeGapSpan (zBOf Q) (nPassageGrammarRank (tCentralInsertionTransition Q)) =
      TowerPrimeGapSpan (zAOf Q) (nPassageGrammarRank (tCentralInsertionTransition Q)) :=
  thm_towerPrimeGapSpan_eq_of_heightGap_zero (tCentralInsertionTransition Q)
    (Q.tCarrier.thm_offTransition_heightGap_zero Q.zOff) _

/-- **La même égalité de portée vaut en réalité sur TOUTE arête `n`**, pas
seulement celle produite par le passage lui-même : c'est la portée de
`thm_towerPrimeGapSpan_eq_of_heightGap_zero`, transportée telle quelle sur ce
couple précis. -/
theorem thm_offCentral_sameSpan_allRanks (Q : TOffQuadrupleInsertion) (nRank : ℕ) :
    TowerPrimeGapSpan (zBOf Q) nRank = TowerPrimeGapSpan (zAOf Q) nRank :=
  thm_towerPrimeGapSpan_eq_of_heightGap_zero (tCentralInsertionTransition Q)
    (Q.tCarrier.thm_offTransition_heightGap_zero Q.zOff) nRank

/-! ## 4. La cible exacte du §11 — nommée, jamais reçue -/

/-- **LA CIBLE DE CARDINALITÉ, nommée en ses trois maillons exacts.**

Trois passages membre-sensibles (`T1`, `T2`, `T3`) s'injectent fidèlement dans
seulement deux transitions premières adjacentes exactement quand chacun de ses
trois maillons atteint son propre membre de sortie — c'est-à-dire quand
`PPassageReachesOwnLaterMember` est vraie sur CHACUN des trois. Si l'un des
trois maillons échoue, la chaîne des trois passages ne se recolle PAS sur une
seule paire de transitions adjacentes de l'histoire première : c'est
exactement, et seulement, le contenu à établir pour clore le §11.

AUCUN théorème de ce module ne reçoit ce `Prop` en hypothèse. -/
def POffChainPreservesCardinality (Q : TOffQuadrupleInsertion) : Prop :=
  PPassageReachesOwnLaterMember (tFirstInsertionTransition Q) ∧
    PPassageReachesOwnLaterMember (tCentralInsertionTransition Q) ∧
      PPassageReachesOwnLaterMember (tLastInsertionTransition Q)

/-! Surface audit. -/

#check TOffQuadrupleInsertion
#check tFirstInsertionTransition
#check tCentralInsertionTransition
#check tLastInsertionTransition
#check thm_offCentral_sameArete_sameSpan_atOwnRank
#check thm_offCentral_sameSpan_allRanks
#check POffChainPreservesCardinality

end RHV3Lean
