/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TowerGrammarMorphism
import RHV3Lean.Objects.TowerTransitionOffSignature
import RHV3Lean.Objects.SamePrimeCollision

/-!
# RHV3Lean — insertion du passage OFF dans le morphisme grammatical produit

    TRACE_ID              : RHV3-OFF-GRAMMAR-DETECTION
    SEMANTIC_OBJECT       : le passage miroir hors ligne, inséré SANS AUCUNE
                            CONSTRUCTION SUPPLÉMENTAIRE dans le même morphisme
                            que tout passage réel (`ZeroPassageGrammarPlace`,
                            `GrammarImageEarlier`, `GrammarImageLater`), pour
                            déterminer, et NON supposer, laquelle des quatre
                            issues nommées par la mission (A/B/C/D) ce
                            morphisme produit réellement.
    SEMANTIC_STATEMENT    : le passage OFF ne reçoit AUCUN traitement
                            particulier : `GrammarImageEarlier` de son passage
                            se déplie, EXACTEMENT COMME POUR TOUT AUTRE
                            PASSAGE, sur le premier central propre du membre
                            d'entrée — ici le membre original.  Ce fait, à lui
                            seul, montre que l'issue B (deux membres distincts
                            envoyés sur la MÊME occurrence) est la SEULE des
                            quatre dont la question se pose littéralement dans
                            les mêmes termes qu'une question déjà nommée dans
                            ce corpus (`PMirrorCollision`), ni renforcée ni
                            affaiblie.  L'issue D, lue naïvement comme
                            `PPassageReachesOwnLaterMember` appliqué au passage
                            OFF lui-même, se révèle être une question
                            DIFFÉRENTE et PLUS FORTE que la collision miroir
                            déjà nommée : elle exigerait que le premier central
                            du miroir soit le SUCCESSEUR ARITHMÉTIQUE du
                            premier central de l'original, pas seulement son
                            égal.  Les issues A et C ne sont produites par
                            AUCUNE construction de ce module.
    MATHEMATICAL_STATEMENT: GrammarImageEarlier(tOffTransition zOff)
                              = nCarrierCentralPrime(original) — PRODUIT, sans
                              hypothèse, par simple dépliage ;
                            GrammarImageEarlier(tOffTransition zOff)
                              = nCarrierCentralPrime(mirror)
                              ↔ nCarrierCentralPrime(original)
                                = nCarrierCentralPrime(mirror)
                              — c'est-à-dire EXACTEMENT `PMirrorCollision`
                              évalué en ce `zOff`, ni plus ni moins ;
                            PPassageReachesOwnLaterMember(tOffTransition zOff)
                              ↔ fnPrimeSuccessor(rang de l'original)
                                = nCarrierCentralPrime(mirror) — une égalité de
                              SUCCESSION, distincte de la collision d'égalité.
    MATHEMATICAL_PARENT   : `TowerGrammarMorphism.lean`,
                            `TowerTransitionOffSignature.lean` (signature
                            hauteur/largeur nulles, radial/phase non nuls),
                            `SamePrimeCollision.lean` (`PMirrorCollision`,
                            `PCentralPrimeInjective`, déjà nommés,
                            explicitement PAS prouvés dans ce corpus).
    PROOF_STRATEGY        : aucune construction nouvelle n'est nécessaire —
                            uniquement un dépliage exact des définitions déjà
                            produites (`GrammarImageEarlier`,
                            `nCarrierCentralPrime`, `tCarrierCell`,
                            `terminalCell`, `tOffTransition`), qui coïncident
                            toutes par construction sur la même cellule du même
                            porteur.  Aucune borne, aucune approximation,
                            aucune hypothèse de croissance.
    REQUIRED_LEMMAS       : thm_grammarImageEarlier_eq_leftCentralPrime,
                            TTrueTowerCarrier.thm_carrierCentralPrime_is_C3,
                            PMirrorCollision, PPassageReachesOwnLaterMember
    WHY_EACH_LEMMA_EXISTS : le premier donne l'entrée produite du morphisme sur
                            n'importe quel passage ; le second identifie la
                            cellule lue par le porteur avec la cellule propre
                            de l'état ; les deux derniers sont les cibles déjà
                            nommées, dont ce module précise exactement le lien
                            au morphisme, sans les prouver.
    LEAN_DEFINITION       : (aucune nouvelle définition — assemblage seul)
    LEAN_THEOREM          : thm_offGrammarImageEarlier_eq_originalCentralPrime,
                            thm_offGrammarImageEarlier_eq_mirrorCentralPrime_iff,
                            thm_offReachesOwnLaterMember_iff_successorCollision
    SAME_MEMBER_CHECK     : chaque quantité lit exclusivement le membre
                            (original ou miroir) que sa propre définition
                            nomme ; aucune substitution n'est exprimable.
    SAME_PASSAGE_CHECK    : toutes les clauses portent sur LE MÊME passage
                            `tCarrier.tOffTransition zOff`.
    SAME_MIDDLE_CHECK     : sans objet — un seul passage, pas de triple, ici.
    SAME_HISTORY_CHECK    : la place produite est indexée dans l'unique
                            histoire première de O6, comme pour tout passage.
    FORBIDDEN_PREMISES    : `PMirrorCollision`, `PCentralPrimeInjective`, T1,
                            T2, R-PASS, `PNullPassageForcesNullPlace`,
                            `PCanonicalSuccession`, `PUniqueCenterRegime`,
                            l'hypothèse de Riemann ou sa négation ; choisir à
                            l'avance l'issue A/B/C/D — ce module ne fait que
                            RÉVÉLER que B est la question qui se pose
                            réellement, jamais ne la RÉSOUT.
    NEXT_CONSUMER         : aucun — ce module s'arrête au premier théorème
                            exact qui manque, conformément à la consigne. La
                            fermeture reste exactement `PMirrorCollision ∧
                            PCentralPrimeInjective`, déjà nommée et non prouvée
                            dans `SamePrimeCollision.lean`.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED — DIAGNOSTIC SEUL. Aucune des quatre
                            issues A/B/C/D n'est close ; ce module détermine
                            SEULEMENT laquelle est la question posée par la
                            construction, et montre que ce n'est PAS D dans sa
                            lecture naïve.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

open TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-! ## 1. Le passage OFF, inséré sans traitement particulier -/

/-- **L'entrée de l'image grammaticale du passage OFF EST le premier central
propre du membre original.**  Aucun traitement spécial : c'est exactement
`thm_grammarImageEarlier_eq_leftCentralPrime`, appliqué à CE passage, puis
identifié à `nCarrierCentralPrime` par dépliage pur — `tCarrierCell` et
`terminalCell` sont, champ par champ, la même cellule. -/
theorem thm_offGrammarImageEarlier_eq_originalCentralPrime
    (zOff : TOffCriticalLineUpperZero) :
    GrammarImageEarlier (tCarrier.tOffTransition zOff) =
      tCarrier.nCarrierCentralPrime (offOriginalUpperMember zOff) := by
  rw [thm_grammarImageEarlier_eq_leftCentralPrime]
  rfl

/-! ## 2. L'issue B, dans ses propres termes, sans plus ni moins -/

/-- **L'issue B, exactement dans les termes déjà nommés.**

L'entrée de l'image grammaticale du passage OFF coïncide avec le premier
central PROPRE du miroir exactement quand `PMirrorCollision` (déjà nommé dans
`SamePrimeCollision.lean`, explicitement non prouvé) est vraie en ce `zOff`.
Aucune construction supplémentaire n'a été nécessaire : insérer OFF dans le
morphisme produit ne pose AUCUNE nouvelle question — c'est LITTÉRALEMENT la
même question. -/
theorem thm_offGrammarImageEarlier_eq_mirrorCentralPrime_iff
    (zOff : TOffCriticalLineUpperZero) :
    GrammarImageEarlier (tCarrier.tOffTransition zOff) =
        tCarrier.nCarrierCentralPrime (offMirrorUpperMember zOff) ↔
      tCarrier.nCarrierCentralPrime (offOriginalUpperMember zOff) =
        tCarrier.nCarrierCentralPrime (offMirrorUpperMember zOff) := by
  rw [thm_offGrammarImageEarlier_eq_originalCentralPrime]

/-! ## 3. L'issue D, lue naïvement, est une question PLUS FORTE et DIFFÉRENTE -/

/-- **L'issue D, lue naïvement sur le passage OFF lui-même, n'est PAS la
collision miroir.**

`PPassageReachesOwnLaterMember` appliqué au passage OFF exigerait que le
premier central du miroir soit le SUCCESSEUR ARITHMÉTIQUE du premier central
de l'original — une coïncidence de succession, distincte et plus forte que la
simple égalité de `PMirrorCollision`.  Rien dans la signature OFF déjà
produite (`heightGap = 0`, `widthGap = 0`) n'a d'incidence sur cette
quantité : `nPassageGrammarRank` ne lit que la cellule du membre d'ENTRÉE, donc
`GrammarImageLater` du passage OFF est calculé exactement comme pour tout
passage ordinaire de même entrée, indépendamment de ce qui se trouve à
droite. -/
theorem thm_offReachesOwnLaterMember_iff_successorCollision
    (zOff : TOffCriticalLineUpperZero) :
    PPassageReachesOwnLaterMember (tCarrier.tOffTransition zOff) ↔
      fnPrimeSuccessor (nPassageGrammarRank (tCarrier.tOffTransition zOff)) =
        tCarrier.nCarrierCentralPrime (offMirrorUpperMember zOff) := by
  constructor
  · intro h; exact h
  · intro h; exact h

/-! Surface audit. -/

#check thm_offGrammarImageEarlier_eq_originalCentralPrime
#check thm_offGrammarImageEarlier_eq_mirrorCentralPrime_iff
#check thm_offReachesOwnLaterMember_iff_successorCollision

end RHV3Lean
