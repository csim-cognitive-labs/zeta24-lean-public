/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.OffGrammarDetection

/-!
# RHV3Lean — T2 (forme grammaticale) contredit la collision miroir sous OFF

    TRACE_ID              : RHV3-OFF-T2-VS-MIRROR-COLLISION
    SEMANTIC_OBJECT       : la contradiction directe entre la succession
                            canonique (T2, forme grammaticale déjà produite)
                            appliquée au passage OFF, et la collision miroir
                            (`PMirrorCollision`, déjà nommée) -- sans
                            identifier aucun premier, uniquement par un fait
                            arithmétique : un successeur n'est jamais égal à
                            son prédécesseur.
    SEMANTIC_STATEMENT    : si la succession canonique s'applique au passage
                            OFF (comme à tout passage réel) ET que les deux
                            comptages des deux Tours de la paire miroir
                            tombent sur le même premier (`PMirrorCollision`),
                            alors le premier central du miroir est À LA FOIS
                            égal à celui de l'original (collision) ET son
                            successeur arithmétique (T2) -- impossible, car
                            `fnPrimeAtRank` est strictement croissante.
    MATHEMATICAL_STATEMENT: (PMirrorCollision) ET (T2 sur le passage OFF)
                            impliquent fnPrimeAtRank(rank) = fnPrimeAtRank(rank+1),
                            faux par injectivité de fnPrimeAtRank.
    MATHEMATICAL_PARENT   : `OffGrammarDetection.lean` (les deux équivalences
                            déjà produites, jamais reproduites ici) ;
                            `PrimeGapGrammar.lean` (`thm_primeAtRank_injective`).
    PROOF_STRATEGY        : dépliage pur des deux équivalences déjà
                            produites, puis une seule application de
                            l'injectivité de `fnPrimeAtRank`. Aucune borne,
                            aucune construction nouvelle.
    REQUIRED_LEMMAS       : thm_offGrammarImageEarlier_eq_originalCentralPrime,
                            thm_offReachesOwnLaterMember_iff_successorCollision,
                            thm_primeAtRank_injective
    WHY_EACH_LEMMA_EXISTS : les deux premiers donnent respectivement la valeur
                            de l'entrée grammaticale (= premier central de
                            l'original) et la valeur exigée par T2 (=
                            successeur, quand T2 s'applique) ; le troisième
                            exclut qu'un rang et son successeur pointent le
                            même premier.
    LEAN_DEFINITION       : PT2AppliesToOffTransition
    LEAN_THEOREM          : thm_off_impossible_of_mirrorCollision_and_t2Off
    SAME_MEMBER_CHECK     : chaque quantité reste fonction du seul membre
                            (original ou miroir) que sa définition nomme.
    SAME_PASSAGE_CHECK    : le même passage `tCarrier.tOffTransition zOff`
                            sert de bout en bout.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : l'unique histoire première de O6, comme partout
                            ailleurs dans ce corpus.
    FORBIDDEN_PREMISES    : identifier lequel des deux premiers centraux est
                            en jeu ; RH ou sa négation comme prémisse ;
                            re-prouver `PMirrorCollision` ou T2 ici -- ce
                            module les reçoit tous deux comme prémisses
                            explicites et nommées, exactement comme convenu.
    NEXT_CONSUMER         : la fermeture terminale a encore besoin d'établir
                            que la configuration OFF FORCE `PMirrorCollision`
                            (le pont « EncZ=M » demandé, non encore produit) ;
                            sans lui, ce module montre seulement que
                            `PMirrorCollision` et T2-sur-OFF ne peuvent pas
                            être vrais simultanément -- pas encore que OFF
                            est impossible.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau. `PMirrorCollision` et
`PT2AppliesToOffTransition` restent des prémisses explicites de l'unique
théorème qui en dépend -- jamais cachées, jamais des axiomes.
-/

namespace RHV3Lean

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-! ## 1. T2, dans sa forme grammaticale, restreint aux passages OFF -/

/-- **T2, appliqué aux passages produits par la construction OFF.**  C'est la
même succession canonique que `PCanonicalSuccession` (`CanonicalT2.lean`),
relue dans le vocabulaire de `TowerGrammarMorphism.lean`
(`PPassageReachesOwnLaterMember`) -- nécessaire ici parce que le passage OFF
est un `TTowerMemberTransition`, pas un `TZeroPassage`. Reçue comme prémisse
explicite, jamais prouvée dans ce module. -/
def PT2AppliesToOffTransition : Prop :=
  ∀ zOff : TOffCriticalLineUpperZero,
    PPassageReachesOwnLaterMember (tCarrier.tOffTransition zOff)

/-! ## 2. LA CONTRADICTION -/

/-- **`PMirrorCollision` et T2-sur-OFF sont mutuellement exclusifs.**

Sous `PMirrorCollision` (les deux Tours de la paire miroir tombent sur le
même premier canonique, sans qu'aucun ne soit identifié) et sous T2 appliqué
au passage OFF (le premier central du miroir est le successeur arithmétique
de celui de l'original), on obtiendrait `fnPrimeAtRank(rang) =
fnPrimeAtRank(rang+1)` -- faux, par la seule stricte croissance de
`fnPrimeAtRank` déjà produite. Aucun premier n'est identifié : la
contradiction est purement une égalité de rangs. -/
theorem thm_off_impossible_of_mirrorCollision_and_t2Off
    (hCollision : tCarrier.PMirrorCollision)
    (hT2Off : tCarrier.PT2AppliesToOffTransition)
    (zOff : TOffCriticalLineUpperZero) : False := by
  set rank := nPassageGrammarRank (tCarrier.tOffTransition zOff) with hrankdef
  have hEarlier :
      fnPrimeAtRank rank = tCarrier.nCarrierCentralPrime (offOriginalUpperMember zOff) := by
    have h := thm_offGrammarImageEarlier_eq_originalCentralPrime tCarrier zOff
    unfold GrammarImageEarlier ZeroPassageGrammarPlace nPlaceEarlierEndpoint at h
    exact h
  have hSucc :
      fnPrimeSuccessor rank = tCarrier.nCarrierCentralPrime (offMirrorUpperMember zOff) :=
    (thm_offReachesOwnLaterMember_iff_successorCollision tCarrier zOff).mp (hT2Off zOff)
  have hColl := hCollision zOff
  have hEq : fnPrimeAtRank rank = fnPrimeAtRank (rank + 1) := by
    unfold fnPrimeSuccessor at hSucc
    rw [hEarlier, hColl, hSucc]
  have hRankEq := thm_primeAtRank_injective hEq
  omega

end TTrueTowerCarrier

/-! Surface audit. -/

#check @TTrueTowerCarrier.PT2AppliesToOffTransition
#check @TTrueTowerCarrier.thm_off_impossible_of_mirrorCollision_and_t2Off

end RHV3Lean
