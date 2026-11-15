/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.Passage

/-!
# RHV3Lean — R-PASS complet : conservation de la nullité du même passage

    TRACE_ID              : RHV3-O8-RPASS-FULL
    SEMANTIC_OBJECT       : R-PASS complet (maître sémantique §6.2)
    SEMANTIC_STATEMENT    : le transport canonique membre-sensible Phi d'un
                            passage conserve non seulement ses deux extrémités
                            mais aussi le statut relationnel nul/non-nul du
                            MÊME passage : Null_Z(E) => Null_P(Phi(E)) et
                            NonNull_Z(E) => NonNull_P(Phi(E)).
    MATHEMATICAL_STATEMENT: Null_Z(E) <-> Null_P(Phi(E)), conjointe à la
                            conservation des deux extrémités déjà produite par
                            `PIsMemberSensitivePassageTransport`.
    MATHEMATICAL_PARENT   : O8 — le passage (`Passage.lean`).
    PROOF_STRATEGY        : la clause de nullité est ajoutée comme un second
                            conjoint à la clause d'extrémités déjà produite,
                            jamais substituée. Le prédicat de nullité côté
                            image reste abstrait : ce module ne prétend pas
                            connaître Phi ni son image, seulement CE QUE Phi
                            doit conserver pour mériter le nom de R-PASS
                            complet.
    REQUIRED_LEMMAS       : aucun ; ce module ajoute une clause à une
                            définition déjà produite et en tire des
                            conséquences purement logiques.
    WHY_EACH_LEMMA_EXISTS : —
    LEAN_DEFINITION       : PIsFullMemberSensitivePassageTransport
    LEAN_THEOREM          : thm_fullRpass_is_memberSensitive,
                            thm_fullRpass_null_iff,
                            thm_fullRpass_null_of_sourceNull,
                            thm_fullRpass_nonNull_of_sourceNonNull
    SAME_MEMBER_CHECK     : hérité de `PIsMemberSensitivePassageTransport`.
    SAME_PASSAGE_CHECK    : la clause de nullité porte sur le MÊME
                            `tPassage` que la clause d'extrémités ; il n'y a
                            jamais deux passages en jeu dans une instance de
                            cette définition.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — le prédicat de nullité côté image
                            reste un paramètre abstrait tant que l'histoire
                            première canonique n'est pas attachée à l'image
                            par un producteur réel (T2).
    FORBIDDEN_PREMISES    : aucune instance de `PIsFullMemberSensitivePassageTransport`
                            n'est fournie ni supposée ici ; ce module ne
                            prétend produire ni T1, ni T2, ni R-PASS lui-même,
                            seulement l'énoncé exact que leur composition
                            devra satisfaire.
    NEXT_CONSUMER         : le producteur T2 réel devra exhiber un terme de
                            `PIsFullMemberSensitivePassageTransport` sur le
                            transport canonique construit depuis l'occurrence
                            complète (§4-§5 du maître) ; la contradiction
                            terminale (§9) consommera alors
                            `thm_fullRpass_null_iff`.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS            : STRUCTURE_PRODUCED — R-PASS lui-même reste
                             NOT_YET_CERTIFIED_LEAN (dépend de T1/T2).

Cette définition ne remplace pas `PIsMemberSensitivePassageTransport` : elle
la contient comme premier conjoint, exactement comme le maître sémantique
distingue les extrémités (déjà transportées) du statut relationnel (encore à
transporter). Rien ici n'affaiblit ni ne renomme la clause d'extrémités
existante.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

variable {TImageMember TImageRelation : Type*}
variable {fnImageEarlierEndpoint fnImageLaterEndpoint : TImageRelation → TImageMember}
variable {fnMemberImage : TNonTrivialZetaZero → TImageMember}
variable {fnTransport : TZeroPassage → TImageRelation}

/-- **R-PASS complet** : le transport conserve les deux extrémités propres
(`PIsMemberSensitivePassageTransport`) ET le statut relationnel nul/non-nul du
même passage, comme une équivalence exacte sur le MÊME `tPassage`.

Le prédicat `PImageRelationNull` côté image reste un paramètre abstrait :
cette définition ne présuppose aucune construction particulière de l'image ni
de son type. Elle énonce exactement ce qu'un futur producteur T2 devra
satisfaire, sans en anticiper le corps. -/
def PIsFullMemberSensitivePassageTransport
    (PImageRelationNull : TImageRelation → Prop) : Prop :=
  PIsMemberSensitivePassageTransport fnImageEarlierEndpoint fnImageLaterEndpoint
      fnMemberImage fnTransport ∧
    ∀ tPassage : TZeroPassage,
      PZeroPassageRelationNull tPassage ↔ PImageRelationNull (fnTransport tPassage)

variable {PImageRelationNull : TImageRelation → Prop}

/-- **R-PASS complet implique R-PASS extrémités-only.**  Aucune clause n'est
perdue : la définition complète contient strictement la définition faible
comme premier conjoint. -/
theorem thm_fullRpass_is_memberSensitive
    (hFull :
      PIsFullMemberSensitivePassageTransport (fnImageEarlierEndpoint := fnImageEarlierEndpoint)
        (fnImageLaterEndpoint := fnImageLaterEndpoint) (fnMemberImage := fnMemberImage)
        (fnTransport := fnTransport) PImageRelationNull) :
    PIsMemberSensitivePassageTransport fnImageEarlierEndpoint fnImageLaterEndpoint
      fnMemberImage fnTransport :=
  hFull.1

/-- **La clause de nullité elle-même**, isolée. -/
theorem thm_fullRpass_null_iff
    (hFull :
      PIsFullMemberSensitivePassageTransport (fnImageEarlierEndpoint := fnImageEarlierEndpoint)
        (fnImageLaterEndpoint := fnImageLaterEndpoint) (fnMemberImage := fnMemberImage)
        (fnTransport := fnTransport) PImageRelationNull)
    (tPassage : TZeroPassage) :
    PZeroPassageRelationNull tPassage ↔ PImageRelationNull (fnTransport tPassage) :=
  hFull.2 tPassage

/-- **`Null_Z(E) => Null_P(Phi(E))`**, exactement le premier boxed du maître
sémantique §6.2 — un sens de l'équivalence, jamais posé comme une hypothèse
séparée du transport complet. -/
theorem thm_fullRpass_null_of_sourceNull
    (hFull :
      PIsFullMemberSensitivePassageTransport (fnImageEarlierEndpoint := fnImageEarlierEndpoint)
        (fnImageLaterEndpoint := fnImageLaterEndpoint) (fnMemberImage := fnMemberImage)
        (fnTransport := fnTransport) PImageRelationNull)
    {tPassage : TZeroPassage} (hNullZ : PZeroPassageRelationNull tPassage) :
    PImageRelationNull (fnTransport tPassage) :=
  (thm_fullRpass_null_iff hFull tPassage).mp hNullZ

/-- **`NonNull_Z(E) => NonNull_P(Phi(E))`**, le second boxed du maître
sémantique §6.2, dérivé de la même équivalence par contraposition — jamais un
second axiome indépendant. -/
theorem thm_fullRpass_nonNull_of_sourceNonNull
    (hFull :
      PIsFullMemberSensitivePassageTransport (fnImageEarlierEndpoint := fnImageEarlierEndpoint)
        (fnImageLaterEndpoint := fnImageLaterEndpoint) (fnMemberImage := fnMemberImage)
        (fnTransport := fnTransport) PImageRelationNull)
    {tPassage : TZeroPassage} (hNonNullZ : PZeroPassageRelationNonNull tPassage) :
    ¬ PImageRelationNull (fnTransport tPassage) :=
  fun hImageNull => hNonNullZ ((thm_fullRpass_null_iff hFull tPassage).mpr hImageNull)

end RHV3Lean
