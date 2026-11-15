/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.MemberSensitiveMZCorrespondence
import RHV3Lean.Objects.TrueTowerCarrier

/-!
# RHV3Lean — l'atterrissage de l'ancre canonique, cible exacte et encore ouverte

    TRACE_ID              : RHV3-ANCHOR-LANDING
    SEMANTIC_OBJECT       : la cible exacte, encore ouverte, qui relierait
                            l'ancre canonique d'un membre (côté zéro-source,
                            transportée par M^Z=M) à sa propre cellule (côté
                            Tour, vrais contacts).
    SEMANTIC_STATEMENT    : `MemberZeroSourceOccurrence` et
                            `MemberSensitiveMZCorrespondence` construisent,
                            sans aucune prémisse, l'identité zéro-source d'un
                            membre et son ancre canonique transportée. Ce
                            module ne prouve PAS que cette ancre tombe dans les
                            deux vrais contacts du même membre : il NOMME cette
                            proposition avec une précision exacte, comme cible
                            explicite, jamais comme fait acquis, jamais comme
                            hypothèse d'aucun autre théorème.
    MATHEMATICAL_STATEMENT: PMemberAnchorLandsInOwnCell(z) := ownCell(z).left <
                            ancre(z) <= ownCell(z).right, où ownCell(z) est
                            produite par la Tour propre du membre (les vrais
                            contacts) et ancre(z) par le seul index
                            zéro-source, transporté sous M9a.
    MATHEMATICAL_PARENT   : O4 (contacts et cellule), `MemberSensitiveMZCorrespondence`
                            (l'ancre canonique).
    PROOF_STRATEGY        : aucune — ce module mesure la forme exacte de la
                            flèche manquante, il ne la ferme pas. La fermer
                            demanderait une loi analytique reliant les deux
                            vrais contacts d'un membre (issus de sa Tour, non
                            explicites en dehors de leur écart logarithmique et
                            de leur loi de tangente) à la position du premier
                            situé au rang de son index zéro-source — un fait
                            qui n'est ni du côté zéro-source ni du côté M^Z=M,
                            mais du côté purement géométrique de la Tour (O4),
                            hors du périmètre de ce module.
    REQUIRED_LEMMAS       : aucun — définition seule.
    WHY_EACH_LEMMA_EXISTS : sans objet.
    LEAN_DEFINITION       : PMemberAnchorLandsInOwnCell
    LEAN_THEOREM          : aucun théorème n'habite cette Prop dans ce module.
    SAME_MEMBER_CHECK     : la Prop compare l'ancre et la cellule du MÊME
                            membre, jamais de deux membres distincts.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet à ce niveau.
    FORBIDDEN_PREMISES    : utiliser `PMemberAnchorLandsInOwnCell` comme
                            hypothèse d'un autre théorème ; la déclarer prouvée
                            par un raisonnement sur le comptage
                            (`nCellFoundCount`, `nCellCentralPrime`) ; la
                            confondre avec `PUniqueCenterRegime`,
                            `PCanonicalSuccession`, `PMirrorCollision`,
                            `PCanonicalPlaceIsMemberIndex` ou toute
                            reformulation de ceux-ci ; la présenter comme une
                            quatrième prémisse ou comme un résultat produit.
    NEXT_CONSUMER         : un futur théorème géométrique de la Tour, encore à
                            écrire, qui devra soit prouver
                            `PMemberAnchorLandsInOwnCell`, soit rester
                            bloqué exactement ici.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : TARGET_NAMED_NOT_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau. Cette Prop n'est ni
prouvée ni supposée : elle est seulement nommée, comme cible exacte du dernier
maillon manquant entre le côté zéro-source déjà produit et T1.
-/

namespace RHV3Lean

variable (tCarrier : TTrueTowerCarrier)

/-- **La cible exacte, encore ouverte, du dernier maillon.**  L'ancre
canonique du membre — construite uniquement depuis son index zéro-source,
transportée sous M9a — tombe-t-elle dans les deux vrais contacts de sa propre
Tour ? Ni prouvée, ni supposée : nommée. -/
def PMemberAnchorLandsInOwnCell (z : TUpperNonTrivialZetaZero) : Prop :=
  (tCarrier.tCarrierCell z).rLeftEndpoint < (nMemberCanonicalAnchor z : ℝ) ∧
    (nMemberCanonicalAnchor z : ℝ) ≤ (tCarrier.tCarrierCell z).rRightEndpoint

#check @PMemberAnchorLandsInOwnCell

end RHV3Lean
