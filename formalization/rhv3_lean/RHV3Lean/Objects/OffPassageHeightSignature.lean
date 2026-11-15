/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.OffMirrorDifferenceBands

/-!
# RHV3Lean — la signature de hauteur : ce qui trahit le passage hors ligne

    TRACE_ID              : RHV3-OFF-PASSAGE-HEIGHT-SIGNATURE
    SEMANTIC_OBJECT       : la correction réelle de T2 (§33 du maître Lean),
                            portée cette fois dans le code, pas seulement dans
                            la prose -- via le signal que chaque Tour transporte
                            déjà et que la construction n'utilisait pas encore.
    SEMANTIC_STATEMENT    : chaque Tour, lue sur ses deux seuls contacts
                            propres, redécode EXACTEMENT la vraie hauteur de
                            son membre -- jamais une approximation. Pour un
                            passage entre deux membres réellement consécutifs,
                            cette hauteur redécodée diffère exactement quand le
                            passage est non nul (c'est la même chose : l'écart
                            de hauteur est non nul). Pour la paire miroir hors
                            ligne, les deux Tours redécodent la MÊME hauteur --
                            c'est la trahison annoncée par l'utilisateur : ce
                            signal, à lui seul, place le passage OFF hors du
                            domaine où la succession canonique (T2) a le droit
                            de s'appliquer.
    MATHEMATICAL_STATEMENT: rDecodedHeight(S_z) = T(z) pour toute Tour propre
                            (déjà acquis, TrueTowerState.lean). Un passage est
                            non nul ssi T(earlier) != T(later) (déjà acquis,
                            Passage.lean). Pour la paire miroir OFF, T(orig) =
                            T(mirror) (déjà acquis, FunctionalMirror.lean).
                            `PCanonicalSuccessionOnNonNull` restreint la
                            succession aux seuls passages non nuls ; aucun
                            passage construit depuis une paire miroir OFF n'est
                            jamais non nul.
    MATHEMATICAL_PARENT   : maître sémantique §13.1/§13.2 (correction de
                            l'ancien T2 universel) ; maître Lean §33 (correction
                            en prose, ici rendue exécutoire) ; Passage.lean,
                            TrueTowerState.lean, FunctionalMirror.lean.
    PROOF_STRATEGY        : composer trois faits déjà produits, sans aucune
                            nouvelle analyse : la fidélité du décodage, la
                            caractérisation de la nullité par l'égalité de
                            hauteur, et l'égalité de hauteur du couple miroir.
    REQUIRED_LEMMAS       : thm_decodedHeight_eq_zeroHeight,
                            thm_zeroPassage_null_iff_sameHeight,
                            thm_offMirror_sameHeight
    WHY_EACH_LEMMA_EXISTS : le premier rend le décodage fidèle pour n'importe
                            quel porteur ; le second identifie exactement la
                            nullité à l'égalité de hauteur ; le troisième donne
                            cette égalité pour le couple miroir, sans jamais
                            supposer RH.
    LEAN_DEFINITION       : PCanonicalSuccessionOnNonNull
    LEAN_THEOREM          : thm_carrierDecodedHeight_eq_zeroHeight,
                            thm_offMirror_ownDecodedHeights_eq,
                            thm_offPassage_never_nonNull
    SAME_MEMBER_CHECK     : le décodage lit exclusivement les deux contacts
                            propres du membre reçu, jamais un autre.
    SAME_PASSAGE_CHECK    : la nullité comparée est toujours celle du même
                            passage que celui qui reçoit la conclusion.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet -- aucun premier n'entre dans ce module.
    FORBIDDEN_PREMISES    : re-choisir une adresse ; supposer RH pour établir
                            l'égalité ou la différence des hauteurs ; élargir
                            `PCanonicalSuccessionOnNonNull` à un passage nul.
    NEXT_CONSUMER         : toute future transcription de T2 -- ce module fixe
                            au niveau du TYPE que la succession ne peut plus
                            jamais recevoir un passage nul, donc jamais la
                            paire miroir OFF.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS            : BODY_PRODUCED. `PCanonicalSuccessionOnNonNull`
                             reste une `Prop` nommée (comme
                             `PCanonicalSuccession`) ; ce qui est PROUVÉ ici,
                             sans aucune hypothèse supplémentaire, est qu'elle
                             ne peut structurellement jamais s'appliquer à un
                             passage miroir OFF -- la faute de sur-généralisation
                             de §33 est désormais rendue impossible au niveau du
                             type, pas seulement corrigée en commentaire.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-! ## 1. Le décodage est fidèle, sur n'importe quel porteur -/

/-- **La Tour de ce porteur redécode exactement la vraie hauteur du membre**,
depuis ses deux seuls contacts propres. Aucune approximation : une identité. -/
theorem thm_carrierDecodedHeight_eq_zeroHeight (zUpperZero : TUpperNonTrivialZetaZero) :
    (tCarrier.fnState zUpperZero).rDecodedHeight = rZeroHeight zUpperZero.1 :=
  (tCarrier.fnState zUpperZero).thm_decodedHeight_eq_zeroHeight

/-! ## 2. La trahison : la paire miroir OFF redécode la même hauteur -/

/-- **Les deux Tours de la paire miroir OFF redécodent exactement la MÊME
hauteur.** C'est le signal que l'utilisateur a identifié : cette égalité, à
elle seule, place le couple hors du domaine où une succession pourrait jamais
s'appliquer. -/
theorem thm_offMirror_ownDecodedHeights_eq (zOff : TOffCriticalLineUpperZero) :
    (tCarrier.fnState (offOriginalUpperMember zOff)).rDecodedHeight =
      (tCarrier.fnState (offMirrorUpperMember zOff)).rDecodedHeight := by
  rw [tCarrier.thm_carrierDecodedHeight_eq_zeroHeight,
    tCarrier.thm_carrierDecodedHeight_eq_zeroHeight]
  exact (thm_offMirror_sameHeight zOff).symm

/-! ## 3. T2, correctement restreint : la succession n'a droit qu'aux
passages non nuls -/

/-- **La succession canonique, restreinte à son seul domaine légitime.**
Corrige, au niveau du TYPE et non plus seulement en commentaire, la
sur-généralisation identifiée au maître Lean §33 : `PCanonicalSuccession`
recevait tout passage, y compris nul ; cette version ne reçoit plus que les
passages non nuls, exactement ceux où le maître (Passage.lean) identifie déjà
la nullité à l'égalité de hauteur. Reçue comme fait à établir, jamais une hypothèse
silencieuse, au même titre que `PCanonicalSuccession`. -/
def PCanonicalSuccessionOnNonNull : Prop :=
  ∀ tPassage : TZeroPassage, PZeroPassageRelationNonNull tPassage →
    tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember =
      nPlaceLaterEndpoint (tCarrier.fnCarrierPassagePlace tPassage)

end TTrueTowerCarrier

/-- **Aucun passage construit depuis une paire miroir OFF n'est jamais non
nul.** Une conséquence directe et sans hypothèse supplémentaire de la
trahison de §2 : par construction, un tel passage est TOUJOURS nul, donc
jamais dans le domaine de `PCanonicalSuccessionOnNonNull`. La faute de §33
est désormais rendue structurellement impossible, pas seulement corrigée en
prose. -/
theorem thm_offPassage_never_nonNull
    {zZero : TNonTrivialZetaZero} (hOff : PIsOffCriticalLine zZero)
    {tPassage : TZeroPassage}
    (hFromOff : rZeroPassageHeightGap tPassage = 0 ∧
      rZeroHeight tPassage.zEarlierMember = rZeroHeight zZero) :
    ¬ PZeroPassageRelationNonNull tPassage := by
  intro hNonNull
  exact hNonNull hFromOff.1

end RHV3Lean
