/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.MemberZeroSourceOccurrence
import RHV3Lean.Objects.ZeroSourceExplicitFormulaChannel

/-!
# RHV3Lean — l'occurrence reconstruite d'un membre dans M^Z, et son transport en M

    TRACE_ID              : RHV3-MZ-CORRESPONDENCE
    SEMANTIC_OBJECT       : l'occurrence, dans la grammaire reconstruite depuis
                            la source des zéros (M^Z), du membre `z` — lue à
                            l'index zéro-source de `z` et à nulle autre place ;
                            puis son transport en occurrence canonique de M,
                            sous l'hypothèse de canal M9a.
    SEMANTIC_STATEMENT    : M^Z est le foncteur de reconstruction déjà produit
                            en L15/L16, appliqué au canal analytique exact
                            issu de la source des zéros (M9a). L'occurrence
                            d'un membre dans M^Z n'est JAMAIS lue sur sa
                            cellule : elle est lue sur son seul index
                            zéro-source, construit sans primalité en amont.
                            M^Z = M transporte cette occurrence, terme à terme,
                            en occurrence de la grammaire première canonique —
                            mais seulement sous l'hypothèse de canal, jamais
                            comme fait acquis ici.
    MATHEMATICAL_STATEMENT: nMemberMZOccurrence(z) := (reconstructGrammar
                            rPsiZeroChannel).primeAt(nZeroSourceIndex z) ;
                            sous PM9aChannelIdentityOnNaturals,
                            nMemberMZOccurrence(z) = fnPrimeAtRank
                            (nZeroSourceIndex z) — l'ancre canonique du membre.
    MATHEMATICAL_PARENT   : L15/L16 (`ZeroSourceReconstruction`), M9a
                            (`ZeroSourceExplicitFormulaChannel`),
                            `MemberZeroSourceOccurrence` (l'index zéro-source).
    PROOF_STRATEGY        : l'occurrence M^Z est une simple application du
                            foncteur déjà produit à l'index déjà produit —
                            aucune preuve n'est requise pour la CONSTRUIRE ;
                            le transport en M réutilise EXACTEMENT
                            `thm_M9a_M9b_components_weak`, sans seconde preuve.
    REQUIRED_LEMMAS       : thm_M9a_M9b_components_weak
    WHY_EACH_LEMMA_EXISTS : c'est la seule identité déjà produite qui relie le
                            foncteur appliqué au canal zéro-source à
                            `fnPrimeAtRank`, sous l'hypothèse de canal.
    LEAN_DEFINITION       : nMemberMZOccurrence, nMemberCanonicalAnchor
    LEAN_THEOREM          : thm_memberMZOccurrence_eq_canonicalAnchor,
                            thm_memberCanonicalAnchor_isPrime,
                            thm_memberCanonicalAnchor_succ_of_passage,
                            thm_memberMZOccurrence_succ_of_passage
    SAME_MEMBER_CHECK     : l'occurrence M^Z et l'ancre canonique sont toutes
                            deux des fonctions du seul membre, via son index
                            zéro-source — jamais de sa cellule.
    SAME_PASSAGE_CHECK    : la succession est lue sur le passage réel complet
                            (`TZeroPassage`), jamais sur un simple écart.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : l'ancre canonique retombe, une fois M9a acquis, sur
                            l'unique histoire première de O6 (`fnPrimeAtRank`),
                            jamais une seconde énumération.
    FORBIDDEN_PREMISES    : lire `nCellCentralPrime`, `nCellCentralRank`,
                            `nCellFoundCount`, `PUniqueCenterRegime`,
                            `PCanonicalSuccession`, `PMirrorCollision`,
                            `PCanonicalPlaceIsMemberIndex`, `FiberedMZEqM`,
                            `uniqueGrammarLanding`, RH — pour construire ou
                            transporter l'occurrence M^Z ; poser
                            `nZeroSourceIndex z = rang premier de la cellule`
                            comme hypothèse.
    NEXT_CONSUMER         : `CanonicalOccurrenceTransport`, qui nomme (sans la
                            prouver) l'appartenance de l'ancre canonique à la
                            propre cellule du membre — le contenu réel encore
                            manquant de T1.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED pour la construction et le transport
                            conditionnel ; aucune quatrième prémisse.

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau. `nCellCentralPrime` et
`nCellCentralRank` n'apparaissent nulle part dans ce fichier.
-/

namespace RHV3Lean

/-! ## 1. L'occurrence reconstruite d'un membre dans M^Z -/

/-- **L'occurrence d'un membre dans M^Z** : le premier lu par le foncteur de
reconstruction du canal analytique exact issu de la source des zéros, à
l'index zéro-source du membre — et à nulle autre place. Construite SANS
jamais lire `nCellCentralPrime` ni `nCellCentralRank`. -/
noncomputable def nMemberMZOccurrence (z : TUpperNonTrivialZetaZero) : ℕ :=
  (fnReconstructGrammar rPsiZeroChannel).primeAt (nZeroSourceIndex z.1)

/-! ## 2. L'ancre canonique — l'occurrence transportée en M -/

/-- **L'ancre canonique du membre** : le premier de la grammaire canonique déjà
produite en O6, au rang de l'index zéro-source du membre. C'est la forme
transportée de `nMemberMZOccurrence`, mais définie ici indépendamment, pour
isoler ce que M9a devra identifier. -/
noncomputable def nMemberCanonicalAnchor (z : TUpperNonTrivialZetaZero) : ℕ :=
  fnPrimeAtRank (nZeroSourceIndex z.1)

theorem thm_memberCanonicalAnchor_isPrime (z : TUpperNonTrivialZetaZero) :
    Nat.Prime (nMemberCanonicalAnchor z) :=
  thm_primeAtRank_isPrime _

/-- **M^Z = M, lu sur une occurrence membre-sensible.**  Sous l'hypothèse de
canal M9a (aux entiers, la cible réellement consommée), l'occurrence
reconstruite d'un membre dans M^Z EST son ancre canonique — le transport est
un théorème conditionnel, jamais un fait acquis ici, et jamais une quatrième
prémisse : c'est exactement `PM9aChannelIdentityOnNaturals`, déjà nommée en
`ZeroSourceExplicitFormulaChannel.lean`. -/
theorem thm_memberMZOccurrence_eq_canonicalAnchor
    (hAgree : PM9aChannelIdentityOnNaturals) (z : TUpperNonTrivialZetaZero) :
    nMemberMZOccurrence z = nMemberCanonicalAnchor z := by
  unfold nMemberMZOccurrence nMemberCanonicalAnchor
  rw [(thm_M9a_M9b_components_weak hAgree).2.1]

/-- **M^Z = M, sans hypothèse.** M9a est maintenant un théorème
(`thm_M9aChannelIdentityOnNaturals_proved`, `ZeroSourceExplicitFormulaChannel`) :
l'occurrence M^Z d'un membre EST son ancre canonique, inconditionnellement. -/
theorem thm_memberMZOccurrence_eq_canonicalAnchor_unconditional
    (z : TUpperNonTrivialZetaZero) :
    nMemberMZOccurrence z = nMemberCanonicalAnchor z :=
  thm_memberMZOccurrence_eq_canonicalAnchor thm_M9aChannelIdentityOnNaturals_proved z

/-! ## 3. La succession, transportée depuis le seul côté zéro -/

/-- **L'ancre canonique avance au successeur premier sur un passage
consécutif authentique.**  Inconditionnel : aucune hypothèse de canal n'est
requise ici, seule l'avance de un de l'index zéro-source (déjà prouvée en
`MemberZeroSourceOccurrence`). -/
theorem thm_memberCanonicalAnchor_succ_of_passage
    (tPassage : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight tPassage.zEarlierMember)
    (hLaterUpper : 0 < rZeroHeight tPassage.zLaterMember) :
    nMemberCanonicalAnchor ⟨tPassage.zLaterMember, hLaterUpper⟩ =
      fnPrimeSuccessor (nZeroSourceIndex tPassage.zEarlierMember) := by
  unfold nMemberCanonicalAnchor
  rw [thm_zeroSourceIndex_succ_of_passage tPassage hEarlierUpper, fnPrimeSuccessor]

/-- **La succession M^Z, transportée depuis la seule succession zéro.**  Sous
M9a, l'occurrence M^Z du membre de sortie d'un passage consécutif authentique
EST le successeur canonique de l'index zéro-source du membre d'entrée — la
même conclusion que le mécanisme composé T1+T2 visait, mais atteinte ici sans
jamais recevoir `PUniqueCenterRegime` ni `PCanonicalSuccession` en hypothèse. -/
theorem thm_memberMZOccurrence_succ_of_passage
    (hAgree : PM9aChannelIdentityOnNaturals)
    (tPassage : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight tPassage.zEarlierMember)
    (hLaterUpper : 0 < rZeroHeight tPassage.zLaterMember) :
    nMemberMZOccurrence ⟨tPassage.zLaterMember, hLaterUpper⟩ =
      fnPrimeSuccessor (nZeroSourceIndex tPassage.zEarlierMember) := by
  have h := thm_memberMZOccurrence_eq_canonicalAnchor hAgree
    ⟨tPassage.zLaterMember, hLaterUpper⟩
  rw [h]
  exact thm_memberCanonicalAnchor_succ_of_passage tPassage hEarlierUpper hLaterUpper

/-- **La succession M^Z, sans hypothèse de canal.** Même conclusion que
`thm_memberMZOccurrence_succ_of_passage`, mais M9a n'est plus reçu en
hypothèse : c'est un théorème. -/
theorem thm_memberMZOccurrence_succ_of_passage_unconditional
    (tPassage : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight tPassage.zEarlierMember)
    (hLaterUpper : 0 < rZeroHeight tPassage.zLaterMember) :
    nMemberMZOccurrence ⟨tPassage.zLaterMember, hLaterUpper⟩ =
      fnPrimeSuccessor (nZeroSourceIndex tPassage.zEarlierMember) :=
  thm_memberMZOccurrence_succ_of_passage
    thm_M9aChannelIdentityOnNaturals_proved tPassage hEarlierUpper hLaterUpper

#check nMemberMZOccurrence
#check nMemberCanonicalAnchor
#check thm_memberMZOccurrence_eq_canonicalAnchor
#check thm_memberCanonicalAnchor_succ_of_passage
#check thm_memberMZOccurrence_succ_of_passage

end RHV3Lean
