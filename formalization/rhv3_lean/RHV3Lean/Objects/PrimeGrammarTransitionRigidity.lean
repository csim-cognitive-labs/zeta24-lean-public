/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.MemberSensitiveMZCorrespondence

/-!
# RHV3Lean — la non-nullité grammaticale du passage, et où son transport s'arrête

    TRACE_ID              : RHV3-GRAMMAR-TRANSITION-RIGIDITY
    SEMANTIC_OBJECT       : la non-nullité de la transition première portée par
                            un passage réel, lue sur l'ancre canonique des deux
                            membres du passage ; et l'audit précis de ce que ce
                            fait permet, ou ne permet pas, de transporter vers
                            la hauteur.
    SEMANTIC_STATEMENT    : les deux ancres canoniques d'un passage réel sont
                            TOUJOURS distinctes — deux premiers successifs ne
                            sont jamais égaux, quel que soit le passage. Ce
                            fait est donc vrai INCONDITIONNELLEMENT, pour tout
                            passage, y compris un passage dont les deux membres
                            seraient de même hauteur (même fibre, séparés
                            seulement par la position radiale). Il ne peut donc,
                            à lui seul, jamais permettre de distinguer un
                            passage de même fibre d'un passage de hauteurs
                            distinctes : le transporter vers la stricte
                            positivité de l'écart de hauteur reviendrait à
                            prouver sans condition qu'aucun passage réel n'est
                            de même fibre — exactement le contenu encore ouvert
                            de T2, jamais dérivé ici, jamais supposé.
    MATHEMATICAL_STATEMENT: pour tout passage réel `tPassage` avec ses deux
                            extrémités supérieures, ancre(entrée) ≠
                            ancre(sortie) ; ce fait est un corollaire immédiat
                            de la stricte croissance de la grammaire première
                            (O6), lue à des rangs qui diffèrent de un.
    MATHEMATICAL_PARENT   : O6 (`PrimeGapGrammar`, `thm_successivePrimes_distinct`),
                            `MemberSensitiveMZCorrespondence`
                            (`nMemberCanonicalAnchor`,
                            `thm_memberCanonicalAnchor_succ_of_passage`).
    PROOF_STRATEGY        : l'ancre de sortie est le successeur premier canonique
                            du rang zéro-source d'entrée (déjà prouvé,
                            inconditionnel) ; l'ancre d'entrée est ce même rang
                            lu directement ; deux premiers successifs sont
                            distincts (O6, `thm_successivePrimes_distinct`) —
                            aucune preuve supplémentaire n'est nécessaire.
    REQUIRED_LEMMAS       : thm_memberCanonicalAnchor_succ_of_passage,
                            thm_successivePrimes_distinct
    WHY_EACH_LEMMA_EXISTS : le premier donne la valeur exacte des deux ancres
                            sur le même passage ; le second dit que deux rangs
                            qui diffèrent de un portent toujours des premiers
                            distincts.
    LEAN_DEFINITION       : aucune nouvelle définition — audit et corollaire
                            seulement.
    LEAN_THEOREM          : thm_primeAtRank_zero_eq_two, thm_primeAtRank_ge_two
                            (O6, garde d'indexation), thm_primeGrammarTransition_nonNull
    SAME_MEMBER_CHECK     : les deux ancres comparées sont celles des deux
                            propres extrémités du MÊME passage, jamais de deux
                            passages distincts.
    SAME_PASSAGE_CHECK    : la non-nullité est lue sur le même `TZeroPassage`,
                            jamais reconstruite par comparaison externe.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : les deux ancres retombent sur la même histoire
                            première canonique de O6 (`fnPrimeAtRank`), jamais
                            une seconde énumération.
    FORBIDDEN_PREMISES    : `PUniqueCenterRegime`, `PCanonicalSuccession`,
                            `PMirrorCollision`, `PCanonicalPlaceIsMemberIndex`,
                            `FiberedMZEqM`, `uniqueGrammarLanding`,
                            `nCellFoundCount = 1`, `centralPrime_in_cell`, `RH` —
                            aucun n'est reçu ici, aucun n'est produit sous un
                            autre nom.
    NEXT_CONSUMER         : aucun théorème de ce module ne consomme la
                            non-nullité grammaticale pour affirmer la
                            non-nullité du passage lui-même (la stricte
                            positivité de l'écart de hauteur) : cette
                            implication est AUDITÉE ici comme IMPOSSIBLE À
                            PRODUIRE depuis ce seul fait, et non comme absente
                            faute d'avoir été cherchée.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED pour la non-nullité grammaticale
                            inconditionnelle ; AUDIT_NEGATIF_HONNETE pour son
                            transport vers la hauteur.

## Pourquoi le transport vers la hauteur s'arrête ici, précisément

`thm_primeGrammarTransition_nonNull` ci-dessous est vraie pour TOUT passage
réel, sans aucune condition sur ses deux hauteurs : elle vaut aussi bien pour
un passage aux hauteurs distinctes que pour un passage dont les deux membres
partageraient la même fibre de hauteur (`sZeroHeightFiber`), séparés
seulement par leur position radiale — cette configuration existe déjà,
formellement, dans la grammaire des écarts de zéros
(`ZeroGapGrammar.thm_distinctSameFiberMembers_haveNullGap` : deux membres
distincts de même hauteur sont comparables, donc ordonnables, donc
potentiellement consécutifs, avec un écart de hauteur nul).

Un théorème qui déduirait la stricte positivité de l'écart de hauteur
(`rZeroHeight earlier < rZeroHeight later`) de la seule non-nullité
grammaticale devrait donc valoir MÊME sur cette configuration de même fibre —
ce qui est directement contradictoire avec l'écart nul déjà établi pour elle.
Une telle déduction est donc structurellement impossible depuis les seuls
faits produits ici : elle demanderait de savoir, en plus, qu'aucun passage
réel n'est de même fibre — c'est exactement le contenu mathématique encore
ouvert que T2/`PCanonicalSuccession` visent côté Tour, et qu'aucune
reformulation sous un autre nom ne doit introduire ici comme prémisse.

Ce module ne construit donc AUCUN théorème reliant la non-nullité
grammaticale à la positivité de l'écart de hauteur : il produit la
non-nullité grammaticale (inconditionnelle, nouvelle, utile), et arrête très
précisément le transport au point exact où il cesserait d'être une preuve.

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

/-! ## 1. L'ancre d'entrée, lue directement sur le même passage -/

/-- **L'ancre canonique de l'extrémité d'entrée**, lue directement au rang
zéro-source de cette même extrémité — la forme d'entrée de
`thm_memberCanonicalAnchor_succ_of_passage`, qui ne donne que la sortie. -/
theorem thm_memberCanonicalAnchor_of_earlier
    (tPassage : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight tPassage.zEarlierMember) :
    nMemberCanonicalAnchor ⟨tPassage.zEarlierMember, hEarlierUpper⟩ =
      fnPrimeAtRank (nZeroSourceIndex tPassage.zEarlierMember) := rfl

/-! ## 2. La non-nullité grammaticale — inconditionnelle -/

/-- **La non-nullité grammaticale d'un passage réel.**  Les deux ancres
canoniques des deux propres extrémités d'un passage réel sont TOUJOURS
distinctes — vrai pour tout passage, sans aucune hypothèse sur les hauteurs. -/
theorem thm_primeGrammarTransition_nonNull
    (tPassage : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight tPassage.zEarlierMember)
    (hLaterUpper : 0 < rZeroHeight tPassage.zLaterMember) :
    nMemberCanonicalAnchor ⟨tPassage.zEarlierMember, hEarlierUpper⟩ ≠
      nMemberCanonicalAnchor ⟨tPassage.zLaterMember, hLaterUpper⟩ := by
  rw [thm_memberCanonicalAnchor_of_earlier tPassage hEarlierUpper,
    thm_memberCanonicalAnchor_succ_of_passage tPassage hEarlierUpper hLaterUpper]
  exact thm_successivePrimes_distinct (nZeroSourceIndex tPassage.zEarlierMember)

#check thm_memberCanonicalAnchor_of_earlier
#check thm_primeGrammarTransition_nonNull

end RHV3Lean
