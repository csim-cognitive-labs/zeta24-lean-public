/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.PrimeOccurrence
import RHV3Lean.Objects.Triple

/-!
# RHV3Lean — la place de l'histoire première, la loi locale, et la séparation
des extrémités qui en dérive

    TRACE_ID              : RHV3-LOCALLAW
    SEMANTIC_OBJECT       : la loi locale du transport ; séparation des
                            extrémités — PROPRIETE DERIVEE
    SEMANTIC_STATEMENT    : tout passage réel est transporté sur une PLACE de
                            l'unique histoire première ; une place est une arête
                            entre deux premiers successifs, donc à extrémités
                            distinctes ; la séparation des extrémités n'est ni
                            une obligation ouverte, ni une hypothèse, ni un
                            attribut à déclarer.
    MATHEMATICAL_STATEMENT: pour tout passage réel E = (A, B), Phi(E) =
                            (p_i, p_(i+1)) est une place de la grammaire des
                            écarts premiers ; P(A) != P(B) parce qu'aucune place
                            nulle n'existe dans cette grammaire, la positivité
                            stricte p_(n+1) - p_n > 0 étant une propriété
                            primitive de l'histoire première seule, antérieure à
                            tout zéro.
    MATHEMATICAL_PARENT   : O6 — la grammaire des écarts premiers ; O8 — le
                            passage et R-PASS ; O5 — l'occurrence première.
    PROOF_STRATEGY        : la place est indexée par un rang ; ses deux
                            extrémités sont le premier de ce rang et son
                            successeur, donc distinctes par O6, et son corridor
                            est vide par O6 ; la loi locale dit que les deux
                            premiers centraux des extrémités propres du passage
                            SONT les deux extrémités d'une même place ; la
                            séparation des extrémités en découle immédiatement.
                            R-PASS ne contient aucune clause de nullité.
    REQUIRED_LEMMAS       : thm_successivePrimes_distinct,
                            thm_noPrimeStrictlyBetweenSuccessivePrimes
    WHY_EACH_LEMMA_EXISTS : les deux premiers sont la grammaire O6 elle-même,
                            antérieure à tout zéro.
    LEAN_DEFINITION       : TPrimeHistoryPlace, nPlaceEarlierEndpoint,
                            nPlaceLaterEndpoint, PPlaceRelationNull,
                            PLocalLawTransportsPassageOntoPlace
    LEAN_THEOREM          : thm_place_isNeverNull, thm_place_corridorEmpty,
                            thm_endpointsDistinct_of_localLaw,
                            thm_passageImage_isNeverNull
    SAME_MEMBER_CHECK     : la loi locale lit les premiers centraux des DEUX
                            EXTREMITES PROPRES du passage, jamais ceux d'un
                            membre étranger.
    SAME_PASSAGE_CHECK    : la place est celle du MÊME passage ; aucune
                            comparaison avec un second passage n'intervient.
    SAME_MIDDLE_CHECK     : sur le triple, les deux places sont celles des deux
                            passages du même triple, recollés sur le même membre
                            médian.
    SAME_HISTORY_CHECK    : la place est indexée dans l'unique histoire première
                            de O6, dont l'unicité est prouvée.
    FORBIDDEN_PREMISES    : poser la séparation des extrémités comme hypothèse
                            ou comme obligation ouverte ; utiliser R-ATT pour
                            séparer deux premiers ; poser la positivité d'un
                            écart de hauteur comme prémisse.
    NEXT_CONSUMER         : le miroir et la contradiction terminale.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : CONTRACT_AND_CONDITIONAL_CONSUMERS_ONLY

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

/-!
Attention : `PLocalLawTransportsPassageOntoPlace` ci-dessous est le contrat de
la loi locale. Ce module ne construit aucun couple de fonctions qui le
satisfait. Les théorèmes qui suivent reçoivent explicitement `hLocalLaw` et
sont donc des consumers conditionnels.
-/

/-! ## 1. La place de l'unique histoire première -/

/-- **Une place** de l'unique histoire première : l'arête entre le premier d'un
rang et son successeur.  Elle n'est jamais une paire quelconque de premiers :
c'est une arête de la grammaire O6. -/
structure TPrimeHistoryPlace where
  /-- Le rang de l'extrémité d'entrée de la place. -/
  nRank : ℕ

/-- L'extrémité d'entrée de la place. -/
noncomputable def nPlaceEarlierEndpoint (tPlace : TPrimeHistoryPlace) : ℕ :=
  fnPrimeAtRank tPlace.nRank

/-- L'extrémité de sortie de la place : le premier SUCCESSEUR. -/
noncomputable def nPlaceLaterEndpoint (tPlace : TPrimeHistoryPlace) : ℕ :=
  fnPrimeSuccessor tPlace.nRank

/-- La nullité d'une place : ses deux extrémités coïncideraient. -/
def PPlaceRelationNull (tPlace : TPrimeHistoryPlace) : Prop :=
  nPlaceEarlierEndpoint tPlace = nPlaceLaterEndpoint tPlace

/-- **AUCUNE PLACE N'EST NULLE.**

C'est la positivité stricte de O6, antérieure à tout zéro et indépendante de
toute hypothèse sur zêta.  Tout ce qui suit en dérive. -/
theorem thm_place_isNeverNull (tPlace : TPrimeHistoryPlace) :
    ¬ PPlaceRelationNull tPlace :=
  thm_successivePrimes_distinct tPlace.nRank

/-- **Le corridor d'une place est vide.**  Aucun premier ne se glisse
strictement entre ses deux extrémités : c'est le voisinage de O6. -/
theorem thm_place_corridorEmpty (tPlace : TPrimeHistoryPlace)
    {nCandidate : ℕ} (hPrime : Nat.Prime nCandidate)
    (hLeft : nPlaceEarlierEndpoint tPlace < nCandidate)
    (hRight : nCandidate < nPlaceLaterEndpoint tPlace) : False :=
  thm_noPrimeStrictlyBetweenSuccessivePrimes tPlace.nRank hPrime hLeft hRight

/-- L'écart porté par une place est strictement positif. -/
theorem thm_place_gap_positive (tPlace : TPrimeHistoryPlace) :
    nPlaceEarlierEndpoint tPlace < nPlaceLaterEndpoint tPlace :=
  thm_primeAtRank_lt_successor tPlace.nRank

/-! ## 2. La loi locale du transport -/

variable (fnMemberCentralPrime : TNonTrivialZetaZero → ℕ)
variable (fnPassagePlace : TZeroPassage → TPrimeHistoryPlace)

/-- **LA LOI LOCALE DU TRANSPORT.**

Tout passage réel est transporté sur une PLACE de l'unique histoire première :
le premier central de son extrémité d'entrée est l'extrémité d'entrée de la
place, et le premier central de son extrémité de sortie en est l'extrémité de
sortie.  Les deux premiers lus sont ceux des deux extrémités PROPRES du
passage. -/
def PLocalLawTransportsPassageOntoPlace : Prop :=
  ∀ tPassage : TZeroPassage,
    fnMemberCentralPrime tPassage.zEarlierMember =
        nPlaceEarlierEndpoint (fnPassagePlace tPassage) ∧
      fnMemberCentralPrime tPassage.zLaterMember =
        nPlaceLaterEndpoint (fnPassagePlace tPassage)

variable {fnMemberCentralPrime fnPassagePlace}

/-! ## 3. La séparation des extrémités — DERIVEE, jamais posée -/

/-- **LA SEPARATION DES EXTREMITES.**

Les deux premiers centraux des deux extrémités d'un passage réel sont
distincts.  Ce n'est ni une obligation ouverte, ni une hypothèse, ni un attribut
à déclarer : c'est une conséquence de la loi locale et de la positivité
primitive des écarts entre premiers successifs — une arête a deux extrémités
distinctes.  R-ATT n'intervient nulle part ici. -/
theorem thm_endpointsDistinct_of_localLaw
    (hLocalLaw :
      PLocalLawTransportsPassageOntoPlace fnMemberCentralPrime fnPassagePlace)
    (tPassage : TZeroPassage) :
    fnMemberCentralPrime tPassage.zEarlierMember ≠
      fnMemberCentralPrime tPassage.zLaterMember := by
  obtain ⟨hEarlier, hLater⟩ := hLocalLaw tPassage
  rw [hEarlier, hLater]
  exact ne_of_lt (thm_place_gap_positive (fnPassagePlace tPassage))

/-- **L'image d'un passage réel n'est jamais nulle.**  Elle est une place, et
aucune place n'est nulle. -/
theorem thm_passageImage_isNeverNull (tPassage : TZeroPassage) :
    ¬ PPlaceRelationNull (fnPassagePlace tPassage) :=
  thm_place_isNeverNull _

end RHV3Lean
