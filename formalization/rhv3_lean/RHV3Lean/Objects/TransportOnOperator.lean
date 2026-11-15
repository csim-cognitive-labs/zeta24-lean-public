/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.CanonicalWindowRule
import RHV3Lean.Objects.OffFibreAndPassage
import RHV3Lean.Objects.PlaceAndLocalLaw
import RHV3Lean.Objects.UpperRepresentative

/-!
# RHV3Lean — la loi locale et R-PASS portés par UN SEUL porteur, décomposés

    TRACE_ID              : RHV3-LL-SAME-OPERATOR
    SEMANTIC_OBJECT       : la loi locale du transport, énoncée sur le premier
                            central DU PORTEUR, et le transport R-PASS du même
                            passage.
    SEMANTIC_STATEMENT    : le premier central lu sur un membre n'est pas une
                            fonction libre : c'est la lecture du porteur
                            canonique unique.  La loi locale et le transport
                            R-PASS doivent être énoncés sur CE premier central,
                            sans quoi deux blocs de la chaîne parleraient de
                            deux Tours différentes.
    MATHEMATICAL_STATEMENT: pour un porteur `O`, la lecture
                            `C3_O(z) = O.premierCentral(représentant supérieur de z)`
                            est totale et fonction du seul membre ; R-PASS sur
                            `C3_O` équivaut exactement à la loi locale sur
                            `C3_O`, sans clause de nullité.
    MATHEMATICAL_PARENT   : O8 — le passage et R-PASS ; O6 — la grammaire des
                            écarts premiers ; S4 — le porteur ; OFF — la fibre
                            finie et le passage nul.
    PROOF_STRATEGY        : les deux clauses de R-PASS sont littéralement les
                            deux clauses de la loi locale, à symétrie près.
    REQUIRED_LEMMAS       : thm_place_isNeverNull, thm_place_gap_positive,
                            thm_place_corridorEmpty
    WHY_EACH_LEMMA_EXISTS : ces lemmes donnent l'ordre, la séparation et le
                            corridor vide de la place après transport des
                            extrémités.
    LEAN_DEFINITION       : fnOperatorMemberCentralPrime, PLocalLawOnOperator,
                            PRPassOnOperator
    LEAN_THEOREM          : thm_rpass_iff_localLaw,
                            thm_rpassClause_endpoints, thm_rpassClause_order,
                            thm_rpassClause_corridorEmpty
    SAME_MEMBER_CHECK     : `fnOperatorMemberCentralPrime` est une composition de
                            fonctions du seul membre ; deux membres égaux ont le
                            même premier central, par `congrArg`.
    SAME_PASSAGE_CHECK    : la contradiction terminale consomme LE MEME passage
                            que celui produit par la branche OFF ; aucun second
                            passage n'est introduit.
    SAME_MIDDLE_CHECK     : sans objet dans ce module.
    SAME_HISTORY_CHECK    : la place image est indexée dans l'unique histoire
                            première de O6.
    FORBIDDEN_PREMISES    : poser la séparation des extrémités comme obligation
                            ouverte ; poser la positivité d'un écart de hauteur
                            comme prémisse ; dissimuler l'hypothèse de Riemann
                            dans un prédicat opaque ; utiliser R-ATT pour
                            séparer deux premiers.
    NEXT_CONSUMER         : l'universalisation vers `RiemannHypothesis`.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

## Ce que la décomposition rend VISIBLE, et pourquoi elle doit l'être

Le maître interdit de dissimuler la conclusion dans un prédicat. R-PASS est
donc réduit ici à ses deux seules clauses constitutives :

    extrémité d'entrée   : donnée par la loi locale       — LIBRE une fois la loi
    extrémité de sortie  : donnée par la loi locale       — LIBRE une fois la loi
    ordre et corridor    : dérivés de la grammaire O6     — LIBRES, jamais posés

La conservation de nullité ne figure plus ici. Elle doit être produite en aval
comme theorem dérivé de la correspondance scientifique exacte.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

/-! ## 1. Le premier central PORTE PAR LE PORTEUR, sur un membre quelconque -/

variable (tOperator : TCanonicalTowerOperator)

/-- **Le premier central d'un membre quelconque, sous un porteur donné.**

Ce n'est pas une fonction libre : c'est la lecture du porteur sur le
représentant supérieur du membre, et le représentant supérieur porte exactement
le même membre lorsque sa hauteur est positive. -/
noncomputable def fnOperatorMemberCentralPrime (zZero : TNonTrivialZetaZero) : ℕ :=
  tOperator.nOperatorCentralPrime (zUpperRepresentative zZero)

/-- Le premier central lu sur le porteur est un vrai premier. -/
theorem thm_operatorMemberCentralPrime_isPrime (zZero : TNonTrivialZetaZero) :
    Nat.Prime (fnOperatorMemberCentralPrime tOperator zZero) :=
  tOperator.thm_operatorCentralPrime_isPrime _

/-- **RIGIDITE — la lecture est fonction du SEUL membre.** -/
theorem thm_operatorMemberCentralPrime_functionOfMember
    {zLeftZero zRightZero : TNonTrivialZetaZero} (hSameMember : zLeftZero = zRightZero) :
    fnOperatorMemberCentralPrime tOperator zLeftZero =
      fnOperatorMemberCentralPrime tOperator zRightZero :=
  congrArg _ hSameMember

/-- Sur la branche supérieure, la lecture est littéralement celle du porteur. -/
theorem thm_operatorMemberCentralPrime_onUpper
    {zZero : TNonTrivialZetaZero} (hPositive : 0 < rZeroHeight zZero) :
    fnOperatorMemberCentralPrime tOperator zZero =
      tOperator.nOperatorCentralPrime ⟨zZero, hPositive⟩ := by
  unfold fnOperatorMemberCentralPrime zUpperRepresentative
  congr 1
  exact Subtype.ext (thm_upperRepresentativeMember_of_positiveHeight hPositive)

/-! ## 2. La loi locale et R-PASS, tous deux portés par CE porteur -/

variable (fnPassagePlace : TZeroPassage → TPrimeHistoryPlace)

/-- **LA LOI LOCALE DU TRANSPORT, SUR LE PORTEUR.**  L'énoncé est porté par le
premier central DE L'OPERATEUR, jamais par une fonction libre. -/
def PLocalLawOnOperator : Prop :=
  PLocalLawTransportsPassageOntoPlace
    (fnOperatorMemberCentralPrime tOperator) fnPassagePlace

/-- **R-PASS, SUR LE PORTEUR.**  Le transport membre-sensible du passage, avec
la même lecture centrale que la loi locale. -/
def PRPassOnOperator : Prop :=
  PIsMemberSensitivePassageTransport nPlaceEarlierEndpoint nPlaceLaterEndpoint
    (fnOperatorMemberCentralPrime tOperator) fnPassagePlace

/-! ## 3. R-PASS est exactement la loi locale -/

variable {tOperator fnPassagePlace}

/-- **DECOMPOSITION EXACTE, FORME GENERIQUE.**

Elle ne dépend d'aucune propriété de la lecture centrale : quelle que soit la
fonction qui lit un premier sur un membre, un transport membre-sensible du
passage vers une place équivaut exactement à la loi locale sur cette lecture. -/
theorem thm_rpass_iff_localLaw_generic
    {fnMemberCentralPrime : TNonTrivialZetaZero → ℕ}
    {fnPassagePlace : TZeroPassage → TPrimeHistoryPlace} :
    PIsMemberSensitivePassageTransport nPlaceEarlierEndpoint nPlaceLaterEndpoint
        fnMemberCentralPrime fnPassagePlace ↔
      PLocalLawTransportsPassageOntoPlace fnMemberCentralPrime fnPassagePlace := by
  constructor
  · intro hTransport tPassage
    exact ⟨(hTransport tPassage).1.symm, (hTransport tPassage).2.symm⟩
  · intro hLocalLaw tPassage
    exact ⟨(hLocalLaw tPassage).1.symm, (hLocalLaw tPassage).2.symm⟩

/-- **DECOMPOSITION EXACTE — R-PASS équivaut à la loi locale seule.** -/
theorem thm_rpass_iff_localLaw :
    PRPassOnOperator tOperator fnPassagePlace ↔
      PLocalLawOnOperator tOperator fnPassagePlace :=
  thm_rpass_iff_localLaw_generic

/-! ## 4. Les clauses libres, une par une -/

/-- **Clause d'extrémités.**  Les deux premiers centraux du passage sont les deux
extrémités de la place image, lues sur le porteur. -/
theorem thm_rpassClause_endpoints
    (hLocalLaw : PLocalLawOnOperator tOperator fnPassagePlace)
    (tPassage : TZeroPassage) :
    fnOperatorMemberCentralPrime tOperator tPassage.zEarlierMember =
        nPlaceEarlierEndpoint (fnPassagePlace tPassage) ∧
      fnOperatorMemberCentralPrime tOperator tPassage.zLaterMember =
        nPlaceLaterEndpoint (fnPassagePlace tPassage) :=
  hLocalLaw tPassage

/-- **Clause d'ordre.**  Le premier central de l'entrée précède strictement celui
de la sortie.  C'est la positivité primitive des écarts entre premiers
successifs, jamais une hypothèse de séparation. -/
theorem thm_rpassClause_order
    (hLocalLaw : PLocalLawOnOperator tOperator fnPassagePlace)
    (tPassage : TZeroPassage) :
    fnOperatorMemberCentralPrime tOperator tPassage.zEarlierMember <
      fnOperatorMemberCentralPrime tOperator tPassage.zLaterMember := by
  obtain ⟨hEarlier, hLater⟩ := hLocalLaw tPassage
  rw [hEarlier, hLater]
  exact thm_place_gap_positive (fnPassagePlace tPassage)

/-- **Clause de corridor.**  Aucun premier ne se glisse strictement entre les
deux premiers centraux du passage : l'image est une arête de la grammaire, pas
une paire quelconque. -/
theorem thm_rpassClause_corridorEmpty
    (hLocalLaw : PLocalLawOnOperator tOperator fnPassagePlace)
    (tPassage : TZeroPassage) {nCandidate : ℕ} (hPrime : Nat.Prime nCandidate)
    (hLeft : fnOperatorMemberCentralPrime tOperator tPassage.zEarlierMember < nCandidate)
    (hRight : nCandidate < fnOperatorMemberCentralPrime tOperator tPassage.zLaterMember) :
    False := by
  obtain ⟨hEarlier, hLater⟩ := hLocalLaw tPassage
  rw [hEarlier] at hLeft
  rw [hLater] at hRight
  exact thm_place_corridorEmpty (fnPassagePlace tPassage) hPrime hLeft hRight

/-- **Clause de séparation des extrémités.**  DERIVEE, jamais posée. -/
theorem thm_rpassClause_endpointsDistinct
    (hLocalLaw : PLocalLawOnOperator tOperator fnPassagePlace)
    (tPassage : TZeroPassage) :
    fnOperatorMemberCentralPrime tOperator tPassage.zEarlierMember ≠
      fnOperatorMemberCentralPrime tOperator tPassage.zLaterMember :=
  ne_of_lt (thm_rpassClause_order hLocalLaw tPassage)

end RHV3Lean
