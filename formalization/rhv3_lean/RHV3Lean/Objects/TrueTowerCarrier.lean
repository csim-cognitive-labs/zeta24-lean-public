/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TrueTowerState
import RHV3Lean.Objects.VonMangoldtChebyshev
import RHV3Lean.Objects.TransportOnOperator
import RHV3Lean.Objects.Universalization

/-!
# RHV3Lean — le porteur d'états propres, et toute la route relue sur LUI

    TRACE_ID              : RHV3-TRUE-CARRIER
    SEMANTIC_OBJECT       : un porteur, comme famille d'ETATS PROPRES
    SEMANTIC_STATEMENT    : un porteur attache à chaque membre un état propre
                            de Tour, donc ses deux vraies rencontres avec l'axe
                            algébrique.  La cellule terminale, le comptage, le
                            premier central et la loi locale sont tous lus sur
                            CE MEME état, jamais sur une fenêtre posée.
    MATHEMATICAL_STATEMENT: pour un porteur `K`, la cellule d'un membre est
                            l'intervalle algébrique `(C-(z), C+(z)]` porté par
                            l'état ; le premier central en est le premier du
                            rang central ; la loi locale et R-PASS sont énoncés
                            directement sur cette lecture contacts-only.
    MATHEMATICAL_PARENT   : S4 corrigé — l'état propre ; O2 ; O10 ; O8 ; O6.
    PROOF_STRATEGY        : la cellule est construite définitionnellement avec
                            les deux contacts de l'état ; tout l'aval lit cette
                            même cellule.
    REQUIRED_LEMMAS       : thm_rpass_iff_localLaw_generic,
                            thm_place_gap_positive,
                            thm_place_corridorEmpty
    WHY_EACH_LEMMA_EXISTS : le premier identifie R-PASS à ses deux seules
                            clauses d'extrémités ; les deux autres dérivent
                            ordre, séparation et corridor de la place.
    LEAN_DEFINITION       : TTrueTowerCarrier,
                            rCarrierContactMinus, rCarrierContactPlus, tCarrierCell,
                            TReadingProvenance, TPrimeOccurrence,
                            tCarrierPrimeOccurrence,
                            nCarrierCentralPrime, fnCarrierMemberCentralPrime,
                            PLocalLawOnCarrier, PRPassOnCarrier
    LEAN_THEOREM          : thm_carrier_rpass_iff_localLaw,
                            thm_carrier_rpassClause_order,
                            thm_carrier_rpassClause_corridorEmpty
    SAME_MEMBER_CHECK     : thm_carrierReadings_are_functions_of_member — toutes
                            les lectures du porteur sont fonctions du seul
                            membre, par transport de l'égalité des membres.
    SAME_PASSAGE_CHECK    : la contradiction terminale consomme LE MEME passage
                            que celui produit par la branche OFF.
    SAME_MIDDLE_CHECK     : sans objet dans ce module.
    SAME_HISTORY_CHECK    : la place image est indexée dans l'unique histoire
                            première de O6.
    FORBIDDEN_PREMISES    : reconstruire les contacts depuis kappa et m ; poser
                            une fenêtre ; présenter un habitant quelconque du
                            type comme le porteur canonique du maître.
    NEXT_CONSUMER         : le producteur de la loi locale.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : MEMBER_READINGS_PRODUCED_LOCAL_LAW_CONDITIONAL

Le porteur canonique n'est pas déclaré dans ce module : les deux équations de
l'état décodent une paire fournie mais ne choisissent pas son incidence.  La
branche principale est conservée ci-dessous comme contrôle explicitement non
scientifique.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

/-! ## 1. Le porteur -/

/-- **Le porteur d'états propres** : un état de Tour par membre, et rien
d'autre.  La causalité imposée est respectée par construction, puisque l'état
porte les contacts et non l'inverse. -/
structure TTrueTowerCarrier where
  /-- L'état propre de chaque membre. -/
  fnState : ∀ zUpperZero : TUpperNonTrivialZetaZero, TTrueHarmonicTowerState zUpperZero

/-- Porteur de contrôle de la branche principale ; il ne réalise pas S4. -/
noncomputable def tPrincipalBranchCarrier : TTrueTowerCarrier where
  fnState := tPrincipalBranchTowerState

theorem thm_principalBranchCarrier_state (zUpperZero : TUpperNonTrivialZetaZero) :
    tPrincipalBranchCarrier.fnState zUpperZero = tPrincipalBranchTowerState zUpperZero := rfl

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-- Le contact inférieur du membre, sous ce porteur. -/
noncomputable def rCarrierContactMinus (zUpperZero : TUpperNonTrivialZetaZero) : ℝ :=
  (tCarrier.fnState zUpperZero).contactMinus

/-- Le contact supérieur consécutif du membre, sous ce porteur. -/
noncomputable def rCarrierContactPlus (zUpperZero : TUpperNonTrivialZetaZero) : ℝ :=
  (tCarrier.fnState zUpperZero).contactPlus

/-- **La cellule terminale du membre**, portée par l'état propre. -/
noncomputable def tCarrierCell (zUpperZero : TUpperNonTrivialZetaZero) : TAlgebraicInterval where
  rLeftEndpoint := tCarrier.rCarrierContactMinus zUpperZero
  rRightEndpoint := tCarrier.rCarrierContactPlus zUpperZero
  hLeftPositive := (tCarrier.fnState zUpperZero).contactMinus_pos
  hOrdered := (tCarrier.fnState zUpperZero).ordered

/-- La cellule est directement `(contactMinus, contactPlus]`, sans fenêtre. -/
theorem thm_carrierCell_contactsOnly (zUpperZero : TUpperNonTrivialZetaZero) :
    (tCarrier.tCarrierCell zUpperZero).rLeftEndpoint =
        (tCarrier.fnState zUpperZero).contactMinus ∧
      (tCarrier.tCarrierCell zUpperZero).rRightEndpoint =
        (tCarrier.fnState zUpperZero).contactPlus :=
  ⟨rfl, rfl⟩

/-- **L'inversion de la cellule recouvre exactement la hauteur du membre**,
`T = π / log(C+/C-)`, sans aucune prémisse, sans aucun premier : la cellule du
porteur porte déjà les deux vrais contacts du membre, et leur inversion est
`thm_decodedHeight_eq_zeroHeight` (TrueTowerState.lean), déjà prouvée,
inconditionnelle. Ceci vaut pour TOUT membre du porteur, pas seulement pour un
successeur : la hauteur d'un membre n'est jamais une inconnue à obtenir depuis
la grammaire première, elle est déjà recouvrable depuis sa propre cellule. -/
theorem thm_carrierCell_heightInversion (zUpperZero : TUpperNonTrivialZetaZero) :
    Real.pi /
        (Real.log (tCarrier.tCarrierCell zUpperZero).rRightEndpoint -
          Real.log (tCarrier.tCarrierCell zUpperZero).rLeftEndpoint) =
      rZeroHeight zUpperZero.1 :=
  (tCarrier.fnState zUpperZero).thm_decodedHeight_eq_zeroHeight

/-! ## 2. Comptage, centre C3 et occurrence contacts-only -/

/-- **Le premier central du membre**, lu par le comptage sur CETTE cellule. -/
noncomputable def nCarrierCentralPrime (zUpperZero : TUpperNonTrivialZetaZero) : ℕ :=
  nCellCentralPrime (tCarrier.tCarrierCell zUpperZero)

theorem thm_carrierCentralPrime_isPrime (zUpperZero : TUpperNonTrivialZetaZero) :
    Nat.Prime (tCarrier.nCarrierCentralPrime zUpperZero) :=
  thm_cellCentralPrime_isPrime _

/-- La formule centrale C3 est lue directement sur la cellule des contacts. -/
theorem thm_carrierCentralPrime_is_C3 (zUpperZero : TUpperNonTrivialZetaZero) :
    tCarrier.nCarrierCentralPrime zUpperZero =
      fnPrimeAtRank
        (nCellCentralRank (tCarrier.tCarrierCell zUpperZero) - 1) := rfl

/-- La reconstruction `Λ → ψ → J → π` lit exactement la cellule contacts-only
du porteur et confirme son cardinal et son C3. -/
theorem thm_carrierVonMangoldtChebyshev_sameCell
    (zUpperZero : TUpperNonTrivialZetaZero) :
    nCellFoundCount (tCarrier.tCarrierCell zUpperZero) =
        nPrimeCountingFromJ rChebyshevJNat
            ⌊(tCarrier.tCarrierCell zUpperZero).rRightEndpoint⌋₊ -
          nPrimeCountingFromJ rChebyshevJNat
            ⌊(tCarrier.tCarrierCell zUpperZero).rLeftEndpoint⌋₊ ∧
      tCarrier.nCarrierCentralPrime zUpperZero =
        fnPrimeAtRank
          (nCellCentralRank (tCarrier.tCarrierCell zUpperZero) - 1) :=
  thm_vonMangoldtChebyshev_reads_same_interval _

/-- L'occurrence centrale produite par les contacts du même membre. -/
noncomputable def tCarrierPrimeOccurrence
    (zUpperZero : TUpperNonTrivialZetaZero) : TPrimeOccurrence where
  nPrime := tCarrier.nCarrierCentralPrime zUpperZero
  nRank := nCellCentralRank (tCarrier.tCarrierCell zUpperZero) - 1
  tProvenance := {
    contactMinus := tCarrier.rCarrierContactMinus zUpperZero
    contactPlus := tCarrier.rCarrierContactPlus zUpperZero
    tCell := tCarrier.tCarrierCell zUpperZero
    cell_left := rfl
    cell_right := rfl
  }
  hPrimeAtRank := rfl

theorem thm_carrierOccurrence_isPrime (zUpperZero : TUpperNonTrivialZetaZero) :
    Nat.Prime (tCarrier.tCarrierPrimeOccurrence zUpperZero).nPrime :=
  tCarrier.thm_carrierCentralPrime_isPrime zUpperZero

/-- R-ATT contacts-only : une même provenance de contacts vrais décode le même
membre, sans `sameSpan`, `sameKappa` ni `sameStage`. -/
theorem thm_sameCarrierProvenance_sameMember
    {zLeft zRight : TUpperNonTrivialZetaZero}
    (hSame : (tCarrier.tCarrierPrimeOccurrence zLeft).tProvenance =
      (tCarrier.tCarrierPrimeOccurrence zRight).tProvenance) :
    zLeft = zRight := by
  apply TTrueHarmonicTowerState.thm_same_true_contacts_same_member
    (tCarrier.fnState zLeft) (tCarrier.fnState zRight)
  · exact congrArg TReadingProvenance.contactMinus hSame
  · exact congrArg TReadingProvenance.contactPlus hSame

/-- Deux membres distincts donnent deux occurrences distinctes par leurs vrais
contacts, sans prétendre que leurs nombres premiers nus sont distincts. -/
theorem thm_distinctMembers_distinctCarrierOccurrences
    {zLeft zRight : TUpperNonTrivialZetaZero} (hDistinct : zLeft ≠ zRight) :
    tCarrier.tCarrierPrimeOccurrence zLeft ≠
      tCarrier.tCarrierPrimeOccurrence zRight := by
  intro hOccurrence
  exact hDistinct (tCarrier.thm_sameCarrierProvenance_sameMember
    (congrArg TPrimeOccurrence.tProvenance hOccurrence))

/-- Le premier central du membre est dans la cellule de son propre état, dès que
l'ensemble trouvé y est non vide. -/
theorem thm_carrierCentralPrime_in_cell
    (zUpperZero : TUpperNonTrivialZetaZero)
    (hFoundNonempty : 0 < nCellFoundCount (tCarrier.tCarrierCell zUpperZero)) :
    (tCarrier.tCarrierCell zUpperZero).rLeftEndpoint <
        (tCarrier.nCarrierCentralPrime zUpperZero : ℝ) ∧
      (tCarrier.nCarrierCentralPrime zUpperZero : ℝ) ≤
        (tCarrier.tCarrierCell zUpperZero).rRightEndpoint :=
  thm_cellCentralPrime_in_interval _ hFoundNonempty

/-- **RIGIDITE — toutes les lectures du porteur sont fonctions du seul
membre.** -/
theorem thm_carrierReadings_are_functions_of_member
    {zLeftZero zRightZero : TUpperNonTrivialZetaZero} (hSameMember : zLeftZero = zRightZero) :
    tCarrier.rCarrierContactMinus zLeftZero = tCarrier.rCarrierContactMinus zRightZero ∧
      tCarrier.rCarrierContactPlus zLeftZero =
          tCarrier.rCarrierContactPlus zRightZero ∧
        tCarrier.tCarrierCell zLeftZero = tCarrier.tCarrierCell zRightZero ∧
          tCarrier.nCarrierCentralPrime zLeftZero =
            tCarrier.nCarrierCentralPrime zRightZero :=
  ⟨congrArg _ hSameMember, congrArg _ hSameMember, congrArg _ hSameMember,
    congrArg _ hSameMember⟩

/-! ## 3. La loi locale et R-PASS, portés par CE porteur -/

/-!
Cette section fixe les fonctions canoniques candidates et le type de leur loi
locale. Seule l'extrémité gauche est démontrée définitionnellement. Le theorem
`thm_carrierLocalLaw_of_laterOccurrence_successor` reste conditionnel à
`hLater`; il ne constitue pas le producteur T2.
-/

/-- **Le premier central d'un membre quelconque, sous ce porteur.** -/
noncomputable def fnCarrierMemberCentralPrime (zZero : TNonTrivialZetaZero) : ℕ :=
  tCarrier.nCarrierCentralPrime (zUpperRepresentative zZero)

theorem thm_carrierMemberCentralPrime_isPrime (zZero : TNonTrivialZetaZero) :
    Nat.Prime (tCarrier.fnCarrierMemberCentralPrime zZero) :=
  tCarrier.thm_carrierCentralPrime_isPrime _

/-- La place candidate d'un passage est construite depuis le rang C3 de son
occurrence d'entrée, dans l'unique histoire première. -/
noncomputable def fnCarrierPassagePlace
    (tPassage : TZeroPassage) : TPrimeHistoryPlace where
  nRank := nCellCentralRank
    (tCarrier.tCarrierCell (zUpperRepresentative tPassage.zEarlierMember)) - 1

/-- L'occurrence d'entrée est définitionnellement `p_r` pour cette place. -/
theorem thm_carrierPassagePlace_earlierEndpoint (tPassage : TZeroPassage) :
    tCarrier.fnCarrierMemberCentralPrime tPassage.zEarlierMember =
      nPlaceEarlierEndpoint (tCarrier.fnCarrierPassagePlace tPassage) := rfl

/-- **LA LOI LOCALE DU TRANSPORT, SUR CE PORTEUR.** -/
def PLocalLawOnCarrier (fnPassagePlace : TZeroPassage → TPrimeHistoryPlace) : Prop :=
  PLocalLawTransportsPassageOntoPlace tCarrier.fnCarrierMemberCentralPrime fnPassagePlace

/-- Une preuve de la succession locale `C3(B)=p_(r+1)` suffit exactement à
matérialiser la loi locale sur la place construite depuis `C3(A)`. -/
theorem thm_carrierLocalLaw_of_laterOccurrence_successor
    (hLater : ∀ tPassage : TZeroPassage,
      tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember =
        nPlaceLaterEndpoint (tCarrier.fnCarrierPassagePlace tPassage)) :
    tCarrier.PLocalLawOnCarrier tCarrier.fnCarrierPassagePlace :=
  fun tPassage =>
    ⟨tCarrier.thm_carrierPassagePlace_earlierEndpoint tPassage, hLater tPassage⟩

/-- **R-PASS, SUR CE PORTEUR.** -/
def PRPassOnCarrier (fnPassagePlace : TZeroPassage → TPrimeHistoryPlace) : Prop :=
  PIsMemberSensitivePassageTransport nPlaceEarlierEndpoint nPlaceLaterEndpoint
    tCarrier.fnCarrierMemberCentralPrime fnPassagePlace

end TTrueTowerCarrier

/-! ## 4. Décomposition contacts-only et clauses de place -/

variable {tCarrier : TTrueTowerCarrier}
variable {fnPassagePlace : TZeroPassage → TPrimeHistoryPlace}

/-- **DECOMPOSITION EXACTE SUR LE PORTEUR D'ETATS.** -/
theorem thm_carrier_rpass_iff_localLaw :
    tCarrier.PRPassOnCarrier fnPassagePlace ↔
      tCarrier.PLocalLawOnCarrier fnPassagePlace :=
  thm_rpass_iff_localLaw_generic

/-- **Clause d'ordre**, sur le porteur d'états. -/
theorem thm_carrier_rpassClause_order
    (hLocalLaw : tCarrier.PLocalLawOnCarrier fnPassagePlace) (tPassage : TZeroPassage) :
    tCarrier.fnCarrierMemberCentralPrime tPassage.zEarlierMember <
      tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember := by
  obtain ⟨hEarlier, hLater⟩ := hLocalLaw tPassage
  rw [hEarlier, hLater]
  exact thm_place_gap_positive (fnPassagePlace tPassage)

/-- **Clause de séparation**, dérivée, jamais posée. -/
theorem thm_carrier_rpassClause_endpointsDistinct
    (hLocalLaw : tCarrier.PLocalLawOnCarrier fnPassagePlace) (tPassage : TZeroPassage) :
    tCarrier.fnCarrierMemberCentralPrime tPassage.zEarlierMember ≠
      tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember :=
  ne_of_lt (thm_carrier_rpassClause_order hLocalLaw tPassage)

/-- **Clause de corridor vide**, sur le porteur d'états. -/
theorem thm_carrier_rpassClause_corridorEmpty
    (hLocalLaw : tCarrier.PLocalLawOnCarrier fnPassagePlace) (tPassage : TZeroPassage)
    {nCandidate : ℕ} (hPrime : Nat.Prime nCandidate)
    (hLeft : tCarrier.fnCarrierMemberCentralPrime tPassage.zEarlierMember < nCandidate)
    (hRight : nCandidate < tCarrier.fnCarrierMemberCentralPrime tPassage.zLaterMember) :
    False := by
  obtain ⟨hEarlier, hLater⟩ := hLocalLaw tPassage
  rw [hEarlier] at hLeft
  rw [hLater] at hRight
  exact thm_place_corridorEmpty (fnPassagePlace tPassage) hPrime hLeft hRight

end RHV3Lean
