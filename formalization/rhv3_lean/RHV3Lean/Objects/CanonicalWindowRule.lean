/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.CanonicalTowerOperator
import Mathlib.NumberTheory.Bertrand

/-!
# RHV3Lean — CONTROLE du rapport quatre (JAMAIS le porteur canonique)

    TRACE_ID              : RHV3-RATIO-FOUR-CONTROL
    SEMANTIC_OBJECT       : CONTROLE — un habitant du type, jamais le porteur
    SEMANTIC_STATEMENT    : la Tour d'un membre porte une fenêtre propre ; tant
                            qu'aucun terme de porteur n'existe, toute la chaîne
                            terminale ne gouverne rien.  Ce module produit un
                            porteur dont les deux coordonnées discrètes sont
                            lues sur le seul état de Tour du membre, et dont la
                            cellule terminale rencontre réellement l'axe
                            algébrique.
    MATHEMATICAL_STATEMENT: pour l'adresse d'entrée `kappa = 0` et le nombre
                            d'étages `m(z) = floor(T*log 4/pi) + 1`, on a
                            `C-(z) = exp(phi(z)/T) >= 1` et
                            `C+(z) >= 4*C-(z)` ; par le postulat de Bertrand
                            appliqué deux fois, l'intervalle algébrique
                            `(C-, C+]` contient au moins deux premiers
                            distincts, donc son ensemble trouvé est non vide et
                            son premier central y appartient réellement.
    MATHEMATICAL_PARENT   : O3 — la Tour harmonique ; O4 — les contacts et la
                            cellule ; O2 — l'axe algébrique ; O10 — le comptage.
    PROOF_STRATEGY        : les deux coordonnées sont des fonctions de la seule
                            hauteur et de la seule phase du membre ; la borne
                            inférieure du contact d'entrée vient de la
                            positivité de la phase tangentielle ; le rapport
                            multiplicatif vient du plancher choisi ; les deux
                            premiers viennent de Bertrand, jamais d'une
                            recherche.
    REQUIRED_LEMMAS       : Nat.lt_floor_add_one, Real.one_le_exp,
                            Nat.exists_prime_lt_and_le_two_mul
    WHY_EACH_LEMMA_EXISTS : le premier borne le plancher par en dessous, donc le
                            diamètre logarithmique par en dessous ; le deuxième
                            place le contact d'entrée au-dessus de un ; le
                            troisième est le postulat de Bertrand, appliqué deux
                            fois pour obtenir DEUX premiers, jamais un seul.
    LEAN_DEFINITION       : nRatioFourSpan, tRatioFourWindow, tRatioFourOperator
    LEAN_THEOREM          : thm_ratioFourSpan_positive,
                            thm_ratioFourSpan_logDiameter_ge_logFour,
                            thm_ratioFourOperator_one_le_contactMinus,
                            thm_ratioFourOperator_ratio_four,
                            thm_ratioFourInterval_containsTwoPrimes,
                            thm_ratioFourOperator_cellFoundCount_positive,
                            thm_ratioFourOperator_centralPrime_in_cell
    SAME_MEMBER_CHECK     : les deux coordonnées, les deux contacts, la cellule
                            et le premier central sont tous des fonctions du
                            SEUL membre, par `thm_operatorReadings_are_functions_of_member`.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : le premier central est lu dans l'unique histoire
                            première par le comptage de O10, jamais choisi.
    FORBIDDEN_PREMISES    : toute fonction de RECHERCHE de `kappa` ou de `m`
                            (interdite par S4) ; tout ancrage sur un premier, un
                            rang, un comptage ou C3 ; toute réintroduction de la
                            lecture retirée « la cellule ne contient qu'un seul
                            premier ».
    NEXT_CONSUMER         : la loi locale du transport, énoncée sur CE MEME
                            porteur.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

## STATUT — à lire avant tout réemploi

    CONTROL_ONLY
    NOT_THE_CANONICAL_CARRIER
    REALISES_NO_OBLIGATION

Ce module produit un TERME de `TCanonicalTowerOperator`, puis un terme de
`TTrueTowerCarrier`.  Exhiber un habitant d'un type ne réalise JAMAIS l'objet
que les maîtres appellent CANONIQUE : il faudrait de plus une règle de
détermination de l'état propre, et les maîtres n'en donnent pas — § S4 fixe
`C_- = min(C1,C2)` et `C_+ = max(C1,C2)` sans définir `C1` ni `C2`.

La raison de fond est ici, et doit rester visible.  Le diamètre est épinglé à
`log 4`, donc quand la hauteur du membre grandit, `C-` tend vers `1`, `C+` tend
vers `4`, l'ensemble trouvé tend vers `{2,3}` et le premier central devient
constant.  Un premier central constant ne progresse d'aucun rang d'un membre au
suivant : ce contrôle ne peut donc pas porter la loi locale du transport, et
aucune tentative ne doit être faite de l'y contraindre.

Ce que ce contrôle établit réellement, et qui reste acquis : le type des états
propres n'est pas vide, et un rapport multiplicatif de quatre suffit à peupler
une cellule de plusieurs premiers par Bertrand seul.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

/-! ## 1. Les deux coordonnées, lues sur le seul état de Tour -/

/-- **Le nombre d'étages qui atteint le rapport quatre** :
`m(z) = floor(T*log 4/pi) + 1`.  Fonction de la seule hauteur du membre. -/
noncomputable def nRatioFourSpan (zUpperZero : TUpperNonTrivialZetaZero) : ℕ :=
  ⌊rTowerHeight zUpperZero * Real.log 4 / Real.pi⌋₊ + 1

theorem thm_ratioFourSpan_positive (zUpperZero : TUpperNonTrivialZetaZero) :
    0 < nRatioFourSpan zUpperZero := Nat.succ_pos _

/-- **Le diamètre logarithmique atteint `log 4`** : `m*pi/T >= log 4`. -/
theorem thm_ratioFourSpan_logDiameter_ge_logFour
    (zUpperZero : TUpperNonTrivialZetaZero) :
    Real.log 4 ≤ (nRatioFourSpan zUpperZero : ℝ) * Real.pi / rTowerHeight zUpperZero := by
  have hHeight : 0 < rTowerHeight zUpperZero := thm_rTowerHeight_positive zUpperZero
  have hPi : 0 < Real.pi := Real.pi_pos
  have hFloor :
      rTowerHeight zUpperZero * Real.log 4 / Real.pi < (nRatioFourSpan zUpperZero : ℝ) := by
    have hStep :=
      Nat.lt_floor_add_one (rTowerHeight zUpperZero * Real.log 4 / Real.pi)
    simpa [nRatioFourSpan] using hStep
  rw [le_div_iff₀ hHeight]
  rw [div_lt_iff₀ hPi] at hFloor
  linarith

/-- **La fenêtre du rapport quatre** : adresse d'entrée à l'origine de l'orbite,
nombre d'étages lu sur la seule hauteur. -/
noncomputable def tRatioFourWindow (zUpperZero : TUpperNonTrivialZetaZero) : TTowerWindow where
  kEntryAddress := 0
  nSpan := nRatioFourSpan zUpperZero
  hSpanPositive := thm_ratioFourSpan_positive zUpperZero

/-- **UN PORTEUR CANONIQUE HABITE.**  Une seule fenêtre par membre, threadée
partout : c'est le terme que la chaîne terminale attendait. -/
noncomputable def tRatioFourOperator : TCanonicalTowerOperator where
  fnWindow := tRatioFourWindow

/-! ## 2. La cellule de ce porteur rencontre réellement l'axe algébrique -/

theorem thm_ratioFourOperator_contactMinus_formula
    (zUpperZero : TUpperNonTrivialZetaZero) :
    tRatioFourOperator.rOperatorContactMinus zUpperZero =
      Real.exp (rTowerPhase zUpperZero / rTowerHeight zUpperZero) := by
  show rContactMinus zUpperZero (tRatioFourWindow zUpperZero) = _
  unfold rContactMinus rTowerIncidence rTowerLogIncidence tRatioFourWindow
  norm_num

/-- **Le contact d'entrée est au-dessus de un**, parce que la phase tangentielle
propre du membre est strictement positive. -/
theorem thm_ratioFourOperator_one_le_contactMinus
    (zUpperZero : TUpperNonTrivialZetaZero) :
    (1 : ℝ) ≤ tRatioFourOperator.rOperatorContactMinus zUpperZero := by
  rw [thm_ratioFourOperator_contactMinus_formula]
  have hHeight : 0 < rTowerHeight zUpperZero := thm_rTowerHeight_positive zUpperZero
  have hPhase : 0 < rTowerPhase zUpperZero := thm_rTowerPhase_positive zUpperZero
  have hQuotient : (0 : ℝ) ≤ rTowerPhase zUpperZero / rTowerHeight zUpperZero :=
    le_of_lt (div_pos hPhase hHeight)
  simpa using Real.one_le_exp hQuotient

/-- **Le rapport multiplicatif de la cellule atteint quatre.** -/
theorem thm_ratioFourOperator_ratio_four (zUpperZero : TUpperNonTrivialZetaZero) :
    4 * tRatioFourOperator.rOperatorContactMinus zUpperZero ≤
      tRatioFourOperator.rOperatorContactPlus zUpperZero := by
  have hMinusPositive : 0 < tRatioFourOperator.rOperatorContactMinus zUpperZero :=
    thm_contactMinus_positive zUpperZero _
  have hPlusPositive : 0 < tRatioFourOperator.rOperatorContactPlus zUpperZero :=
    thm_contactPlus_positive zUpperZero _
  have hDiameter :
      Real.log (tRatioFourOperator.rOperatorContactPlus zUpperZero) -
          Real.log (tRatioFourOperator.rOperatorContactMinus zUpperZero) =
        (nRatioFourSpan zUpperZero : ℝ) * Real.pi / rTowerHeight zUpperZero := by
    have hFormula := thm_cellLogDiameter_formula zUpperZero (tRatioFourWindow zUpperZero)
    simpa [rCellLogDiameter, TCanonicalTowerOperator.rOperatorContactPlus,
      TCanonicalTowerOperator.rOperatorContactMinus, tRatioFourOperator,
      tRatioFourWindow] using hFormula
  have hLogFour : Real.log 4 ≤
      Real.log (tRatioFourOperator.rOperatorContactPlus zUpperZero) -
        Real.log (tRatioFourOperator.rOperatorContactMinus zUpperZero) := by
    rw [hDiameter]
    exact thm_ratioFourSpan_logDiameter_ge_logFour zUpperZero
  have hProduct :
      Real.log (4 * tRatioFourOperator.rOperatorContactMinus zUpperZero) ≤
        Real.log (tRatioFourOperator.rOperatorContactPlus zUpperZero) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hMinusPositive)]
    linarith
  exact (Real.log_le_log_iff (by positivity) hPlusPositive).mp hProduct

/-! ## 3. Deux premiers dans la cellule, par Bertrand seul -/

/-- **Un intervalle algébrique qui part d'au moins un et dont le rapport atteint
quatre contient DEUX premiers distincts.**

Deux applications du postulat de Bertrand suffisent.  Rien ici ne prétend que
l'ensemble trouvé serait un singleton : la lecture retirée n'apparaît nulle
part, et c'est au contraire la PLURALITE qui est produite. -/
theorem thm_ratioFourInterval_containsTwoPrimes
    {rLeft rRight : ℝ} (hOneLe : 1 ≤ rLeft) (hRatio : 4 * rLeft ≤ rRight) :
    ∃ nSmallPrime nLargePrime : ℕ,
      Nat.Prime nSmallPrime ∧ Nat.Prime nLargePrime ∧ nSmallPrime < nLargePrime ∧
        rLeft < (nSmallPrime : ℝ) ∧ (nLargePrime : ℝ) ≤ rRight := by
  have hLeftNonneg : (0 : ℝ) ≤ rLeft := le_trans zero_le_one hOneLe
  set nFloor : ℕ := ⌊rLeft⌋₊ with hFloor
  have hFloorLe : (nFloor : ℝ) ≤ rLeft := Nat.floor_le hLeftNonneg
  have hLtSucc : rLeft < (nFloor : ℝ) + 1 := by
    simpa using Nat.lt_floor_add_one rLeft
  have hFloorPositive : 0 < nFloor := Nat.floor_pos.mpr hOneLe
  obtain ⟨nSmallPrime, hSmallPrime, hFloorLt, hSmallLe⟩ :=
    Nat.exists_prime_lt_and_le_two_mul nFloor hFloorPositive.ne'
  obtain ⟨nLargePrime, hLargePrime, hSmallLt, hLargeLe⟩ :=
    Nat.exists_prime_lt_and_le_two_mul nSmallPrime hSmallPrime.pos.ne'
  refine ⟨nSmallPrime, nLargePrime, hSmallPrime, hLargePrime, hSmallLt, ?_, ?_⟩
  · have hSucc : (nFloor : ℝ) + 1 ≤ (nSmallPrime : ℝ) := by exact_mod_cast hFloorLt
    linarith
  · have hSmallReal : (nSmallPrime : ℝ) ≤ 2 * (nFloor : ℝ) := by exact_mod_cast hSmallLe
    have hLargeReal : (nLargePrime : ℝ) ≤ 2 * (nSmallPrime : ℝ) := by exact_mod_cast hLargeLe
    linarith

/-- **L'ENSEMBLE TROUVE DE LA CELLULE EST NON VIDE**, pour tout membre. -/
theorem thm_ratioFourOperator_cellFoundCount_positive
    (zUpperZero : TUpperNonTrivialZetaZero) :
    0 < nCellFoundCount (tRatioFourOperator.tOperatorCell zUpperZero) := by
  obtain ⟨nSmallPrime, nLargePrime, hSmallPrime, _hLargePrime, hSmallLt,
      hLeftLt, hLargeLe⟩ :=
    thm_ratioFourInterval_containsTwoPrimes
      (thm_ratioFourOperator_one_le_contactMinus zUpperZero)
      (thm_ratioFourOperator_ratio_four zUpperZero)
  have hSmallLe : (nSmallPrime : ℝ) ≤ (nLargePrime : ℝ) := by
    exact_mod_cast le_of_lt hSmallLt
  have hMember :
      nSmallPrime ∈
        sAlgebraicIntervalFoundPrimes (tRatioFourOperator.tOperatorCell zUpperZero) := by
    rw [thm_mem_foundPrimes_iff]
    exact ⟨hSmallPrime, hLeftLt, le_trans hSmallLe hLargeLe⟩
  have hCard := Finset.card_pos.mpr ⟨nSmallPrime, hMember⟩
  simpa [nCellFoundCount] using hCard

/-- **LE PREMIER CENTRAL EST REELLEMENT DANS LA CELLULE**, pour tout membre. -/
theorem thm_ratioFourOperator_centralPrime_in_cell
    (zUpperZero : TUpperNonTrivialZetaZero) :
    (tRatioFourOperator.tOperatorCell zUpperZero).rLeftEndpoint <
        (tRatioFourOperator.nOperatorCentralPrime zUpperZero : ℝ) ∧
      (tRatioFourOperator.nOperatorCentralPrime zUpperZero : ℝ) ≤
        (tRatioFourOperator.tOperatorCell zUpperZero).rRightEndpoint :=
  tRatioFourOperator.thm_operatorCentralPrime_in_cell zUpperZero
    (thm_ratioFourOperator_cellFoundCount_positive zUpperZero)

/-- **Le premier central du membre est un vrai premier de l'ensemble trouvé**,
donc la cellule est réellement peuplée et le comptage confirme un rang au lieu
de choisir un premier. -/
theorem thm_ratioFourOperator_centralPrime_mem_found
    (zUpperZero : TUpperNonTrivialZetaZero) :
    tRatioFourOperator.nOperatorCentralPrime zUpperZero ∈
      sAlgebraicIntervalFoundPrimes (tRatioFourOperator.tOperatorCell zUpperZero) :=
  thm_cellCentralPrime_mem_found _
    (thm_ratioFourOperator_cellFoundCount_positive zUpperZero)

end RHV3Lean
