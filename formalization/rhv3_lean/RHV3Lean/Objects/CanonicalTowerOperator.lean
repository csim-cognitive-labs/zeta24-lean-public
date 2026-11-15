/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.PrimeOccurrence

/-!
# RHV3Lean — S4, les deux coordonnées discrètes, et l'opérateur canonique

    TRACE_ID              : RHV3-S4
    SEMANTIC_OBJECT       : S4 — coordonnées discrètes de la Tour ; le porteur
                            canonique unique
    SEMANTIC_STATEMENT    : le membre possède déjà sa Tour propre et l'événement
                            de Tour possède déjà ses deux rencontres réelles
                            avec l'axe algébrique ; kappa et m ne construisent
                            ni la Tour ni les contacts, ils ADRESSENT ces deux
                            rencontres dans l'orbite ordonnée des rayons.
    MATHEMATICAL_STATEMENT: kappa = (T*log(C-) - phi)/pi et
                            m = (T/pi)*(log(C+) - log(C-)) ; réciproquement
                            T = m*pi/(log C+ - log C-) et
                            beta = T/tan(T*log C-) ; donc
                            (beta,T) + evenement de Tour <-> (C-,C+) <-> (kappa,m),
                            sans selection premiere et sans recherche d'un
                            entier.
    MATHEMATICAL_PARENT   : O3 — la Tour harmonique ; O4 — les contacts et la
                            cellule.
    PROOF_STRATEGY        : l'equation d'incidence donne la relecture de kappa ;
                            la formule du diametre donne celle de m ; les deux
                            reciproques sont deja prouvees en O4. Le porteur
                            canonique est un OPERATEUR unique, une fenetre par
                            membre, threade partout : aucune etape aval ne peut
                            re-choisir une fenetre.
    REQUIRED_LEMMAS       : thm_rTowerLogIncidence_phaseEquation,
                            thm_cellLogDiameter_formula,
                            thm_inversion_recovers_height,
                            thm_inversion_recovers_radialPosition,
                            thm_sameContactData_sameMember
    WHY_EACH_LEMMA_EXISTS : les deux premiers donnent les deux relectures
                            discretes ; les deux suivants les deux reciproques
                            continues ; le dernier ferme l'injectivite de la
                            lecture complete.
    LEAN_DEFINITION       : TCanonicalTowerOperator, nOperatorEntryAddress,
                            nOperatorSpan, rOperatorContactMinus,
                            rOperatorContactPlus, tOperatorCell,
                            nOperatorCentralPrime, tOperatorPrimeOccurrence
    LEAN_THEOREM          : thm_kappa_eq_entry_quotient,
                            thm_span_eq_density_mul_logDiameter,
                            thm_operator_kappa_eq_entry_quotient,
                            thm_operator_span_eq_density_mul_logDiameter,
                            thm_operator_sameContactData_sameMember,
                            thm_operatorReadings_are_functions_of_member
    SAME_MEMBER_CHECK     : une fois l'operateur fixe, contacts, cellule,
                            premier central et occurrence sont des fonctions du
                            SEUL membre ; plus aucune fenetre libre en aval.
    SAME_PASSAGE_CHECK    : sans objet a ce niveau.
    SAME_MIDDLE_CHECK     : sans objet a ce niveau.
    SAME_HISTORY_CHECK    : le premier central est lu dans l'unique histoire
                            premiere, par le comptage de O10.
    FORBIDDEN_PREMISES    : toute fonction de RECHERCHE de kappa ou de m ; tout
                            ancrage sur un premier, un rang, un comptage ou C3 ;
                            tout `Classical.choose` guide par une loi de
                            localisation ; deux operateurs distincts recolles en
                            une seule chaine.
    NEXT_CONSUMER         : la loi locale du transport, enoncee sur CE MEME
                            operateur.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

## Ce que ce module ne fait PAS, et pourquoi

Il ne produit aucune fonction qui calculerait `kappa` ou `m` a partir du membre :
le maitre Lean S4 l'interdit explicitement (`SEARCH_FOR_KAPPA = FORBIDDEN`,
`SEARCH_FOR_M = FORBIDDEN`). Les deux coordonnees discretes ne sont pas
construites : elles ADRESSENT deux rencontres deja existantes, et ce module en
donne la relecture exacte dans les deux sens. La canonicite n'est donc pas une
formule : c'est l'unicite du porteur, un seul operateur threade partout.

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

/-! ## 1. Les deux relectures discrètes du maître S4 -/

variable (zUpperZero : TUpperNonTrivialZetaZero) (tWindow : TTowerWindow)

/-- **RELECTURE DE `kappa`** : `kappa = (T*log(C-) - phi)/pi`.

L'adresse d'entrée n'est pas cherchée : elle se relit exactement sur le contact
d'entrée et la phase propre du membre. -/
theorem thm_kappa_eq_entry_quotient :
    ((tWindow.kEntryAddress : ℝ)) =
      (rTowerHeight zUpperZero *
          Real.log (rContactMinus zUpperZero tWindow) -
        rTowerPhase zUpperZero) / Real.pi := by
  have hLogContact :
      Real.log (rContactMinus zUpperZero tWindow) =
        rTowerLogIncidence zUpperZero tWindow.kEntryAddress := by
    unfold rContactMinus rTowerIncidence
    exact Real.log_exp _
  rw [hLogContact, thm_rTowerLogIncidence_phaseEquation]
  field_simp
  ring

/-- **Le quotient d'entrée EST un entier**, et c'est exactement l'adresse
d'entrée : la relecture ne fabrique aucun nouvel entier. -/
theorem thm_kappa_quotient_isInteger :
    ∃ kAddress : ℤ,
      (rTowerHeight zUpperZero *
          Real.log (rContactMinus zUpperZero tWindow) -
        rTowerPhase zUpperZero) / Real.pi = (kAddress : ℝ) :=
  ⟨tWindow.kEntryAddress, (thm_kappa_eq_entry_quotient zUpperZero tWindow).symm⟩

/-- **RELECTURE DE `m`** : `m = (T/pi)*(log(C+) - log(C-))`.

Le nombre d'étages n'est pas cherché : il se relit exactement sur le diamètre
logarithmique de la cellule et la densité propre du membre. -/
theorem thm_span_eq_density_mul_logDiameter :
    ((tWindow.nSpan : ℝ)) =
      rTowerDensity zUpperZero * rCellLogDiameter zUpperZero tWindow := by
  have hHeight : rTowerHeight zUpperZero ≠ 0 :=
    ne_of_gt (thm_rTowerHeight_positive zUpperZero)
  rw [thm_cellLogDiameter_formula, rTowerDensity]
  field_simp

/-! ## 2. L'opérateur canonique : un seul porteur, threadé partout -/

/-- **L'opérateur canonique de Tour** : une fenêtre par membre.

C'est le porteur du maître : il n'est pas calculé, il est FIXÉ une fois, et
threadé dans toute la chaîne.  C'est ce qui fait qu'aucune étape en aval ne peut
re-choisir une fenêtre et que deux blocs ne peuvent jamais parler de deux Tours
différentes. -/
structure TCanonicalTowerOperator where
  /-- La fenêtre propre de chaque membre. -/
  fnWindow : TUpperNonTrivialZetaZero → TTowerWindow

namespace TCanonicalTowerOperator

variable (tOperator : TCanonicalTowerOperator)

/-- L'adresse d'entrée du membre, sous cet opérateur. -/
def nOperatorEntryAddress (zUpperZero : TUpperNonTrivialZetaZero) : ℤ :=
  (tOperator.fnWindow zUpperZero).kEntryAddress

/-- Le nombre d'étages du membre, sous cet opérateur. -/
def nOperatorSpan (zUpperZero : TUpperNonTrivialZetaZero) : ℕ :=
  (tOperator.fnWindow zUpperZero).nSpan

theorem nOperatorSpan_positive (zUpperZero : TUpperNonTrivialZetaZero) :
    0 < tOperator.nOperatorSpan zUpperZero :=
  (tOperator.fnWindow zUpperZero).hSpanPositive

/-- Le contact d'entrée du membre : fonction du SEUL membre. -/
noncomputable def rOperatorContactMinus
    (zUpperZero : TUpperNonTrivialZetaZero) : ℝ :=
  rContactMinus zUpperZero (tOperator.fnWindow zUpperZero)

/-- Le contact terminal du membre : fonction du SEUL membre. -/
noncomputable def rOperatorContactPlus
    (zUpperZero : TUpperNonTrivialZetaZero) : ℝ :=
  rContactPlus zUpperZero (tOperator.fnWindow zUpperZero)

/-- La cellule terminale du membre : fonction du SEUL membre. -/
noncomputable def tOperatorCell (zUpperZero : TUpperNonTrivialZetaZero) :
    TAlgebraicInterval :=
  tCellAlgebraicInterval zUpperZero (tOperator.fnWindow zUpperZero)

/-- **Le premier central du membre**, `C3(z)` : fonction du SEUL membre, une
fois l'opérateur fixé. -/
noncomputable def nOperatorCentralPrime
    (zUpperZero : TUpperNonTrivialZetaZero) : ℕ :=
  nCellCentralPrime (tOperator.tOperatorCell zUpperZero)

/-- **L'occurrence première du membre** : fonction du SEUL membre. -/
noncomputable def tOperatorPrimeOccurrence
    (zUpperZero : TUpperNonTrivialZetaZero) : TPrimeOccurrence where
  nPrime := tOperator.nOperatorCentralPrime zUpperZero
  nRank := nCellCentralRank (tOperator.tOperatorCell zUpperZero) - 1
  tProvenance := {
    tCell := tOperator.tOperatorCell zUpperZero
    contactMinus := tOperator.rOperatorContactMinus zUpperZero
    contactPlus := tOperator.rOperatorContactPlus zUpperZero
    cell_left := rfl
    cell_right := rfl
  }
  hPrimeAtRank := rfl

theorem thm_operatorCentralPrime_isPrime
    (zUpperZero : TUpperNonTrivialZetaZero) :
    Nat.Prime (tOperator.nOperatorCentralPrime zUpperZero) :=
  thm_cellCentralPrime_isPrime _

/-- Le premier central du membre est dans la cellule de sa propre Tour. -/
theorem thm_operatorCentralPrime_in_cell
    (zUpperZero : TUpperNonTrivialZetaZero)
    (hFoundNonempty : 0 < nCellFoundCount (tOperator.tOperatorCell zUpperZero)) :
    (tOperator.tOperatorCell zUpperZero).rLeftEndpoint <
        (tOperator.nOperatorCentralPrime zUpperZero : ℝ) ∧
      (tOperator.nOperatorCentralPrime zUpperZero : ℝ) ≤
        (tOperator.tOperatorCell zUpperZero).rRightEndpoint :=
  thm_cellCentralPrime_in_interval _ hFoundNonempty

/-! ### Le dictionnaire complet de S4, sur l'opérateur -/

/-- `kappa` relu sur les contacts du membre. -/
theorem thm_operator_kappa_eq_entry_quotient
    (zUpperZero : TUpperNonTrivialZetaZero) :
    ((tOperator.nOperatorEntryAddress zUpperZero : ℝ)) =
      (rTowerHeight zUpperZero *
          Real.log (tOperator.rOperatorContactMinus zUpperZero) -
        rTowerPhase zUpperZero) / Real.pi :=
  thm_kappa_eq_entry_quotient zUpperZero _

/-- `m` relu sur le diamètre de la cellule du membre. -/
theorem thm_operator_span_eq_density_mul_logDiameter
    (zUpperZero : TUpperNonTrivialZetaZero) :
    ((tOperator.nOperatorSpan zUpperZero : ℝ)) =
      rTowerDensity zUpperZero *
        rCellLogDiameter zUpperZero (tOperator.fnWindow zUpperZero) :=
  thm_span_eq_density_mul_logDiameter zUpperZero _

/-- La hauteur relue sur les contacts et le nombre d'étages. -/
theorem thm_operator_height_eq_span_pi_div_logDiameter
    (zUpperZero : TUpperNonTrivialZetaZero) :
    rTowerHeight zUpperZero =
      (tOperator.nOperatorSpan zUpperZero : ℝ) * Real.pi /
        rCellLogDiameter zUpperZero (tOperator.fnWindow zUpperZero) :=
  thm_inversion_recovers_height zUpperZero _

/-- La position radiale relue sur le contact d'entrée. -/
theorem thm_operator_radialPosition_eq_height_div_tan
    (zUpperZero : TUpperNonTrivialZetaZero) :
    rTowerRadialPosition zUpperZero =
      rTowerHeight zUpperZero /
        Real.tan (rTowerHeight zUpperZero *
          Real.log (tOperator.rOperatorContactMinus zUpperZero)) :=
  thm_inversion_recovers_radialPosition zUpperZero _

/-- **Même donnée complète de contacts, même membre**, sur un seul et même
opérateur. -/
theorem thm_operator_sameContactData_sameMember
    {zLeftZero zRightZero : TUpperNonTrivialZetaZero}
    (hSameSpan :
      tOperator.nOperatorSpan zLeftZero = tOperator.nOperatorSpan zRightZero)
    (hSameContactMinus :
      tOperator.rOperatorContactMinus zLeftZero =
        tOperator.rOperatorContactMinus zRightZero)
    (hSameContactPlus :
      tOperator.rOperatorContactPlus zLeftZero =
        tOperator.rOperatorContactPlus zRightZero) :
    zLeftZero = zRightZero :=
  thm_sameContactData_sameMember hSameSpan hSameContactMinus hSameContactPlus

/-- **RIGIDITE — toutes les lectures canoniques sont des fonctions du seul
membre.** -/
theorem thm_operatorReadings_are_functions_of_member
    {zLeftZero zRightZero : TUpperNonTrivialZetaZero}
    (hSameMember : zLeftZero = zRightZero) :
    tOperator.rOperatorContactMinus zLeftZero =
        tOperator.rOperatorContactMinus zRightZero ∧
      tOperator.rOperatorContactPlus zLeftZero =
          tOperator.rOperatorContactPlus zRightZero ∧
        tOperator.tOperatorCell zLeftZero = tOperator.tOperatorCell zRightZero ∧
          tOperator.nOperatorCentralPrime zLeftZero =
              tOperator.nOperatorCentralPrime zRightZero ∧
            tOperator.tOperatorPrimeOccurrence zLeftZero =
              tOperator.tOperatorPrimeOccurrence zRightZero :=
  ⟨congrArg _ hSameMember, congrArg _ hSameMember, congrArg _ hSameMember,
    congrArg _ hSameMember, congrArg _ hSameMember⟩

end TCanonicalTowerOperator

end RHV3Lean
