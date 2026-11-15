/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TrueZero
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# RHV3Lean — O3, la Tour harmonique

    TRACE_ID              : RHV3-O3
    SEMANTIC_OBJECT       : O3 — la Tour harmonique
    SEMANTIC_STATEMENT    : la Tour harmonique est un objet géométrique
                            dynamique, antérieur au comptage premier, qui reçoit
                            un vrai zéro non trivial et un seul et transporte
                            exactement ce membre le long de son mouvement propre.
    MATHEMATICAL_STATEMENT: phi(z) = arctan(T/beta), nu(z) = T/pi,
                            log x_k(z) = (phi(z) + k*pi)/T,
                            log x_(k+n) - log x_k = n*pi/T, et pour n > 0,
                            x_k < x_(k+n) ; la Tour ne transporte jamais deux
                            zéros distincts à la fois.
    MATHEMATICAL_PARENT   : O1 — le vrai zéro.
    PROOF_STRATEGY        : transcription directe des formules du maître Lean
                            S3 ; la phase, la densité et les incidences sont des
                            fonctions du seul membre, donc l'état de Tour
                            conserve sa source par construction.
    REQUIRED_LEMMAS       : Real.arctan_pos, Real.arctan_lt_pi_div_two,
                            Real.exp_lt_exp, div_lt_div_of_pos_left
    WHY_EACH_LEMMA_EXISTS : les deux premiers bornent la phase tangentielle dans
                            le quadrant ouvert ; les deux derniers donnent
                            l'ordre strict des rayons avec l'adresse.
    LEAN_DEFINITION       : rTowerPhase, rTowerReducedPhase, rTowerDensity,
                            rTowerLogIncidence, rTowerIncidence, TTowerState,
                            tTowerState
    LEAN_THEOREM          : thm_rTowerPhase_positive, thm_rTowerPhase_lt_piDivTwo,
                            thm_rTowerDensity_positive, thm_rTowerLogIncidence_shift,
                            thm_rTowerLogIncidence_strictOrder,
                            thm_rTowerIncidence_positive,
                            thm_rTowerIncidence_strictOrder,
                            thm_tTowerState_sourceZero
    SAME_MEMBER_CHECK     : thm_tTowerState_sourceZero — l'état de Tour rend
                            exactement le membre qu'il a reçu ; la Tour ne
                            transporte jamais deux zéros à la fois.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre ici. La Tour est
                            antérieure au comptage.
    FORBIDDEN_PREMISES    : tout premier, tout rang, tout comptage, toute
                            cellule en entrée d'une définition de ce module ;
                            toute sélection d'une adresse par une lecture
                            arithmétique.
    NEXT_CONSUMER         : O4 (les contacts et la cellule terminale).
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

variable (zUpperZero : TUpperNonTrivialZetaZero)

/-! ## 1. Les coordonnées propres de la Tour -/

/-- Hauteur du membre porté par la Tour. -/
def rTowerHeight : ℝ := rZeroHeight zUpperZero.1

/-- Position radiale du membre porté par la Tour. -/
def rTowerRadialPosition : ℝ := rZeroRadialPosition zUpperZero.1

theorem thm_rTowerHeight_positive : 0 < rTowerHeight zUpperZero := zUpperZero.2

theorem thm_rTowerRadialPosition_positive : 0 < rTowerRadialPosition zUpperZero :=
  thm_zeroRadialPosition_positive zUpperZero.1

/-- **La phase tangentielle propre** `phi(z) = arctan(T/beta)`. -/
noncomputable def rTowerPhase : ℝ :=
  Real.arctan (rTowerHeight zUpperZero / rTowerRadialPosition zUpperZero)

/-- **La phase réduite** `alpha = phi/pi`. -/
noncomputable def rTowerReducedPhase : ℝ := rTowerPhase zUpperZero / Real.pi

/-- **La densité propre** `nu(z) = T/pi`. -/
noncomputable def rTowerDensity : ℝ := rTowerHeight zUpperZero / Real.pi

theorem thm_rTowerPhase_positive : 0 < rTowerPhase zUpperZero :=
  Real.arctan_pos.mpr
    (div_pos (thm_rTowerHeight_positive zUpperZero)
      (thm_rTowerRadialPosition_positive zUpperZero))

theorem thm_rTowerPhase_lt_piDivTwo : rTowerPhase zUpperZero < Real.pi / 2 :=
  Real.arctan_lt_pi_div_two _

theorem thm_rTowerDensity_positive : 0 < rTowerDensity zUpperZero :=
  div_pos (thm_rTowerHeight_positive zUpperZero) Real.pi_pos

/-! ## 2. Les rayons et leurs incidences -/

/-- **L'incidence logarithmique à l'adresse `k`** : `log x_k = (phi + k*pi)/T`. -/
noncomputable def rTowerLogIncidence (kAddress : ℤ) : ℝ :=
  (rTowerPhase zUpperZero + (kAddress : ℝ) * Real.pi) / rTowerHeight zUpperZero

/-- **L'incidence à l'adresse `k`** : `x_k = exp(log x_k)`. -/
noncomputable def rTowerIncidence (kAddress : ℤ) : ℝ :=
  Real.exp (rTowerLogIncidence zUpperZero kAddress)

/-- **L'équation d'incidence**, sous sa forme sans division :
`T * log x_k = phi + k*pi`. -/
theorem thm_rTowerLogIncidence_phaseEquation (kAddress : ℤ) :
    rTowerHeight zUpperZero * rTowerLogIncidence zUpperZero kAddress =
      rTowerPhase zUpperZero + (kAddress : ℝ) * Real.pi := by
  have hHeight : rTowerHeight zUpperZero ≠ 0 :=
    ne_of_gt (thm_rTowerHeight_positive zUpperZero)
  unfold rTowerLogIncidence
  field_simp

/-- **Le décalage exact d'adresse** : `log x_(k+n) - log x_k = n*pi/T`. -/
theorem thm_rTowerLogIncidence_shift (kAddress nShift : ℤ) :
    rTowerLogIncidence zUpperZero (kAddress + nShift) -
        rTowerLogIncidence zUpperZero kAddress =
      (nShift : ℝ) * Real.pi / rTowerHeight zUpperZero := by
  have hHeight : rTowerHeight zUpperZero ≠ 0 :=
    ne_of_gt (thm_rTowerHeight_positive zUpperZero)
  unfold rTowerLogIncidence
  push_cast
  field_simp
  ring

/-- **Le demi-tour** : deux adresses consécutives sont séparées de `pi/T`. -/
theorem thm_rTowerLogIncidence_successor (kAddress : ℤ) :
    rTowerLogIncidence zUpperZero (kAddress + 1) -
        rTowerLogIncidence zUpperZero kAddress =
      Real.pi / rTowerHeight zUpperZero := by
  simpa using thm_rTowerLogIncidence_shift zUpperZero kAddress 1

/-- **L'ordre strict des rayons avec l'adresse.** -/
theorem thm_rTowerLogIncidence_strictOrder
    {kLeftAddress kRightAddress : ℤ} (hOrder : kLeftAddress < kRightAddress) :
    rTowerLogIncidence zUpperZero kLeftAddress <
      rTowerLogIncidence zUpperZero kRightAddress := by
  have hHeight : 0 < rTowerHeight zUpperZero :=
    thm_rTowerHeight_positive zUpperZero
  have hCast : (kLeftAddress : ℝ) < (kRightAddress : ℝ) := by exact_mod_cast hOrder
  unfold rTowerLogIncidence
  rw [div_lt_div_iff_of_pos_right hHeight]
  nlinarith [Real.pi_pos]

theorem thm_rTowerIncidence_positive (kAddress : ℤ) :
    0 < rTowerIncidence zUpperZero kAddress := Real.exp_pos _

/-- **L'ordre strict des incidences avec l'adresse.** -/
theorem thm_rTowerIncidence_strictOrder
    {kLeftAddress kRightAddress : ℤ} (hOrder : kLeftAddress < kRightAddress) :
    rTowerIncidence zUpperZero kLeftAddress <
      rTowerIncidence zUpperZero kRightAddress :=
  Real.exp_lt_exp.mpr (thm_rTowerLogIncidence_strictOrder zUpperZero hOrder)

/-! ## 3. L'état de Tour conserve exactement son membre source -/

/-- **L'état de Tour du membre.**  Il porte le membre source lui-même. -/
structure TTowerState where
  /-- Le membre unique transporté par cette Tour. -/
  zSourceZero : TUpperNonTrivialZetaZero

/-- L'état de Tour attaché au membre. -/
def tTowerState : TTowerState := ⟨zUpperZero⟩

/-- **RIGIDITE — la Tour ne transporte jamais deux zéros distincts à la fois.**
L'état rend exactement le membre reçu. -/
theorem thm_tTowerState_sourceZero :
    (tTowerState zUpperZero).zSourceZero = zUpperZero := rfl

/-- **RIGIDITE, forme contrapposée.**  Deux Tours de même source sont la Tour du
même membre : la source n'est jamais perdue en aval. -/
theorem thm_tTowerState_injective
    {zLeftZero zRightZero : TUpperNonTrivialZetaZero}
    (hSameState : tTowerState zLeftZero = tTowerState zRightZero) :
    zLeftZero = zRightZero :=
  congrArg TTowerState.zSourceZero hSameState

/-- **Toutes les coordonnées propres sont fonctions du seul membre.**  Aucune
n'est recalculée ni approchée en aval. -/
theorem thm_towerCoordinates_are_functions_of_member
    {zLeftZero zRightZero : TUpperNonTrivialZetaZero}
    (hSameMember : zLeftZero = zRightZero) :
    rTowerPhase zLeftZero = rTowerPhase zRightZero ∧
      rTowerDensity zLeftZero = rTowerDensity zRightZero ∧
        ∀ kAddress : ℤ,
          rTowerIncidence zLeftZero kAddress =
            rTowerIncidence zRightZero kAddress :=
  ⟨congrArg rTowerPhase hSameMember, congrArg rTowerDensity hSameMember,
    fun kAddress => congrArg (fun z => rTowerIncidence z kAddress) hSameMember⟩

end RHV3Lean
