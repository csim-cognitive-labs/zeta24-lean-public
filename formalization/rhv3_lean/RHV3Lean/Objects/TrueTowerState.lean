/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.HarmonicTower
import RHV3Lean.Objects.AlgebraicAxis

/-!
# RHV3Lean — la Tour propre par ses deux vrais contacts consécutifs

La représentation active suit `RHV2_STRATEGIE_MATHEMATIQUE.md`, §49, et
`RHV2_STRATEGIE_LEAN.md`, §T. Elle ne contient aucune adresse, aucun nombre
d'étages et aucune recherche de branche.

    TRACE_ID              : RHV3-S3-S4-TRUE-CONSECUTIVE-CONTACTS
    SEMANTIC_OBJECT       : Tour harmonique propre d'un vrai zéro
    SEMANTIC_STATEMENT    : l'état porte une paire de contacts consécutifs
                            déjà produite par le vrai événement de Tour ; les
                            deux lois la décodent mais ne la sélectionnent pas
    MATHEMATICAL_STATEMENT: log C+ - log C- = pi/T et
                            beta * tan (T * log C-) = T
    MATHEMATICAL_PARENT   : O1 vrai zéro ; O3 Tour harmonique ; maître §49
    PROOF_STRATEGY        : inverser la largeur exacte puis la loi tangentielle
                            en utilisant T>0, beta>0 et l'identité du support
    REQUIRED_LEMMAS       : Real.pi_pos, div_eq_iff,
                            thm_zero_identity_of_sameSupport
    WHY_EACH_LEMMA_EXISTS : pi et T non nuls ferment l'inversion de hauteur ;
                            la loi tangentielle rend le dénominateur non nul ;
                            l'identité du support referme le même membre
    LEAN_DEFINITION       : TTrueHarmonicTowerState, rDecodedHeight,
                            rDecodedRadialPosition, terminalCell
    LEAN_THEOREM          : thm_decodedHeight_eq_zeroHeight,
                            thm_decodedRadialPosition_eq_zeroRadialPosition,
                            thm_contacts_decode_same_member,
                            thm_same_true_contacts_same_member
    SAME_MEMBER_CHECK     : thm_contacts_decode_same_member
    SAME_PASSAGE_CHECK    : sans objet à ce niveau
    SAME_MIDDLE_CHECK     : sans objet à ce niveau
    SAME_HISTORY_CHECK    : sans objet à ce niveau
    FORBIDDEN_PREMISES    : premier, rang, comptage, kappa, span, stage,
                            contactIndex, fenêtre ou sélection de branche
    NEXT_CONSUMER         : comptage et T1 sur `terminalCell`
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED
-/

namespace RHV3Lean

/-- L'état propre actif d'une Tour : les deux vrais contacts consécutifs et
leurs deux lois exactes. -/
structure TTrueHarmonicTowerState (z : TUpperNonTrivialZetaZero) where
  contactMinus : ℝ
  contactPlus : ℝ
  contactMinus_pos : 0 < contactMinus
  contactPlus_pos : 0 < contactPlus
  ordered : contactMinus < contactPlus
  consecutive_width :
    Real.log contactPlus - Real.log contactMinus = Real.pi / rZeroHeight z.1
  tangent_law :
    rZeroRadialPosition z.1 *
        Real.tan (rZeroHeight z.1 * Real.log contactMinus) =
      rZeroHeight z.1

namespace TTrueHarmonicTowerState

variable {z : TUpperNonTrivialZetaZero}

/-- La cellule propre est une projection directe des deux contacts de la Tour
du même membre. Aucune coordonnée discrète ni donnée première n'intervient. -/
noncomputable def terminalCell (S : TTrueHarmonicTowerState z) :
    TAlgebraicInterval where
  rLeftEndpoint := S.contactMinus
  rRightEndpoint := S.contactPlus
  hLeftPositive := S.contactMinus_pos
  hOrdered := S.ordered

/-- Les bords de la cellule propre sont définitionnellement les contacts du
même état de Tour. -/
theorem terminalCell_endpoints (S : TTrueHarmonicTowerState z) :
    S.terminalCell.rLeftEndpoint = S.contactMinus ∧
      S.terminalCell.rRightEndpoint = S.contactPlus :=
  ⟨rfl, rfl⟩

/-- Hauteur décodée depuis les seuls contacts consécutifs. -/
noncomputable def rDecodedHeight (S : TTrueHarmonicTowerState z) : ℝ :=
  Real.pi / (Real.log S.contactPlus - Real.log S.contactMinus)

/-- Position radiale décodée depuis les seuls contacts consécutifs. -/
noncomputable def rDecodedRadialPosition (S : TTrueHarmonicTowerState z) : ℝ :=
  S.rDecodedHeight /
    Real.tan (S.rDecodedHeight * Real.log S.contactMinus)

/-- La largeur consécutive `pi/T` inverse réellement la hauteur. -/
theorem thm_decodedHeight_eq_zeroHeight (S : TTrueHarmonicTowerState z) :
    S.rDecodedHeight = rZeroHeight z.1 := by
  have hHeight : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  unfold rDecodedHeight
  rw [S.consecutive_width]
  field_simp

/-- La loi tangentielle inverse réellement la position radiale. -/
theorem thm_decodedRadialPosition_eq_zeroRadialPosition
    (S : TTrueHarmonicTowerState z) :
    S.rDecodedRadialPosition = rZeroRadialPosition z.1 := by
  have hTan :
      Real.tan (rZeroHeight z.1 * Real.log S.contactMinus) ≠ 0 := by
    intro hZero
    have hLaw := S.tangent_law
    rw [hZero, mul_zero] at hLaw
    exact (ne_of_gt z.2) hLaw.symm
  unfold rDecodedRadialPosition
  rw [S.thm_decodedHeight_eq_zeroHeight]
  apply (div_eq_iff hTan).2
  exact S.tangent_law.symm

/-- Les contacts décodent exactement le support complexe du même membre. -/
theorem thm_contacts_decode_same_member (S : TTrueHarmonicTowerState z) :
    Complex.mk S.rDecodedRadialPosition S.rDecodedHeight = cZeroSupport z.1 := by
  apply Complex.ext
  · exact S.thm_decodedRadialPosition_eq_zeroRadialPosition
  · exact S.thm_decodedHeight_eq_zeroHeight

/-- La cellule directe conserve exactement `(beta,T)` du membre source via
ses deux contacts. -/
theorem terminalCell_decodes_source (S : TTrueHarmonicTowerState z) :
    Complex.mk S.rDecodedRadialPosition S.rDecodedHeight = cZeroSupport z.1 :=
  S.thm_contacts_decode_same_member

/-- Une même paire de vrais contacts consécutifs ne peut porter deux membres. -/
theorem thm_same_true_contacts_same_member
    {zLeft zRight : TUpperNonTrivialZetaZero}
    (SLeft : TTrueHarmonicTowerState zLeft)
    (SRight : TTrueHarmonicTowerState zRight)
    (hMinus : SLeft.contactMinus = SRight.contactMinus)
    (hPlus : SLeft.contactPlus = SRight.contactPlus) :
    zLeft = zRight := by
  have hHeight : rZeroHeight zLeft.1 = rZeroHeight zRight.1 := by
    rw [← SLeft.thm_decodedHeight_eq_zeroHeight,
      ← SRight.thm_decodedHeight_eq_zeroHeight]
    unfold rDecodedHeight
    rw [hMinus, hPlus]
  have hDecodedHeight : SLeft.rDecodedHeight = SRight.rDecodedHeight := by
    rw [SLeft.thm_decodedHeight_eq_zeroHeight,
      SRight.thm_decodedHeight_eq_zeroHeight, hHeight]
  have hRadial :
      rZeroRadialPosition zLeft.1 = rZeroRadialPosition zRight.1 := by
    rw [← SLeft.thm_decodedRadialPosition_eq_zeroRadialPosition,
      ← SRight.thm_decodedRadialPosition_eq_zeroRadialPosition]
    unfold rDecodedRadialPosition
    rw [hMinus, hDecodedHeight]
  exact Subtype.ext (thm_zero_identity_of_sameSupport (Complex.ext hRadial hHeight))

end TTrueHarmonicTowerState

/-! ## Diagnostic de branche principale — jamais producteur scientifique

Les deux lois ci-dessus ont une infinité de solutions, obtenues en ajoutant
un multiple entier de `pi` à l'angle du contact inférieur.  La paire ci-dessous
est uniquement la solution d'incidence zéro.  La régression historique Z1--Z4
montre qu'elle n'est pas la paire du vrai événement (`k = 4, 10, 14, 22` dans
la notation diagnostique révoquée).  Elle reste compilée pour contrôler les
identités analytiques, mais ne réalise ni S4 ni le porteur canonique.
-/

/-- Contact d'incidence zéro, contrôle analytique seulement. -/
noncomputable def rPrincipalBranchContactMinus (z : TUpperNonTrivialZetaZero) : ℝ :=
  Real.exp (rTowerPhase z / rTowerHeight z)

/-- Contact suivant l'incidence zéro, contrôle analytique seulement. -/
noncomputable def rPrincipalBranchContactPlus (z : TUpperNonTrivialZetaZero) : ℝ :=
  Real.exp ((rTowerPhase z + Real.pi) / rTowerHeight z)

/-- Habitant de contrôle sur la branche principale ; non canonique. -/
noncomputable def tPrincipalBranchTowerState
    (z : TUpperNonTrivialZetaZero) : TTrueHarmonicTowerState z where
  contactMinus := rPrincipalBranchContactMinus z
  contactPlus := rPrincipalBranchContactPlus z
  contactMinus_pos := Real.exp_pos _
  contactPlus_pos := Real.exp_pos _
  ordered := by
    apply Real.exp_lt_exp.mpr
    rw [div_lt_div_iff_of_pos_right (thm_rTowerHeight_positive z)]
    linarith [Real.pi_pos]
  consecutive_width := by
    unfold rPrincipalBranchContactPlus rPrincipalBranchContactMinus
    rw [Real.log_exp, Real.log_exp]
    have hHeight : rTowerHeight z ≠ 0 := ne_of_gt (thm_rTowerHeight_positive z)
    change (rTowerPhase z + Real.pi) / rTowerHeight z -
        rTowerPhase z / rTowerHeight z = Real.pi / rTowerHeight z
    field_simp
    ring
  tangent_law := by
    unfold rPrincipalBranchContactMinus
    rw [Real.log_exp]
    have hHeight : rTowerHeight z ≠ 0 := ne_of_gt (thm_rTowerHeight_positive z)
    have hAngle :
        rTowerHeight z * (rTowerPhase z / rTowerHeight z) = rTowerPhase z := by
      field_simp
    rw [show rZeroHeight z.1 = rTowerHeight z from rfl,
      show rZeroRadialPosition z.1 = rTowerRadialPosition z from rfl,
      hAngle, rTowerPhase, Real.tan_arctan]
    field_simp [ne_of_gt (thm_rTowerRadialPosition_positive z)]

end RHV3Lean
