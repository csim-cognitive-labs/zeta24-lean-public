/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.ZeroGapGrammar
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# RHV3Lean — S1, le miroir fonctionnel

    TRACE_ID              : RHV3-MIRROR
    SEMANTIC_OBJECT       : S1 — miroir analytique du vrai zéro
    SEMANTIC_STATEMENT    : un vrai zéro hors ligne possède, par symétrie, un
                            miroir distinct situé exactement à la même hauteur.
    MATHEMATICAL_STATEMENT: si zeta(rho) = 0 avec rho = beta + iT dans la bande
                            ouverte, alors zeta(1 - conj rho) = 0, et
                            1 - conj rho = (1 - beta) + iT : même hauteur,
                            position radiale réfléchie ; le miroir est distinct
                            de rho exactement lorsque beta != 1/2.
    MATHEMATICAL_PARENT   : O1 — le vrai zéro ; O7 — la fibre de hauteur.
    PROOF_STRATEGY        : la symétrie de conjugaison de zêta annule zêta au
                            conjugué ; l'équation fonctionnelle, applicable
                            parce que le conjugué n'est ni le pôle ni un entier
                            négatif, transporte cette annulation en
                            1 - conj rho ; les deux coordonnées se lisent
                            directement.
    REQUIRED_LEMMAS       : riemannZeta_conj, riemannZeta_one_sub
    WHY_EACH_LEMMA_EXISTS : le premier donne l'annulation au conjugué ; le
                            second la transporte par l'équation fonctionnelle,
                            sans jamais supposer quoi que ce soit sur la
                            position radiale.
    LEAN_DEFINITION       : cMirrorSupport, PIsOffCriticalLine, zMirrorZero,
                            zUpperMirrorZero
    LEAN_THEOREM          : thm_mirrorSupport_zetaVanishes,
                            thm_mirror_sameHeight,
                            thm_mirror_radialPosition,
                            thm_offCriticalLine_mirror_distinct,
                            thm_offCriticalLineUpper_twoDistinctSameFiberMembers
    SAME_MEMBER_CHECK     : le miroir est un vrai zéro à part entière, avec ses
                            cinq attributs ; il n'est jamais une copie du membre
                            d'origine ni un point synthétique.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre ici.
    FORBIDDEN_PREMISES    : toute hypothèse sur la position radiale du membre ;
                            toute utilisation de l'hypothèse de Riemann ou de sa
                            négation ; tout point synthétique.
    NEXT_CONSUMER         : la contradiction terminale, qui a besoin d'un vrai
                            passage consécutif de gap nul.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

open Complex

/-! ## 1. Le support du miroir -/

/-- **Le support du miroir fonctionnel** : `1 - conj rho`. -/
def cMirrorSupport (zZero : TNonTrivialZetaZero) : ℂ :=
  1 - (starRingEnd ℂ) (cZeroSupport zZero)

@[simp]
theorem thm_mirrorSupport_re (zZero : TNonTrivialZetaZero) :
    (cMirrorSupport zZero).re = 1 - rZeroRadialPosition zZero := by
  simp [cMirrorSupport, rZeroRadialPosition]

@[simp]
theorem thm_mirrorSupport_im (zZero : TNonTrivialZetaZero) :
    (cMirrorSupport zZero).im = rZeroHeight zZero := by
  simp [cMirrorSupport, rZeroHeight]

/-- **Zêta s'annule au support du miroir.**

La conjugaison annule zêta au conjugué du membre ; l'équation fonctionnelle,
applicable parce que ce conjugué n'est ni le pôle ni un entier négatif,
transporte l'annulation en `1 - conj rho`.  Aucune hypothèse sur la position
radiale n'intervient. -/
theorem thm_mirrorSupport_zetaVanishes (zZero : TNonTrivialZetaZero) :
    riemannZeta (cMirrorSupport zZero) = 0 := by
  have hRadialPos : 0 < rZeroRadialPosition zZero :=
    thm_zeroRadialPosition_positive zZero
  have hRadialLt : rZeroRadialPosition zZero < 1 :=
    thm_zeroRadialPosition_lt_one zZero
  have hConjRe : ((starRingEnd ℂ) (cZeroSupport zZero)).re =
      rZeroRadialPosition zZero := by
    simp [rZeroRadialPosition]
  have hConjZero : riemannZeta ((starRingEnd ℂ) (cZeroSupport zZero)) = 0 := by
    rw [riemannZeta_conj, thm_zeroProvenance_zeta, map_zero]
  have hNotNegInt : ∀ nIndex : ℕ,
      (starRingEnd ℂ) (cZeroSupport zZero) ≠ -(nIndex : ℂ) := by
    intro nIndex hEq
    have hRe := congrArg Complex.re hEq
    rw [hConjRe] at hRe
    simp only [Complex.neg_re, Complex.natCast_re] at hRe
    have hNonneg : (0 : ℝ) ≤ (nIndex : ℝ) := Nat.cast_nonneg nIndex
    linarith
  have hNotPole : (starRingEnd ℂ) (cZeroSupport zZero) ≠ 1 := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    rw [hConjRe, Complex.one_re] at hRe
    linarith
  rw [cMirrorSupport, riemannZeta_one_sub hNotNegInt hNotPole, hConjZero,
    mul_zero]

/-- **Le miroir est un vrai zéro à part entière.** -/
noncomputable def zMirrorZero (zZero : TNonTrivialZetaZero) :
    TNonTrivialZetaZero :=
  ⟨cMirrorSupport zZero, thm_mirrorSupport_zetaVanishes zZero, by
      simpa using sub_pos.mpr (thm_zeroRadialPosition_lt_one zZero), by
      simpa using thm_zeroRadialPosition_positive zZero⟩

/-! ## 2. Les deux coordonnées du miroir -/

/-- **Le miroir est exactement à la MÊME HAUTEUR.** -/
@[simp]
theorem thm_mirror_sameHeight (zZero : TNonTrivialZetaZero) :
    rZeroHeight (zMirrorZero zZero) = rZeroHeight zZero :=
  thm_mirrorSupport_im zZero

/-- **La position radiale du miroir est réfléchie.** -/
@[simp]
theorem thm_mirror_radialPosition (zZero : TNonTrivialZetaZero) :
    rZeroRadialPosition (zMirrorZero zZero) = 1 - rZeroRadialPosition zZero :=
  thm_mirrorSupport_re zZero

/-- Le miroir d'un membre de la branche supérieure est encore de la branche
supérieure. -/
noncomputable def zUpperMirrorZero (zUpperZero : TUpperNonTrivialZetaZero) :
    TUpperNonTrivialZetaZero :=
  ⟨zMirrorZero zUpperZero.1, by
      show 0 < rZeroHeight (zMirrorZero zUpperZero.1)
      rw [thm_mirror_sameHeight]
      exact zUpperZero.2⟩

/-! ## 3. Hors ligne critique : le miroir est DISTINCT -/

/-- **Être hors de la ligne critique.** -/
def PIsOffCriticalLine (zZero : TNonTrivialZetaZero) : Prop :=
  rZeroRadialPosition zZero ≠ 1 / 2

/-- **Un vrai zéro hors ligne possède un miroir DISTINCT.**  Les deux positions
radiales `beta` et `1 - beta` coïncideraient exactement sur la ligne
critique. -/
theorem thm_offCriticalLine_mirror_distinct
    {zZero : TNonTrivialZetaZero} (hOff : PIsOffCriticalLine zZero) :
    zMirrorZero zZero ≠ zZero := by
  intro hSame
  have hRadial :
      rZeroRadialPosition (zMirrorZero zZero) = rZeroRadialPosition zZero :=
    congrArg rZeroRadialPosition hSame
  rw [thm_mirror_radialPosition] at hRadial
  exact hOff (by linarith)

/-- **Un vrai zéro hors ligne fournit deux membres DISTINCTS de la MÊME
FIBRE.**

C'est le troisième paragraphe du maître, dans sa première moitié : par symétrie,
le zéro hors ligne possède un miroir distinct à exactement la même hauteur.  Ces
deux membres sont donc comparables par l'ordre membre-sensible, et l'écart de
hauteur du couple qu'ils forment est nul. -/
theorem thm_offCriticalLineUpper_twoDistinctSameFiberMembers
    {zZero : TNonTrivialZetaZero} (hOff : PIsOffCriticalLine zZero) :
    zMirrorZero zZero ≠ zZero ∧
      rZeroHeight (zMirrorZero zZero) = rZeroHeight zZero ∧
        (PZeroMemberPrecedes (zMirrorZero zZero) zZero ∨
          PZeroMemberPrecedes zZero (zMirrorZero zZero)) ∧
        rZeroPairHeightGap (zMirrorZero zZero) zZero = 0 := by
  have hDistinct : zMirrorZero zZero ≠ zZero :=
    thm_offCriticalLine_mirror_distinct hOff
  have hSameHeight :
      rZeroHeight (zMirrorZero zZero) = rZeroHeight zZero :=
    thm_mirror_sameHeight zZero
  obtain ⟨hComparable, hGapZero⟩ :=
    thm_distinctSameFiberMembers_haveNullGap hDistinct hSameHeight
  exact ⟨hDistinct, hSameHeight, hComparable, hGapZero⟩

end RHV3Lean
