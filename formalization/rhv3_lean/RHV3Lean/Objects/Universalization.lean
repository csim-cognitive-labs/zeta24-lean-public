/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TransportOnOperator

/-!
# RHV3Lean — universalisation vers `RiemannHypothesis` de Mathlib

    TRACE_ID              : RHV3-UNIVERSALIZATION
    SEMANTIC_OBJECT       : le passage de la branche supérieure à l'énoncé
                            public de l'hypothèse de Riemann.
    SEMANTIC_STATEMENT    : la centralité lue sur la branche supérieure vaut
                            pour tous les vrais zéros non triviaux, puis pour
                            tous les zéros que l'énoncé public désigne : les
                            zéros triviaux et le pôle sont exclus par l'énoncé
                            lui-même, et tout autre zéro est confiné dans la
                            bande ouverte.
    MATHEMATICAL_STATEMENT: un zéro de zêta de partie réelle au moins un
                            n'existe pas ; un zéro de partie réelle au plus zéro
                            est un entier pair négatif ; donc un zéro non
                            trivial est dans la bande ouverte, et y est un vrai
                            zéro au sens de O1.
    MATHEMATICAL_PARENT   : O1 — le vrai zéro ; le représentant supérieur.
    PROOF_STRATEGY        : `riemannZeta_ne_zero_of_one_le_re` ferme la droite ;
                            l'équation fonctionnelle, appliquée en `1 - s`,
                            ramène un zéro de partie réelle négative à
                            l'annulation d'un cosinus, dont les racines sont
                            exactement les entiers pairs négatifs ; le zéro en
                            zéro est exclu par `riemannZeta_zero`.
    REQUIRED_LEMMAS       : riemannZeta_ne_zero_of_one_le_re, riemannZeta_one_sub,
                            Complex.Gamma_ne_zero, Complex.cos_eq_zero_iff,
                            riemannZeta_zero
    WHY_EACH_LEMMA_EXISTS : le premier ferme le demi-plan droit ; le deuxième
                            transporte l'annulation ; les deux suivants isolent
                            le facteur qui s'annule ; le dernier écarte
                            l'origine.
    LEAN_DEFINITION       : zNonTrivialZeroOfMathlib
    LEAN_THEOREM          : thm_re_lt_one_of_zetaVanishes,
                            thm_trivialIndex_of_zetaVanishes_of_re_nonpos,
                            thm_inOpenStrip_of_mathlibHypotheses,
                            thm_riemannHypothesis_of_allUpperOnCriticalLine
    SAME_MEMBER_CHECK     : `zNonTrivialZeroOfMathlib` a pour support le point
                            donné, littéralement, par `rfl`.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre ici.
    FORBIDDEN_PREMISES    : toute hypothèse de Tour, de premier, de comptage ou
                            de transport dans ce module ; l'hypothèse de Riemann
                            ou sa négation.
    NEXT_CONSUMER         : le verdict terminal.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Ce module ne contient AUCUNE hypothèse scientifique de la route : il est
purement le raccord entre le vocabulaire de O1 et l'énoncé public.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

open Complex

/-! ## 1. Le confinement dans la bande ouverte -/

/-- **Aucun zéro de zêta n'a de partie réelle au moins un.** -/
theorem thm_re_lt_one_of_zetaVanishes {cPoint : ℂ} (hZero : riemannZeta cPoint = 0) :
    cPoint.re < 1 := by
  by_contra hNotLt
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hNotLt) hZero

/-- **Un zéro de partie réelle au plus zéro est un entier pair négatif.** -/
theorem thm_trivialIndex_of_zetaVanishes_of_re_nonpos
    {cPoint : ℂ} (hZero : riemannZeta cPoint = 0) (hNonpos : cPoint.re ≤ 0) :
    ∃ nIndex : ℕ, cPoint = -2 * (nIndex + 1) := by
  have hNotPole : (1 : ℂ) - cPoint ≠ 1 := by
    intro hEq
    have hOrigin : cPoint = 0 := by
      have := congrArg (fun cArg => (1 : ℂ) - cArg) hEq
      simpa using this
    rw [hOrigin, riemannZeta_zero] at hZero
    norm_num at hZero
  have hNotNegInt : ∀ nIndex : ℕ, (1 : ℂ) - cPoint ≠ -nIndex := by
    intro nIndex hEq
    have hRe : ((1 : ℂ) - cPoint).re = 1 - cPoint.re := by simp
    rw [hEq] at hRe
    simp only [Complex.neg_re, Complex.natCast_re] at hRe
    have hCastNonneg : (0 : ℝ) ≤ (nIndex : ℝ) := Nat.cast_nonneg nIndex
    linarith
  have hFunctional := riemannZeta_one_sub hNotNegInt hNotPole
  simp only [sub_sub_cancel] at hFunctional
  have hReflectedNeZero : riemannZeta ((1 : ℂ) - cPoint) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    have hRe : ((1 : ℂ) - cPoint).re = 1 - cPoint.re := by simp
    rw [hRe]
    linarith
  rw [hZero] at hFunctional
  have hProduct :
      2 * (2 * (Real.pi : ℂ)) ^ (-(1 - cPoint)) * Complex.Gamma (1 - cPoint) *
        Complex.cos ((Real.pi : ℂ) * (1 - cPoint) / 2) = 0 := by
    rcases mul_eq_zero.mp hFunctional.symm with hLeft | hRight
    · exact hLeft
    · exact absurd hRight hReflectedNeZero
  have hCpowNeZero : (2 * (Real.pi : ℂ)) ^ (-(1 - cPoint)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨two_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero⟩)]
    exact Complex.exp_ne_zero _
  have hGammaNeZero : Complex.Gamma ((1 : ℂ) - cPoint) ≠ 0 :=
    Complex.Gamma_ne_zero hNotNegInt
  have hCosZero : Complex.cos ((Real.pi : ℂ) * (1 - cPoint) / 2) = 0 := by
    rcases mul_eq_zero.mp hProduct with hLeft | hRight
    · rcases mul_eq_zero.mp hLeft with hInner | hGamma
      · rcases mul_eq_zero.mp hInner with hTwo | hCpow
        · exact absurd hTwo two_ne_zero
        · exact absurd hCpow hCpowNeZero
      · exact absurd hGamma hGammaNeZero
    · exact hRight
  rw [Complex.cos_eq_zero_iff] at hCosZero
  obtain ⟨kIndex, hRoot⟩ := hCosZero
  have hPiNeZero : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hScaled :
      (Real.pi : ℂ) * (1 - cPoint) = (Real.pi : ℂ) * (2 * (kIndex : ℂ) + 1) := by
    linear_combination (2 : ℂ) * hRoot
  have hValue : cPoint = -(2 * (kIndex : ℂ)) := by
    have hCancel := mul_left_cancel₀ hPiNeZero hScaled
    linear_combination -hCancel
  have hRealPart : cPoint.re = -(2 * (kIndex : ℝ)) := by
    rw [hValue]; push_cast; simp
  have hIndexNonneg : 0 ≤ (kIndex : ℝ) := by
    rw [hRealPart] at hNonpos; linarith
  have hIndexNeZero : kIndex ≠ 0 := by
    intro hEq
    rw [hEq] at hValue
    simp only [Int.cast_zero, mul_zero, neg_zero] at hValue
    rw [hValue, riemannZeta_zero] at hZero
    norm_num at hZero
  have hIndexOneLe : 1 ≤ kIndex := by
    rcases lt_trichotomy kIndex 0 with hNegative | hZeroIndex | hPositive
    · exact absurd (by exact_mod_cast hIndexNonneg : (0 : ℤ) ≤ kIndex) (by omega)
    · exact absurd hZeroIndex hIndexNeZero
    · omega
  obtain ⟨nIndex, hShift⟩ : ∃ nIndex : ℕ, kIndex = (nIndex : ℤ) + 1 :=
    ⟨(kIndex - 1).toNat, by omega⟩
  exact ⟨nIndex, by rw [hValue, hShift]; push_cast; ring⟩

/-- **Les hypothèses publiques placent le point strictement dans la bande
ouverte.** -/
theorem thm_inOpenStrip_of_mathlibHypotheses
    {cPoint : ℂ} (hZero : riemannZeta cPoint = 0)
    (hNotTrivial : ¬ ∃ nIndex : ℕ, cPoint = -2 * (nIndex + 1)) :
    0 < cPoint.re ∧ cPoint.re < 1 := by
  refine ⟨?_, thm_re_lt_one_of_zetaVanishes hZero⟩
  by_contra hNotPositive
  exact hNotTrivial
    (thm_trivialIndex_of_zetaVanishes_of_re_nonpos hZero (not_lt.mp hNotPositive))

/-- **Le vrai zéro de O1 attaché à un zéro non trivial de l'énoncé public.** -/
def zNonTrivialZeroOfMathlib
    (cPoint : ℂ) (hZero : riemannZeta cPoint = 0)
    (hNotTrivial : ¬ ∃ nIndex : ℕ, cPoint = -2 * (nIndex + 1)) :
    TNonTrivialZetaZero :=
  ⟨cPoint, hZero, (thm_inOpenStrip_of_mathlibHypotheses hZero hNotTrivial).1,
    (thm_inOpenStrip_of_mathlibHypotheses hZero hNotTrivial).2⟩

@[simp]
theorem thm_zNonTrivialZeroOfMathlib_support
    (cPoint : ℂ) (hZero : riemannZeta cPoint = 0)
    (hNotTrivial : ¬ ∃ nIndex : ℕ, cPoint = -2 * (nIndex + 1)) :
    cZeroSupport (zNonTrivialZeroOfMathlib cPoint hZero hNotTrivial) = cPoint := rfl

/-! ## 2. Le raccord terminal -/

/-- **La centralité de la branche supérieure donne l'énoncé public.**

Aucune hypothèse de Tour, de premier ou de transport n'entre ici : la branche
supérieure est exhaustive grâce au représentant supérieur, et la bande ouverte
est atteinte grâce au confinement. -/
theorem thm_riemannHypothesis_of_allUpperOnCriticalLine
    (hUpper : ∀ zUpperZero : TUpperNonTrivialZetaZero,
      rZeroRadialPosition zUpperZero.1 = 1 / 2) :
    RiemannHypothesis := by
  intro cPoint hZero hNotTrivial _hNotPole
  have hCentral :
      rZeroRadialPosition (zNonTrivialZeroOfMathlib cPoint hZero hNotTrivial) = 1 / 2 :=
    thm_allRadialPositions_of_upperBranch hUpper _
  exact hCentral

end RHV3Lean
