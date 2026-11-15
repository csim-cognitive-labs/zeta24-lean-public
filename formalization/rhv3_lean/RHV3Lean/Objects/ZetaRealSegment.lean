/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TrueZero
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# RHV3Lean — l'entrée analytique orthogonale : aucun vrai zéro n'est réel

    TRACE_ID              : RHV3-REAL-SEGMENT
    SEMANTIC_OBJECT       : entrée analytique orthogonale de l'universalisation
    SEMANTIC_STATEMENT    : un vrai zéro non trivial n'est jamais posé sur l'axe
                            réel ; il possède donc toujours une hauteur non
                            nulle, et par conséquent une branche supérieure.
    MATHEMATICAL_STATEMENT: zêta ne s'annule en aucun point réel du segment
                            ouvert (0,1) ; en conséquence tout vrai zéro non
                            trivial vérifie Im rho != 0.
    MATHEMATICAL_PARENT   : O1 — le vrai zéro.
    PROOF_STRATEGY        : en un zéro réel du segment, `Gammaℝ` ne s'annule pas,
                            donc la fonction complétée s'annule ; l'équation
                            `Λ = Λ₀ - 1/s - 1/(1-s)` force alors
                            `Λ₀(x) = 1/x + 1/(1-x) >= 4` ; or la représentation
                            de Mellin de `Λ₀` se majore explicitement par
                            `2 + 4/e < 4` grâce à la décroissance du noyau thêta.
    REQUIRED_LEMMAS       : HurwitzZeta.hasSum_nat_cosKernel₀,
                            HurwitzZeta.evenKernel_functional_equation,
                            WeakFEPair.isStrongFEPair_toStrongFEPair,
                            completedRiemannZeta_eq, Gammaℝ_ne_zero_of_re_pos
    WHY_EACH_LEMMA_EXISTS : les deux premiers donnent la somme explicite et la
                            réflexion du noyau, donc sa décroissance ; le
                            troisième donne l'intégrabilité de l'intégrande de
                            Mellin ; les deux derniers relient zêta à la
                            fonction complétée sans hypothèse.
    LEAN_DEFINITION       : PNoRealZetaZeroInOpenUnitSegment
    LEAN_THEOREM          : thm_noRealZetaZeroInOpenUnitSegment,
                            thm_zeroHeight_ne_zero
    SAME_MEMBER_CHECK     : ce module ne construit aucun membre ; il ne fait que
                            constater une propriété du support d'un membre déjà
                            donné.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre ici.
    FORBIDDEN_PREMISES    : l'hypothèse de Riemann ou sa négation ; toute
                            hypothèse sur la position radiale ; tout axiome.
    NEXT_CONSUMER         : le représentant supérieur, puis l'universalisation.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Ce module est ANALYTIQUEMENT ORTHOGONAL au cœur sémantique : il ne dit rien de
la position radiale d'un vrai zéro.  Il est ici parce que la branche supérieure
n'est pas exhaustive sans lui, et que le maître interdit de supposer ce qui peut
être démontré.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

open Real HurwitzZeta MeasureTheory Set Complex

/-! ## 1. La décroissance explicite du noyau thêta -/

private theorem thm_exp_neg_pi_lt_half : Real.exp (-Real.pi) < 1 / 2 := by
  have hPiGtOne : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hStep : Real.exp (-Real.pi) < Real.exp (-1) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hInverse : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have hTwoLt : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have hHalf : (Real.exp 1)⁻¹ < 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hTwoLt
  linarith [hStep, hInverse ▸ hHalf]

private theorem thm_hasSum_evenKernel_zero_sub_one {rTime : ℝ} (hPositive : 0 < rTime) :
    HasSum (fun nIndex : ℕ => 2 * Real.exp (-Real.pi * ((nIndex : ℝ) + 1) ^ 2 * rTime))
      (evenKernel 0 rTime - 1) := by
  have hSum := HurwitzZeta.hasSum_nat_cosKernel₀ (0 : ℝ) hPositive
  have hEven : evenKernel (0 : UnitAddCircle) rTime = cosKernel (0 : UnitAddCircle) rTime := by
    rw [evenKernel_eq_cosKernel_of_zero]
  rw [hEven]
  have hZero : ((0 : ℝ) : UnitAddCircle) = (0 : UnitAddCircle) := by simp
  rw [hZero] at hSum
  refine hSum.congr_fun fun nIndex => ?_
  simp

private theorem thm_evenKernel_zero_sub_one_nonneg {rTime : ℝ} (hPositive : 0 < rTime) :
    0 ≤ evenKernel 0 rTime - 1 := by
  refine (thm_hasSum_evenKernel_zero_sub_one hPositive).nonneg fun nIndex => ?_
  positivity

private theorem thm_evenKernel_zero_sub_one_le {rTime : ℝ} (hOneLe : 1 ≤ rTime) :
    evenKernel 0 rTime - 1 ≤ 4 * Real.exp (-Real.pi * rTime) := by
  have hPositive : (0 : ℝ) < rTime := lt_of_lt_of_le zero_lt_one hOneLe
  have hPi : (0 : ℝ) < Real.pi := Real.pi_pos
  set rRatio : ℝ := Real.exp (-Real.pi * rTime) with hRatio
  have hRatioPositive : 0 < rRatio := Real.exp_pos _
  have hRatioHalf : rRatio < 1 / 2 := by
    have hMono : Real.exp (-Real.pi * rTime) ≤ Real.exp (-Real.pi) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    exact lt_of_le_of_lt hMono thm_exp_neg_pi_lt_half
  have hRatioLtOne : rRatio < 1 := by linarith
  have hGeometric :
      HasSum (fun nIndex : ℕ => 2 * rRatio * rRatio ^ nIndex) (2 * rRatio * (1 - rRatio)⁻¹) :=
    (hasSum_geometric_of_lt_one hRatioPositive.le hRatioLtOne).mul_left (2 * rRatio)
  have hDominated : evenKernel 0 rTime - 1 ≤ 2 * rRatio * (1 - rRatio)⁻¹ := by
    refine hasSum_le (fun nIndex => ?_)
      (thm_hasSum_evenKernel_zero_sub_one hPositive) hGeometric
    have hPower :
        2 * rRatio * rRatio ^ nIndex =
          2 * Real.exp (-Real.pi * ((nIndex : ℝ) + 1) * rTime) := by
      rw [hRatio, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      ring_nf
    rw [hPower]
    have hSquare :
        -Real.pi * ((nIndex : ℝ) + 1) ^ 2 * rTime ≤
          -Real.pi * ((nIndex : ℝ) + 1) * rTime := by
      have hNonneg : (0 : ℝ) ≤ (nIndex : ℝ) := Nat.cast_nonneg nIndex
      have hLe : ((nIndex : ℝ) + 1) ≤ ((nIndex : ℝ) + 1) ^ 2 := by nlinarith
      have hProduct :
          0 ≤ (Real.pi * rTime) * (((nIndex : ℝ) + 1) ^ 2 - ((nIndex : ℝ) + 1)) :=
        mul_nonneg (mul_pos hPi hPositive).le (by linarith)
      nlinarith [hProduct]
    have := Real.exp_le_exp.mpr hSquare
    linarith
  have hInverse : (1 - rRatio)⁻¹ < 2 := by
    have hPositiveGap : 0 < 1 - rRatio := by linarith
    rw [inv_lt_comm₀ hPositiveGap (by norm_num)]
    linarith
  nlinarith [hRatioPositive, hDominated, hInverse]

/-! ## 2. Le noyau modifié de la paire fonctionnelle -/

private theorem thm_fModif_of_one_lt {rTime : ℝ} (hOneLt : 1 < rTime) :
    (hurwitzEvenFEPair 0).f_modif rTime = ((evenKernel 0 rTime - 1 : ℝ) : ℂ) := by
  unfold WeakFEPair.f_modif
  simp only [hurwitzEvenFEPair]
  rw [Pi.add_apply, Set.indicator_of_mem (mem_Ioi.mpr hOneLt),
    Set.indicator_of_notMem (by simp; intro _; linarith)]
  simp

private theorem thm_fModif_of_lt_one {rTime : ℝ} (hPositive : 0 < rTime)
    (hLtOne : rTime < 1) :
    (hurwitzEvenFEPair 0).f_modif rTime =
      ((rTime ^ (-(1 / 2) : ℝ) * (evenKernel 0 (1 / rTime) - 1) : ℝ) : ℂ) := by
  unfold WeakFEPair.f_modif
  simp only [hurwitzEvenFEPair]
  rw [Pi.add_apply, Set.indicator_of_notMem (by simp; linarith),
    Set.indicator_of_mem (mem_Ioo.mpr ⟨hPositive, hLtOne⟩)]
  have hReflection :
      evenKernel 0 rTime = rTime ^ (-(1 / 2) : ℝ) * evenKernel 0 (1 / rTime) := by
    rw [evenKernel_functional_equation 0 rTime, ← evenKernel_eq_cosKernel_of_zero,
      Real.rpow_neg hPositive.le]
    ring
  simp only [Function.comp_apply, one_mul, smul_eq_mul, mul_one, zero_add]
  rw [← Complex.ofReal_sub]
  norm_cast
  rw [hReflection]
  ring

private theorem thm_norm_fModif_of_one_lt {rTime : ℝ} (hOneLt : 1 < rTime) :
    ‖(hurwitzEvenFEPair 0).f_modif rTime‖ ≤ 4 * Real.exp (-Real.pi * rTime) := by
  rw [thm_fModif_of_one_lt hOneLt, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (thm_evenKernel_zero_sub_one_nonneg (by linarith))]
  exact thm_evenKernel_zero_sub_one_le hOneLt.le

private theorem thm_norm_fModif_of_lt_one {rTime : ℝ} (hPositive : 0 < rTime)
    (hLtOne : rTime < 1) :
    ‖(hurwitzEvenFEPair 0).f_modif rTime‖ ≤
      4 * rTime ^ (-(1 / 2) : ℝ) * Real.exp (-Real.pi * (1 / rTime)) := by
  have hInversePositive : (0 : ℝ) < 1 / rTime := by positivity
  have hInverseOneLe : (1 : ℝ) ≤ 1 / rTime := by
    rw [le_div_iff₀ hPositive]; linarith
  have hNonneg : 0 ≤ evenKernel 0 (1 / rTime) - 1 :=
    thm_evenKernel_zero_sub_one_nonneg hInversePositive
  have hPower : (0 : ℝ) < rTime ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hPositive _
  rw [thm_fModif_of_lt_one hPositive hLtOne, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have := thm_evenKernel_zero_sub_one_le hInverseOneLe
  nlinarith [hPower, hNonneg, this]

/-! ## 3. La majoration de l'intégrande de Mellin -/

private theorem thm_exp_neg_le_four_div_sq {rArg : ℝ} (hPositive : 0 < rArg) :
    Real.exp (-rArg) ≤ 4 / rArg ^ 2 := by
  have hSquarePositive : (0 : ℝ) < rArg ^ 2 := by positivity
  have hLinear : rArg / 2 + 1 ≤ Real.exp (rArg / 2) := Real.add_one_le_exp _
  have hSquare : (Real.exp (rArg / 2)) ^ 2 = Real.exp rArg := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hLower : rArg ^ 2 / 4 ≤ Real.exp rArg := by
    rw [← hSquare]
    nlinarith [Real.exp_pos (rArg / 2), hLinear]
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos rArg) hSquarePositive]
  linarith

private theorem thm_fModif_one : (hurwitzEvenFEPair 0).f_modif 1 = 0 := by
  unfold WeakFEPair.f_modif
  simp only [hurwitzEvenFEPair]
  rw [Pi.add_apply, Set.indicator_of_notMem (by simp),
    Set.indicator_of_notMem (by simp)]
  simp

private theorem thm_norm_mellin_integrand {rTime : ℝ} (hPositive : 0 < rTime) (cArg : ℂ) :
    ‖(rTime : ℂ) ^ (cArg - 1) • (hurwitzEvenFEPair 0).f_modif rTime‖ =
      rTime ^ (cArg.re - 1) * ‖(hurwitzEvenFEPair 0).f_modif rTime‖ := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hPositive]
  simp

private theorem thm_mellin_integrand_le_of_mem_Ioc {rPoint rTime : ℝ}
    (hPointPositive : 0 < rPoint) (hPointLtOne : rPoint < 1)
    (hTimePositive : 0 < rTime) (hTimeLeOne : rTime ≤ 1) :
    ‖(rTime : ℂ) ^ ((((rPoint / 2 : ℝ) : ℂ)) - 1) •
        (hurwitzEvenFEPair 0).f_modif rTime‖ ≤ 2 := by
  have hPiGtThree : (3 : ℝ) < Real.pi := Real.pi_gt_three
  rcases eq_or_lt_of_le hTimeLeOne with rfl | hTimeLtOne
  · rw [thm_fModif_one]; simp
  · rw [thm_norm_mellin_integrand hTimePositive]
    simp only [Complex.ofReal_re]
    have hPower : (0 : ℝ) < rTime ^ (rPoint / 2 - 1) := Real.rpow_pos_of_pos hTimePositive _
    have hKernel := thm_norm_fModif_of_lt_one hTimePositive hTimeLtOne
    have hArgPositive : (0 : ℝ) < Real.pi / rTime := by positivity
    have hExp : Real.exp (-Real.pi * (1 / rTime)) ≤ 4 * rTime ^ 2 / Real.pi ^ 2 := by
      have hBound := thm_exp_neg_le_four_div_sq hArgPositive
      have hRewrite : -Real.pi * (1 / rTime) = -(Real.pi / rTime) := by ring
      rw [hRewrite]
      refine le_trans hBound (le_of_eq ?_)
      field_simp
    have hSquareCast : rTime ^ (2 : ℝ) = rTime ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hCollect :
        rTime ^ (rPoint / 2 - 1) * rTime ^ (-(1 / 2) : ℝ) * rTime ^ (2 : ℝ) =
          rTime ^ (rPoint / 2 + 1 / 2) := by
      rw [← Real.rpow_add hTimePositive, ← Real.rpow_add hTimePositive]; ring_nf
    have hLeOne : rTime ^ (rPoint / 2 + 1 / 2) ≤ 1 :=
      Real.rpow_le_one hTimePositive.le hTimeLeOne (by linarith)
    have hHalfPower : (0 : ℝ) < rTime ^ (-(1 / 2) : ℝ) :=
      Real.rpow_pos_of_pos hTimePositive _
    have hStep :
        rTime ^ (rPoint / 2 - 1) * ‖(hurwitzEvenFEPair 0).f_modif rTime‖ ≤
          rTime ^ (rPoint / 2 - 1) *
            (4 * rTime ^ (-(1 / 2) : ℝ) * (4 * rTime ^ 2 / Real.pi ^ 2)) := by
      refine mul_le_mul_of_nonneg_left (le_trans hKernel ?_) hPower.le
      have hCoefficient : (0 : ℝ) ≤ 4 * rTime ^ (-(1 / 2) : ℝ) := by positivity
      nlinarith [hExp, hHalfPower]
    have hIdentity :
        rTime ^ (rPoint / 2 - 1) *
            (4 * rTime ^ (-(1 / 2) : ℝ) * (4 * rTime ^ 2 / Real.pi ^ 2)) =
          (16 / Real.pi ^ 2) * (rTime ^ (rPoint / 2 + 1 / 2)) := by
      rw [← hCollect, ← hSquareCast]; field_simp; ring
    rw [hIdentity] at hStep
    have hCoefficientLe : (16 : ℝ) / Real.pi ^ 2 ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hPiGtThree]
    nlinarith [hStep, hLeOne, hCoefficientLe,
      Real.rpow_pos_of_pos hTimePositive (rPoint / 2 + 1 / 2)]

private theorem thm_mellin_integrand_le_of_mem_Ioi {rPoint rTime : ℝ}
    (hPointPositive : 0 < rPoint) (hPointLtOne : rPoint < 1) (hTimeGtOne : 1 < rTime) :
    ‖(rTime : ℂ) ^ ((((rPoint / 2 : ℝ) : ℂ)) - 1) •
        (hurwitzEvenFEPair 0).f_modif rTime‖ ≤ 4 * Real.exp (-rTime) := by
  have hTimePositive : (0 : ℝ) < rTime := lt_trans zero_lt_one hTimeGtOne
  have hPiGtThree : (3 : ℝ) < Real.pi := Real.pi_gt_three
  rw [thm_norm_mellin_integrand hTimePositive]
  simp only [Complex.ofReal_re]
  have hPowerLe : rTime ^ (rPoint / 2 - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hTimeGtOne.le (by linarith)
  have hPowerPositive : (0 : ℝ) < rTime ^ (rPoint / 2 - 1) :=
    Real.rpow_pos_of_pos hTimePositive _
  have hKernel := thm_norm_fModif_of_one_lt hTimeGtOne
  have hExp : Real.exp (-Real.pi * rTime) ≤ Real.exp (-rTime) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hNonneg : 0 ≤ ‖(hurwitzEvenFEPair 0).f_modif rTime‖ := norm_nonneg _
  nlinarith [hKernel, hExp, hPowerLe, hPowerPositive, hNonneg, Real.exp_pos (-rTime)]

/-! ## 4. La borne finie sur la fonction complétée entière -/

private theorem thm_norm_completedRiemannZeta₀_lt_four {rPoint : ℝ}
    (hPositive : 0 < rPoint) (hLtOne : rPoint < 1) :
    ‖completedRiemannZeta₀ (rPoint : ℂ)‖ < 4 := by
  set cArg : ℂ := (((rPoint / 2 : ℝ)) : ℂ) with hArg
  set fnIntegrand : ℝ → ℂ :=
    fun rTime => (rTime : ℂ) ^ (cArg - 1) • (hurwitzEvenFEPair 0).f_modif rTime with hIntegrand
  have hIntegrable : IntegrableOn fnIntegrand (Set.Ioi (0 : ℝ)) :=
    ((hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin cArg).1
  have hNormIntegrable : IntegrableOn (fun rTime => ‖fnIntegrand rTime‖) (Set.Ioi (0 : ℝ)) :=
    hIntegrable.norm
  have hSplit : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  have hDisjoint : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro rTime hLeft hRight
    simp only [Set.mem_Ioc, Set.mem_Ioi] at hLeft hRight
    linarith [hLeft.2]
  have hLowerIntegrable :
      IntegrableOn (fun rTime => ‖fnIntegrand rTime‖) (Set.Ioc (0 : ℝ) 1) :=
    hNormIntegrable.mono_set (by rw [← hSplit]; exact Set.subset_union_left)
  have hUpperIntegrable :
      IntegrableOn (fun rTime => ‖fnIntegrand rTime‖) (Set.Ioi (1 : ℝ)) :=
    hNormIntegrable.mono_set (by rw [← hSplit]; exact Set.subset_union_right)
  have hDecompose :
      (∫ rTime in Set.Ioi (0 : ℝ), ‖fnIntegrand rTime‖) =
        (∫ rTime in Set.Ioc (0 : ℝ) 1, ‖fnIntegrand rTime‖) +
          ∫ rTime in Set.Ioi (1 : ℝ), ‖fnIntegrand rTime‖ := by
    rw [← hSplit, MeasureTheory.setIntegral_union hDisjoint measurableSet_Ioi
      hLowerIntegrable hUpperIntegrable]
  have hConstIntegrable : IntegrableOn (fun _ : ℝ => (2 : ℝ)) (Set.Ioc (0 : ℝ) 1) :=
    integrableOn_const (by simp)
  have hLowerBound : (∫ rTime in Set.Ioc (0 : ℝ) 1, ‖fnIntegrand rTime‖) ≤ 2 := by
    have hMono :
        (∫ rTime in Set.Ioc (0 : ℝ) 1, ‖fnIntegrand rTime‖) ≤
          ∫ _rTime in Set.Ioc (0 : ℝ) 1, (2 : ℝ) := by
      refine MeasureTheory.setIntegral_mono_on hLowerIntegrable hConstIntegrable
        measurableSet_Ioc fun rTime hMember => ?_
      exact thm_mellin_integrand_le_of_mem_Ioc hPositive hLtOne hMember.1 hMember.2
    have hValue : (∫ _rTime in Set.Ioc (0 : ℝ) 1, (2 : ℝ)) = 2 := by
      rw [MeasureTheory.setIntegral_const]; simp
    linarith [hMono, hValue.le, hValue.ge]
  have hExpIntegrable :
      IntegrableOn (fun rTime : ℝ => 4 * Real.exp (-rTime)) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_exp_neg_Ioi 1).const_mul 4
  have hUpperBound :
      (∫ rTime in Set.Ioi (1 : ℝ), ‖fnIntegrand rTime‖) ≤ 4 * Real.exp (-1) := by
    have hMono :
        (∫ rTime in Set.Ioi (1 : ℝ), ‖fnIntegrand rTime‖) ≤
          ∫ rTime in Set.Ioi (1 : ℝ), 4 * Real.exp (-rTime) := by
      refine MeasureTheory.setIntegral_mono_on hUpperIntegrable hExpIntegrable
        measurableSet_Ioi fun rTime hMember => ?_
      exact thm_mellin_integrand_le_of_mem_Ioi hPositive hLtOne hMember
    have hValue : (∫ rTime in Set.Ioi (1 : ℝ), 4 * Real.exp (-rTime)) = 4 * Real.exp (-1) := by
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]
    linarith [hMono, hValue.le, hValue.ge]
  have hExpOne : Real.exp (-1) < 1 / 2 := by
    have hTwoLt : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hTwoLt
  have hMellinNorm :
      ‖(hurwitzEvenFEPair 0).Λ₀ cArg‖ ≤ ∫ rTime in Set.Ioi (0 : ℝ), ‖fnIntegrand rTime‖ := by
    change ‖mellin (hurwitzEvenFEPair 0).f_modif cArg‖ ≤ _
    exact MeasureTheory.norm_integral_le_integral_norm _
  have hLambdaBound : ‖(hurwitzEvenFEPair 0).Λ₀ cArg‖ < 4 := by
    rw [hDecompose] at hMellinNorm
    linarith [hLowerBound, hUpperBound, hExpOne]
  have hCompleted :
      completedRiemannZeta₀ (rPoint : ℂ) = ((hurwitzEvenFEPair 0).Λ₀ cArg) / 2 := by
    change ((hurwitzEvenFEPair 0).Λ₀ (((rPoint : ℂ)) / 2)) / 2 = _
    congr 2
    rw [hArg]
    push_cast
    ring
  rw [hCompleted, norm_div]
  simp only [Complex.norm_ofNat]
  linarith [hLambdaBound, norm_nonneg ((hurwitzEvenFEPair 0).Λ₀ cArg)]

/-! ## 5. Le théorème orthogonal -/

/-- **Aucun zéro de zêta n'est réel dans le segment ouvert `(0,1)`.** -/
def PNoRealZetaZeroInOpenUnitSegment : Prop :=
  ∀ cPoint : ℂ, riemannZeta cPoint = 0 → 0 < cPoint.re → cPoint.re < 1 → cPoint.im ≠ 0

private theorem thm_four_le_reciprocal_sum {rPoint : ℝ}
    (hPositive : 0 < rPoint) (hLtOne : rPoint < 1) :
    4 ≤ 1 / rPoint + 1 / (1 - rPoint) := by
  have hComplement : 0 < 1 - rPoint := by linarith
  rw [div_add_div _ _ (ne_of_gt hPositive) (ne_of_gt hComplement),
    le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * rPoint - 1)]

/-- **THEOREME — zêta n'a aucun zéro réel dans le segment ouvert `(0,1)`.**

En un tel zéro, `Gammaℝ` ne s'annule pas, donc la fonction complétée s'annule,
donc `Λ₀(x) = 1/x + 1/(1-x) >= 4` ; la borne de Mellin donne `< 4`. -/
theorem thm_noRealZetaZeroInOpenUnitSegment : PNoRealZetaZeroInOpenUnitSegment := by
  intro cPoint hZero hPositive hLtOne hImZero
  have hReal : cPoint = ((cPoint.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hImZero]
  set rPoint : ℝ := cPoint.re with hPoint
  have hPointPositive : 0 < rPoint := hPositive
  have hPointLtOne : rPoint < 1 := hLtOne
  have hNeZero : cPoint ≠ 0 := by
    intro hContradiction
    have hZeroRe : rPoint = 0 := by rw [hPoint, hContradiction]; simp
    linarith
  have hGamma : Gammaℝ cPoint ≠ 0 := Gammaℝ_ne_zero_of_re_pos hPositive
  have hQuotient : completedRiemannZeta cPoint / Gammaℝ cPoint = 0 := by
    rw [← riemannZeta_def_of_ne_zero hNeZero]; exact hZero
  have hCompletedZero : completedRiemannZeta cPoint = 0 := by
    rcases div_eq_zero_iff.mp hQuotient with hNumerator | hDenominator
    · exact hNumerator
    · exact absurd hDenominator hGamma
  have hEntire : completedRiemannZeta₀ cPoint = 1 / cPoint + 1 / (1 - cPoint) := by
    have hEquation := completedRiemannZeta_eq cPoint
    rw [hCompletedZero] at hEquation
    linear_combination -hEquation
  have hRealForm :
      (1 : ℂ) / cPoint + 1 / (1 - cPoint) =
        (((1 / rPoint + 1 / (1 - rPoint) : ℝ)) : ℂ) := by
    rw [hReal]; push_cast; ring
  rw [hRealForm] at hEntire
  have hNorm : ‖completedRiemannZeta₀ cPoint‖ = |1 / rPoint + 1 / (1 - rPoint)| := by
    rw [hEntire, Complex.norm_real, Real.norm_eq_abs]
  have hFourLe : (4 : ℝ) ≤ |1 / rPoint + 1 / (1 - rPoint)| :=
    le_trans (thm_four_le_reciprocal_sum hPointPositive hPointLtOne) (le_abs_self _)
  have hLtFour : ‖completedRiemannZeta₀ cPoint‖ < 4 := by
    rw [hReal]
    exact thm_norm_completedRiemannZeta₀_lt_four hPointPositive hPointLtOne
  rw [hNorm] at hLtFour
  linarith

/-- **La hauteur d'un vrai zéro n'est jamais nulle.**

C'est ce qui rend la branche supérieure EXHAUSTIVE une fois la conjugaison
disponible : aucun vrai zéro ne reste hors des deux branches. -/
theorem thm_zeroHeight_ne_zero (zZero : TNonTrivialZetaZero) :
    rZeroHeight zZero ≠ 0 :=
  thm_noRealZetaZeroInOpenUnitSegment (cZeroSupport zZero)
    (thm_zeroProvenance_zeta zZero)
    (thm_zeroRadialPosition_positive zZero)
    (thm_zeroRadialPosition_lt_one zZero)

end RHV3Lean
