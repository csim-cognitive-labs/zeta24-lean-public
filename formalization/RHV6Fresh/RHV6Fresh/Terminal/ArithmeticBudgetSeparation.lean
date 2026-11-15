/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.AlternatingCellSeries
import RHV6Fresh.Terminal.PairAsymmetryOverPrimes
import RHV6Fresh.Terminal.RawMeetingRemainder

/-!
# RHV6Fresh — Terminal/ArithmeticBudgetSeparation : séparation du budget arithmétique et du fond, somme naturelle contre
somme à signes rectifiés, contribution complexe effective de la paire, pont de Ψ3 aux termes de fibre (E472 phase A, §19.105)
(réponse à l'audit externe du build Ψ, 2026-11-13 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse, aucun
axiome, aucun `sorry`)

Stratégie (règle R-Ψ). Cible : lever les quatre ambiguïtés relevées par l'audit AVANT toute mesure (E472 phase B).
Objet cumulé : les mêmes séries de cellules que Ψ4 (budget alterné, sommes de parts), mais (P1) le budget est SÉPARÉ en une
part lue sur les premiers seuls et une part de fond, bornée à l'échelle `x_N` (donc évanescente à l'échelle de la ligne) ;
(P3) la somme « alternée » d'une Tour est reconnue pour ce qu'elle est : une somme à SIGNES RECTIFIÉS, dont le module est la
somme des modules des parts ; la somme NATURELLE (l'alternance propre de la Tour) est télescopée, bornée par la première,
minorée par un multiple fixe de la première, même classement ligne / miroir ; (P2) la contribution COMPLEXE de la paire (somme,
non somme de normes) est non bornée à l'échelle de la ligne, dans les deux formes, avec le coefficient imposé par la recomposition
quand le miroir est porteur ; (P4) l'asymétrie de Ψ3 est reliée aux termes de fibre de la paire aux abscisses premières (pont
géométrique exact), et il est consigné qu'aucun pont à une obligation arithmétique n'est compilé.
Pourquoi le ponctuel échoue : inchangé (une cellule ne s'annule avec rien). Signature d'un hors-ligne : inchangée (croissance
`e^{Nπ(β−1/2)/T}`), désormais portée par la contribution complexe effective et non par une somme de normes.
Suite dans les deux issues : si tout compile, la phase B mesure le budget arithmétique `arithmeticAlternatingBudget` sur les
premiers réels, quantité qui ne dépend d'aucune recomposition ; sinon, consigner l'énoncé réclamé.

* B1 `arithmeticAlternatingBudget` (ℝ, premiers seuls), `backgroundCellTerm`, `backgroundAlternatingBudget`,
  `alternatingCellTotal_eq_arithmetic_sub_background`, `alternatingCellTotal_independent` (indépendant de la recomposition),
  `norm_backgroundCellTerm_le`, `norm_backgroundAlternatingBudget_le`, `sum_cells_le`,
  `norm_backgroundAlternatingBudget_le_scale` (fond à l'échelle `x_N`), `background_relative_le` (fond / x_N^{3/2} ≤ C / x_N^{1/2}),
  `naturalCellTotal`, `naturalCellTotal_eq_telescope` (le fond du budget NATUREL se réduit aux deux bords), `tower_term_natural`.
* B2 `towerNaturalSum`, `towerNaturalSum_telescope`, `cellFactor_ne_one`, `towerNaturalSum_eq`, `norm_cellFactor`,
  `norm_cellFactor_sub_one`, `norm_towerCellShare_iterate`, `norm_towerAlternatingSum_eq`,
  `norm_towerAlternatingSum_eq_sum_norms` (la somme à signes rectifiés a pour module la somme des modules),
  `norm_towerNaturalSum_le`, `norm_towerNaturalSum_ge`, `relativeNatural`, `relativeNatural_le_relativeAlternating`,
  `relativeNatural_line_le`, `relativeAlternating_le_relativeNatural_mul`, `relativeNatural_unbounded_of_half_lt`.
* B3 `relativeAlternating_le_of_le_half`, `pairAlternatingSum`, `pairComplexRelative`, `pairComplexRelative_ge`,
  `pairComplexRelative_unbounded_of_lt_half`, `pairNaturalSum`, `pairNaturalRelative`, `pairNaturalRelative_ge`,
  `pairNaturalRelative_unbounded_of_lt_half`, `recomposition_pair_alternating`, `recomposition_mirror_pair_unbounded`.
* B4 `norm_integratedKernel_towerPoint`, `norm_towerCellShare_eq`, `towerShareScale`, `norm_towerPoint_mul_pos`,
  `log_norm_towerCellShare`, `pairAsymmetryAt_eq_log_share_ratio`, `cumulativeAsymmetry_eq_sum_log_share_ratio`.
Portée : identités, bornes et équivalences exactes ; rien n'exclut seul un zéro hors ligne.
-/

namespace RHV6Fresh

open Real

/-! ## B1 : budget arithmétique (premiers seuls), budget du fond, séparation -/

noncomputable def arithmeticAlternatingBudget (T x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n *
    demandArea (x * Real.exp (π / T) ^ n) (x * Real.exp (π / T) ^ n * Real.exp (π / T))

noncomputable def backgroundCellTerm (T y : ℝ) : ℂ :=
  ((y * Real.exp (π / T) : ℝ) : ℂ) * residualBackground (y * Real.exp (π / T)) - (y : ℂ) * residualBackground y

noncomputable def backgroundAlternatingBudget (T x : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * backgroundCellTerm T (x * Real.exp (π / T) ^ n)

theorem alternatingCellTotal_eq_arithmetic_sub_background {ι : Type*} (Rec : ArithmeticRecomposition ι) {T x : ℝ}
    (hT : 0 < T) (hx : 1 < x) (N : ℕ) :
    alternatingCellTotal Rec T x N =
      ((arithmeticAlternatingBudget T x N : ℝ) : ℂ) - backgroundAlternatingBudget T x N := by
  rw [alternatingCellTotal_eq_demandAreas Rec hT hx N]
  unfold arithmeticAlternatingBudget backgroundAlternatingBudget backgroundCellTerm
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Le budget alterné ne dépend pas de la recomposition : c'est une quantité des premiers et du fond. -/
theorem alternatingCellTotal_independent {ι ι' : Type*} (Rec : ArithmeticRecomposition ι)
    (Rec' : ArithmeticRecomposition ι') {T x : ℝ} (hT : 0 < T) (hx : 1 < x) (N : ℕ) :
    alternatingCellTotal Rec T x N = alternatingCellTotal Rec' T x N := by
  rw [alternatingCellTotal_eq_arithmetic_sub_background Rec hT hx N,
    alternatingCellTotal_eq_arithmetic_sub_background Rec' hT hx N]

theorem norm_backgroundCellTerm_le {T y : ℝ} (hT : 0 < T) (hy : 1 < y) :
    ‖backgroundCellTerm T y‖ ≤ backgroundConstant * (Real.exp (π / T) + 1) * y := by
  have hye := one_lt_mul_exp_cell hT hy
  have h1 : ‖residualBackground (y * Real.exp (π / T))‖ ≤ backgroundConstant := norm_background_sub_half_le hye
  have h2 : ‖residualBackground y‖ ≤ backgroundConstant := norm_background_sub_half_le hy
  have hy0 : 0 ≤ y := by linarith
  have hye0 : 0 ≤ y * Real.exp (π / T) := mul_nonneg hy0 (Real.exp_pos _).le
  unfold backgroundCellTerm
  calc ‖((y * Real.exp (π / T) : ℝ) : ℂ) * residualBackground (y * Real.exp (π / T)) -
        (y : ℂ) * residualBackground y‖
      ≤ ‖((y * Real.exp (π / T) : ℝ) : ℂ) * residualBackground (y * Real.exp (π / T))‖ +
        ‖(y : ℂ) * residualBackground y‖ := norm_sub_le _ _
    _ = y * Real.exp (π / T) * ‖residualBackground (y * Real.exp (π / T))‖ + y * ‖residualBackground y‖ := by
        rw [norm_mul, norm_mul, Complex.norm_of_nonneg hye0, Complex.norm_of_nonneg hy0]
    _ ≤ y * Real.exp (π / T) * backgroundConstant + y * backgroundConstant :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hye0) (mul_le_mul_of_nonneg_left h2 hy0)
    _ = backgroundConstant * (Real.exp (π / T) + 1) * y := by ring

theorem norm_backgroundAlternatingBudget_le {T x : ℝ} (hT : 0 < T) (hx : 1 < x) (N : ℕ) :
    ‖backgroundAlternatingBudget T x N‖ ≤
      backgroundConstant * (Real.exp (π / T) + 1) * ∑ n ∈ Finset.range N, x * Real.exp (π / T) ^ n := by
  unfold backgroundAlternatingBudget
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact norm_backgroundCellTerm_le hT (one_lt_mul_exp_pow hT hx n)

theorem sum_cells_le {T x : ℝ} (hT : 0 < T) (hx : 0 < x) (N : ℕ) :
    ∑ n ∈ Finset.range N, x * Real.exp (π / T) ^ n ≤ x * Real.exp (π / T) ^ N / (Real.exp (π / T) - 1) := by
  have hE : 1 < Real.exp (π / T) := Real.one_lt_exp_iff.mpr (div_pos Real.pi_pos hT)
  have hE1 : 0 < Real.exp (π / T) - 1 := by linarith
  rw [← Finset.mul_sum, geom_sum_eq hE.ne' N, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hE1.le) hx.le

/-- Le fond du budget alterné est à l'échelle `x_N` (et non `x_N^{3/2}`). -/
theorem norm_backgroundAlternatingBudget_le_scale {T x : ℝ} (hT : 0 < T) (hx : 1 < x) (N : ℕ) :
    ‖backgroundAlternatingBudget T x N‖ ≤
      backgroundConstant * (Real.exp (π / T) + 1) / (Real.exp (π / T) - 1) * (x * Real.exp (π / T) ^ N) := by
  have h := norm_backgroundAlternatingBudget_le hT hx N
  have hs := sum_cells_le hT (by linarith : 0 < x) N
  have hC : 0 ≤ backgroundConstant * (Real.exp (π / T) + 1) :=
    mul_nonneg backgroundConstant_nonneg (by positivity)
  calc ‖backgroundAlternatingBudget T x N‖
      ≤ backgroundConstant * (Real.exp (π / T) + 1) * ∑ n ∈ Finset.range N, x * Real.exp (π / T) ^ n := h
    _ ≤ backgroundConstant * (Real.exp (π / T) + 1) * (x * Real.exp (π / T) ^ N / (Real.exp (π / T) - 1)) :=
        mul_le_mul_of_nonneg_left hs hC
    _ = backgroundConstant * (Real.exp (π / T) + 1) / (Real.exp (π / T) - 1) * (x * Real.exp (π / T) ^ N) := by
        ring

/-- Rapporté à l'échelle de la ligne, le fond est au plus `C / x_N^{1/2}` : il s'efface. -/
theorem background_relative_le {T x : ℝ} (hT : 0 < T) (hx : 1 < x) (N : ℕ) :
    ‖backgroundAlternatingBudget T x N‖ / (x * Real.exp (π / T) ^ N) ^ ((3 : ℝ) / 2) ≤
      backgroundConstant * (Real.exp (π / T) + 1) / (Real.exp (π / T) - 1) /
        (x * Real.exp (π / T) ^ N) ^ ((1 : ℝ) / 2) := by
  set y := x * Real.exp (π / T) ^ N with hy
  have hy0 : 0 < y := mul_pos (by linarith) (pow_pos (Real.exp_pos _) _)
  have hb := norm_backgroundAlternatingBudget_le_scale hT hx N
  rw [← hy] at hb
  have h32 : y ^ ((3 : ℝ) / 2) = y * y ^ ((1 : ℝ) / 2) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hy0, Real.rpow_one]
  have h12 : 0 < y ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hy0 _
  rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hy0 _) h12, h32, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hb h12.le

noncomputable def naturalCellTotal {ι : Type*} (Rec : ArithmeticRecomposition ι) (T x : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, fiberCellTotal Rec T (x * Real.exp (π / T) ^ n)

/-- Le budget NATUREL (sans signes) télescope : son fond se réduit aux deux bords. -/
theorem naturalCellTotal_eq_telescope {ι : Type*} (Rec : ArithmeticRecomposition ι) {T x : ℝ} (hT : 0 < T)
    (hx : 1 < x) (N : ℕ) :
    naturalCellTotal Rec T x N =
      ((demandArea x (x * Real.exp (π / T) ^ N) : ℝ) : ℂ) -
        (((x * Real.exp (π / T) ^ N : ℝ) : ℂ) * residualBackground (x * Real.exp (π / T) ^ N) -
          (x : ℂ) * residualBackground x) := by
  have h0 : demandArea x x = 0 := by
    rw [← integratedSignal_variation_eq_demandArea le_rfl]
    ring
  induction N with
  | zero => simp [naturalCellTotal, h0]
  | succ n ih =>
    unfold naturalCellTotal at ih ⊢
    rw [Finset.sum_range_succ, ih, fiberCellTotal_eq_demandArea Rec hT (one_lt_mul_exp_pow hT hx n)]
    have hE1 : 1 ≤ Real.exp (π / T) := Real.one_le_exp (div_pos Real.pi_pos hT).le
    have hxn : 0 < x * Real.exp (π / T) ^ n := mul_pos (by linarith) (pow_pos (Real.exp_pos _) _)
    have hle1 : x ≤ x * Real.exp (π / T) ^ n := le_mul_of_one_le_right (by linarith) (one_le_pow₀ hE1)
    have hle2 : x * Real.exp (π / T) ^ n ≤ x * Real.exp (π / T) ^ n * Real.exp (π / T) :=
      le_mul_of_one_le_right hxn.le hE1
    have hA := demandArea_add hle1 hle2
    have hpow : x * Real.exp (π / T) ^ (n + 1) = x * Real.exp (π / T) ^ n * Real.exp (π / T) := by
      rw [pow_succ, mul_assoc]
    rw [hpow, ← hA]
    push_cast
    ring

theorem tower_term_natural {ι : Type*} (Rec : ArithmeticRecomposition ι) {β T : ℝ} {j : ι}
    (hj : Rec.point j = towerPoint β T) (x : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, fiberCellTerm Rec T j (x * Real.exp (π / T) ^ n) =
      ∑ n ∈ Finset.range N, towerCellShare (Rec.weight j) β T (x * Real.exp (π / T) ^ n) := by
  apply Finset.sum_congr rfl
  intro n _
  rw [fiberCellTerm_eq_towerCellShare Rec hj]

/-! ## B2 : somme naturelle d'une Tour contre somme à signes rectifiés -/

noncomputable def towerNaturalSum (w : ℂ) (β T x : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, towerCellShare w β T (x * Real.exp (π / T) ^ n)

/-- La somme naturelle des parts télescope : elle ne dépend que des deux bords. -/
theorem towerNaturalSum_telescope (w : ℂ) (β T x : ℝ) (N : ℕ) :
    towerNaturalSum w β T x N =
      w * (integratedKernel (x * Real.exp (π / T) ^ N) (towerPoint β T) - integratedKernel x (towerPoint β T)) := by
  unfold towerNaturalSum towerCellShare
  have h : ∀ n ∈ Finset.range N,
      w * (integratedKernel (x * Real.exp (π / T) ^ n * Real.exp (π / T)) (towerPoint β T) -
        integratedKernel (x * Real.exp (π / T) ^ n) (towerPoint β T)) =
      w * (integratedKernel (x * Real.exp (π / T) ^ (n + 1)) (towerPoint β T) -
        integratedKernel (x * Real.exp (π / T) ^ n) (towerPoint β T)) := by
    intro n _
    rw [pow_succ, mul_assoc]
  have htel : ∑ n ∈ Finset.range N,
      (integratedKernel (x * Real.exp (π / T) ^ (n + 1)) (towerPoint β T) -
        integratedKernel (x * Real.exp (π / T) ^ n) (towerPoint β T)) =
      integratedKernel (x * Real.exp (π / T) ^ N) (towerPoint β T) - integratedKernel x (towerPoint β T) := by
    have := Finset.sum_range_sub (fun n => integratedKernel (x * Real.exp (π / T) ^ n) (towerPoint β T)) N
    simpa using this
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, htel]

theorem cellFactor_ne_one {β T : ℝ} : cellFactor β T ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [cellFactor, Complex.neg_re, Complex.ofReal_re, Complex.one_re] at hre
  linarith [Real.exp_pos (π / T * (1 + β))]

theorem towerNaturalSum_eq {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) (N : ℕ) :
    towerNaturalSum w β T x N =
      towerCellShare w β T x * ((cellFactor β T ^ N - 1) / (cellFactor β T - 1)) := by
  unfold towerNaturalSum
  have hterm : ∀ n ∈ Finset.range N,
      towerCellShare w β T (x * Real.exp (π / T) ^ n) = cellFactor β T ^ n * towerCellShare w β T x :=
    fun n _ => towerCellShare_iterate hT hx w n
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, geom_sum_eq cellFactor_ne_one N]
  ring

theorem norm_cellFactor (β T : ℝ) : ‖cellFactor β T‖ = cellGrowth β T := by
  unfold cellFactor cellGrowth
  rw [norm_neg, Complex.norm_of_nonneg (Real.exp_pos _).le]

theorem norm_cellFactor_sub_one (β T : ℝ) : ‖cellFactor β T - 1‖ = cellGrowth β T + 1 := by
  unfold cellGrowth
  have h : cellFactor β T - 1 = -((Real.exp (π / T * (1 + β)) + 1 : ℝ) : ℂ) := by
    unfold cellFactor
    push_cast
    ring
  rw [h, norm_neg, Complex.norm_of_nonneg (by linarith [Real.exp_pos (π / T * (1 + β))])]

theorem norm_towerCellShare_iterate {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) (n : ℕ) :
    ‖towerCellShare w β T (x * Real.exp (π / T) ^ n)‖ = cellGrowth β T ^ n * ‖towerCellShare w β T x‖ := by
  rw [towerCellShare_iterate hT hx w n, norm_mul, norm_pow, norm_cellFactor]

theorem norm_towerAlternatingSum_eq {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hβ : 0 ≤ β) (w : ℂ) (N : ℕ) :
    ‖towerAlternatingSum w β T x N‖ =
      ‖towerCellShare w β T x‖ * ((cellGrowth β T ^ N - 1) / (cellGrowth β T - 1)) := by
  have hE := one_lt_cellGrowth hT hβ
  rw [towerAlternatingSum_eq hT hx hβ w N, norm_mul]
  congr 1
  have h1 : (1 : ℝ) ≤ cellGrowth β T ^ N := one_le_pow₀ hE.le
  have hnn : 0 ≤ (cellGrowth β T ^ N - 1) / (cellGrowth β T - 1) := div_nonneg (by linarith) (by linarith)
  rw [← Complex.norm_of_nonneg hnn]
  congr 1
  push_cast
  ring

/-- La somme « alternée » de Ψ4 est une somme à signes RECTIFIÉS : son module est la somme des modules des parts. -/
theorem norm_towerAlternatingSum_eq_sum_norms {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hβ : 0 ≤ β) (w : ℂ) (N : ℕ) :
    ‖towerAlternatingSum w β T x N‖ =
      ∑ n ∈ Finset.range N, ‖towerCellShare w β T (x * Real.exp (π / T) ^ n)‖ := by
  have hE := one_lt_cellGrowth hT hβ
  have hterm : ∀ n ∈ Finset.range N, ‖towerCellShare w β T (x * Real.exp (π / T) ^ n)‖ =
      ‖towerCellShare w β T x‖ * cellGrowth β T ^ n := by
    intro n _
    rw [norm_towerCellShare_iterate hT hx w n, mul_comm]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, geom_sum_eq hE.ne' N, norm_towerAlternatingSum_eq hT hx hβ w N]

theorem norm_towerNaturalSum_le {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hβ : 0 ≤ β) (w : ℂ) (N : ℕ) :
    ‖towerNaturalSum w β T x N‖ ≤ ‖towerAlternatingSum w β T x N‖ := by
  rw [norm_towerAlternatingSum_eq_sum_norms hT hx hβ w N]
  exact norm_sum_le _ _

theorem norm_towerNaturalSum_ge {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hβ : 0 ≤ β) (w : ℂ) (N : ℕ) :
    ‖towerAlternatingSum w β T x N‖ * ((cellGrowth β T - 1) / (cellGrowth β T + 1)) ≤
      ‖towerNaturalSum w β T x N‖ := by
  have hE := one_lt_cellGrowth hT hβ
  have hg1 : 0 < cellGrowth β T + 1 := by linarith
  have hlow : cellGrowth β T ^ N - 1 ≤ ‖cellFactor β T ^ N - 1‖ := by
    have := norm_sub_norm_le (cellFactor β T ^ N) 1
    rwa [norm_pow, norm_cellFactor, norm_one] at this
  rw [norm_towerAlternatingSum_eq hT hx hβ w N, towerNaturalSum_eq hT hx w N, norm_mul, norm_div,
    norm_cellFactor_sub_one]
  have hne : cellGrowth β T - 1 ≠ 0 := (by linarith : (0 : ℝ) < cellGrowth β T - 1).ne'
  have heq : ‖towerCellShare w β T x‖ * ((cellGrowth β T ^ N - 1) / (cellGrowth β T - 1)) *
      ((cellGrowth β T - 1) / (cellGrowth β T + 1)) =
      ‖towerCellShare w β T x‖ * ((cellGrowth β T ^ N - 1) / (cellGrowth β T + 1)) := by
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlow hg1.le) (norm_nonneg _)

noncomputable def relativeNatural (w : ℂ) (β T x : ℝ) (N : ℕ) : ℝ :=
  ‖towerNaturalSum w β T x N‖ / (x * Real.exp (π / T) ^ N) ^ ((3 : ℝ) / 2)

theorem relativeNatural_le_relativeAlternating {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hβ : 0 ≤ β) (w : ℂ) (N : ℕ) :
    relativeNatural w β T x N ≤ relativeAlternating w β T x N :=
  div_le_div_of_nonneg_right (norm_towerNaturalSum_le hT hx hβ w N)
    (Real.rpow_nonneg (mul_pos hx (pow_pos (Real.exp_pos _) _)).le _)

theorem relativeNatural_line_le {T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) (N : ℕ) :
    relativeNatural w (1 / 2) T x N ≤
      ‖towerCellShare w (1 / 2) T x‖ / ((cellGrowth (1 / 2) T - 1) * x ^ ((3 : ℝ) / 2)) :=
  (relativeNatural_le_relativeAlternating hT hx (by norm_num) w N).trans (relativeAlternating_line_le hT hx w N)

theorem relativeAlternating_le_relativeNatural_mul {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hβ : 0 ≤ β) (w : ℂ)
    (N : ℕ) :
    relativeAlternating w β T x N * ((cellGrowth β T - 1) / (cellGrowth β T + 1)) ≤ relativeNatural w β T x N := by
  unfold relativeAlternating relativeNatural
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (norm_towerNaturalSum_ge hT hx hβ w N)
    (Real.rpow_nonneg (mul_pos hx (pow_pos (Real.exp_pos _) _)).le _)

/-- La somme NATURELLE du miroir diverge aussi à l'échelle de la ligne. -/
theorem relativeNatural_unbounded_of_half_lt {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) {w : ℂ} (hw : w ≠ 0)
    (hβ : 1 / 2 < β) (M : ℝ) : ∃ N : ℕ, M < relativeNatural w β T x N := by
  have hβ0 : 0 ≤ β := by linarith
  have hE := one_lt_cellGrowth hT hβ0
  have hc : 0 < (cellGrowth β T - 1) / (cellGrowth β T + 1) := div_pos (by linarith) (by linarith)
  obtain ⟨N, hN⟩ := relativeAlternating_unbounded_of_half_lt hT hx hw hβ
    (M / ((cellGrowth β T - 1) / (cellGrowth β T + 1)))
  refine ⟨N, ?_⟩
  have h1 : M < relativeAlternating w β T x N * ((cellGrowth β T - 1) / (cellGrowth β T + 1)) := by
    rwa [div_lt_iff₀ hc] at hN
  exact lt_of_lt_of_le h1 (relativeAlternating_le_relativeNatural_mul hT hx hβ0 w N)

/-! ## B3 : la contribution complexe effective de la paire -/

theorem relativeAlternating_le_of_le_half {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (w : ℂ) (N : ℕ) :
    relativeAlternating w β T x N ≤ ‖towerCellShare w β T x‖ / ((cellGrowth β T - 1) * x ^ ((3 : ℝ) / 2)) := by
  rw [relativeAlternating_eq hT hx hβ0 w N]
  have hE := one_lt_cellGrowth hT hβ0
  have hx32 : 0 < x ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hx _
  have hD : 0 < Real.exp (N * (π / T * (3 / 2))) := Real.exp_pos _
  have hE1 : 0 < cellGrowth β T - 1 := by linarith
  have hgN : cellGrowth β T ^ N ≤ Real.exp (N * (π / T * (3 / 2))) := by
    unfold cellGrowth
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by linarith) (div_pos Real.pi_pos hT).le) (Nat.cast_nonneg N)
  rw [div_le_div_iff₀ (mul_pos hx32 hD) (mul_pos hE1 hx32)]
  have heq : ‖towerCellShare w β T x‖ * ((cellGrowth β T ^ N - 1) / (cellGrowth β T - 1)) *
      ((cellGrowth β T - 1) * x ^ ((3 : ℝ) / 2)) =
      ‖towerCellShare w β T x‖ * x ^ ((3 : ℝ) / 2) * (cellGrowth β T ^ N - 1) := by
    field_simp
  rw [heq]
  have hA : 0 ≤ ‖towerCellShare w β T x‖ * x ^ ((3 : ℝ) / 2) := mul_nonneg (norm_nonneg _) hx32.le
  nlinarith [mul_nonneg hA (sub_nonneg.mpr hgN)]

noncomputable def pairAlternatingSum (w w' : ℂ) (β T x : ℝ) (N : ℕ) : ℂ :=
  towerAlternatingSum w β T x N + towerAlternatingSum w' (1 - β) T x N

noncomputable def pairComplexRelative (w w' : ℂ) (β T x : ℝ) (N : ℕ) : ℝ :=
  ‖pairAlternatingSum w w' β T x N‖ / (x * Real.exp (π / T) ^ N) ^ ((3 : ℝ) / 2)

theorem pairComplexRelative_ge (w w' : ℂ) (β T : ℝ) {x : ℝ} (hx : 0 < x) (N : ℕ) :
    relativeAlternating w' (1 - β) T x N - relativeAlternating w β T x N ≤ pairComplexRelative w w' β T x N := by
  unfold pairComplexRelative relativeAlternating pairAlternatingSum
  rw [← sub_div]
  refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg (mul_pos hx (pow_pos (Real.exp_pos _) _)).le _)
  have := norm_sub_norm_le (towerAlternatingSum w' (1 - β) T x N) (-towerAlternatingSum w β T x N)
  rwa [norm_neg, sub_neg_eq_add, add_comm] at this

/-- La contribution COMPLEXE de la paire (somme, non somme de normes) est non bornée à l'échelle de la ligne. -/
theorem pairComplexRelative_unbounded_of_lt_half {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hβ0 : 0 ≤ β)
    (hβ : β < 1 / 2) (w : ℂ) {w' : ℂ} (hw' : w' ≠ 0) (M : ℝ) :
    ∃ N : ℕ, M < pairComplexRelative w w' β T x N := by
  obtain ⟨N, hN⟩ := relativeAlternating_unbounded_of_half_lt hT hx hw' (by linarith : 1 / 2 < 1 - β)
    (M + ‖towerCellShare w β T x‖ / ((cellGrowth β T - 1) * x ^ ((3 : ℝ) / 2)))
  refine ⟨N, ?_⟩
  have h1 := relativeAlternating_le_of_le_half hT hx hβ0 hβ.le w N
  have h2 := pairComplexRelative_ge w w' β T hx N
  linarith

noncomputable def pairNaturalSum (w w' : ℂ) (β T x : ℝ) (N : ℕ) : ℂ :=
  towerNaturalSum w β T x N + towerNaturalSum w' (1 - β) T x N

noncomputable def pairNaturalRelative (w w' : ℂ) (β T x : ℝ) (N : ℕ) : ℝ :=
  ‖pairNaturalSum w w' β T x N‖ / (x * Real.exp (π / T) ^ N) ^ ((3 : ℝ) / 2)

theorem pairNaturalRelative_ge (w w' : ℂ) (β T : ℝ) {x : ℝ} (hx : 0 < x) (N : ℕ) :
    relativeNatural w' (1 - β) T x N - relativeNatural w β T x N ≤ pairNaturalRelative w w' β T x N := by
  unfold pairNaturalRelative relativeNatural pairNaturalSum
  rw [← sub_div]
  refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg (mul_pos hx (pow_pos (Real.exp_pos _) _)).le _)
  have := norm_sub_norm_le (towerNaturalSum w' (1 - β) T x N) (-towerNaturalSum w β T x N)
  rwa [norm_neg, sub_neg_eq_add, add_comm] at this

/-- Même conclusion pour la somme NATURELLE de la paire (alternance propre des deux membres). -/
theorem pairNaturalRelative_unbounded_of_lt_half {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hβ0 : 0 ≤ β)
    (hβ : β < 1 / 2) (w : ℂ) {w' : ℂ} (hw' : w' ≠ 0) (M : ℝ) :
    ∃ N : ℕ, M < pairNaturalRelative w w' β T x N := by
  have hβ' : 0 ≤ 1 - β := by linarith
  have hE := one_lt_cellGrowth hT hβ'
  have hc : 0 < (cellGrowth (1 - β) T - 1) / (cellGrowth (1 - β) T + 1) := div_pos (by linarith) (by linarith)
  set K := ‖towerCellShare w β T x‖ / ((cellGrowth β T - 1) * x ^ ((3 : ℝ) / 2)) with hK
  obtain ⟨N, hN⟩ := relativeAlternating_unbounded_of_half_lt hT hx hw' (by linarith : 1 / 2 < 1 - β)
    ((M + K) / ((cellGrowth (1 - β) T - 1) / (cellGrowth (1 - β) T + 1)))
  refine ⟨N, ?_⟩
  have h1 : relativeNatural w β T x N ≤ K :=
    (relativeNatural_le_relativeAlternating hT hx hβ0 w N).trans (relativeAlternating_le_of_le_half hT hx hβ0 hβ.le w N)
  have h2 := relativeAlternating_le_relativeNatural_mul hT hx hβ' w' N
  have h3 : M + K < relativeAlternating w' (1 - β) T x N *
      ((cellGrowth (1 - β) T - 1) / (cellGrowth (1 - β) T + 1)) := by
    rwa [div_lt_iff₀ hc] at hN
  have h4 := pairNaturalRelative_ge w w' β T hx N
  linarith

theorem recomposition_pair_alternating {ι : Type*} (Rec : ArithmeticRecomposition ι) {β T : ℝ} {j j' : ι}
    (hj : Rec.point j = towerPoint β T) (hj' : Rec.point j' = towerPoint (1 - β) T) (x : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * fiberCellTerm Rec T j (x * Real.exp (π / T) ^ n)) +
      ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * fiberCellTerm Rec T j' (x * Real.exp (π / T) ^ n) =
      pairAlternatingSum (Rec.weight j) (Rec.weight j') β T x N := by
  unfold pairAlternatingSum
  rw [tower_term_alternating Rec hj, tower_term_alternating Rec hj']

/-- Avec le coefficient IMPOSÉ par la recomposition : si le miroir est porteur, la contribution complexe de la paire
(quel que soit le coefficient du membre bas) est non bornée à l'échelle de la ligne. -/
theorem recomposition_mirror_pair_unbounded {ι : Type*} (Rec : ArithmeticRecomposition ι) {β T x : ℝ}
    (hT : 0 < T) (hx : 0 < x) (hβ0 : 0 ≤ β) (hβ : β < 1 / 2) (hc : IsCarrier (1 - β) T) (w : ℂ) (M : ℝ) :
    ∃ j', Rec.point j' = towerPoint (1 - β) T ∧ ∃ N : ℕ, M < pairComplexRelative w (Rec.weight j') β T x N := by
  obtain ⟨j', hj', hs⟩ := recomposition_cellShare_ne_zero_of_isCarrier Rec hT hx hc
  have hw' : Rec.weight j' ≠ 0 := (towerCellShare_ne_zero_iff hT hx _).mp hs
  exact ⟨j', hj', pairComplexRelative_unbounded_of_lt_half hT hx hβ0 hβ w hw' M⟩

/-! ## B4 : pont de Ψ3 aux termes de fibre de la paire aux abscisses premières -/

theorem norm_integratedKernel_towerPoint {β T x : ℝ} (hx : 0 < x) :
    ‖integratedKernel x (towerPoint β T)‖ = x ^ (β + 1) / ‖towerPoint β T * (towerPoint β T + 1)‖ := by
  rw [integratedKernel_eq hx, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, towerPoint_re,
    Complex.one_re]

theorem norm_towerCellShare_eq {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) :
    ‖towerCellShare w β T x‖ =
      ‖w‖ * (1 + Real.exp (π / T * (1 + β))) * (x ^ (β + 1) / ‖towerPoint β T * (towerPoint β T + 1)‖) := by
  rw [towerCellShare_eq hT hx w, norm_mul, norm_mul, norm_neg, Complex.norm_of_nonneg (by positivity),
    norm_integratedKernel_towerPoint hx]

noncomputable def towerShareScale (w : ℂ) (β T : ℝ) : ℝ :=
  Real.log (‖w‖ * (1 + Real.exp (π / T * (1 + β)))) - Real.log ‖towerPoint β T * (towerPoint β T + 1)‖

theorem norm_towerPoint_mul_pos {β T : ℝ} (hT : 0 < T) : 0 < ‖towerPoint β T * (towerPoint β T + 1)‖ :=
  norm_pos_iff.mpr (mul_ne_zero (towerPoint_ne_zero_of_height_pos hT) (towerPoint_add_one_ne_zero_of_height_pos hT))

theorem log_norm_towerCellShare {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) {w : ℂ} (hw : w ≠ 0) :
    Real.log ‖towerCellShare w β T x‖ = (β + 1) * Real.log x + towerShareScale w β T := by
  have hA : ‖w‖ * (1 + Real.exp (π / T * (1 + β))) ≠ 0 := mul_ne_zero (norm_ne_zero_iff.mpr hw) (by positivity)
  have hD := norm_towerPoint_mul_pos (β := β) hT
  have hq : x ^ (β + 1) / ‖towerPoint β T * (towerPoint β T + 1)‖ ≠ 0 :=
    (div_pos (Real.rpow_pos_of_pos hx _) hD).ne'
  rw [norm_towerCellShare_eq hT hx w, Real.log_mul hA hq, Real.log_div (Real.rpow_pos_of_pos hx _).ne' hD.ne',
    Real.log_rpow hx]
  unfold towerShareScale
  ring

/-- Ψ3 relu dans les termes de fibre : l'asymétrie en un premier est l'écart des logarithmes des modules des parts des deux
membres sur la cellule issue de ce premier, à une constante (indépendante du premier) près. Pont GÉOMÉTRIQUE exact ; aucun
pont à une obligation arithmétique n'est compilé. -/
theorem pairAsymmetryAt_eq_log_share_ratio {β T : ℝ} (hT : 0 < T) {p : ℕ} (hp : 0 < p) {w w' : ℂ} (hw : w ≠ 0)
    (hw' : w' ≠ 0) :
    pairAsymmetryAt β p =
      (Real.log ‖towerCellShare w' (1 - β) T p‖ - Real.log ‖towerCellShare w β T p‖) -
        (towerShareScale w' (1 - β) T - towerShareScale w β T) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [pairAsymmetryAt_eq hp, log_norm_towerCellShare hT hp' hw', log_norm_towerCellShare hT hp' hw]
  ring

theorem cumulativeAsymmetry_eq_sum_log_share_ratio {β T : ℝ} (hT : 0 < T) {w w' : ℂ} (hw : w ≠ 0) (hw' : w' ≠ 0)
    (N : ℕ) :
    cumulativeAsymmetry β N =
      (∑ p ∈ primeSet N, (Real.log ‖towerCellShare w' (1 - β) T p‖ - Real.log ‖towerCellShare w β T p‖)) -
        (primeSet N).card * (towerShareScale w' (1 - β) T - towerShareScale w β T) := by
  unfold cumulativeAsymmetry
  have h : ∀ p ∈ primeSet N, pairAsymmetryAt β p =
      (Real.log ‖towerCellShare w' (1 - β) T p‖ - Real.log ‖towerCellShare w β T p‖) -
        (towerShareScale w' (1 - β) T - towerShareScale w β T) :=
    fun p hp => pairAsymmetryAt_eq_log_share_ratio hT (mem_primeSet.mp hp).2.pos hw hw'
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

#print axioms alternatingCellTotal_eq_arithmetic_sub_background
#print axioms alternatingCellTotal_independent
#print axioms norm_backgroundAlternatingBudget_le_scale
#print axioms background_relative_le
#print axioms naturalCellTotal_eq_telescope
#print axioms towerNaturalSum_telescope
#print axioms towerNaturalSum_eq
#print axioms norm_towerAlternatingSum_eq_sum_norms
#print axioms norm_towerNaturalSum_le
#print axioms norm_towerNaturalSum_ge
#print axioms relativeNatural_line_le
#print axioms relativeNatural_unbounded_of_half_lt
#print axioms relativeAlternating_le_of_le_half
#print axioms pairComplexRelative_unbounded_of_lt_half
#print axioms pairNaturalRelative_unbounded_of_lt_half
#print axioms recomposition_mirror_pair_unbounded
#print axioms pairAsymmetryAt_eq_log_share_ratio
#print axioms cumulativeAsymmetry_eq_sum_log_share_ratio

end RHV6Fresh
