/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FiberAnnihilator

/-!
# RHV6Fresh — Terminal/AlternatingCellSeries : l'alternance cumulée, stabilité de la grammaire et budget alterné (Ψ4 + Ψ6, E470, §19.104)
(plan Ψ, 2026-11-13 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse, aucun axiome, aucun `sorry`)

Stratégie (règle R-Ψ). Cible : la stabilité de la grammaire est un mécanisme d'ANNULATION PAR ALTERNANCE le long des cellules ;
une Tour de ligne a une somme alternée de parts bornée à l'échelle de la ligne, le miroir d'une paire hors ligne la fait diverger.
Objet cumulé : sommes partielles alternées des parts d'une Tour sur N cellules ; côté premiers, la somme alternée des totaux de
cellules (aires de demande, E465), quantité lue sur les premiers seuls. Pourquoi le ponctuel échoue : une cellule ne s'annule avec
rien. Signature d'un hors-ligne : la somme alternée relative du miroir croît comme `e^{Nπ(β−1/2)/T}`. Suite (Ψ6, H15 en série) : le
budget ALTERNÉ des premiers égale la somme des sommes alternées de toutes les Tours ; la paire y est non bornée relativement ; ce que
les autres hauteurs doivent fournir au cumul est écrit.

* G1 `cellGrowth`, `towerAlternatingSum`, `towerAlternatingSum_eq` : forme close (série géométrique de raison `e^{π(1+β)/T}`).
* G2 `relativeAlternating`, `relativeAlternating_eq`.
* G3 `relativeAlternating_line_le` : sur la ligne, bornée par une constante explicite (annulation).
* G4 `relativeAlternating_unbounded_of_half_lt` : le miroir diverge.
* G5 `alternatingCellTotal`, `alternatingCellTotal_eq_demandAreas` (premiers seuls), `alternatingCellTotal_eq_tsum`,
  `tower_term_alternating` : budget alterné = somme des sommes alternées des Tours.
* G6 `pairRelativeAlternating_unbounded_of_lt_half` (Ψ6) : la paire est non bornée dans le budget alterné.
Portée : identités, bornes et équivalences exactes ; rien n'exclut seul un zéro hors ligne.

Rectification de vocabulaire (E472, audit externe, 2026-11-13 ; `ArithmeticBudgetSeparation.lean`). Le facteur de cellule est
DÉJÀ négatif : multiplier par `(−1)^n` rectifie les signes, la raison devient `cellGrowth > 0`. `towerAlternatingSum` est donc une
somme à SIGNES RECTIFIÉS, de module égal à la somme des modules des parts (`norm_towerAlternatingSum_eq_sum_norms`), et NON une
annulation par alternance ; la somme NATURELLE (`towerNaturalSum`) télescope et vérifie
`(g−1)/(g+1)·‖rectifiée‖ ≤ ‖naturelle‖ ≤ ‖rectifiée‖`. `alternatingCellTotal_eq_demandAreas` contient le fond
(`residualBackground`) : « premiers seuls » est rectifié en « premiers + fond », le fond étant à l'échelle `x_N` (`background_relative_le`).
`pairRelativeAlternating` est une somme de normes ; la contribution complexe effective est `pairComplexRelative` (même module).
-/

namespace RHV6Fresh

open Real

/-! ## G1 : somme à signes rectifiés des parts d'une Tour, forme close -/

noncomputable def cellGrowth (β T : ℝ) : ℝ := Real.exp (π / T * (1 + β))

theorem neg_cellFactor (β T : ℝ) : -cellFactor β T = (cellGrowth β T : ℂ) := by
  unfold cellFactor cellGrowth
  ring

theorem one_lt_cellGrowth {β T : ℝ} (hT : 0 < T) (hβ : 0 ≤ β) : 1 < cellGrowth β T :=
  Real.one_lt_exp_iff.mpr (mul_pos (div_pos Real.pi_pos hT) (by linarith))

noncomputable def towerAlternatingSum (w : ℂ) (β T x : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * towerCellShare w β T (x * Real.exp (π / T) ^ n)

theorem towerAlternatingSum_eq {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hβ : 0 ≤ β) (w : ℂ) (N : ℕ) :
    towerAlternatingSum w β T x N =
      towerCellShare w β T x * (((cellGrowth β T : ℂ) ^ N - 1) / ((cellGrowth β T : ℂ) - 1)) := by
  have hq : (cellGrowth β T : ℂ) ≠ 1 := by
    intro h
    have h1 : cellGrowth β T = 1 := Complex.ofReal_inj.mp (h.trans Complex.ofReal_one.symm)
    linarith [one_lt_cellGrowth hT hβ]
  unfold towerAlternatingSum
  have hterm : ∀ n ∈ Finset.range N, (-1 : ℂ) ^ n * towerCellShare w β T (x * Real.exp (π / T) ^ n) =
      (cellGrowth β T : ℂ) ^ n * towerCellShare w β T x := by
    intro n _
    rw [towerCellShare_iterate hT hx w n, ← mul_assoc, ← mul_pow, neg_one_mul, neg_cellFactor]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, geom_sum_eq hq N]
  ring

/-! ## G2 : à l'échelle de la ligne -/

noncomputable def relativeAlternating (w : ℂ) (β T x : ℝ) (N : ℕ) : ℝ :=
  ‖towerAlternatingSum w β T x N‖ / (x * Real.exp (π / T) ^ N) ^ ((3 : ℝ) / 2)

theorem line_scale_pow {T x : ℝ} (hx : 0 < x) (N : ℕ) :
    (x * Real.exp (π / T) ^ N) ^ ((3 : ℝ) / 2) = x ^ ((3 : ℝ) / 2) * Real.exp (N * (π / T * (3 / 2))) := by
  rw [Real.mul_rpow hx.le (pow_pos (Real.exp_pos _) _).le, ← Real.exp_nat_mul, ← Real.exp_mul]
  congr 2
  ring

theorem relativeAlternating_eq {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hβ : 0 ≤ β) (w : ℂ) (N : ℕ) :
    relativeAlternating w β T x N =
      ‖towerCellShare w β T x‖ * ((cellGrowth β T ^ N - 1) / (cellGrowth β T - 1)) /
        (x ^ ((3 : ℝ) / 2) * Real.exp (N * (π / T * (3 / 2)))) := by
  unfold relativeAlternating
  rw [towerAlternatingSum_eq hT hx hβ w N, norm_mul, line_scale_pow hx N]
  congr 2
  have hE := one_lt_cellGrowth hT hβ
  have h1 : (1 : ℝ) ≤ cellGrowth β T ^ N := one_le_pow₀ hE.le
  have hnn : 0 ≤ (cellGrowth β T ^ N - 1) / (cellGrowth β T - 1) := div_nonneg (by linarith) (by linarith)
  rw [← Complex.norm_of_nonneg hnn]
  congr 1
  push_cast
  ring

/-! ## G3 : sur la ligne, la somme alternée relative est bornée -/

theorem relativeAlternating_line_le {T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) (N : ℕ) :
    relativeAlternating w (1 / 2) T x N ≤
      ‖towerCellShare w (1 / 2) T x‖ / ((cellGrowth (1 / 2) T - 1) * x ^ ((3 : ℝ) / 2)) := by
  rw [relativeAlternating_eq hT hx (by norm_num) w N]
  have hE := one_lt_cellGrowth hT (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hEN : Real.exp (N * (π / T * (3 / 2))) = cellGrowth (1 / 2) T ^ N := by
    unfold cellGrowth
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hEN]
  have hx32 : 0 < x ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hx _
  have hEN0 : 0 < cellGrowth (1 / 2) T ^ N := pow_pos (by linarith) _
  have hE1 : 0 < cellGrowth (1 / 2) T - 1 := by linarith
  rw [div_le_div_iff₀ (mul_pos hx32 hEN0) (mul_pos hE1 hx32)]
  have hA : 0 ≤ ‖towerCellShare w (1 / 2) T x‖ * x ^ ((3 : ℝ) / 2) :=
    mul_nonneg (norm_nonneg _) hx32.le
  have heq : ‖towerCellShare w (1 / 2) T x‖ * ((cellGrowth (1 / 2) T ^ N - 1) / (cellGrowth (1 / 2) T - 1)) *
      ((cellGrowth (1 / 2) T - 1) * x ^ ((3 : ℝ) / 2)) =
      ‖towerCellShare w (1 / 2) T x‖ * x ^ ((3 : ℝ) / 2) * (cellGrowth (1 / 2) T ^ N - 1) := by
    field_simp
  rw [heq]
  nlinarith [hA]

/-! ## G4 : le miroir diverge -/

theorem relativeAlternating_unbounded_of_half_lt {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) {w : ℂ} (hw : w ≠ 0)
    (hβ : 1 / 2 < β) (M : ℝ) : ∃ N : ℕ, M < relativeAlternating w β T x N := by
  have hs : 0 < ‖towerCellShare w β T x‖ := norm_pos_iff.mpr ((towerCellShare_ne_zero_iff hT hx w).mpr hw)
  have hβ0 : 0 ≤ β := by linarith
  have hE := one_lt_cellGrowth hT hβ0
  have hx32 : 0 < x ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hx _
  set d := π / T * (β - 1 / 2) with hd
  have hd0 : 0 < d := mul_pos (div_pos Real.pi_pos hT) (by linarith)
  set K := ‖towerCellShare w β T x‖ / ((cellGrowth β T - 1) * x ^ ((3 : ℝ) / 2)) with hK
  have hK0 : 0 < K := div_pos hs (mul_pos (by linarith) hx32)
  obtain ⟨N, hN⟩ := exists_nat_gt (M / (d * K))
  refine ⟨N, ?_⟩
  rw [relativeAlternating_eq hT hx hβ0 w N]
  have hEN : cellGrowth β T ^ N = Real.exp (N * d) * Real.exp (N * (π / T * (3 / 2))) := by
    unfold cellGrowth
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [hd]
    ring
  have hD : 0 < Real.exp (N * (π / T * (3 / 2))) := Real.exp_pos _
  have hD1 : 1 ≤ Real.exp (N * (π / T * (3 / 2))) :=
    Real.one_le_exp (by positivity)
  have hlow : Real.exp (N * d) - 1 ≤ (cellGrowth β T ^ N - 1) / Real.exp (N * (π / T * (3 / 2))) := by
    rw [hEN, le_div_iff₀ hD]
    nlinarith [Real.exp_pos (N * d)]
  have h1 : M < N * (d * K) := by rwa [div_lt_iff₀ (mul_pos hd0 hK0)] at hN
  have h2 := Real.add_one_le_exp (N * d)
  have hE1 : 0 < cellGrowth β T - 1 := by linarith
  calc M < N * (d * K) := h1
    _ ≤ K * (Real.exp (N * d) - 1) := by nlinarith
    _ ≤ K * ((cellGrowth β T ^ N - 1) / Real.exp (N * (π / T * (3 / 2)))) :=
        mul_le_mul_of_nonneg_left hlow hK0.le
    _ = ‖towerCellShare w β T x‖ * ((cellGrowth β T ^ N - 1) / (cellGrowth β T - 1)) /
        (x ^ ((3 : ℝ) / 2) * Real.exp (N * (π / T * (3 / 2)))) := by
        rw [hK]
        field_simp

/-! ## G5 : le budget alterné des premiers -/

noncomputable def alternatingCellTotal {ι : Type*} (Rec : ArithmeticRecomposition ι) (T x : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * fiberCellTotal Rec T (x * Real.exp (π / T) ^ n)

theorem one_lt_mul_exp_pow {T x : ℝ} (hT : 0 < T) (hx : 1 < x) (n : ℕ) : 1 < x * Real.exp (π / T) ^ n :=
  lt_of_lt_of_le hx (le_mul_of_one_le_right (by linarith)
    (one_le_pow₀ (Real.one_le_exp (div_pos Real.pi_pos hT).le)))

/-- Le budget alterné ne contient que des quantités lues sur les premiers (aires de demande) et le fond. -/
theorem alternatingCellTotal_eq_demandAreas {ι : Type*} (Rec : ArithmeticRecomposition ι) {T x : ℝ} (hT : 0 < T)
    (hx : 1 < x) (N : ℕ) :
    alternatingCellTotal Rec T x N =
      ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n *
        (((demandArea (x * Real.exp (π / T) ^ n) (x * Real.exp (π / T) ^ n * Real.exp (π / T)) : ℝ) : ℂ) -
          (((x * Real.exp (π / T) ^ n * Real.exp (π / T) : ℝ) : ℂ) *
              residualBackground (x * Real.exp (π / T) ^ n * Real.exp (π / T)) -
            ((x * Real.exp (π / T) ^ n : ℝ) : ℂ) * residualBackground (x * Real.exp (π / T) ^ n))) := by
  unfold alternatingCellTotal
  apply Finset.sum_congr rfl
  intro n _
  rw [fiberCellTotal_eq_demandArea Rec hT (one_lt_mul_exp_pow hT hx n)]

theorem alternatingCellTotal_eq_tsum {ι : Type*} (Rec : ArithmeticRecomposition ι) {T x : ℝ} (hT : 0 < T)
    (hx : 1 < x) (N : ℕ) :
    alternatingCellTotal Rec T x N =
      ∑' i, ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * fiberCellTerm Rec T i (x * Real.exp (π / T) ^ n) := by
  have h := Summable.tsum_finsetSum (s := Finset.range N)
    (f := fun n i => (-1 : ℂ) ^ n * fiberCellTerm Rec T i (x * Real.exp (π / T) ^ n))
    (fun n _ => (fiberCellTerm_summable Rec hT (one_lt_mul_exp_pow hT hx n)).mul_left _)
  rw [h]
  unfold alternatingCellTotal fiberCellTotal
  apply Finset.sum_congr rfl
  intro n _
  rw [tsum_mul_left]

theorem tower_term_alternating {ι : Type*} (Rec : ArithmeticRecomposition ι) {β T : ℝ} {j : ι}
    (hj : Rec.point j = towerPoint β T) (x : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * fiberCellTerm Rec T j (x * Real.exp (π / T) ^ n) =
      towerAlternatingSum (Rec.weight j) β T x N := by
  unfold towerAlternatingSum
  apply Finset.sum_congr rfl
  intro n _
  rw [fiberCellTerm_eq_towerCellShare Rec hj]

/-! ## G6 (Ψ6) : la paire dans le budget alterné -/

noncomputable def pairRelativeAlternating (w w' : ℂ) (β T x : ℝ) (N : ℕ) : ℝ :=
  relativeAlternating w β T x N + relativeAlternating w' (1 - β) T x N

theorem relativeAlternating_nonneg (w : ℂ) (β T : ℝ) {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ relativeAlternating w β T x N :=
  div_nonneg (norm_nonneg _) (Real.rpow_nonneg (mul_pos hx (pow_pos (Real.exp_pos _) _)).le _)

theorem pairRelativeAlternating_unbounded_of_lt_half {β T x : ℝ} (hT : 0 < T) (hx : 0 < x) (w : ℂ) {w' : ℂ}
    (hw' : w' ≠ 0) (hβ : β < 1 / 2) (M : ℝ) :
    ∃ N : ℕ, M < pairRelativeAlternating w w' β T x N := by
  obtain ⟨N, hN⟩ := relativeAlternating_unbounded_of_half_lt hT hx hw' (by linarith : 1 / 2 < 1 - β) M
  refine ⟨N, lt_of_lt_of_le hN ?_⟩
  unfold pairRelativeAlternating
  exact le_add_of_nonneg_left (relativeAlternating_nonneg w β T hx N)

#print axioms towerAlternatingSum_eq
#print axioms relativeAlternating_eq
#print axioms relativeAlternating_line_le
#print axioms relativeAlternating_unbounded_of_half_lt
#print axioms alternatingCellTotal_eq_demandAreas
#print axioms alternatingCellTotal_eq_tsum
#print axioms tower_term_alternating
#print axioms pairRelativeAlternating_unbounded_of_lt_half

end RHV6Fresh
