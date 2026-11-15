/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RemainderExponent
import RHV6Fresh.Terminal.RayEnergy

/-!
# RHV6Fresh — énergie quadratique : diagonale arithmétique et résonance de cellule (E154, auteur, 2026-10-02)

Cible de l'auteur : POIDS EXACTS ⟹ BORNE QUADRATIQUE CRITIQUE DU RESTE ⟹ `θ* = 1/2`, pas « moyenne quadratique ⟺ RH ».
Ce fichier écrit ce qui, dans cette cible, se lit sur les seuls premiers et sur la Tour à sa résolution `π/T` (E151).

* **Diagonale arithmétique critique, depuis les premiers** (§1) : `Λ(n)² ≤ log n · Λ(n)`
  (`vonMangoldt_sq_le_log_mul`), donc `Σ_{n ≤ x} Λ(n)² ≤ log x · ψ(x) ≤ (log 4 + 4)·x·log x`
  (`vonMangoldt_sq_sum_le_log_mul_psi`, `vonMangoldt_sq_sum_linear`) : l'énergie diagonale du côté des premiers a
  l'exposant critique `1` (au logarithme près), sans aucune hypothèse.
* **Le poids du témoin au carré** (§2) : `w_δ(n)² ≥ 4Λ(n)²`, égalité ⟺ `δ = 0` (`shiftedWorld_weight_sq_ge`,
  `shiftedWorld_weight_sq_eq_iff`) : la diagonale du témoin est strictement plus lourde ; c'est elle qui porte son
  exposant quadratique `1 + 2δ` (E154, panneau D).
* **Résonance d'un membre avec ses propres cellules** (§3) : la cellule `k` de la Tour d'un membre est un
  demi-tour de son propre terme ; sa largeur est `C_k (e^{π/T} − 1)` (`cell_width_eq`) ; l'incrément du terme propre
  à travers la cellule est réel, de signe `−(−1)^k`, de valeur `(C_{k+1}^β + C_k^β)/‖ρ‖`
  (`ownCellIncrement_eq`), au moins `2 C_k^β/‖ρ‖` (`ownCellIncrement_abs_ge`) : chaque cellule lit le terme propre
  à pleine amplitude.
* **Énergie propre par unité de largeur** (§4) : d'une cellule à la suivante elle est multipliée par
  `exp((2β − 1)π/T)` (`ownCellEnergyDensity_succ`) — l'exposant radial doublé, forme quadratique de
  `amplitude_ratio_eq_rpow` ; constante ⟺ `β = 1/2` (`ownCellEnergyDensity_flat_iff`).

Borne : §3–§4 caractérisent, membre par membre, et valent pour tout `β` (donc dans le monde témoin) ; §1 est la
diagonale, pas le reste : le transfert « énergie du reste ≤ C · diagonale arithmétique » n'est pas dérivé ; c'est
la pièce du verdict 4 de E154. Dans une cellule, le poids du témoin est celui de `ζ²` multiplié par un facteur presque
constant `n^δ + n^{−δ}` : le rapport énergie/diagonale y est le même par construction et ne teste aucune loi.
Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction

/-! ## 1. Diagonale arithmétique critique, depuis les premiers -/

theorem vonMangoldt_sq_le_log_mul (n : ℕ) : Λ n ^ 2 ≤ Real.log n * Λ n := by
  have h0 : 0 ≤ Λ n := vonMangoldt_nonneg
  have h1 : Λ n ≤ Real.log n := vonMangoldt_le_log
  nlinarith

/-- **La diagonale arithmétique** : `Σ_{n ≤ x} Λ(n)² ≤ log x · ψ(x)`. -/
theorem vonMangoldt_sq_sum_le_log_mul_psi {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n ^ 2 ≤ Real.log x * Chebyshev.psi x := by
  rw [Chebyshev.psi_eq_sum_Icc, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hnx : (n : ℝ) ≤ x := by
    have := (Finset.mem_Icc.mp hn).2
    exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith))
  have h0 : 0 ≤ Λ n := vonMangoldt_nonneg
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  have hlog : Real.log n ≤ Real.log x :=
    Real.log_le_log (Nat.cast_pos.mpr hn0) hnx
  calc Λ n ^ 2 ≤ Real.log n * Λ n := vonMangoldt_sq_le_log_mul n
    _ ≤ Real.log x * Λ n := mul_le_mul_of_nonneg_right hlog h0

/-- **Exposant critique de la diagonale** : `Σ_{n ≤ x} Λ(n)² ≤ (log 4 + 4)·x·log x`, sans hypothèse. -/
theorem vonMangoldt_sq_sum_linear {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n ^ 2 ≤ (Real.log 4 + 4) * x * Real.log x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  calc ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n ^ 2 ≤ Real.log x * Chebyshev.psi x :=
        vonMangoldt_sq_sum_le_log_mul_psi hx
    _ ≤ Real.log x * ((Real.log 4 + 4) * x) :=
        mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self (by linarith)) hlog
    _ = (Real.log 4 + 4) * x * Real.log x := by ring

/-! ## 2. Le poids du témoin au carré -/

theorem shiftedWorld_weight_sq_ge (d : ℝ) (n : ℕ) :
    4 * Λ n ^ 2 ≤ (Λ n * ((n : ℝ) ^ d + (n : ℝ) ^ (-d))) ^ 2 := by
  obtain ⟨h0, h1⟩ := shiftedWorld_weight_ge d n
  nlinarith

/-- **Le carré du poids sépare** : sur une puissance de premier, `w_δ² = 4Λ²` ⟺ `δ = 0`. -/
theorem shiftedWorld_weight_sq_eq_iff (d : ℝ) {n : ℕ} (hn : 2 ≤ n) (hΛ : Λ n ≠ 0) :
    (Λ n * ((n : ℝ) ^ d + (n : ℝ) ^ (-d))) ^ 2 = 4 * Λ n ^ 2 ↔ d = 0 := by
  rw [← shiftedWorld_weight_eq_iff d hn hΛ]
  obtain ⟨h0, h1⟩ := shiftedWorld_weight_ge d n
  constructor
  · intro h
    have h4 : (Λ n * ((n : ℝ) ^ d + (n : ℝ) ^ (-d))) ^ 2 = (2 * Λ n) ^ 2 := by rw [h]; ring
    exact (pow_left_inj₀ (h0.trans h1) h0 two_ne_zero).mp h4
  · intro h; rw [h]; ring

/-! ## 3. Résonance d'un membre avec ses propres cellules -/

/-- Le contact suivant est le contact courant multiplié par `e^{π/T}`. -/
theorem contact_succ_eq (z : TrueZero) (k : ℤ) :
    contactMinusAt z (k + 1) = contactMinusAt z k * Real.exp (Real.pi / rZeroHeight z.1) := by
  have h := contactAt_consecutive_logWidth z k
  have hp : contactPlusAt z k = contactMinusAt z (k + 1) := rfl
  rw [hp] at h
  have hpos := contactMinusAt_positive z k
  have hpos' := contactMinusAt_positive z (k + 1)
  rw [← Real.exp_log hpos', ← Real.exp_log hpos, ← Real.exp_add]
  congr 1
  linarith

/-- **Largeur de cellule** : `C_{k+1} − C_k = C_k (e^{π/T} − 1)` ; la hauteur seule fixe la résolution. -/
theorem cell_width_eq (z : TrueZero) (k : ℤ) :
    contactMinusAt z (k + 1) - contactMinusAt z k =
      contactMinusAt z k * (Real.exp (Real.pi / rZeroHeight z.1) - 1) := by
  rw [contact_succ_eq]; ring

/-- Incrément du terme propre (partie réelle) à travers la cellule `k`. -/
noncomputable def ownCellIncrement (z : TrueZero) (k : ℤ) : ℝ :=
  (zeroTerm z (contactMinusAt z (k + 1))).re - (zeroTerm z (contactMinusAt z k)).re

/-- **La cellule est un demi-tour du terme propre** : l'incrément vaut `−(−1)^k (C_{k+1}^β + C_k^β)/‖ρ‖`. -/
theorem ownCellIncrement_eq (z : TrueZero) (k : ℤ) :
    ownCellIncrement z k =
      -((-1 : ℝ) ^ k) * ((contactMinusAt z (k + 1)) ^ rZeroRadialPosition z.1 +
        (contactMinusAt z k) ^ rZeroRadialPosition z.1) / ‖zeroPoint z‖ := by
  unfold ownCellIncrement
  rw [ray_energy, ray_energy, zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  ring

theorem ownCellIncrement_sq (z : TrueZero) (k : ℤ) :
    ownCellIncrement z k ^ 2 =
      ((contactMinusAt z (k + 1)) ^ rZeroRadialPosition z.1 +
        (contactMinusAt z k) ^ rZeroRadialPosition z.1) ^ 2 / ‖zeroPoint z‖ ^ 2 := by
  rw [ownCellIncrement_eq, div_pow, mul_pow, neg_sq, ← zpow_natCast, ← zpow_mul,
    mul_comm k, zpow_mul]
  norm_num

/-- **Pleine amplitude** : la cellule lit le terme propre au moins à `2 C_k^β/‖ρ‖`. -/
theorem ownCellIncrement_abs_ge (z : TrueZero) (k : ℤ) :
    2 * (contactMinusAt z k) ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖ ≤ |ownCellIncrement z k| := by
  have hN := zeroPoint_norm_pos z
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hC := contactMinusAt_positive z k
  have hCC : contactMinusAt z k ≤ contactMinusAt z (k + 1) := by
    rw [contact_succ_eq]
    exact le_mul_of_one_le_right hC.le (Real.one_le_exp (div_nonneg Real.pi_pos.le z.2.le))
  have hle : (contactMinusAt z k) ^ rZeroRadialPosition z.1 ≤
      (contactMinusAt z (k + 1)) ^ rZeroRadialPosition z.1 :=
    Real.rpow_le_rpow hC.le hCC hβ.le
  rw [ownCellIncrement_eq, abs_div, abs_of_pos hN, abs_mul, abs_neg, abs_zpow, abs_neg, abs_one,
    one_zpow, one_mul]
  apply div_le_div_of_nonneg_right _ hN.le
  rw [abs_of_pos (add_pos (Real.rpow_pos_of_pos (contactMinusAt_positive z (k + 1)) _)
    (Real.rpow_pos_of_pos hC _))]
  linarith

/-! ## 4. Énergie propre par unité de largeur -/

/-- Énergie du terme propre dans la cellule `k`, par unité de largeur. -/
noncomputable def ownCellEnergyDensity (z : TrueZero) (k : ℤ) : ℝ :=
  ownCellIncrement z k ^ 2 / (contactMinusAt z (k + 1) - contactMinusAt z k)

/-- **Exposant radial doublé** : d'une cellule à la suivante, l'énergie propre par unité de largeur est
multipliée par `exp((2β − 1)π/T)`. -/
theorem ownCellEnergyDensity_succ (z : TrueZero) (k : ℤ) :
    ownCellEnergyDensity z (k + 1) =
      Real.exp ((2 * rZeroRadialPosition z.1 - 1) * (Real.pi / rZeroHeight z.1)) *
        ownCellEnergyDensity z k := by
  have hC := contactMinusAt_positive z k
  have hc : 0 < Real.pi / rZeroHeight z.1 := div_pos Real.pi_pos z.2
  have hN := zeroPoint_norm_pos z
  unfold ownCellEnergyDensity
  rw [ownCellIncrement_sq, ownCellIncrement_sq, contact_succ_eq z (k + 1), contact_succ_eq z k]
  generalize contactMinusAt z k = C at hC ⊢
  generalize Real.pi / rZeroHeight z.1 = c at hc ⊢
  generalize rZeroRadialPosition z.1 = β
  have hE1 : 1 < Real.exp c := Real.one_lt_exp_iff.mpr hc
  have hE : Real.exp c - 1 ≠ 0 := by linarith
  have hpow : ∀ y : ℝ, 0 < y → (y * Real.exp c) ^ β = y ^ β * Real.exp (c * β) := by
    intro y hy
    rw [Real.mul_rpow hy.le (Real.exp_pos c).le, ← Real.exp_mul]
  have hexp : Real.exp ((2 * β - 1) * c) = Real.exp (c * β) ^ 2 / Real.exp c := by
    rw [sq, ← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  rw [hpow (C * Real.exp c) (by positivity), hpow C hC, hexp]
  have hw1 : C * Real.exp c * Real.exp c - C * Real.exp c = C * Real.exp c * (Real.exp c - 1) := by ring
  have hw0 : C * Real.exp c - C = C * (Real.exp c - 1) := by ring
  rw [hw1, hw0]
  field_simp

theorem ownCellEnergyDensity_pos (z : TrueZero) (k : ℤ) : 0 < ownCellEnergyDensity z k := by
  have hN := zeroPoint_norm_pos z
  have hC := contactMinusAt_positive z k
  have ha : 0 < 2 * (contactMinusAt z k) ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖ := by positivity
  have hinc : 0 < |ownCellIncrement z k| := ha.trans_le (ownCellIncrement_abs_ge z k)
  have hw : 0 < contactMinusAt z (k + 1) - contactMinusAt z k := by
    rw [cell_width_eq]
    have h1 : 1 < Real.exp (Real.pi / rZeroHeight z.1) := Real.one_lt_exp_iff.mpr (div_pos Real.pi_pos z.2)
    exact mul_pos hC (by linarith)
  unfold ownCellEnergyDensity
  exact div_pos (by rw [← sq_abs]; positivity) hw

/-- **Platitude de l'énergie propre** : l'énergie par unité de largeur est la même dans deux cellules
consécutives ⟺ le membre est en ligne. Caractérisation, vraie pour tout membre de tout monde. -/
theorem ownCellEnergyDensity_flat_iff (z : TrueZero) (k : ℤ) :
    ownCellEnergyDensity z (k + 1) = ownCellEnergyDensity z k ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  have hd := ownCellEnergyDensity_pos z k
  have hc : 0 < Real.pi / rZeroHeight z.1 := div_pos Real.pi_pos z.2
  rw [ownCellEnergyDensity_succ]
  constructor
  · intro h
    have h1 : Real.exp ((2 * rZeroRadialPosition z.1 - 1) * (Real.pi / rZeroHeight z.1)) = 1 := by
      have := mul_right_cancel₀ hd.ne' (h.trans (one_mul _).symm)
      exact this
    rw [Real.exp_eq_one_iff, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · linarith
    · exact absurd h1 hc.ne'
  · intro h
    rw [h]
    norm_num

end RHV6Fresh
