/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MirrorGroupNonCompensation

/-!
# Décomposition de la borne du reste depuis les poids premiers : blocs et couverture (auteur, 2026-10-11)

Prompt 1 de la revue : dérouler `smoothedRemainder` jusqu'aux sommes finies de poids `Λ(n)`, décomposer la borne
cherchée en une estimation sur blocs d'abscisses (les entiers `N ≥ 2`) et une estimation qui couvre les abscisses
intermédiaires, et démontrer leur composition avec des constantes explicites.

* `primeMass N = Σ_{n<N} Λ(n)(N − n)` : somme finie de poids premiers (puissances de premiers comprises) ;
  aux entiers `S(N) = primeMass N / N` (`smoothedVonMangoldtSum_natCast`).
* fond hors du terme linéaire : `‖bg(x) − x/2‖ ≤ B₀ = c₀ + c₁ + K` (`background_sub_half_le`).
* bloc → reste aux entiers : `‖R(N)‖ ≤ |primeMass N − N²/2|/N + B₀` (`remainder_natCast_le`).
* COUVERTURE (démontrée, Chebyshev) : `x ∈ ]N, N+1]` ⟹ `‖R(x) − R(N+1)‖ ≤ D = (log 4 + 4) + 1/2 + 2B₀`
  (`remainder_cover`).
* COMPOSITION : blocs `|primeMass N − N²/2| ≤ C·N^{1+θ}` pour tout `N ≥ 2` ⟹ `‖R(x)‖ ≤ C'·x^{max θ 0}` pour tout
  `x > 1`, `C' = max C 0 · 2^{max θ 0} + B₀ + D` (`remainder_growth_of_blocks`).

L'estimation de blocs n'est PAS démontrée ici ; seul son exposant `1` l'est (Chebyshev, `primeMass_block_linear`).
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction

/-- Masse première d'un bloc : `Σ_{n<N} Λ(n)(N − n)` (somme finie de poids de von Mangoldt). -/
noncomputable def primeMass (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, Λ n * ((N : ℝ) - n)

/-- Constante du fond hors du terme linéaire. -/
noncomputable def backgroundConst : ℝ :=
  ‖-logDeriv riemannZeta 0‖ + ‖logDeriv riemannZeta (-1)‖ + ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2

theorem backgroundConst_nonneg : 0 ≤ backgroundConst := by
  unfold backgroundConst
  have : 0 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := tsum_nonneg fun n => by positivity
  positivity

/-- Constante de couverture. -/
noncomputable def coverConst : ℝ := (Real.log 4 + 4) + 1 / 2 + 2 * backgroundConst

/-- Aux entiers, la somme lissée est la masse première divisée par `N`. -/
theorem smoothedVonMangoldtSum_natCast {N : ℕ} (hN : 1 ≤ N) :
    smoothedVonMangoldtSum (N : ℝ) = ((primeMass N / N : ℝ) : ℂ) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold smoothedVonMangoldtSum primeMass
  rw [Nat.ceil_natCast, Finset.sum_div]
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  have : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp

/-- Le fond, hors du terme `x/2`, est borné uniformément en `x > 1`. -/
theorem background_sub_half_le {x : ℝ} (hx : 1 < x) :
    ‖smoothedZeroBackground x - (x : ℂ) / 2‖ ≤ backgroundConst := by
  have hx0 : 0 < x := lt_trans one_pos hx
  have hT := trivialZeroSum_norm_le hx
  have hinv : ‖logDeriv riemannZeta (-1) * (x : ℂ)⁻¹‖ ≤ ‖logDeriv riemannZeta (-1)‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    exact mul_le_of_le_one_right (norm_nonneg _) (inv_le_one_of_one_le₀ hx.le)
  have heq : smoothedZeroBackground x - (x : ℂ) / 2 = (-logDeriv riemannZeta 0) +
      logDeriv riemannZeta (-1) * (x : ℂ)⁻¹ + ∑' n : ℕ, trivialZeroResidueTerm x n := by
    unfold smoothedZeroBackground; ring
  rw [heq]
  unfold backgroundConst
  calc _ ≤ ‖(-logDeriv riemannZeta 0) + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹‖ +
        ‖∑' n : ℕ, trivialZeroResidueTerm x n‖ := norm_add_le _ _
    _ ≤ (‖-logDeriv riemannZeta 0‖ + ‖logDeriv riemannZeta (-1) * (x : ℂ)⁻¹‖) +
        ‖∑' n : ℕ, trivialZeroResidueTerm x n‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by gcongr

/-- **Bloc → reste aux entiers** : `‖R(N)‖ ≤ |primeMass N − N²/2|/N + B₀`. -/
theorem remainder_natCast_le {N : ℕ} (hN : 2 ≤ N) :
    ‖smoothedRemainder (N : ℝ)‖ ≤ |primeMass N - (N : ℝ) ^ 2 / 2| / N + backgroundConst := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hsplit : smoothedRemainder (N : ℝ) = (((primeMass N - (N : ℝ) ^ 2 / 2) / N : ℝ) : ℂ) -
      (smoothedZeroBackground (N : ℝ) - ((N : ℝ) : ℂ) / 2) := by
    unfold smoothedRemainder
    rw [smoothedVonMangoldtSum_natCast (by omega)]
    have : ((primeMass N / N : ℝ) : ℂ) = (((primeMass N - (N : ℝ) ^ 2 / 2) / N : ℝ) : ℂ) + ((N : ℝ) : ℂ) / 2 := by
      push_cast; field_simp; ring
    rw [this]; ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans (add_le_add ?_ (background_sub_half_le hN1))
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hNpos]

/-- La somme lissée en partie réelle explicite. -/
theorem smoothedVonMangoldtSum_real (x : ℝ) :
    smoothedVonMangoldtSum x = ((∑ n ∈ Finset.range ⌈x⌉₊, Λ n * (1 - n / x) : ℝ) : ℂ) := by
  unfold smoothedVonMangoldtSum; push_cast; rfl

/-- `Σ_{n ≤ N} Λ(n) = ψ(N)`. -/
theorem sum_range_succ_vonMangoldt_eq_psi (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), Λ n = Chebyshev.psi N := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  congr 1
  ext n; simp [Finset.mem_range, Finset.mem_Icc]

/-- **Couverture** : sur `]N, N+1]`, le reste ne s'écarte de sa valeur en `N + 1` que de `D`. -/
theorem remainder_cover {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : (N : ℝ) < x) (hx' : x ≤ N + 1) :
    ‖smoothedRemainder x - smoothedRemainder ((N + 1 : ℕ) : ℝ)‖ ≤ coverConst := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 1 < x := lt_of_le_of_lt hN1 hx
  have hx0 : 0 < x := by linarith
  have hM1 : (1 : ℝ) < ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hceil : ⌈x⌉₊ = N + 1 := by
    rw [Nat.ceil_eq_iff (by omega)]; push_cast; exact ⟨by simpa using hx, hx'⟩
  -- partie arithmétique
  have hS : ‖smoothedVonMangoldtSum x - smoothedVonMangoldtSum ((N + 1 : ℕ) : ℝ)‖ ≤ Real.log 4 + 4 := by
    rw [smoothedVonMangoldtSum_real, smoothedVonMangoldtSum_real, hceil, Nat.ceil_natCast, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, ← Finset.sum_sub_distrib]
    set d : ℝ := 1 / x - 1 / ((N : ℝ) + 1)
    have hd0 : 0 ≤ d := by
      simp only [d]; rw [sub_nonneg]; exact one_div_le_one_div_of_le hx0 (by linarith)
    have hd1 : d ≤ 1 / ((N : ℝ) * ((N : ℝ) + 1)) := by
      simp only [d]
      have : 1 / x ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le (by linarith) hx.le
      have he : 1 / (N : ℝ) - 1 / ((N : ℝ) + 1) = 1 / ((N : ℝ) * ((N : ℝ) + 1)) := by
        field_simp; ring
      linarith
    have hterm : ∀ n ∈ Finset.range (N + 1), Λ n * (1 - n / x) - Λ n * (1 - n / ((N + 1 : ℕ) : ℝ)) =
        -(Λ n * n * d) := by
      intro n _; simp only [d]; push_cast; field_simp; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, abs_neg, ← Finset.sum_mul]
    have hsum0 : 0 ≤ ∑ n ∈ Finset.range (N + 1), Λ n * (n : ℝ) :=
      Finset.sum_nonneg fun n _ => mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
    have hsumle : ∑ n ∈ Finset.range (N + 1), Λ n * (n : ℝ) ≤ N * Chebyshev.psi N := by
      rw [← sum_range_succ_vonMangoldt_eq_psi, Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      have : (n : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [mul_comm (N : ℝ)]; exact mul_le_mul_of_nonneg_left this vonMangoldt_nonneg
    have hpsi : Chebyshev.psi N ≤ (Real.log 4 + 4) * N := Chebyshev.psi_le_const_mul_self (by positivity)
    rw [abs_of_nonneg (mul_nonneg hsum0 hd0)]
    have hNpos : (0 : ℝ) < N := by linarith
    calc (∑ n ∈ Finset.range (N + 1), Λ n * (n : ℝ)) * d
        ≤ (N * ((Real.log 4 + 4) * N)) * (1 / ((N : ℝ) * ((N : ℝ) + 1))) :=
          mul_le_mul (hsumle.trans (mul_le_mul_of_nonneg_left hpsi hNpos.le)) hd1 hd0 (by positivity)
      _ = (Real.log 4 + 4) * (N / ((N : ℝ) + 1)) := by field_simp
      _ ≤ (Real.log 4 + 4) * 1 := by
          have h4 : 0 ≤ Real.log 4 + 4 := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
          exact mul_le_mul_of_nonneg_left (by rw [div_le_one (by linarith)]; linarith) h4
      _ = Real.log 4 + 4 := mul_one _
  -- fond
  have hB1 := background_sub_half_le hx1
  have hB2 := background_sub_half_le hM1
  have hhalf : ‖(x : ℂ) / 2 - (((N + 1 : ℕ) : ℝ) : ℂ) / 2‖ ≤ 1 / 2 := by
    rw [← sub_div, ← Complex.ofReal_sub, norm_div, Complex.norm_real, Real.norm_eq_abs]
    have : |x - ((N + 1 : ℕ) : ℝ)| ≤ 1 := by
      push_cast; rw [abs_le]; constructor <;> linarith
    simpa using div_le_div_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ ‖(2 : ℂ)‖)
  have heq : smoothedRemainder x - smoothedRemainder ((N + 1 : ℕ) : ℝ) =
      (smoothedVonMangoldtSum x - smoothedVonMangoldtSum ((N + 1 : ℕ) : ℝ)) -
        ((x : ℂ) / 2 - (((N + 1 : ℕ) : ℝ) : ℂ) / 2) -
        (smoothedZeroBackground x - (x : ℂ) / 2) +
        (smoothedZeroBackground ((N + 1 : ℕ) : ℝ) - (((N + 1 : ℕ) : ℝ) : ℂ) / 2) := by
    unfold smoothedRemainder; ring
  rw [heq]
  unfold coverConst
  calc _ ≤ ‖(smoothedVonMangoldtSum x - smoothedVonMangoldtSum ((N + 1 : ℕ) : ℝ)) -
          ((x : ℂ) / 2 - (((N + 1 : ℕ) : ℝ) : ℂ) / 2) - (smoothedZeroBackground x - (x : ℂ) / 2)‖ +
        ‖smoothedZeroBackground ((N + 1 : ℕ) : ℝ) - (((N + 1 : ℕ) : ℝ) : ℂ) / 2‖ := norm_add_le _ _
    _ ≤ (‖smoothedVonMangoldtSum x - smoothedVonMangoldtSum ((N + 1 : ℕ) : ℝ)‖ +
          ‖(x : ℂ) / 2 - (((N + 1 : ℕ) : ℝ) : ℂ) / 2‖ + ‖smoothedZeroBackground x - (x : ℂ) / 2‖) +
        ‖smoothedZeroBackground ((N + 1 : ℕ) : ℝ) - (((N + 1 : ℕ) : ℝ) : ℂ) / 2‖ := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (Real.log 4 + 4 + 1 / 2 + backgroundConst) + backgroundConst := by gcongr
    _ = _ := by ring

/-- **Composition des blocs et de la couverture** (constantes explicites). -/
theorem remainder_growth_of_blocks {θ C : ℝ}
    (hBlock : ∀ N : ℕ, 2 ≤ N → |primeMass N - (N : ℝ) ^ 2 / 2| ≤ C * (N : ℝ) ^ (1 + θ)) :
    ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤
      (max C 0 * 2 ^ max θ 0 + backgroundConst + coverConst) * x ^ max θ 0 := by
  intro x hx
  set θ' := max θ 0
  have hθ' : 0 ≤ θ' := le_max_right _ _
  have hx0 : 0 < x := by linarith
  set N := ⌈x⌉₊ - 1 with hNdef
  have hceil1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hceil2 : 2 ≤ ⌈x⌉₊ := by
    have : (1 : ℝ) < ⌈x⌉₊ := lt_of_lt_of_le hx (Nat.le_ceil x)
    exact_mod_cast this
  have hN1 : 1 ≤ N := by omega
  have hNc : N + 1 = ⌈x⌉₊ := by omega
  have hxN : (N : ℝ) < x := by
    have := Nat.ceil_lt_add_one hx0.le
    have h' : ((N + 1 : ℕ) : ℝ) < x + 1 := by rw [hNc]; exact this
    push_cast at h'; linarith
  have hxN' : x ≤ (N : ℝ) + 1 := by
    have := Nat.le_ceil x
    have h' : x ≤ ((N + 1 : ℕ) : ℝ) := by rw [hNc]; exact this
    push_cast at h'; exact h'
  have hM : 2 ≤ N + 1 := by omega
  set M : ℝ := ((N + 1 : ℕ) : ℝ)
  have hMpos : (0 : ℝ) < M := by positivity
  have hMx : M ≤ 2 * x := by
    simp only [M]; push_cast
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    linarith
  have hMge : x ≤ M := by simp only [M]; push_cast; exact hxN'
  -- bloc au point entier M
  have hRM : ‖smoothedRemainder M‖ ≤ max C 0 * M ^ θ + backgroundConst := by
    refine (remainder_natCast_le hM).trans (add_le_add ?_ le_rfl)
    rw [div_le_iff₀ hMpos]
    calc |primeMass (N + 1) - ((N + 1 : ℕ) : ℝ) ^ 2 / 2| ≤ C * M ^ (1 + θ) := hBlock _ hM
      _ ≤ max C 0 * M ^ (1 + θ) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = max C 0 * M ^ θ * M := by rw [Real.rpow_add hMpos, Real.rpow_one]; ring
  have hcov := remainder_cover hN1 hxN hxN'
  have hpow : M ^ θ ≤ 2 ^ θ' * x ^ θ' := by
    have h1 : M ^ θ ≤ M ^ θ' := by
      have hM1 : (1 : ℝ) ≤ M := by simp only [M]; push_cast; linarith
      exact Real.rpow_le_rpow_of_exponent_le hM1 (le_max_left _ _)
    have h2 : M ^ θ' ≤ (2 * x) ^ θ' := Real.rpow_le_rpow hMpos.le hMx hθ'
    rw [Real.mul_rpow (by norm_num) hx0.le] at h2
    linarith
  have hx1 : 1 ≤ x ^ θ' := Real.one_le_rpow hx.le hθ'
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hB0 := backgroundConst_nonneg
  have hD0 : 0 ≤ coverConst := by
    unfold coverConst
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  calc ‖smoothedRemainder x‖ ≤ ‖smoothedRemainder M‖ + ‖smoothedRemainder x - smoothedRemainder M‖ := by
        simpa using norm_add_le (smoothedRemainder M) (smoothedRemainder x - smoothedRemainder M)
    _ ≤ (max C 0 * M ^ θ + backgroundConst) + coverConst := add_le_add hRM hcov
    _ ≤ max C 0 * (2 ^ θ' * x ^ θ') + backgroundConst * x ^ θ' + coverConst * x ^ θ' := by
        gcongr
        · exact le_mul_of_one_le_right hB0 hx1
        · exact le_mul_of_one_le_right hD0 hx1
    _ = _ := by ring

/-- **Blocs, exposant 1 (démontré)** : `|primeMass N − N²/2| ≤ (log 4 + 5)·N²` (Chebyshev). -/
theorem primeMass_block_linear (N : ℕ) :
    |primeMass N - (N : ℝ) ^ 2 / 2| ≤ (Real.log 4 + 5) * (N : ℝ) ^ (1 + (1 : ℝ)) := by
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hpos : 0 ≤ primeMass N := Finset.sum_nonneg fun n hn => mul_nonneg vonMangoldt_nonneg (by
    have : (n : ℝ) < N := by exact_mod_cast Finset.mem_range.mp hn
    linarith)
  have hle : primeMass N ≤ (Real.log 4 + 4) * (N : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [primeMass]
    have hN' : N = (N - 1) + 1 := by omega
    calc primeMass N ≤ ∑ n ∈ Finset.range N, Λ n * (N : ℝ) := Finset.sum_le_sum fun n _ =>
          mul_le_mul_of_nonneg_left (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) vonMangoldt_nonneg
      _ = (N : ℝ) * ∑ n ∈ Finset.range N, Λ n := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ ≤ (N : ℝ) * Chebyshev.psi N := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          rw [← sum_range_succ_vonMangoldt_eq_psi]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.le_succ N))
            fun _ _ _ => vonMangoldt_nonneg
      _ ≤ (N : ℝ) * ((Real.log 4 + 4) * N) :=
          mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      _ = (Real.log 4 + 4) * (N : ℝ) ^ 2 := by ring
  have hsq : (N : ℝ) ^ (1 + (1 : ℝ)) = (N : ℝ) ^ 2 := by norm_num
  rw [hsq, abs_le]
  have hN2 : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
  constructor <;> nlinarith

/-- **Fermeture par les blocs** : une estimation de blocs d'exposant `θ < 1 − β_z`, avec `β_z < 1/2`, contredit `β_z`. -/
theorem mirror_closes_of_blocks (z : TrueZero) (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (h : ∃ θ C : ℝ, θ < 1 - rZeroRadialPosition z.1 ∧
      ∀ N : ℕ, 2 ≤ N → |primeMass N - (N : ℝ) ^ 2 / 2| ≤ C * (N : ℝ) ^ (1 + θ)) : False := by
  obtain ⟨θ, C, hθ, hB⟩ := h
  exact mirror_closes_of_remainder_growth z ⟨max θ 0, _, max_lt hθ (by linarith),
    remainder_growth_of_blocks hB⟩

#print axioms remainder_cover
#print axioms remainder_growth_of_blocks
#print axioms primeMass_block_linear
#print axioms mirror_closes_of_blocks

end RHV6Fresh
