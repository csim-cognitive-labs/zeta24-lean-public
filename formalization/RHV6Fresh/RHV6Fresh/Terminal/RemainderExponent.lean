/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ClosureRoutes
import Mathlib.NumberTheory.Chebyshev

/-!
# RHV6Fresh — l'exposant du reste lissé, encadré depuis les premiers (E153, auteur, 2026-10-02)

Correction de portée de E152 (audit de l'auteur) : la route compilée est `Λ → reste lissé de ψ → θ → β → D` ;
`Li` n'y figure pas. Ce fichier instancie le pont sans aucune hypothèse, depuis les seuls premiers.

* **Extrémité θ = 1, depuis les premiers** (§1) : `Λ ≥ 0` place la somme lissée entre `0` et `ψ(x)`
  (`smoothedVonMangoldtSum_norm_le_psi`) ; la borne de Chebyshev `ψ(x) ≤ (log 4 + 4)·x` (Mathlib) et le fond
  (terme `x/2`, deux constantes, zéros triviaux bornés par `Σ 1/(n+1)²`, `trivialZeroResidueTerm_norm_le`) donnent
  `‖A(x)‖ ≤ C·x` (`smoothedRemainder_linear_growth`). Par le pont : bande fermée `0 ≤ β ≤ 1`, `|D| ≤ 1`
  (`radial_strip_from_primes`, `radial_transport_le_one_from_primes`).
* **L'exposant critique comme un seul nombre** (§2) : `remainderExponent` = borne inférieure des exposants de
  croissance admissibles ; `1/2 ≤ θ* ≤ 1` sans condition (`remainderExponent_mem_bracket`) ; RH ⟺ `θ* = 1/2`
  (`riemannHypothesis_iff_remainderExponent_eq_half`).
* **Anti-compensation** (§3) : sous une borne d'exposant `θ`, `max(β, 1 − β) ≤ θ` pour tout membre
  (`mirror_pair_exponent_le`). La raison est la lecture du pôle par Mellin (`cpow_series_growth_fibre_zero`) :
  chaque exposant est lu séparément, aucun coefficient d'un autre membre ne l'annule. L'inégalité du paquet nu
  `x^β + x^{1−β} ≥ 2√x` (`pair_amplitude_ge_critical`) ne porte pas les coefficients `m/(ρ(ρ+1))` ni les phases ;
  elle n'est pas l'argument d'anti-compensation.
* **Audit de la positivité** (§4) : le poids du monde témoin `Λ(n)(n^δ + n^{−δ})` est positif et majore `2Λ(n)`
  (`shiftedWorld_weight_ge`) ; il égale le poids de `ζ²` ⟺ `δ = 0` (`shiftedWorld_weight_eq_iff`). La positivité est
  vraie dans tout monde témoin, dont les membres sont à `1/2 ± δ` (`shiftedWorld_pair_off`) : elle ne peut pas porter
  `θ* = 1/2`. Seule la taille exacte du poids sépare.

Borne : l'extrémité obtenue (`β ∈ [0, 1]`) est plus faible que la bande ouverte connue ; `Λ ≥ 0` ne donne que
l'exposant `1` ; `θ* < 1` n'est pas dérivé. Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction

/-! ## 1. Extrémité θ = 1, depuis les premiers -/

/-- **Positivité de `Λ`** : la somme lissée `Σ_{n<x} Λ(n)(1 − n/x)` est de norme au plus `ψ(x)`. -/
theorem smoothedVonMangoldtSum_norm_le_psi {x : ℝ} (hx : 0 < x) :
    ‖smoothedVonMangoldtSum x‖ ≤ Chebyshev.psi x := by
  unfold smoothedVonMangoldtSum
  calc ‖∑ n ∈ Finset.range ⌈x⌉₊, (Λ n : ℂ) * (1 - (n : ℂ) / (x : ℂ))‖
      ≤ ∑ n ∈ Finset.range ⌈x⌉₊, ‖(Λ n : ℂ) * (1 - (n : ℂ) / (x : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range ⌈x⌉₊, Λ n := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hnx : (n : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
        have hc : (1 - (n : ℂ) / (x : ℂ)) = ((1 - n / x : ℝ) : ℂ) := by push_cast; ring
        have h0 : 0 ≤ 1 - n / x := by rw [sub_nonneg, div_le_one hx]; exact hnx.le
        have h1 : 1 - n / x ≤ 1 := by
          have : 0 ≤ (n : ℝ) / x := by positivity
          linarith
        rw [hc, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg vonMangoldt_nonneg, abs_of_nonneg h0]
        exact mul_le_of_le_one_right vonMangoldt_nonneg h1
    _ ≤ ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun _ _ _ => vonMangoldt_nonneg
        rw [Finset.mem_range] at hn
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor (Nat.lt_ceil.mp hn).le⟩
    _ = Chebyshev.psi x := (Chebyshev.psi_eq_sum_Icc x).symm

/-- Le terme d'un zéro trivial est borné par `1/(n+1)²`, uniformément en `x > 1`. -/
theorem trivialZeroResidueTerm_norm_le {x : ℝ} (hx : 1 < x) (n : ℕ) :
    ‖trivialZeroResidueTerm x n‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  have hx0 : 0 < x := lt_trans one_pos hx
  rw [trivial_zero_residue_term_eq hx, norm_neg]
  have hden : trivialZetaZeroAt n * (trivialZetaZeroAt n + 1) =
      (((2 * ((n : ℝ) + 1)) * (2 * (n : ℝ) + 1) : ℝ) : ℂ) := by
    simp only [trivialZetaZeroAt]; push_cast; ring
  have hre : (trivialZetaZeroAt n).re = -(2 * ((n : ℝ) + 1)) := by
    simp [trivialZetaZeroAt]
  have hpow : x ^ (-(2 * ((n : ℝ) + 1))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx.le (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : ((n : ℝ) + 1) ^ 2 ≤ (2 * ((n : ℝ) + 1)) * (2 * (n : ℝ) + 1) := by nlinarith
  have hdpos : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  show ‖(x : ℂ) ^ trivialZetaZeroAt n / (trivialZetaZeroAt n * (trivialZetaZeroAt n + 1))‖ ≤ _
  rw [norm_div, hden, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
  calc x ^ (-(2 * ((n : ℝ) + 1))) / ((2 * ((n : ℝ) + 1)) * (2 * (n : ℝ) + 1))
      ≤ 1 / ((2 * ((n : ℝ) + 1)) * (2 * (n : ℝ) + 1)) :=
        div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ 1 / ((n : ℝ) + 1) ^ 2 := one_div_le_one_div_of_le hdpos hd

theorem summable_one_div_succ_sq : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa [Nat.cast_add, Nat.cast_one] using this

/-- La somme des zéros triviaux est bornée uniformément en `x > 1`. -/
theorem trivialZeroSum_norm_le {x : ℝ} (hx : 1 < x) :
    ‖∑' n : ℕ, trivialZeroResidueTerm x n‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
  have hs : Summable fun n : ℕ => ‖trivialZeroResidueTerm x n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (trivialZeroResidueTerm_norm_le hx)
      summable_one_div_succ_sq
  exact (norm_tsum_le_tsum_norm hs).trans
    (hs.tsum_le_tsum (trivialZeroResidueTerm_norm_le hx) summable_one_div_succ_sq)

/-- **Le pont instancié depuis les premiers** : `‖A(x)‖ ≤ C·x` pour tout `x > 1`, par `Λ ≥ 0` et Chebyshev. -/
theorem smoothedRemainder_linear_growth :
    ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 : ℝ) := by
  set c₀ := ‖-logDeriv riemannZeta 0‖
  set c₁ := ‖logDeriv riemannZeta (-1)‖
  set K := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2
  refine ⟨(Real.log 4 + 4) + 1 / 2 + c₀ + c₁ + K, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_trans one_pos hx
  have hK : 0 ≤ K := tsum_nonneg fun n => by positivity
  have hS := (smoothedVonMangoldtSum_norm_le_psi hx0).trans (Chebyshev.psi_le_const_mul_self hx0.le)
  have hT := trivialZeroSum_norm_le hx
  have hx2 : ‖(x : ℂ) / 2‖ = x / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; norm_num
  have hinv : ‖logDeriv riemannZeta (-1) * (x : ℂ)⁻¹‖ ≤ c₁ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    have hc₁ : 0 ≤ c₁ := norm_nonneg _
    calc c₁ * x⁻¹ ≤ c₁ * 1 := mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hx.le) hc₁
      _ = c₁ := mul_one _
  have hB : ‖smoothedZeroBackground x‖ ≤ x / 2 + c₀ + c₁ + K := by
    unfold smoothedZeroBackground
    calc _ ≤ ‖(x : ℂ) / 2 + (-logDeriv riemannZeta 0) + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹‖ +
          ‖∑' n : ℕ, trivialZeroResidueTerm x n‖ := norm_add_le _ _
      _ ≤ (‖(x : ℂ) / 2 + (-logDeriv riemannZeta 0)‖ + ‖logDeriv riemannZeta (-1) * (x : ℂ)⁻¹‖) +
          ‖∑' n : ℕ, trivialZeroResidueTerm x n‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖(x : ℂ) / 2‖ + c₀) + c₁) + K := by gcongr; exact norm_add_le _ _
      _ = x / 2 + c₀ + c₁ + K := by rw [hx2]
  have hc₀ : 0 ≤ c₀ := norm_nonneg _
  have hc₁ : 0 ≤ c₁ := norm_nonneg _
  rw [Real.rpow_one]
  unfold smoothedRemainder
  calc ‖smoothedVonMangoldtSum x - smoothedZeroBackground x‖
      ≤ ‖smoothedVonMangoldtSum x‖ + ‖smoothedZeroBackground x‖ := norm_sub_le _ _
    _ ≤ (Real.log 4 + 4) * x + (x / 2 + c₀ + c₁ + K) := add_le_add hS hB
    _ ≤ ((Real.log 4 + 4) + 1 / 2 + c₀ + c₁ + K) * x := by
        have : c₀ + c₁ + K ≤ (c₀ + c₁ + K) * x := le_mul_of_one_le_right (by positivity) hx.le
        nlinarith

/-- **Bande fermée depuis les premiers** : tout membre a `0 ≤ β ≤ 1`, par le pont à `θ = 1`. -/
theorem radial_strip_from_primes (z : TrueZero) :
    0 ≤ rZeroRadialPosition z.1 ∧ rZeroRadialPosition z.1 ≤ 1 := by
  obtain ⟨C, hC⟩ := smoothedRemainder_linear_growth
  have := radial_strip_of_remainder_growth hC z
  exact ⟨by linarith [this.1], this.2⟩

/-- **Transport radial borné depuis les premiers** : `|β_l − β_e| ≤ 1` pour tout couple. -/
theorem radial_transport_le_one_from_primes (e l : TrueZero) :
    |rZeroRadialPosition l.1 - rZeroRadialPosition e.1| ≤ 1 := by
  obtain ⟨C, hC⟩ := smoothedRemainder_linear_growth
  have := radial_transport_le_of_remainder_growth hC e l
  linarith

/-! ## 2. L'exposant critique comme un seul nombre -/

/-- Les exposants de croissance admissibles du reste lissé. -/
def remainderExponents : Set ℝ :=
  {θ | ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ θ}

/-- **L'exposant du reste** `θ*` : borne inférieure des exposants admissibles. -/
noncomputable def remainderExponent : ℝ := sInf remainderExponents

theorem remainderExponents_bddBelow : BddBelow remainderExponents :=
  ⟨1 / 2, fun _ ⟨_, hC⟩ => remainder_exponent_ge_half hC⟩

theorem one_mem_remainderExponents : (1 : ℝ) ∈ remainderExponents :=
  smoothedRemainder_linear_growth

/-- **Encadrement sans condition** : `1/2 ≤ θ* ≤ 1`, l'extrémité haute depuis les premiers seuls. -/
theorem remainderExponent_mem_bracket : 1 / 2 ≤ remainderExponent ∧ remainderExponent ≤ 1 :=
  ⟨le_csInf ⟨1, one_mem_remainderExponents⟩ fun _ ⟨_, hC⟩ => remainder_exponent_ge_half hC,
    csInf_le remainderExponents_bddBelow one_mem_remainderExponents⟩

/-- Un exposant admissible reste admissible au-dessus. -/
theorem remainderExponents_mono {θ θ' : ℝ} (h : θ ∈ remainderExponents) (hle : θ ≤ θ') :
    θ' ∈ remainderExponents := by
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := by
    have h2 := hC 2 (by norm_num)
    have hp : 0 < (2 : ℝ) ^ θ := Real.rpow_pos_of_pos (by norm_num) _
    by_contra hneg
    push Not at hneg
    have : C * (2 : ℝ) ^ θ < 0 := mul_neg_of_neg_of_pos hneg hp
    linarith [norm_nonneg (smoothedRemainder 2)]
  exact ⟨C, fun x hx => (hC x hx).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx.le hle) hC0)⟩

/-- **RH ⟺ `θ* = 1/2`** : la cible écrite comme la valeur d'un seul nombre défini par les premiers. -/
theorem riemannHypothesis_iff_remainderExponent_eq_half :
    RiemannHypothesis ↔ remainderExponent = 1 / 2 := by
  constructor
  · intro hRH
    obtain ⟨C, hC⟩ := remainder_sqrt_growth_of_riemannHypothesis hRH
    exact le_antisymm (csInf_le remainderExponents_bddBelow ⟨C, hC⟩) remainderExponent_mem_bracket.1
  · intro h
    refine riemannHypothesis_iff_remainder_growth_all_eps.mpr fun ε hε => ?_
    have hlt : remainderExponent < 1 / 2 + ε := by linarith
    obtain ⟨θ, hθ, hθlt⟩ := exists_lt_of_csInf_lt ⟨1, one_mem_remainderExponents⟩ hlt
    exact remainderExponents_mono hθ hθlt.le

/-! ## 3. Anti-compensation : chaque exposant est lu séparément -/

/-- **Aucune compensation dans la paire miroir** : sous une borne d'exposant `θ`, l'exposant le plus haut de la
paire `{β, 1 − β}` ne dépasse pas `θ`. L'argument est la lecture du pôle (Mellin) exposant par exposant. -/
theorem mirror_pair_exponent_le {θ C : ℝ}
    (h : ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ θ) (z : TrueZero) :
    max (rZeroRadialPosition z.1) (1 - rZeroRadialPosition z.1) ≤ θ := by
  have := radial_strip_of_remainder_growth h z
  exact max_le this.2 (by linarith [this.1])

/-- **Paire miroir sous `θ*`** : la paire miroir de tout membre a son exposant le plus haut au plus `θ*`. -/
theorem mirror_pair_exponent_le_remainderExponent (z : TrueZero) :
    max (rZeroRadialPosition z.1) (1 - rZeroRadialPosition z.1) ≤ remainderExponent := by
  refine le_of_forall_gt_imp_ge_of_dense fun t ht => ?_
  obtain ⟨θ, ⟨C, hC⟩, hθlt⟩ := exists_lt_of_csInf_lt ⟨1, one_mem_remainderExponents⟩ ht
  exact (mirror_pair_exponent_le hC z).trans hθlt.le

/-! ## 4. Audit de la positivité : partagée par le monde témoin -/

/-- **La positivité est partagée** : le poids du monde témoin `Λ(n)(n^δ + n^{−δ})` est positif et majore
`2Λ(n)`, le poids de `ζ²` (même monde à `δ = 0`), pour tout `δ` réel. -/
theorem shiftedWorld_weight_ge (d : ℝ) (n : ℕ) :
    0 ≤ 2 * Λ n ∧ 2 * Λ n ≤ Λ n * ((n : ℝ) ^ d + (n : ℝ) ^ (-d)) := by
  have hΛ : 0 ≤ Λ n := vonMangoldt_nonneg
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set a := (n : ℝ) ^ d with ha
  have hapos : 0 < a := Real.rpow_pos_of_pos hn0 d
  have hinv : (n : ℝ) ^ (-d) = a⁻¹ := Real.rpow_neg hn0.le d
  rw [hinv]
  have h2 : 2 ≤ a + a⁻¹ := by
    have : a + a⁻¹ - 2 = (a - 1) ^ 2 / a := by field_simp; ring
    have : 0 ≤ (a - 1) ^ 2 / a := by positivity
    linarith
  nlinarith

/-- **Le poids exact sépare** : sur une puissance de premier `n ≥ 2`, le poids du monde témoin égale celui de `ζ²`
exactement quand `δ = 0`. Seule la taille exacte du poids distingue les mondes ; son signe ne les distingue pas. -/
theorem shiftedWorld_weight_eq_iff (d : ℝ) {n : ℕ} (hn : 2 ≤ n) (hΛ : Λ n ≠ 0) :
    Λ n * ((n : ℝ) ^ d + (n : ℝ) ^ (-d)) = 2 * Λ n ↔ d = 0 := by
  have hn0 : (1 : ℝ) < n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_trans one_pos hn0
  constructor
  · intro h
    set a := (n : ℝ) ^ d with ha
    have hapos : 0 < a := Real.rpow_pos_of_pos hnpos d
    rw [Real.rpow_neg hnpos.le d, ← ha] at h
    have hsum : a + a⁻¹ = 2 := by
      have := mul_left_cancel₀ hΛ (h.trans (mul_comm 2 (Λ n)))
      exact this
    have ha1 : a = 1 := by
      have : (a - 1) ^ 2 = 0 := by
        have : (a - 1) ^ 2 = a * (a + a⁻¹ - 2) := by field_simp; ring
        rw [this, hsum, sub_self, mul_zero]
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    have hl : d * Real.log n = 0 := by rw [← Real.log_rpow hnpos, ← ha, ha1, Real.log_one]
    exact (mul_eq_zero.mp hl).resolve_right (Real.log_pos hn0).ne'
  · rintro rfl
    simp only [neg_zero, Real.rpow_zero]
    ring

#print axioms smoothedVonMangoldtSum_norm_le_psi
#print axioms trivialZeroResidueTerm_norm_le
#print axioms summable_one_div_succ_sq
#print axioms trivialZeroSum_norm_le
#print axioms smoothedRemainder_linear_growth
#print axioms radial_strip_from_primes
#print axioms radial_transport_le_one_from_primes
#print axioms remainderExponents_bddBelow
#print axioms one_mem_remainderExponents
#print axioms remainderExponent_mem_bracket
#print axioms remainderExponents_mono
#print axioms riemannHypothesis_iff_remainderExponent_eq_half
#print axioms mirror_pair_exponent_le
#print axioms mirror_pair_exponent_le_remainderExponent
#print axioms shiftedWorld_weight_ge
#print axioms shiftedWorld_weight_eq_iff

end RHV6Fresh
