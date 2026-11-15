/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PrimeBlockDecomposition
import RHV6Fresh.Grammar.Mod6Rigidity

/-!
# La masse première d'un bloc par les quatre transitions grammaticales (auteur, 2026-10-11, prompt 2)

Sur le but de blocs `|primeMass N − N²/2| ≤ C·N^{1+θ}` (`Terminal/PrimeBlockDecomposition.lean`) :

* §1 décomposition EXACTE `primeMass = primePart + powerPart` (premiers / puissances de premiers, `Λ` conservé) ;
  `0 ≤ powerPart N ≤ 2·N^{3/2} log N` (Mathlib, `ψ − ϑ`) : la part des puissances est sous tout exposant `> 1/2`
  (`powerPart_le`) ;
* §2 décomposition EXACTE de `primePart` par les quatre transitions `(état de p, état du premier suivant)`, `A = 6k − 1`,
  `B = 6k + 1`, avec le terme de bord `p ∈ {2, 3}` (`primePart_four_transitions`) : magnitudes `log p`, poids `N − p`,
  extrémités conservées ; chaque somme de transition est `≥ 0` ;
* §3 ce que la grammaire borne EFFECTIVEMENT : les premiers `> 3` sont dans deux états (densité `1/3` des entiers), donc
  `primePart N ≤ 2N log 3 + N log N·(N/3 + 2)` (`primePart_grammar_upper`) : une majoration UNILATÉRALE d'exposant `1`
  avec perte logarithmique, plus faible que Chebyshev ; AUCUNE minoration ; une avance minimale des premiers n'est pas une
  réduction du terme signé ;
* §4 composition : la part des puissances étant démontrée, le but de blocs se réduit au terme signé des seuls premiers
  `|primePart N − N²/2| ≤ C·N^{1+θ}` (`mirror_closes_of_prime_blocks`).
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction

/-! ## 1. Premiers et puissances -/

/-- Part des premiers : `Σ_{p<N premier} log p·(N − p)`. -/
noncomputable def primePart (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range N).filter Nat.Prime, Λ n * ((N : ℝ) - n)

/-- Part des puissances de premiers (et de `Λ = 0` ailleurs) : `Σ_{n<N non premier} Λ(n)(N − n)`. -/
noncomputable def powerPart (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range N).filter (fun n => ¬ n.Prime), Λ n * ((N : ℝ) - n)

theorem primeMass_split (N : ℕ) : primeMass N = primePart N + powerPart N := by
  unfold primeMass primePart powerPart
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem weight_nonneg_of_lt {N n : ℕ} (hn : n ∈ Finset.range N) : 0 ≤ Λ n * ((N : ℝ) - n) := by
  have : (n : ℝ) < N := by exact_mod_cast Finset.mem_range.mp hn
  exact mul_nonneg vonMangoldt_nonneg (by linarith)

/-- `Σ_{n ≤ N non premier} Λ(n) = ψ(N) − ϑ(N)`. -/
theorem sum_nonprime_vonMangoldt_eq (N : ℕ) :
    ∑ n ∈ (Finset.range (N + 1)).filter (fun n => ¬ n.Prime), Λ n =
      Chebyshev.psi N - Chebyshev.theta N := by
  have hθ : ∑ n ∈ (Finset.range (N + 1)).filter Nat.Prime, Λ n = Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
    have hset : (Finset.range (N + 1)).filter Nat.Prime = (Finset.Icc 0 N).filter Nat.Prime := by
      ext n; simp [Finset.mem_range, Finset.mem_Icc]
    rw [hset]
    exact Finset.sum_congr rfl fun n hn => vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2
  have h := Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1)) Nat.Prime (fun n => Λ n)
  rw [sum_range_succ_vonMangoldt_eq_psi, hθ] at h
  linarith

theorem powerPart_nonneg (N : ℕ) : 0 ≤ powerPart N :=
  Finset.sum_nonneg fun n hn => weight_nonneg_of_lt (Finset.mem_filter.mp hn).1

/-- **Puissances de premiers, démontré** : `powerPart N ≤ 2·N·√N·log N`. -/
theorem powerPart_le {N : ℕ} (hN : 1 ≤ N) :
    powerPart N ≤ 2 * (N : ℝ) * Real.sqrt N * Real.log N := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : powerPart N ≤ (N : ℝ) * ∑ n ∈ (Finset.range (N + 1)).filter (fun n => ¬ n.Prime), Λ n := by
    unfold powerPart
    rw [Finset.mul_sum]
    calc ∑ n ∈ (Finset.range N).filter (fun n => ¬ n.Prime), Λ n * ((N : ℝ) - n)
        ≤ ∑ n ∈ (Finset.range N).filter (fun n => ¬ n.Prime), (N : ℝ) * Λ n :=
          Finset.sum_le_sum fun n _ => by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
              vonMangoldt_nonneg
      _ ≤ ∑ n ∈ (Finset.range (N + 1)).filter (fun n => ¬ n.Prime), (N : ℝ) * Λ n :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr (Nat.le_succ N)))
            fun _ _ _ => mul_nonneg hN0 vonMangoldt_nonneg
  rw [sum_nonprime_vonMangoldt_eq] at h1
  have h2 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := (N : ℝ)) (by exact_mod_cast hN)
  have h3 : Chebyshev.psi N - Chebyshev.theta N ≤ 2 * Real.sqrt N * Real.log N := (le_abs_self _).trans h2
  calc powerPart N ≤ (N : ℝ) * (Chebyshev.psi N - Chebyshev.theta N) := h1
    _ ≤ (N : ℝ) * (2 * Real.sqrt N * Real.log N) := mul_le_mul_of_nonneg_left h3 hN0
    _ = _ := by ring

/-! ## 2. Les quatre transitions -/

/-- Premier suivant `p` : le premier de rang `count(p) + 1`. -/
noncomputable def nextPrimeOf (p : ℕ) : ℕ := fnPrimeAtRank (Nat.count Nat.Prime p + 1)

/-- Transition d'un premier : `(état de p, état du suivant)`, `false = A (6k − 1)`, `true = B (6k + 1)`.
`(A,A)`, `(A,B)`, `(B,A)`, `(B,B)` : les quatre transitions. -/
noncomputable def transitionOf (p : ℕ) : Bool × Bool := (state6 p, state6 (nextPrimeOf p))

/-- Somme d'une transition `τ` : `Σ_{3<p<N premier, transition τ} log p·(N − p)`. -/
noncomputable def transitionSum (N : ℕ) (τ : Bool × Bool) : ℝ :=
  ∑ n ∈ ((Finset.range N).filter Nat.Prime).filter (fun p => 3 < p ∧ transitionOf p = τ), Λ n * ((N : ℝ) - n)

/-- Terme de bord : `p ∈ {2, 3}`. -/
noncomputable def boundaryPart (N : ℕ) : ℝ :=
  ∑ n ∈ ((Finset.range N).filter Nat.Prime).filter (fun p => ¬ 3 < p), Λ n * ((N : ℝ) - n)

/-- **Décomposition exacte par les quatre transitions** (bord compris). -/
theorem primePart_four_transitions (N : ℕ) :
    primePart N = boundaryPart N + ∑ τ : Bool × Bool, transitionSum N τ := by
  unfold primePart boundaryPart transitionSum
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.range N).filter Nat.Prime) (fun p => 3 < p), add_comm]
  congr 1
  rw [← Finset.sum_fiberwise ((((Finset.range N).filter Nat.Prime).filter (fun p => 3 < p)))
    transitionOf (fun n => Λ n * ((N : ℝ) - n))]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.filter_filter]

theorem transitionSum_nonneg (N : ℕ) (τ : Bool × Bool) : 0 ≤ transitionSum N τ :=
  Finset.sum_nonneg fun n hn =>
    weight_nonneg_of_lt (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1

theorem boundaryPart_nonneg (N : ℕ) : 0 ≤ boundaryPart N :=
  Finset.sum_nonneg fun n hn =>
    weight_nonneg_of_lt (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1

/-! ## 3. Ce que les états bornent -/

/-- Les entiers `< N` dans les deux états mod 6 sont au plus `2(N/6 + 1)`. -/
theorem card_goodMod6_le (N : ℕ) :
    ((Finset.range N).filter (fun n => n % 6 = 1 ∨ n % 6 = 5)).card ≤ 2 * (N / 6 + 1) := by
  have hinj : Set.InjOn (fun n => (n / 6, decide (n % 6 = 1)))
      ((Finset.range N).filter (fun n => n % 6 = 1 ∨ n % 6 = 5) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Prod.mk.injEq] at ha hb hab
    obtain ⟨h1, h2⟩ := hab
    have : a % 6 = b % 6 := by
      rcases ha.2 with ha' | ha' <;> rcases hb.2 with hb' | hb' <;> simp_all
    omega
  have hmaps : ∀ n ∈ (Finset.range N).filter (fun n => n % 6 = 1 ∨ n % 6 = 5),
      (fun n => (n / 6, decide (n % 6 = 1))) n ∈ (Finset.range (N / 6 + 1)) ×ˢ (Finset.univ : Finset Bool) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
    have : n / 6 ≤ N / 6 := Nat.div_le_div_right hn.1.le
    omega
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  simpa [Finset.card_product, mul_comm] using this

/-- **Majoration unilatérale par les états** : `primePart N ≤ 2N log 3 + N log N·(N/3 + 2)`. -/
theorem primePart_grammar_upper {N : ℕ} (hN : 1 ≤ N) :
    primePart N ≤ 2 * N * Real.log 3 + N * Real.log N * ((N : ℝ) / 3 + 2) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rw [primePart_four_transitions]
  -- bord
  have hB : boundaryPart N ≤ 2 * N * Real.log 3 := by
    unfold boundaryPart
    have hsub : ((Finset.range N).filter Nat.Prime).filter (fun p => ¬ 3 < p) ⊆ {2, 3} := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      have h2 := hn.1.2.two_le
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    calc _ ≤ ∑ n ∈ ((Finset.range N).filter Nat.Prime).filter (fun p => ¬ 3 < p), (N : ℝ) * Real.log 3 :=
          Finset.sum_le_sum fun n hn => by
            simp only [Finset.mem_filter, Finset.mem_range] at hn
            have hn3 : n ≤ 3 := by omega
            have hn1 : 1 ≤ n := hn.1.2.one_lt.le
            rw [vonMangoldt_apply_prime hn.1.2, mul_comm]
            exact mul_le_mul (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
              (Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hn3))
              (Real.log_nonneg (by exact_mod_cast hn1)) hN0
      _ ≤ ∑ n ∈ ({2, 3} : Finset ℕ), (N : ℝ) * Real.log 3 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
            mul_nonneg hN0 (Real.log_nonneg (by norm_num))
      _ = 2 * N * Real.log 3 := by simp; ring
  -- quatre transitions réunies : premiers > 3, dans les deux états
  have hT : ∑ τ : Bool × Bool, transitionSum N τ ≤ N * Real.log N * ((N : ℝ) / 3 + 2) := by
    have hre : ∑ τ : Bool × Bool, transitionSum N τ =
        ∑ n ∈ ((Finset.range N).filter Nat.Prime).filter (fun p => 3 < p), Λ n * ((N : ℝ) - n) := by
      unfold transitionSum
      rw [← Finset.sum_fiberwise ((((Finset.range N).filter Nat.Prime).filter (fun p => 3 < p)))
        transitionOf (fun n => Λ n * ((N : ℝ) - n))]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [Finset.filter_filter, and_assoc]
    rw [hre]
    have hsub : ((Finset.range N).filter Nat.Prime).filter (fun p => 3 < p) ⊆
        (Finset.range N).filter (fun n => n % 6 = 1 ∨ n % 6 = 5) := by
      intro n hn
      simp only [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1.1, prime_goodMod6 n hn.1.2 hn.2⟩
    have hcard : ((((Finset.range N).filter Nat.Prime).filter (fun p => 3 < p)).card : ℝ) ≤ (N : ℝ) / 3 + 2 := by
      have h1 := (Finset.card_le_card hsub).trans (card_goodMod6_le N)
      have h2 : ((2 * (N / 6 + 1) : ℕ) : ℝ) ≤ (N : ℝ) / 3 + 2 := by
        push_cast
        have := Nat.cast_div_le (α := ℝ) (m := N) (n := 6)
        linarith
      exact (Nat.cast_le.mpr h1).trans h2
    calc _ ≤ ∑ n ∈ ((Finset.range N).filter Nat.Prime).filter (fun p => 3 < p), (N : ℝ) * Real.log N :=
          Finset.sum_le_sum fun n hn => by
            simp only [Finset.mem_filter, Finset.mem_range] at hn
            rw [vonMangoldt_apply_prime hn.1.2, mul_comm]
            have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1.2.one_lt.le
            exact mul_le_mul (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
              (Real.log_le_log (by linarith) (by exact_mod_cast hn.1.1.le))
              (Real.log_nonneg hn1) hN0
      _ = (N : ℝ) * Real.log N * ((((Finset.range N).filter Nat.Prime).filter (fun p => 3 < p)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcard (mul_nonneg hN0 hlogN)
  linarith

/-! ## 4. Composition : réduction au terme signé des premiers -/

/-- **Absorption des puissances** : une estimation de blocs des premiers seuls d'exposant `1 + θ` donne une estimation de
blocs de la masse entière d'exposant `1 + max θ η`, pour tout `η > 1/2` (constante explicite). -/
theorem primeMass_blocks_of_prime_blocks {θ C η : ℝ} (hη : 1 / 2 < η)
    (hB : ∀ N : ℕ, 2 ≤ N → |primePart N - (N : ℝ) ^ 2 / 2| ≤ C * (N : ℝ) ^ (1 + θ)) :
    ∀ N : ℕ, 2 ≤ N → |primeMass N - (N : ℝ) ^ 2 / 2| ≤
      (max C 0 + 2 / (η - 1 / 2)) * (N : ℝ) ^ (1 + max θ η) := by
  intro N hN
  set θ'' := max θ η
  set ε := η - 1 / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hsplit := primeMass_split N
  have hP0 := powerPart_nonneg N
  have hPle := powerPart_le (show 1 ≤ N by omega)
  have hlog : Real.log N ≤ (N : ℝ) ^ ε / ε := Real.log_le_rpow_div hN0.le hε
  have hsqrt : Real.sqrt N = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hpow1 : (N : ℝ) ^ (1 + η) = (N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ ε := by
    rw [show (1 : ℝ) + η = 1 + 1 / 2 + ε by simp only [ε]; ring, Real.rpow_add hN0, Real.rpow_add hN0,
      Real.rpow_one]
  have hPow : powerPart N ≤ (2 / ε) * (N : ℝ) ^ (1 + θ'') := by
    have hmono : (N : ℝ) ^ (1 + η) ≤ (N : ℝ) ^ (1 + θ'') :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by simp only [θ'']; linarith [le_max_right θ η])
    have hs0 : 0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hN0.le _
    calc powerPart N ≤ 2 * (N : ℝ) * Real.sqrt N * Real.log N := hPle
      _ ≤ 2 * (N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) * ((N : ℝ) ^ ε / ε) := by
          rw [hsqrt]; exact mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (2 / ε) * (N : ℝ) ^ (1 + η) := by rw [hpow1]; field_simp
      _ ≤ (2 / ε) * (N : ℝ) ^ (1 + θ'') := mul_le_mul_of_nonneg_left hmono (by positivity)
  have hPrime : |primePart N - (N : ℝ) ^ 2 / 2| ≤ max C 0 * (N : ℝ) ^ (1 + θ'') := by
    calc _ ≤ C * (N : ℝ) ^ (1 + θ) := hB N hN
      _ ≤ max C 0 * (N : ℝ) ^ (1 + θ) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * (N : ℝ) ^ (1 + θ'') := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hN1 (by simp only [θ'']; linarith [le_max_left θ η]))
          (le_max_right _ _)
  rw [hsplit, show primePart N + powerPart N - (N : ℝ) ^ 2 / 2 = (primePart N - (N : ℝ) ^ 2 / 2) + powerPart N
    by ring, add_mul]
  refine (abs_add_le _ _).trans (add_le_add hPrime ?_)
  rw [abs_of_nonneg hP0]; exact hPow

/-- **Fermeture par les premiers seuls** : la part des puissances étant démontrée, une estimation
`|primePart N − N²/2| ≤ C·N^{1+θ}` avec `θ < 1 − β_z` contredit `β_z < 1/2`. -/
theorem mirror_closes_of_prime_blocks (z : TrueZero) (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (h : ∃ θ C : ℝ, θ < 1 - rZeroRadialPosition z.1 ∧
      ∀ N : ℕ, 2 ≤ N → |primePart N - (N : ℝ) ^ 2 / 2| ≤ C * (N : ℝ) ^ (1 + θ)) : False := by
  obtain ⟨θ, C, hθ, hB⟩ := h
  set η : ℝ := (1 / 2 + (1 - rZeroRadialPosition z.1)) / 2
  have hη1 : 1 / 2 < η := by simp only [η]; linarith
  have hη2 : η < 1 - rZeroRadialPosition z.1 := by simp only [η]; linarith
  exact mirror_closes_of_blocks z hβ ⟨max θ η, _, max_lt hθ hη2, primeMass_blocks_of_prime_blocks hη1 hB⟩

/-- **Portée du but : une bande sans zéro.** Une estimation de blocs des premiers seuls d'exposant `1 + θ` force TOUT
zéro à une partie réelle `≤ max θ (1/2)`. Avec `θ < 1`, c'est une bande `Re s > max θ (1/2)` sans zéro : le but n'est
pas local au passage, il porte sur tous les zéros à la fois. -/
theorem prime_blocks_zero_free_strip {θ C : ℝ}
    (hB : ∀ N : ℕ, 2 ≤ N → |primePart N - (N : ℝ) ^ 2 / 2| ≤ C * (N : ℝ) ^ (1 + θ)) (w : TrueZero) :
    rZeroRadialPosition w.1 ≤ max θ (1 / 2) := by
  by_contra hlt
  push Not at hlt
  set η : ℝ := (max θ (1 / 2) + rZeroRadialPosition w.1) / 2
  have hη1 : 1 / 2 < η := by simp only [η]; linarith [le_max_right θ (1 / 2)]
  have hηθ : θ ≤ η := by simp only [η]; linarith [le_max_left θ (1 / 2)]
  have hηw : η < rZeroRadialPosition w.1 := by simp only [η]; linarith
  have hmax : max (max θ η) 0 = η := by
    rw [max_eq_right hηθ, max_eq_left (by linarith)]
  have hG := remainder_growth_of_blocks (primeMass_blocks_of_prime_blocks hη1 hB)
  rw [hmax] at hG
  have := radial_le_of_remainder_growth hG w
  linarith

/-! ## 5. Portée exacte du but : caractérisation (aucune dérivation) -/

/-- **Sens réciproque** : si tout zéro a une partie réelle `≤ θ`, le reste lissé est borné par `C·x^θ` (par la
représentation démontrée, absolument convergente). Généralise `remainder_sqrt_growth_of_riemannHypothesis`. -/
theorem remainder_growth_of_zero_free {θ : ℝ} (h : ∀ w : TrueZero, rZeroRadialPosition w.1 ≤ θ) :
    ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ θ := by
  refine ⟨∑' ρ : ExplicitIndex,
    ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_trans one_pos hx
  have hterm : ∀ ρ : ExplicitIndex, ‖nontrivialZeroResidueTerm x ρ‖ ≤
      ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖ * x ^ θ := by
    intro ρ
    have hre : (ρ : ℂ).re ≤ θ := by
      obtain ⟨_, hr⟩ := explicitIndex_upper_readings ρ
      rw [← hr]; exact h _
    change ‖-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
      ((x : ℂ) ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1)))‖ ≤ _
    rw [norm_mul, norm_neg, norm_div, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have h1 : x ^ (ρ : ℂ).re ≤ x ^ θ := Real.rpow_le_rpow_of_exponent_le hx.le hre
    have h2 : 0 ≤ ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ := by positivity
    calc ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ * (x ^ (ρ : ℂ).re / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖)
        = (‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) * x ^ (ρ : ℂ).re := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
  have hsumm : Summable fun ρ : ExplicitIndex => ‖nontrivialZeroResidueTerm x ρ‖ :=
    (nontrivial_zero_residue_series_summable hx).norm
  have hdom : Summable fun ρ : ExplicitIndex =>
      ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖ * x ^ θ :=
    multiplicity_weight_summable.mul_right _
  unfold smoothedRemainder
  rw [← channel_eq_arithmetic hx]
  calc ‖∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm x ρ‖
      ≤ ∑' ρ : ExplicitIndex, ‖nontrivialZeroResidueTerm x ρ‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' ρ : ExplicitIndex,
          ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖ * x ^ θ :=
        hsumm.tsum_le_tsum hterm hdom
    _ = _ := tsum_mul_right

/-- **Sens réciproque, blocs** : zéros sous `θ` (`θ > 1/2`) ⟹ estimation de blocs des premiers seuls d'exposant `1 + θ`. -/
theorem prime_blocks_of_zero_free {θ : ℝ} (hθ : 1 / 2 < θ)
    (h : ∀ w : TrueZero, rZeroRadialPosition w.1 ≤ θ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → |primePart N - (N : ℝ) ^ 2 / 2| ≤ C * (N : ℝ) ^ (1 + θ) := by
  obtain ⟨C, hC⟩ := remainder_growth_of_zero_free h
  set ε := θ - 1 / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  refine ⟨max C 0 + backgroundConst + 2 / ε, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hNθ : 0 ≤ (N : ℝ) ^ θ := Real.rpow_nonneg hN0.le _
  have hpow : (N : ℝ) ^ (1 + θ) = (N : ℝ) * (N : ℝ) ^ θ := by rw [Real.rpow_add hN0, Real.rpow_one]
  -- masse entière : |primeMass N − N²/2| ≤ N(‖R(N)‖ + B₀)
  have hmass : |primeMass N - (N : ℝ) ^ 2 / 2| ≤ (N : ℝ) * (max C 0 * (N : ℝ) ^ θ + backgroundConst) := by
    have hsplit : (((primeMass N - (N : ℝ) ^ 2 / 2) / N : ℝ) : ℂ) =
        smoothedRemainder (N : ℝ) + (smoothedZeroBackground (N : ℝ) - ((N : ℝ) : ℂ) / 2) := by
      unfold smoothedRemainder
      rw [smoothedVonMangoldtSum_natCast (by omega)]
      have : ((primeMass N / N : ℝ) : ℂ) = (((primeMass N - (N : ℝ) ^ 2 / 2) / N : ℝ) : ℂ) + ((N : ℝ) : ℂ) / 2 := by
        push_cast; field_simp; ring
      rw [this]; ring
    have h1 : |primeMass N - (N : ℝ) ^ 2 / 2| / N ≤ max C 0 * (N : ℝ) ^ θ + backgroundConst := by
      have := congrArg norm hsplit
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hN0] at this
      rw [this]
      refine (norm_add_le _ _).trans (add_le_add ?_ (background_sub_half_le hN1))
      exact (hC N hN1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hNθ)
    rwa [div_le_iff₀ hN0, mul_comm] at h1
  have hP0 := powerPart_nonneg N
  have hPle := powerPart_le (show 1 ≤ N by omega)
  have hlog : Real.log N ≤ (N : ℝ) ^ ε / ε := Real.log_le_rpow_div hN0.le hε
  have hsqrt : Real.sqrt N = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hpow1 : (N : ℝ) ^ (1 + θ) = (N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ ε := by
    rw [show (1 : ℝ) + θ = 1 + 1 / 2 + ε by simp only [ε]; ring, Real.rpow_add hN0, Real.rpow_add hN0,
      Real.rpow_one]
  have hPow : powerPart N ≤ (2 / ε) * (N : ℝ) ^ (1 + θ) := by
    calc powerPart N ≤ 2 * (N : ℝ) * Real.sqrt N * Real.log N := hPle
      _ ≤ 2 * (N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) * ((N : ℝ) ^ ε / ε) := by
          rw [hsqrt]; exact mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (2 / ε) * (N : ℝ) ^ (1 + θ) := by rw [hpow1]; field_simp
  have hB1 : backgroundConst ≤ backgroundConst * (N : ℝ) ^ θ :=
    le_mul_of_one_le_right backgroundConst_nonneg (Real.one_le_rpow hN1.le (by linarith))
  have hsplitP : primePart N - (N : ℝ) ^ 2 / 2 = (primeMass N - (N : ℝ) ^ 2 / 2) - powerPart N := by
    rw [primeMass_split]; ring
  rw [hsplitP]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg hP0]
  calc |primeMass N - (N : ℝ) ^ 2 / 2| + powerPart N
      ≤ (N : ℝ) * (max C 0 * (N : ℝ) ^ θ + backgroundConst * (N : ℝ) ^ θ) + (2 / ε) * (N : ℝ) ^ (1 + θ) :=
        add_le_add (hmass.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hB1) hN0.le)) hPow
      _ = (max C 0 + backgroundConst + 2 / ε) * (N : ℝ) ^ (1 + θ) := by rw [hpow]; ring

/-- **Caractérisation exacte du but de la transmission** (`θ > 1/2`) : l'estimation de blocs des premiers seuls
d'exposant `1 + θ` ⟺ tout zéro a une partie réelle `≤ θ` (demi-plan `Re s > θ` sans zéro). Ni l'un ni l'autre n'est
dérivé ici : le but porte sur tous les zéros à la fois. -/
theorem prime_blocks_iff_zero_free {θ : ℝ} (hθ : 1 / 2 < θ) :
    (∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → |primePart N - (N : ℝ) ^ 2 / 2| ≤ C * (N : ℝ) ^ (1 + θ)) ↔
      ∀ w : TrueZero, rZeroRadialPosition w.1 ≤ θ := by
  constructor
  · rintro ⟨C, hC⟩ w
    have := prime_blocks_zero_free_strip hC w
    rwa [max_eq_left hθ.le] at this
  · exact prime_blocks_of_zero_free hθ

/-- **Réduction à l'avenir sous l'historique ON** : si tout membre de hauteur `< T` est ON, le but ⟺ tout membre de
hauteur `≥ T` a une partie réelle `≤ θ` (`1/2 < θ`). La borne arithmétique ne peut pas être locale au passage : par
la lecture du pôle, elle lit tous les zéros au-dessus de l'arrivée. -/
theorem prime_blocks_iff_future_zero_free {θ T : ℝ} (hθ : 1 / 2 < θ)
    (hPast : ∀ w : TrueZero, rZeroHeight w.1 < T → rZeroRadialPosition w.1 = 1 / 2) :
    (∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → |primePart N - (N : ℝ) ^ 2 / 2| ≤ C * (N : ℝ) ^ (1 + θ)) ↔
      ∀ w : TrueZero, T ≤ rZeroHeight w.1 → rZeroRadialPosition w.1 ≤ θ := by
  rw [prime_blocks_iff_zero_free hθ]
  constructor
  · exact fun h w _ => h w
  · intro h w
    by_cases hw : T ≤ rZeroHeight w.1
    · exact h w hw
    · rw [hPast w (not_le.mp hw)]; exact hθ.le

#print axioms primeMass_split
#print axioms powerPart_le
#print axioms primePart_four_transitions
#print axioms primePart_grammar_upper
#print axioms mirror_closes_of_prime_blocks
#print axioms prime_blocks_zero_free_strip
#print axioms prime_blocks_iff_zero_free
#print axioms prime_blocks_iff_future_zero_free

/-! ## 5. Déroulement signé : bord, quatre transitions, fond (auteur, 2026-10-11, correctif) -/

/-- **Bord** `p ∈ {2, 3}` : `0 ≤ boundaryPart N ≤ 2N log 3` (démontré). -/
theorem boundaryPart_le (N : ℕ) : boundaryPart N ≤ 2 * N * Real.log 3 := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold boundaryPart
  have hsub : ((Finset.range N).filter Nat.Prime).filter (fun p => ¬ 3 < p) ⊆ {2, 3} := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    have h2 := hn.1.2.two_le
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  calc _ ≤ ∑ n ∈ ((Finset.range N).filter Nat.Prime).filter (fun p => ¬ 3 < p), (N : ℝ) * Real.log 3 :=
        Finset.sum_le_sum fun n hn => by
          simp only [Finset.mem_filter, Finset.mem_range] at hn
          have hn3 : n ≤ 3 := by omega
          have hn1 : 1 ≤ n := hn.1.2.one_lt.le
          rw [vonMangoldt_apply_prime hn.1.2, mul_comm]
          exact mul_le_mul (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
            (Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hn3))
            (Real.log_nonneg (by exact_mod_cast hn1)) hN0
    _ ≤ ∑ n ∈ ({2, 3} : Finset ℕ), (N : ℝ) * Real.log 3 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
          mul_nonneg hN0 (Real.log_nonneg (by norm_num))
    _ = 2 * N * Real.log 3 := by simp; ring

/-- **Somme des quatre transitions, écrite explicitement** : `Σ_τ transitionSum N τ = Σ_{3<p<N premier} Λ(p)(N − p)`. -/
theorem sum_transitionSum_eq (N : ℕ) : ∑ τ : Bool × Bool, transitionSum N τ =
    ∑ n ∈ ((Finset.range N).filter Nat.Prime).filter (fun p => 3 < p), Λ n * ((N : ℝ) - n) := by
  unfold transitionSum
  rw [← Finset.sum_fiberwise ((((Finset.range N).filter Nat.Prime).filter (fun p => 3 < p)))
    transitionOf (fun n => Λ n * ((N : ℝ) - n))]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Finset.filter_filter, and_assoc]

/-- **Côté supérieur signé, démontré à l'exposant `1 + 1`** (Chebyshev) :
`Σ_τ transitionSum N τ − N²/2 ≤ (log 4 + 5)·N^{1+1}`. -/
theorem transitions_upper_acquired (N : ℕ) :
    (∑ τ : Bool × Bool, transitionSum N τ) - (N : ℝ) ^ 2 / 2 ≤ (Real.log 4 + 5) * (N : ℝ) ^ (1 + (1 : ℝ)) := by
  have h := primeMass_block_linear N
  have hsplit := primeMass_split N
  have hfour := primePart_four_transitions N
  have hB := boundaryPart_nonneg N
  have hP := powerPart_nonneg N
  have := (abs_le.mp h).2
  linarith

/-- **Côté inférieur signé, démontré à l'exposant `1 + 1`** (positivité) :
`N²/2 − Σ_τ transitionSum N τ ≤ (1/2)·N^{1+1}`. -/
theorem transitions_lower_acquired (N : ℕ) :
    (N : ℝ) ^ 2 / 2 - ∑ τ : Bool × Bool, transitionSum N τ ≤ 1 / 2 * (N : ℝ) ^ (1 + (1 : ℝ)) := by
  have hsq : (N : ℝ) ^ (1 + (1 : ℝ)) = (N : ℝ) ^ 2 := by norm_num
  rw [hsq]
  have := Finset.sum_nonneg fun τ (_ : τ ∈ (Finset.univ : Finset (Bool × Bool))) => transitionSum_nonneg N τ
  linarith

/-- **Composition, signes conservés** : deux estimations SIGNÉES des quatre transitions contre le fond `N²/2`, d'exposant
`1 + θ` (`θ ≥ 0`) et de constante `C`, donnent l'estimation de `primePart` avec la constante explicite `C + 2 log 3`
(le bord `{2, 3}` est absorbé ; il est `≥ 0`, il ne compte que du côté supérieur). -/
theorem prime_blocks_of_transition_bounds {θ C : ℝ} (hθ : 0 ≤ θ)
    (h : ∀ N : ℕ, 2 ≤ N →
      (∑ τ : Bool × Bool, transitionSum N τ) - (N : ℝ) ^ 2 / 2 ≤ C * (N : ℝ) ^ (1 + θ) ∧
      (N : ℝ) ^ 2 / 2 - ∑ τ : Bool × Bool, transitionSum N τ ≤ C * (N : ℝ) ^ (1 + θ)) :
    ∀ N : ℕ, 2 ≤ N → |primePart N - (N : ℝ) ^ 2 / 2| ≤ (C + 2 * Real.log 3) * (N : ℝ) ^ (1 + θ) := by
  intro N hN
  obtain ⟨hup, hlo⟩ := h N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNθ : (N : ℝ) ≤ (N : ℝ) ^ (1 + θ) := by
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hB0 := boundaryPart_nonneg N
  have hB1 := boundaryPart_le N
  have hB2 : 2 * N * Real.log 3 ≤ 2 * Real.log 3 * (N : ℝ) ^ (1 + θ) := by
    nlinarith
  have hpos : 0 ≤ 2 * Real.log 3 * (N : ℝ) ^ (1 + θ) := by
    have : 0 ≤ (N : ℝ) ^ (1 + θ) := by linarith
    positivity
  rw [primePart_four_transitions, abs_le]
  constructor <;> nlinarith

#print axioms boundaryPart_le
#print axioms sum_transitionSum_eq
#print axioms transitions_upper_acquired
#print axioms transitions_lower_acquired
#print axioms prime_blocks_of_transition_bounds

end RHV6Fresh
