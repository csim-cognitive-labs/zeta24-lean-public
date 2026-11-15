/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.ZeroSourceExplicitFormulaChannel
import Mathlib.NumberTheory.AbelSummation

/-!
# RHV3Lean — le pont arithmétique exact Π ↔ ψ, porté sans prémisse nouvelle

    TRACE_ID              : RHV3-EXPLICIT-FORMULA-ARITHMETIC-BRIDGE
    SEMANTIC_OBJECT       : la fonction pondérée de Riemann tronquée
                            `PiWeighted`, sa forme en poids de von Mangoldt
                            `PiMangoldt`, et l'identité de sommation d'Abel
                            exacte qui les relie à `Chebyshev.psi` — la moitié
                            ARITHMÉTIQUE (sans zéro) du canal M9a.
    SEMANTIC_STATEMENT    : ce module ne parle d'aucun zéro. Il établit,
                            uniquement depuis O6 (`fnPrimeAtRank`) et Mathlib
                            (von Mangoldt, sommation d'Abel), l'identité exacte
                            entre la fonction pondérée de Riemann et `ψ` de
                            Chebyshev. C'est un porT MÉCANIQUE d'un corps déjà
                            démontré ailleurs (`formalization/rh_gap_criterion`,
                            fichiers `ZeroPrimeReconstruction.lean` /
                            `ExplicitFormulaBridge.lean`), adapté ici à O6
                            (`fnPrimeAtRank`/`thm_primeAtRank_isPrime`/
                            `nPrimeGap`) au lieu de ses propres `p`/`p_prime`/
                            `gnat` — les deux sont définitionnellement les
                            mêmes objets (`Nat.nth Nat.Prime`), donc ceci n'est
                            pas une seconde énumération.
    MATHEMATICAL_STATEMENT: PiMangoldt(x) = Σ_{n≤⌊x⌋} Λ(n)/log(n) ;
                            PiMangoldt(x) = PiWeighted(x, ⌊log x/log 2⌋) ;
                            PiMangoldt(x) = (log x)⁻¹ψ(x) − ∫₂ˣ (−t⁻¹/log²t)ψ(t)dt
                            (et sa réciproque) — pour x ≥ 2.
    MATHEMATICAL_PARENT   : O6 (`PrimeGapGrammar`), Mathlib
                            (`Mathlib.NumberTheory.Chebyshev`,
                            `Mathlib.NumberTheory.AbelSummation`,
                            `Mathlib.NumberTheory.PrimeCounting`).
    PROOF_STRATEGY        : transcription directe du corps déjà vérifié dans
                            `rh_gap_criterion` (mathlib `fabf563a`, 15/06),
                            revérifiée ici contre le mathlib de RHV3
                            (`51e6992e`, 03/08) — aucune preuve nouvelle,
                            seulement un portage mécanique entre deux
                            révisions mathlib compatibles.
    REQUIRED_LEMMAS       : Chebyshev.sum_PrimePow_eq_sum_sum, Chebyshev.psi_eq_sum_Icc,
                            sum_mul_eq_sub_integral_mul₁, Real.deriv_inv_log,
                            Real.deriv_log', Nat.primesLE_card_eq_primeCounting
    WHY_EACH_LEMMA_EXISTS : les deux premiers réindexent la somme sur les
                            puissances premières en somme sur les rangs de
                            puissance ; le troisième est la sommation d'Abel
                            générique ; les deux suivants portent le noyau de
                            la sommation (dérivée de `log` et de `1/log`) ; le
                            dernier identifie le cardinal des premiers `≤ n`
                            au comptage canonique.
    LEAN_DEFINITION       : nPiCount, rPiReal, rPiWeighted, rPrimePowerWeight,
                            rPiMangoldt
    LEAN_THEOREM          : thm_piCount_eq_primeCounting, thm_piReal_eq_primeCounting,
                            thm_logMulPrimePowerWeight_eq_vonMangoldt,
                            thm_piMangoldt_eq_piWeighted, thm_piMangoldt_eq_psi_abel_raw,
                            thm_psi_eq_piMangoldt_abel_raw, thm_piWeighted_eq_psi_abel_raw
    SAME_MEMBER_CHECK     : sans objet — aucun zéro, aucun membre ici.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : `thm_piCount_eq_primeCounting` identifie le
                            comptage local à l'unique `Nat.primeCounting` déjà
                            utilisé par O6/O10 — jamais un second comptage.
    FORBIDDEN_PREMISES    : ce module ne mentionne aucun zéro, aucune Tour,
                            aucune cellule, aucun T1/T2/PMirrorCollision/RH ;
                            il ne pose jamais l'identité de canal M9a comme
                            hypothèse — il ne construit que le côté
                            ARITHMÉTIQUE (sans zéro) de l'identité à venir.
    NEXT_CONSUMER         : le côté ZÉRO du canal (formule explicite,
                            Perron/Hadamard, encore à porter), qui devra
                            fournir `rPsiZeroChannel` en fonction des zéros et
                            se raccorder à `thm_piMangoldt_eq_psi_abel_raw`
                            pour finalement démontrer `PM9aChannelIdentityOnNaturals`.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED (portage mécanique, revérifié)

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV3Lean

open Finset BigOperators ArithmeticFunction

/-! ## 1. Comptage tronqué et fonction pondérée de Riemann -/

/-- Nombre de premiers `≤ m`, identique à `Nat.primeCounting` (rendu explicite
ici pour suivre exactement la forme du canal M9a). -/
def nPiCount (m : ℕ) : ℕ := Nat.count Nat.Prime (m + 1)

/-- Version réelle du comptage : `π(x) = π(⌊x⌋)`. -/
noncomputable def rPiReal (x : ℝ) : ℝ := (nPiCount ⌊x⌋₊ : ℝ)

/-- Fonction pondérée de Riemann tronquée :
`Π(x, M) = Σ_{m=1}^{M} (1/m)·π(x^{1/m})`. -/
noncomputable def rPiWeighted (x : ℝ) (M : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ)) * rPiReal (x ^ (1 / (m : ℝ) : ℝ))

theorem thm_piCount_eq_primeCounting (n : ℕ) :
    nPiCount n = Nat.primeCounting n := rfl

theorem thm_piReal_eq_primeCounting (x : ℝ) :
    rPiReal x = (Nat.primeCounting ⌊x⌋₊ : ℝ) := rfl

/-! ## 2. La fonction pondérée en poids de von Mangoldt -/

/-- Poids atomique `Λ(n)/log n`. Nul en `0` et `1` car `Λ` y est nulle. -/
noncomputable def rPrimePowerWeight (n : ℕ) : ℝ :=
  (Real.log (n : ℝ))⁻¹ * ArithmeticFunction.vonMangoldt n

@[simp] theorem thm_primePowerWeight_zero : rPrimePowerWeight 0 = 0 := by
  simp [rPrimePowerWeight]

@[simp] theorem thm_primePowerWeight_one : rPrimePowerWeight 1 = 0 := by
  simp [rPrimePowerWeight]

/-- Fonction pondérée de Riemann écrite comme somme de `Λ(n)/log n`. -/
noncomputable def rPiMangoldt (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, rPrimePowerWeight n

/-- Multiplier le poids atomique par `log n` restitue exactement `Λ(n)`. -/
theorem thm_logMulPrimePowerWeight_eq_vonMangoldt (n : ℕ) :
    Real.log (n : ℝ) * rPrimePowerWeight n
      = ArithmeticFunction.vonMangoldt n := by
  by_cases hzero : ArithmeticFunction.vonMangoldt n = 0
  · simp [rPrimePowerWeight, hzero]
  · have hpp : IsPrimePow n :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hzero
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hpp.pos
    have hnne : (n : ℝ) ≠ 1 := by exact_mod_cast hpp.ne_one
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one hnpos hnne
    simp [rPrimePowerWeight, hlog]

/-- **`PiMangoldt` reconstruit exactement `PiWeighted` à la troncature
canonique.** -/
theorem thm_piMangoldt_eq_piWeighted {x : ℝ} (hx : 2 ≤ x) :
    rPiMangoldt x = rPiWeighted x ⌊Real.log x / Real.log 2⌋₊ := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  unfold rPiMangoldt
  rw [← add_sum_Ioc_eq_sum_Icc]
  · simp only [thm_primePowerWeight_zero, zero_add]
    calc
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, rPrimePowerWeight n
          = ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter IsPrimePow,
              rPrimePowerWeight n := by
            symm
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro n hn hnot
            have hpp : ¬ IsPrimePow n := by
              intro hp
              exact hnot (Finset.mem_filter.mpr ⟨hn, hp⟩)
            rw [rPrimePowerWeight,
              ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, mul_zero]
      _ = ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
            ∑ p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
              rPrimePowerWeight (p ^ k) := by
            exact Chebyshev.sum_PrimePow_eq_sum_sum
              (x := x) rPrimePowerWeight hx0
      _ = rPiWeighted x ⌊Real.log x / Real.log 2⌋₊ := by
        unfold rPiWeighted
        apply Finset.sum_congr rfl
        intro k hk
        have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
        have hk0 : k ≠ 0 := ne_of_gt hkpos
        calc
          ∑ p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
                rPrimePowerWeight (p ^ k)
              = ∑ p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
                  (1 / (k : ℝ)) := by
                    apply Finset.sum_congr rfl
                    intro p hp
                    have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
                    unfold rPrimePowerWeight
                    rw [ArithmeticFunction.vonMangoldt_apply_pow hk0,
                      ArithmeticFunction.vonMangoldt_apply_prime hpprime]
                    push_cast
                    rw [Real.log_pow]
                    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
                    have hpRpos : (0 : ℝ) < p := by
                      exact_mod_cast hpprime.pos
                    have hpRne : (p : ℝ) ≠ 1 := by
                      exact_mod_cast hpprime.ne_one
                    have hlog : Real.log (p : ℝ) ≠ 0 :=
                      Real.log_ne_zero_of_pos_of_ne_one hpRpos hpRne
                    field_simp
          _ = (1 / (k : ℝ)) * rPiReal (x ^ (1 / (k : ℝ) : ℝ)) := by
                have hset :
                    (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime
                      = Nat.primesLE ⌊x ^ ((1 : ℝ) / k)⌋₊ := by
                  ext q
                  simp only [Finset.mem_filter, Finset.mem_Ioc,
                    Nat.mem_primesLE]
                  constructor
                  · rintro ⟨⟨_, hqle⟩, hqprime⟩
                    exact ⟨hqle, hqprime⟩
                  · rintro ⟨hqle, hqprime⟩
                    exact ⟨⟨hqprime.pos, hqle⟩, hqprime⟩
                rw [hset, Finset.sum_const, nsmul_eq_mul,
                  Nat.primesLE_card_eq_primeCounting,
                  thm_piReal_eq_primeCounting]
                ring
  · exact Nat.zero_le _

/-! ## 3. Sommation d'Abel exacte, dans les deux sens -/

/-- Forme brute de la sommation d'Abel de `ψ` vers `Π`. -/
theorem thm_piMangoldt_eq_psi_abel_raw {x : ℝ} (hx : 2 ≤ x) :
    rPiMangoldt x
      = (Real.log x)⁻¹ * Chebyshev.psi x
        - ∫ t in 2..x,
            (-t⁻¹ / Real.log t ^ 2) * Chebyshev.psi t := by
  unfold rPiMangoldt rPrimePowerWeight
  rw [sum_mul_eq_sub_integral_mul₁
      (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
      (f := fun t : ℝ => (Real.log t)⁻¹)
      (by simp) (by simp),
    ← intervalIntegral.integral_of_le hx]
  · simp_rw [Real.deriv_inv_log]
    simp_rw [← Chebyshev.psi_eq_sum_Icc]
  · intro z ⟨hz, _⟩
    have hz0 : z ≠ 0 := by linarith
    have hzlog : Real.log z ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z hz =>
      ContinuousWithinAt.congr ?_
        (fun _ _ => Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have hzlog : Real.log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <|
        Real.log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith [hz.1]
    exact ContinuousAt.continuousWithinAt <| by fun_prop

/-- Sommation d'Abel exacte, sens inverse, de `Π` vers `ψ`. -/
theorem thm_psi_eq_piMangoldt_abel_raw {x : ℝ} (hx : 2 ≤ x) :
    Chebyshev.psi x
      = Real.log x * rPiMangoldt x
        - ∫ t in 2..x, t⁻¹ * rPiMangoldt t := by
  calc
    Chebyshev.psi x
        = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt n := Chebyshev.psi_eq_sum_Icc x
    _ = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊,
          Real.log (n : ℝ) * rPrimePowerWeight n := by
        apply Finset.sum_congr rfl
        intro n _
        exact (thm_logMulPrimePowerWeight_eq_vonMangoldt n).symm
    _ = Real.log x * rPiMangoldt x
          - ∫ t in 2..x, t⁻¹ * rPiMangoldt t := by
      rw [sum_mul_eq_sub_integral_mul₁ rPrimePowerWeight
          (f := fun t : ℝ => Real.log t)
          thm_primePowerWeight_zero thm_primePowerWeight_one,
        ← intervalIntegral.integral_of_le hx]
      · simp_rw [Real.deriv_log']
        simp [rPiMangoldt]
      · intro z ⟨hz, _⟩
        fun_prop (disch := linarith)
      · rw [Real.deriv_log']
        refine ContinuousOn.integrableOn_Icc ?_
        fun_prop (disch := grind)

/-- Composition exacte de la forme d'Abel avec `rPiWeighted`. -/
theorem thm_piWeighted_eq_psi_abel_raw {x : ℝ} (hx : 2 ≤ x) :
    rPiWeighted x ⌊Real.log x / Real.log 2⌋₊
      = (Real.log x)⁻¹ * Chebyshev.psi x
        - ∫ t in 2..x,
            (-t⁻¹ / Real.log t ^ 2) * Chebyshev.psi t := by
  rw [← thm_piMangoldt_eq_piWeighted hx]
  exact thm_piMangoldt_eq_psi_abel_raw hx

#check nPiCount
#check rPiReal
#check rPiWeighted
#check rPiMangoldt
#check thm_piMangoldt_eq_piWeighted
#check thm_piMangoldt_eq_psi_abel_raw
#check thm_psi_eq_piMangoldt_abel_raw
#check thm_piWeighted_eq_psi_abel_raw

end RHV3Lean
