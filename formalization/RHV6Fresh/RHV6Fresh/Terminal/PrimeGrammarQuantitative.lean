/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PrimeCellError
import RHV6Fresh.Terminal.ReadingArithmetic
import RHV6Fresh.Zeta23Port.Chebyshev

/-!
# Grammaire quantitative des écarts premiers : résidus, termes croisés, portée des obstructions (auteur, 2026-10-17)

Objets écrits avec les seuls premiers `p_n = fnPrimeAtRank n` (`p_0 = 2`), sans aucun zéro :
`g_n = p_{n+1} − p_n`, résidu `r_n = g_n − log p_n` (`gapResidual`), somme de fenêtre `R_{a,b} = Σ_{a≤n<b} r_n`
(`windowResidual`), `ϑ(p_m) = Σ_{n≤m} log p_n` (`rankTheta`), classe `c_n = g_n mod 6` (`gapClass`).

* §1 (A1) identité cumulative `R_{0,m} = p_m − ϑ(p_m) + log p_m − 2` et forme de fenêtre
  `R_{a,b} = p_b − p_a − Σ_{a≤n<b} log p_n` (identités, aucune borne) ;
* §2 (A2) raccord aux cellules : `ϑ₃(p_k) = ϑ(p_k) − log 2 − log 3` ; une borne aux SEULS premiers
  `|p_k − ϑ(p_k)| ≤ C p_k^η` donne le contrôle des cellules `|ϑ₃(M) − M| ≤ C' M^η` pour tout `M ≥ 1` (Bertrand) ;
* §3 (A5) fermeture CONDITIONNELLE : la borne critique du résidu cumulé
  `|R_{0,m} + 2 − log p_m| ≤ C √p_m (log p_m)²` implique RH (par les blocs premiers et la lecture du pôle déjà compilés) ;
  (A6) réciproque sous forme INTÉGRÉE seulement (blocs d'exposant `1 + θ`, `θ > 1/2`) ; la forme ponctuelle en `(log)²`
  (von Koch) n'est pas dans Mathlib et n'est pas démontrée ici ;
* §4 (A3, A3′) obstructions, portée EXACTE : le résidu n'est fonction ni de la transition mod 6 avec l'écart
  (témoins 5 → 7, 11 → 13), ni du mot de deux écarts avec les trois classes (témoins 29 → 31 → 37, 59 → 61 → 67,
  redémontrés ici, aucun import de `RhGapCriterion`) ; avec la position `p_n` et l'écart, le résidu est déterminé
  (tautologie, `gapResidual_of_position_and_gap`) : ces obstructions ne concernent ni une loi qui conserve la
  position, ni une loi de portée longue, ni une compensation entre fenêtres ;
* §5 (A7) termes croisés : `(Σ r)² = Σ r² + 2 Σ_{j<n} r_n r_j`, découpage de deux fenêtres consécutives, répartition
  exacte des termes croisés par couples de classes ; identités algébriques, PAS une loi : la contrainte cherchée porte
  sur le signe, l'amplitude et l'évolution d'échelle de ces termes, elle n'est pas démontrée ;
* §6 (A8) modes `T = S₀ + S₂ + S₄`, `B = 2S₀ − S₂ − S₄`, `O = S₂ − S₄` : partition, inverses, énergie
  `S₀² + S₂² + S₄² = T²/3 + B²/6 + O²/2` ; non-détermination ALGÉBRIQUE de `T` par `(B, O)` sur `ℝ³` seulement (aucun
  témoin réel sur la suite des premiers, aucune indépendance statistique ni arithmétique affirmée).

Tout est démontré (axiomes standard). Aucune borne d'exposant `< 1` du résidu cumulé n'est démontrée.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction

/-! ## 0. Objets (premiers seuls) -/

/-- Résidu d'écart `r_n = g_n − log p_n`. -/
noncomputable def gapResidual (n : ℕ) : ℝ :=
  ((fnPrimeAtRank (n + 1) : ℝ) - fnPrimeAtRank n) - Real.log (fnPrimeAtRank n)

/-- Somme de fenêtre `R_{a,b} = Σ_{a≤n<b} r_n`. -/
noncomputable def windowResidual (a b : ℕ) : ℝ := ∑ n ∈ Finset.Ico a b, gapResidual n

/-- `ϑ(p_m) = Σ_{n≤m} log p_n` (somme sur les `m + 1` premiers premiers). -/
noncomputable def rankTheta (m : ℕ) : ℝ := ∑ n ∈ Finset.range (m + 1), Real.log (fnPrimeAtRank n)

/-- Classe d'écart `c_n = g_n mod 6`. -/
noncomputable def gapClass (n : ℕ) : ℕ := (fnPrimeAtRank (n + 1) - fnPrimeAtRank n) % 6

/-! ## 1. (A1) Identité cumulative -/

/-- **Fenêtre** : `R_{a,b} = p_b − p_a − Σ_{a≤n<b} log p_n`. -/
theorem windowResidual_eq {a b : ℕ} (h : a ≤ b) :
    windowResidual a b = (fnPrimeAtRank b : ℝ) - fnPrimeAtRank a -
      ∑ n ∈ Finset.Ico a b, Real.log (fnPrimeAtRank n) := by
  induction b, h using Nat.le_induction with
  | base => simp [windowResidual]
  | succ b hb ih =>
    unfold windowResidual at ih ⊢
    rw [Finset.sum_Ico_succ_top hb, Finset.sum_Ico_succ_top hb, ih]
    unfold gapResidual; ring

/-- **Identité cumulative** (rapport p4, vérifiée ici) : `R_{0,m} = p_m − ϑ(p_m) + log p_m − 2`. -/
theorem cumulativeResidual_eq (m : ℕ) :
    windowResidual 0 m = (fnPrimeAtRank m : ℝ) - rankTheta m + Real.log (fnPrimeAtRank m) - 2 := by
  rw [windowResidual_eq (Nat.zero_le m), thm_primeAtRank_zero_eq_two, ← Finset.range_eq_Ico]
  unfold rankTheta; rw [Finset.sum_range_succ]; push_cast; ring

/-- Forme équivalente : `R_{0,m} + 2 − log p_m = p_m − ϑ(p_m)`. -/
theorem cumulativeResidual_shift (m : ℕ) :
    windowResidual 0 m + 2 - Real.log (fnPrimeAtRank m) = (fnPrimeAtRank m : ℝ) - rankTheta m := by
  rw [cumulativeResidual_eq]; ring

/-! ## 2. (A2) Raccord aux cellules : une borne aux seuls premiers contrôle toute cellule -/

/-- Si `q` est premier au-delà de `p_k`, alors `p_{k+1} ≤ q`. -/
theorem primeAtRank_succ_le_of_prime_gt {k q : ℕ} (hq : q.Prime) (h : fnPrimeAtRank k < q) :
    fnPrimeAtRank (k + 1) ≤ q := by
  have he : fnPrimeAtRank (Nat.count Nat.Prime q) = q := Nat.nth_count hq
  rw [← he] at h ⊢
  have := thm_primeAtRank_strictMono.lt_iff_lt.mp h
  exact thm_primeAtRank_strictMono.monotone (by omega)

/-- Pas élémentaire : `p_k = a`, `b` premier, aucun premier strictement entre ⟹ `p_{k+1} = b`. -/
theorem primeAtRank_step {k a b : ℕ} (ha : fnPrimeAtRank k = a) (hb : b.Prime) (hab : a < b)
    (hcomp : ∀ m, a < m → m < b → ¬ m.Prime) : fnPrimeAtRank (k + 1) = b := by
  have h1 := thm_primeAtRank_strictMono (Nat.lt_succ_self k)
  have h2 := primeAtRank_succ_le_of_prime_gt hb (by rw [ha]; exact hab)
  rw [ha] at h1
  rcases lt_or_eq_of_le h2 with hlt | heq
  · exact absurd (thm_primeAtRank_isPrime _) (hcomp _ h1 hlt)
  · exact heq

theorem primeAtRank_one_eq : fnPrimeAtRank 1 = 3 := Nat.nth_prime_one_eq_three

theorem tailWeight_primeAtRank {k : ℕ} (hk : 2 ≤ k) :
    tailWeight (fnPrimeAtRank k) = Real.log (fnPrimeAtRank k) := by
  have hp := thm_primeAtRank_isPrime k
  have h3 : 3 < fnPrimeAtRank k := by
    have := thm_primeAtRank_strictMono (show 1 < k by omega)
    rwa [primeAtRank_one_eq] at this
  simp [tailWeight, hp, h3, vonMangoldt_apply_prime hp]

/-- **`ϑ₃` aux premiers** : `ϑ₃(p_k) = ϑ(p_k) − log 2 − log 3` pour `k ≥ 1`. -/
theorem cellTheta_primeAtRank {k : ℕ} (hk : 1 ≤ k) :
    cellTheta (fnPrimeAtRank k) = rankTheta k - Real.log 2 - Real.log 3 := by
  induction k, hk using Nat.le_induction with
  | base =>
    rw [primeAtRank_one_eq, cellTheta_eq_sum]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, tailWeight]
    unfold rankTheta
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, thm_primeAtRank_zero_eq_two,
      primeAtRank_one_eq]
    norm_num
  | succ k hk ih =>
    have hlt : fnPrimeAtRank k < fnPrimeAtRank (k + 1) := thm_primeAtRank_strictMono (Nat.lt_succ_self k)
    have hpos : 1 ≤ fnPrimeAtRank (k + 1) := by omega
    have hcell := cellTheta_on_cell k (fnPrimeAtRank (k + 1) - 1) (by omega) (by omega)
    have hs : cellTheta (fnPrimeAtRank (k + 1)) =
        cellTheta (fnPrimeAtRank (k + 1) - 1) + tailWeight (fnPrimeAtRank (k + 1)) := by
      have := cellTheta_succ (fnPrimeAtRank (k + 1) - 1)
      rwa [Nat.sub_add_cancel hpos] at this
    rw [hs, hcell, ih, tailWeight_primeAtRank (by omega)]
    unfold rankTheta
    rw [Finset.sum_range_succ _ (k + 1)]; ring

/-- Tout `M ≥ 2` est dans une cellule `[p_k, p_{k+1}[`. -/
theorem exists_prime_cell {M : ℕ} (hM : 2 ≤ M) :
    ∃ k, fnPrimeAtRank k ≤ M ∧ M < fnPrimeAtRank (k + 1) := by
  classical
  have hex : ∃ k, M < fnPrimeAtRank (k + 1) :=
    ⟨M, lt_of_lt_of_le (Nat.lt_succ_self M) (thm_primeAtRank_strictMono.id_le (M + 1))⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, thm_primeAtRank_zero_eq_two]; exact hM
  · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [Nat.sub_add_cancel hpos] at hmin
    omega

theorem cellTheta_small {M : ℕ} (hM : M < 3) : cellTheta M = 0 := by
  rw [cellTheta_eq_sum]
  interval_cases M <;> simp [Finset.sum_range_succ, tailWeight]

/-- **(A2) Des premiers aux cellules** : une borne `|p_k − ϑ(p_k)| ≤ C p_k^η` lue aux SEULS premiers
(`0 < η ≤ 1`) contrôle toutes les cellules : `|ϑ₃(M) − M| ≤ (2C + 2/η + 3) M^η` pour tout `M ≥ 1`. -/
theorem cell_control_of_rank_bound {η C : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hC : 0 ≤ C)
    (hE : ∀ k, |(fnPrimeAtRank k : ℝ) - rankTheta k| ≤ C * (fnPrimeAtRank k : ℝ) ^ η) :
    ∀ M : ℕ, 1 ≤ M → |cellTheta M - M| ≤ (2 * C + 2 / η + 3) * (M : ℝ) ^ η := by
  intro M hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMη : 1 ≤ (M : ℝ) ^ η := Real.one_le_rpow hM1 hη0.le
  have h2η : 0 ≤ 2 / η := by positivity
  rcases lt_or_ge M 3 with hsmall | hbig
  · rw [cellTheta_small hsmall, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    have : (M : ℝ) ≤ 2 := by exact_mod_cast (by omega : M ≤ 2)
    nlinarith [mul_nonneg hC (by linarith : (0 : ℝ) ≤ (M : ℝ) ^ η), mul_nonneg h2η (by linarith : (0 : ℝ) ≤ (M : ℝ) ^ η)]
  · obtain ⟨k, hk1, hk2⟩ := exists_prime_cell (by omega : 2 ≤ M)
    have hk : 1 ≤ k := by
      by_contra h0
      have : k = 0 := by omega
      subst this
      rw [show (0 : ℕ) + 1 = 1 from rfl, primeAtRank_one_eq] at hk2
      omega
    rw [cellTheta_on_cell k M hk1 hk2, cellTheta_primeAtRank hk]
    obtain ⟨q, hq, hMq, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul M (by omega)
    have hQ : fnPrimeAtRank (k + 1) ≤ 2 * M :=
      le_trans (primeAtRank_succ_le_of_prime_gt hq (lt_of_le_of_lt hk1 hMq)) hq2
    set P : ℝ := (fnPrimeAtRank k : ℝ) with hPdef
    set Q : ℝ := (fnPrimeAtRank (k + 1) : ℝ) with hQdef
    have hP1 : (2 : ℝ) ≤ P := by
      have := (thm_primeAtRank_isPrime k).two_le; simp only [hPdef]; exact_mod_cast this
    have hQ1 : (2 : ℝ) ≤ Q := by
      have := (thm_primeAtRank_isPrime (k + 1)).two_le; simp only [hQdef]; exact_mod_cast this
    have hPM : P ≤ M := by simp only [hPdef]; exact_mod_cast hk1
    have hQM : Q ≤ 2 * M := by simp only [hQdef]; exact_mod_cast hQ
    have hMQ : (M : ℝ) ≤ Q := by simp only [hQdef]; exact_mod_cast hk2.le
    have hθk1 : rankTheta (k + 1) = rankTheta k + Real.log Q := by
      unfold rankTheta; rw [Finset.sum_range_succ _ (k + 1)]
    have hEk := abs_le.mp (hE k)
    have hEk1 := abs_le.mp (hE (k + 1))
    rw [hθk1] at hEk1
    have hPη : P ^ η ≤ (M : ℝ) ^ η := Real.rpow_le_rpow (by linarith) hPM hη0.le
    have h2pow : (2 : ℝ) ^ η ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hη1
      rwa [Real.rpow_one] at this
    have hQη : Q ^ η ≤ 2 * (M : ℝ) ^ η := by
      calc Q ^ η ≤ (2 * (M : ℝ)) ^ η := Real.rpow_le_rpow (by linarith) hQM hη0.le
        _ = 2 ^ η * (M : ℝ) ^ η := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ 2 * (M : ℝ) ^ η := mul_le_mul_of_nonneg_right h2pow (by linarith)
    have hlogQ : Real.log Q ≤ 2 / η * (M : ℝ) ^ η := by
      have := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ Q) hη0
      calc Real.log Q ≤ Q ^ η / η := this
        _ ≤ (2 * (M : ℝ) ^ η) / η := div_le_div_of_nonneg_right hQη hη0.le
        _ = 2 / η * (M : ℝ) ^ η := by ring
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hlog3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
    have hlog2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog3' : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have hlogQ' : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
    have hCP : C * P ^ η ≤ C * (M : ℝ) ^ η := mul_le_mul_of_nonneg_left hPη hC
    have hCQ : C * Q ^ η ≤ C * (2 * (M : ℝ) ^ η) := mul_le_mul_of_nonneg_left hQη hC
    have hCM : 0 ≤ C * (M : ℝ) ^ η := mul_nonneg hC (by linarith)
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith

/-! ## 3. (A5) Fermeture conditionnelle, (A6) réciproque intégrée -/

/-- **Bande sans zéro depuis une borne aux premiers** : `|p_k − ϑ(p_k)| ≤ C p_k^η` (`1/2 < η ≤ 1`) ⟹ tout vrai zéro
a une partie réelle `≤ η` (cellules §2, accumulation `goal_sides_of_cell_control`, bord `{2, 3}`, blocs premiers,
lecture du pôle `prime_blocks_zero_free_strip`). -/
theorem zero_free_of_rank_bound {η C : ℝ} (hη : 1 / 2 < η) (hη1 : η ≤ 1) (hC : 0 ≤ C)
    (hE : ∀ k, |(fnPrimeAtRank k : ℝ) - rankTheta k| ≤ C * (fnPrimeAtRank k : ℝ) ^ η) (w : TrueZero) :
    rZeroRadialPosition w.1 ≤ η := by
  have hη0 : 0 < η := by linarith
  have hcell := cell_control_of_rank_bound hη0 hη1 hC hE
  set K : ℝ := 2 * C + 2 / η + 3 with hKdef
  have hK : 0 ≤ K := by simp only [hKdef]; positivity
  have hg := goal_sides_of_cell_control (θ := η) hη0.le hK
    (fun M hM => (abs_le.mp (hcell M hM)).2) (fun M hM => by linarith [(abs_le.mp (hcell M hM)).1])
  have hB : ∀ N : ℕ, 2 ≤ N →
      |primePart N - (N : ℝ) ^ 2 / 2| ≤ (K + 1 / 2 + 2 * Real.log 3) * (N : ℝ) ^ (1 + η) := by
    intro N hN
    have hs := primeMass_goal_split N
    have hm := primeMass_split N
    have hb0 := boundaryPart_nonneg N
    have hb1 := boundaryPart_le N
    obtain ⟨hup, hlo⟩ := hg N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hNpow : (N : ℝ) ≤ (N : ℝ) ^ (1 + η) := by
      have := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (1 : ℝ) ≤ 1 + η)
      rwa [Real.rpow_one] at this
    have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have hbd : boundaryPart N ≤ 2 * Real.log 3 * (N : ℝ) ^ (1 + η) := by
      calc boundaryPart N ≤ 2 * N * Real.log 3 := hb1
        _ = 2 * Real.log 3 * N := by ring
        _ ≤ 2 * Real.log 3 * (N : ℝ) ^ (1 + η) := mul_le_mul_of_nonneg_left hNpow (by positivity)
    have hpp : primePart N - (N : ℝ) ^ 2 / 2 = goalError N + boundaryPart N := by
      unfold goalError at hs ⊢; linarith
    unfold goalError at hpp
    rw [hpp, abs_le]
    have hNe : 0 ≤ (N : ℝ) ^ (1 + η) := by positivity
    constructor <;> nlinarith
  have := prime_blocks_zero_free_strip hB w
  rwa [max_eq_left (by linarith : (1 : ℝ) / 2 ≤ η)] at this

/-- `√p (log p)² ≤ (4/δ²) p^{1/2+δ}` pour `p ≥ 1`, `δ > 0`. -/
theorem sqrt_log_sq_le_rpow {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) :
    Real.sqrt x * Real.log x ^ 2 ≤ 4 / δ ^ 2 * x ^ (1 / 2 + δ) := by
  have hx0 : 0 ≤ x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hl : Real.log x ≤ x ^ (δ / 2) / (δ / 2) := Real.log_le_rpow_div hx0 (by linarith)
  have hsq : Real.log x ^ 2 ≤ (x ^ (δ / 2) / (δ / 2)) ^ 2 := pow_le_pow_left₀ hl0 hl 2
  have hpow : (x ^ (δ / 2) / (δ / 2)) ^ 2 = 4 / δ ^ 2 * x ^ δ := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; push_cast; field_simp; ring_nf
  have hsqrt : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
  rw [hsqrt]
  calc x ^ (1 / 2 : ℝ) * Real.log x ^ 2 ≤ x ^ (1 / 2 : ℝ) * (4 / δ ^ 2 * x ^ δ) :=
        mul_le_mul_of_nonneg_left (hpow ▸ hsq) (by positivity)
    _ = 4 / δ ^ 2 * (x ^ (1 / 2 : ℝ) * x ^ δ) := by ring
    _ = 4 / δ ^ 2 * x ^ (1 / 2 + δ) := by
        rw [Real.rpow_add (by linarith : (0 : ℝ) < x)]

/-- **(A5) Fermeture conditionnelle par le résidu cumulé des écarts premiers** : si
`|R_{0,m} + 2 − log p_m| ≤ C √p_m (log p_m)²` pour tout `m` (énoncé sans aucun zéro), alors RH. L'hypothèse a la force
de RH (forme de von Koch) ; elle n'est démontrée nulle part. -/
theorem riemannHypothesis_of_cumulative_residual_bound
    (h : ∃ C : ℝ, ∀ m : ℕ, |windowResidual 0 m + 2 - Real.log (fnPrimeAtRank m)| ≤
      C * Real.sqrt (fnPrimeAtRank m) * Real.log (fnPrimeAtRank m) ^ 2) :
    RiemannHypothesis := by
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := by
    have h0 := hC 0
    have : 0 ≤ Real.sqrt (fnPrimeAtRank 0) * Real.log (fnPrimeAtRank 0) ^ 2 := by positivity
    rw [thm_primeAtRank_zero_eq_two] at h0 this
    have hpos : 0 < Real.sqrt ((2 : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ) ^ 2 := by
      have : 0 < Real.log ((2 : ℕ) : ℝ) := Real.log_pos (by norm_num)
      positivity
    by_contra hneg
    push Not at hneg
    have := abs_nonneg (windowResidual 0 0 + 2 - Real.log ((2 : ℕ) : ℝ))
    nlinarith
  -- borne ponctuelle pour tout exposant `η ∈ ]1/2, 1]`
  have hstrip : ∀ η : ℝ, 1 / 2 < η → η ≤ 1 → ∀ w : TrueZero, rZeroRadialPosition w.1 ≤ η := by
    intro η hη hη1 w
    refine zero_free_of_rank_bound (C := C * (4 / (η - 1 / 2) ^ 2)) hη hη1 (by positivity) (fun k => ?_) w
    have hk := hC k
    rw [cumulativeResidual_shift] at hk
    have hp1 : (1 : ℝ) ≤ fnPrimeAtRank k := by
      have := (thm_primeAtRank_isPrime k).two_le; exact_mod_cast (by omega : 1 ≤ fnPrimeAtRank k)
    have hb := sqrt_log_sq_le_rpow hp1 (by linarith : 0 < η - 1 / 2)
    rw [show 1 / 2 + (η - 1 / 2) = η by ring] at hb
    calc |(fnPrimeAtRank k : ℝ) - rankTheta k|
        ≤ C * Real.sqrt (fnPrimeAtRank k) * Real.log (fnPrimeAtRank k) ^ 2 := hk
      _ = C * (Real.sqrt (fnPrimeAtRank k) * Real.log (fnPrimeAtRank k) ^ 2) := by ring
      _ ≤ C * (4 / (η - 1 / 2) ^ 2 * (fnPrimeAtRank k : ℝ) ^ η) := mul_le_mul_of_nonneg_left hb hC0
      _ = C * (4 / (η - 1 / 2) ^ 2) * (fnPrimeAtRank k : ℝ) ^ η := by ring
  have hhalf : ∀ w : TrueZero, rZeroRadialPosition w.1 ≤ 1 / 2 := by
    intro w
    by_contra hgt
    push Not at hgt
    set β := rZeroRadialPosition w.1
    have := hstrip (min ((β + 1 / 2) / 2) 1) (lt_min (by linarith) (by norm_num)) (min_le_right _ _) w
    have := le_trans this (min_le_left _ _)
    linarith
  refine riemannHypothesis_iff_noLowerSide.mpr (fun z hz => ?_)
  have := hhalf (mirrorMember z)
  rw [mirrorMember_radial] at this
  linarith

/-- **(A6) Réciproque, forme INTÉGRÉE seulement** : sous RH, les blocs premiers ont tout exposant `1 + θ`, `θ > 1/2`.
La forme ponctuelle en `√p (log p)²` n'est pas démontrée ici. -/
theorem prime_blocks_of_riemannHypothesis (hRH : RiemannHypothesis) {θ : ℝ} (hθ : 1 / 2 < θ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → |primePart N - (N : ℝ) ^ 2 / 2| ≤ C * (N : ℝ) ^ (1 + θ) :=
  prime_blocks_of_zero_free hθ (fun w => by
    rw [thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1]; exact hθ.le)

/-! ## 4. (A3, A3′) Obstructions, portée exacte -/

theorem primeAtRank_two_eq : fnPrimeAtRank 2 = 5 := Nat.nth_prime_two_eq_five
theorem primeAtRank_three_eq : fnPrimeAtRank 3 = 7 :=
  primeAtRank_step primeAtRank_two_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m; norm_num)
theorem primeAtRank_four_eq : fnPrimeAtRank 4 = 11 :=
  primeAtRank_step primeAtRank_three_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m <;> norm_num)
theorem primeAtRank_five_eq : fnPrimeAtRank 5 = 13 :=
  primeAtRank_step primeAtRank_four_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m; norm_num)
theorem primeAtRank_six_eq : fnPrimeAtRank 6 = 17 :=
  primeAtRank_step primeAtRank_five_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m <;> norm_num)
theorem primeAtRank_seven_eq : fnPrimeAtRank 7 = 19 :=
  primeAtRank_step primeAtRank_six_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m; norm_num)
theorem primeAtRank_eight_eq : fnPrimeAtRank 8 = 23 :=
  primeAtRank_step primeAtRank_seven_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m <;> norm_num)
theorem primeAtRank_nine_eq : fnPrimeAtRank 9 = 29 :=
  primeAtRank_step primeAtRank_eight_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m <;> norm_num)
theorem primeAtRank_ten_eq : fnPrimeAtRank 10 = 31 :=
  primeAtRank_step primeAtRank_nine_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m; norm_num)
theorem primeAtRank_eleven_eq : fnPrimeAtRank 11 = 37 :=
  primeAtRank_step primeAtRank_ten_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m <;> norm_num)
theorem primeAtRank_twelve_eq : fnPrimeAtRank 12 = 41 :=
  primeAtRank_step primeAtRank_eleven_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m <;> norm_num)
theorem primeAtRank_thirteen_eq : fnPrimeAtRank 13 = 43 :=
  primeAtRank_step primeAtRank_twelve_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m; norm_num)
theorem primeAtRank_fourteen_eq : fnPrimeAtRank 14 = 47 :=
  primeAtRank_step primeAtRank_thirteen_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m <;> norm_num)
theorem primeAtRank_fifteen_eq : fnPrimeAtRank 15 = 53 :=
  primeAtRank_step primeAtRank_fourteen_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m <;> norm_num)
theorem primeAtRank_sixteen_eq : fnPrimeAtRank 16 = 59 :=
  primeAtRank_step primeAtRank_fifteen_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m <;> norm_num)
theorem primeAtRank_seventeen_eq : fnPrimeAtRank 17 = 61 :=
  primeAtRank_step primeAtRank_sixteen_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m; norm_num)
theorem primeAtRank_eighteen_eq : fnPrimeAtRank 18 = 67 :=
  primeAtRank_step primeAtRank_seventeen_eq (by norm_num) (by norm_num) (by intro m h1 h2; interval_cases m <;> norm_num)

/-- **(A3) Transition mod 6 et écart ne fixent pas le résidu** (portée : une transition isolée) : aucune fonction de
`(p_n mod 6, p_{n+1} mod 6, g_n)` ne reproduit `r_n` ; témoins `5 → 7` et `11 → 13` (transition `5 → 1`, écart `2`),
`2 − log 5 ≠ 2 − log 11`. -/
theorem residual_not_function_of_transition :
    ¬ ∃ φ : ℕ → ℕ → ℕ → ℝ, ∀ n, gapResidual n =
      φ (fnPrimeAtRank n % 6) (fnPrimeAtRank (n + 1) % 6) (fnPrimeAtRank (n + 1) - fnPrimeAtRank n) := by
  rintro ⟨φ, hφ⟩
  have a := hφ 2
  have b := hφ 4
  simp only [gapResidual, show (2 : ℕ) + 1 = 3 from rfl, show (4 : ℕ) + 1 = 5 from rfl, primeAtRank_two_eq,
    primeAtRank_three_eq, primeAtRank_four_eq, primeAtRank_five_eq] at a b
  norm_num at a b
  have hlt : Real.log 5 < Real.log 11 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [← a] at b
  linarith

/-- **(A3′) État quantifié de deux écarts** (portée : la classe de profils qui confond ces deux mots) : aucune fonction
du mot `(g_n, g_{n+1})` et des trois classes `(p_n, p_{n+1}, p_{n+2}) mod 6` ne reproduit `r_{n+1}` ; témoins
`29 → 31 → 37` et `59 → 61 → 67` (mot `(2, 6)`, classes `5, 1, 1`), `6 − log 31 ≠ 6 − log 61`. Redémontré ici, sans
import de `RhGapCriterion`. -/
theorem residual_not_function_of_two_gap_state :
    ¬ ∃ φ : ℕ × ℕ → ℕ × ℕ × ℕ → ℝ, ∀ n, gapResidual (n + 1) =
      φ (fnPrimeAtRank (n + 1) - fnPrimeAtRank n, fnPrimeAtRank (n + 2) - fnPrimeAtRank (n + 1))
        (fnPrimeAtRank n % 6, fnPrimeAtRank (n + 1) % 6, fnPrimeAtRank (n + 2) % 6) := by
  rintro ⟨φ, hφ⟩
  have a := hφ 9
  have b := hφ 16
  simp only [gapResidual, show (9 : ℕ) + 1 = 10 from rfl, show (10 : ℕ) + 1 = 11 from rfl,
    show (16 : ℕ) + 1 = 17 from rfl, show (17 : ℕ) + 1 = 18 from rfl,
    primeAtRank_nine_eq, primeAtRank_ten_eq, primeAtRank_eleven_eq,
    primeAtRank_sixteen_eq, primeAtRank_seventeen_eq, primeAtRank_eighteen_eq] at a b
  norm_num at a b
  have hlt : Real.log 31 < Real.log 61 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [← a] at b
  linarith

/-- **Portée des obstructions** : avec la position `p_n` et l'écart `g_n`, le résidu est déterminé (tautologie). Toute
« prédiction » de `r_n` qui reçoit `p_n` et `g_n` ne mesure rien ; A3 et A3′ ne concernent pas une loi qui conserve
la position. -/
theorem gapResidual_of_position_and_gap (n : ℕ) :
    gapResidual n = ((fnPrimeAtRank (n + 1) - fnPrimeAtRank n : ℕ) : ℝ) - Real.log (fnPrimeAtRank n) := by
  unfold gapResidual
  rw [Nat.cast_sub (thm_primeAtRank_strictMono (Nat.lt_succ_self n)).le]

/-! ## 5. (A7) Termes croisés : la compensation est entièrement dans les termes croisés -/

/-- **Diagonale et termes croisés** : `(Σ_{n<m} r_n)² = Σ_{n<m} r_n² + 2 Σ_{n<m} r_n Σ_{j<n} r_j`, pour toute suite. -/
theorem sum_sq_eq_diag_add_cross (r : ℕ → ℝ) (m : ℕ) :
    (∑ n ∈ Finset.range m, r n) ^ 2 =
      ∑ n ∈ Finset.range m, r n ^ 2 + 2 * ∑ n ∈ Finset.range m, r n * ∑ j ∈ Finset.range n, r j := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, add_sq, ih]; ring

/-- Instance : résidu cumulé des écarts premiers. -/
theorem cumulativeResidual_sq (m : ℕ) :
    windowResidual 0 m ^ 2 = ∑ n ∈ Finset.range m, gapResidual n ^ 2 +
      2 * ∑ n ∈ Finset.range m, gapResidual n * ∑ j ∈ Finset.range n, gapResidual j := by
  unfold windowResidual; rw [← Finset.range_eq_Ico]; exact sum_sq_eq_diag_add_cross gapResidual m

/-- **Deux fenêtres consécutives** : `R_{a,c}² = R_{a,b}² + R_{b,c}² + 2 R_{a,b} R_{b,c}`. -/
theorem windowResidual_sq_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    windowResidual a c ^ 2 =
      windowResidual a b ^ 2 + windowResidual b c ^ 2 + 2 * windowResidual a b * windowResidual b c := by
  have : windowResidual a c = windowResidual a b + windowResidual b c := by
    unfold windowResidual; rw [Finset.sum_Ico_consecutive _ hab hbc]
  rw [this]; ring

/-- Bloc croisé par couple de classes : `Σ_{n<m, c_n = a} Σ_{j<n, c_j = b} r_n r_j` (tous décalages réunis ; la tranche de
décalage `h` est `K_{a,b}(h)`). -/
noncomputable def classCross (m a b : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range m).filter (fun n => gapClass n = a),
    ∑ j ∈ (Finset.range n).filter (fun j => gapClass j = b), gapResidual n * gapResidual j

theorem gapClass_lt (n : ℕ) : gapClass n < 6 := Nat.mod_lt _ (by norm_num)

/-- **Répartition exacte des termes croisés par couples de classes** : le terme croisé total est la somme des blocs
`classCross m a b`, `a, b < 6`. Identité ; aucune contrainte sur le signe des blocs. -/
theorem cross_eq_sum_classCross (m : ℕ) :
    ∑ n ∈ Finset.range m, gapResidual n * ∑ j ∈ Finset.range n, gapResidual j =
      ∑ a ∈ Finset.range 6, ∑ b ∈ Finset.range 6, classCross m a b := by
  have hj : ∀ n, ∑ j ∈ Finset.range n, gapResidual j =
      ∑ b ∈ Finset.range 6, ∑ j ∈ (Finset.range n).filter (fun j => gapClass j = b), gapResidual j :=
    fun n => (Finset.sum_fiberwise_of_maps_to
      (fun j _ => Finset.mem_range.mpr (gapClass_lt j)) gapResidual).symm
  calc ∑ n ∈ Finset.range m, gapResidual n * ∑ j ∈ Finset.range n, gapResidual j
      = ∑ n ∈ Finset.range m, ∑ b ∈ Finset.range 6,
          ∑ j ∈ (Finset.range n).filter (fun j => gapClass j = b), gapResidual n * gapResidual j := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [hj, Finset.mul_sum]; simp_rw [Finset.mul_sum]
    _ = ∑ a ∈ Finset.range 6, ∑ n ∈ (Finset.range m).filter (fun n => gapClass n = a), ∑ b ∈ Finset.range 6,
          ∑ j ∈ (Finset.range n).filter (fun j => gapClass j = b), gapResidual n * gapResidual j :=
        (Finset.sum_fiberwise_of_maps_to (fun n _ => Finset.mem_range.mpr (gapClass_lt n)) _).symm
    _ = ∑ a ∈ Finset.range 6, ∑ b ∈ Finset.range 6, classCross m a b := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        unfold classCross; exact Finset.sum_comm

/-! ## 6. (A8) Modes de classe : identités et non-détermination ALGÉBRIQUE -/

/-- Somme de classe `S_d(m) = Σ_{n<m, c_n = d} r_n`. -/
noncomputable def classResidualSum (d m : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range m).filter (fun n => gapClass n = d), gapResidual n

/-- **Partition** : `R_{0,m} = Σ_{d<6} S_d(m)`. -/
theorem windowResidual_class_partition (m : ℕ) :
    windowResidual 0 m = ∑ d ∈ Finset.range 6, classResidualSum d m := by
  unfold windowResidual classResidualSum; rw [← Finset.range_eq_Ico]
  exact (Finset.sum_fiberwise_of_maps_to (fun n _ => Finset.mem_range.mpr (gapClass_lt n)) gapResidual).symm

noncomputable def residualModeT (m : ℕ) : ℝ := classResidualSum 0 m + classResidualSum 2 m + classResidualSum 4 m
noncomputable def residualModeB (m : ℕ) : ℝ := 2 * classResidualSum 0 m - classResidualSum 2 m - classResidualSum 4 m
noncomputable def residualModeO (m : ℕ) : ℝ := classResidualSum 2 m - classResidualSum 4 m

/-- Inverses exactes : `S₀ = (T + B)/3`, `S₂ = (2T − B + 3O)/6`, `S₄ = (2T − B − 3O)/6`. -/
theorem residualMode_inverse (m : ℕ) :
    classResidualSum 0 m = (residualModeT m + residualModeB m) / 3 ∧
    classResidualSum 2 m = (2 * residualModeT m - residualModeB m + 3 * residualModeO m) / 6 ∧
    classResidualSum 4 m = (2 * residualModeT m - residualModeB m - 3 * residualModeO m) / 6 := by
  unfold residualModeT residualModeB residualModeO; exact ⟨by ring, by ring, by ring⟩

/-- **Énergie ponctuelle des modes** : `S₀² + S₂² + S₄² = T²/3 + B²/6 + O²/2` (orthogonalité algébrique). -/
theorem residualMode_energy (m : ℕ) :
    classResidualSum 0 m ^ 2 + classResidualSum 2 m ^ 2 + classResidualSum 4 m ^ 2 =
      residualModeT m ^ 2 / 3 + residualModeB m ^ 2 / 6 + residualModeO m ^ 2 / 2 := by
  unfold residualModeT residualModeB residualModeO; ring

/-- **Non-détermination ALGÉBRIQUE** : sur `ℝ³`, `T = s₀ + s₂ + s₄` n'est fonction d'aucune lecture de
`(B, O) = (2s₀ − s₂ − s₄, s₂ − s₄)` (témoins `(0,0,0)` et `(1,1,1)`). Énoncé sur des vecteurs arbitraires : il ne dit
rien de la suite réelle des premiers, ni indépendance statistique ni absence de contrainte arithmétique. -/
theorem modeT_not_function_of_BO :
    ¬ ∃ f : ℝ → ℝ → ℝ, ∀ s₀ s₂ s₄ : ℝ, s₀ + s₂ + s₄ = f (2 * s₀ - s₂ - s₄) (s₂ - s₄) := by
  rintro ⟨f, hf⟩
  have a := hf 0 0 0
  have b := hf 1 1 1
  norm_num at a b
  linarith

/-! ## 7. (D) Loi de compensation à l'échelle logarithmique, démontrée sans RH -/

/-- Résidu d'écart à l'échelle logarithmique : `r̃_n = log(p_{n+1}/p_n) − log p_n / p_n` (écart logarithmique moins sa
cadence attendue). -/
noncomputable def logGapResidual (n : ℕ) : ℝ :=
  Real.log ((fnPrimeAtRank (n + 1) : ℝ) / fnPrimeAtRank n) - Real.log (fnPrimeAtRank n) / fnPrimeAtRank n

/-- Les premiers `≤ p_m` sont exactement `p_0, …, p_m`. -/
theorem primes_le_primeAtRank_eq_image (m : ℕ) :
    (Finset.Ioc 0 (fnPrimeAtRank m)).filter Nat.Prime = (Finset.range (m + 1)).image fnPrimeAtRank := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, hq⟩, hp⟩
    refine ⟨Nat.count Nat.Prime q, ?_, Nat.nth_count hp⟩
    have he : fnPrimeAtRank (Nat.count Nat.Prime q) = q := Nat.nth_count hp
    rw [← he] at hq
    have := thm_primeAtRank_strictMono.le_iff_le.mp hq
    omega
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨(thm_primeAtRank_isPrime k).pos, thm_primeAtRank_strictMono.monotone (by omega)⟩,
      thm_primeAtRank_isPrime k⟩

/-- `Σ_{n≤m} log p_n / p_n = Σ_{d≤p_m premier} Λ(d)/d`. -/
theorem rank_log_div_eq_prime_sum (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), Real.log (fnPrimeAtRank n) / fnPrimeAtRank n =
      ∑ d ∈ (Finset.Ioc 0 (fnPrimeAtRank m)).filter Nat.Prime, Λ d / d := by
  rw [primes_le_primeAtRank_eq_image, Finset.sum_image (fun a _ b _ h => thm_primeAtRank_strictMono.injective h)]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [vonMangoldt_apply_prime (thm_primeAtRank_isPrime n)]

/-- Puissances de premiers non premières : `Σ_{d≤x, d non premier} Λ(d)/d ≤ 1537 / log 2` (par le défaut
`Σ Λ(d)(log d − Λ(d))/d ≤ 1537` du port zeta23, et `log d − Λ(d) ≥ log 2` sur ces `d`). -/
theorem nonprime_mangoldt_div_le (N : ℕ) :
    ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime), Λ d / d ≤ 1537 / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdef := Zeta23.Cheb.defect_bounded_explicit (N : ℝ)
  rw [Nat.floor_natCast] at hdef
  have hterm : ∀ d ∈ Finset.Ioc 0 N, 0 ≤ Λ d * (Real.log d - Λ d) / d := by
    intro d _
    have := vonMangoldt_le_log (n := d)
    exact div_nonneg (mul_nonneg vonMangoldt_nonneg (by linarith)) (Nat.cast_nonneg _)
  have hsub : ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime), Λ d * (Real.log d - Λ d) / d ≤ 1537 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun d hd _ => hterm d hd)) hdef
  rw [le_div_iff₀ hl2, Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum (fun d hd => ?_)) hsub
  rw [Finset.mem_filter, Finset.mem_Ioc] at hd
  by_cases hΛ : Λ d = 0
  · rw [hΛ]; simp
  · have hpp : IsPrimePow d := vonMangoldt_ne_zero_iff.mp hΛ
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hp' : p.Prime := hp.nat_prime
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst this; exact hd.2 (by simpa using hp')
    have hΛp : Λ (p ^ k) = Real.log p := by
      rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp']
    have hlogp : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp'.two_le)
    have hlogpk : Real.log ((p ^ k : ℕ) : ℝ) = k * Real.log p := by push_cast; rw [Real.log_pow]
    have hdiff : Real.log 2 ≤ Real.log ((p ^ k : ℕ) : ℝ) - Λ (p ^ k) := by
      rw [hlogpk, hΛp]
      have : (1 : ℝ) ≤ (k : ℝ) - 1 := by
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        linarith
      nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast hp'.one_lt.le)]
    have hpos : 0 ≤ Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) := div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
    calc Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) * Real.log 2
        ≤ Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) * (Real.log ((p ^ k : ℕ) : ℝ) - Λ (p ^ k)) :=
          mul_le_mul_of_nonneg_left hdiff hpos
      _ = Λ (p ^ k) * (Real.log ((p ^ k : ℕ) : ℝ) - Λ (p ^ k)) / ((p ^ k : ℕ) : ℝ) := by ring

/-- **Mertens aux seuls premiers** : `|Σ_{n≤m} log p_n / p_n − log p_m| ≤ log 4 + 6 + 1537/log 2`. -/
theorem rank_mertens (m : ℕ) :
    |∑ n ∈ Finset.range (m + 1), Real.log (fnPrimeAtRank n) / fnPrimeAtRank n - Real.log (fnPrimeAtRank m)| ≤
      Real.log 4 + 6 + 1537 / Real.log 2 := by
  set N := fnPrimeAtRank m
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (thm_primeAtRank_isPrime m).one_lt.le
  have hM := Zeta23.Cheb.mertensFirst hN
  rw [Nat.floor_natCast] at hM
  have hsplit : ∑ d ∈ Finset.Ioc 0 N, Λ d / d =
      ∑ d ∈ (Finset.Ioc 0 N).filter Nat.Prime, Λ d / d +
        ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime), Λ d / d :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hnp := nonprime_mangoldt_div_le N
  have hnp0 : 0 ≤ ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ d.Prime), Λ d / d :=
    Finset.sum_nonneg (fun d _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
  rw [rank_log_div_eq_prime_sum]
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le] at hM ⊢
  constructor <;> linarith [hM.1, hM.2]

/-- **(D) Compensation à l'échelle logarithmique, sans RH** : le résidu cumulé des écarts logarithmiques
`Σ_{n<m} (log(p_{n+1}/p_n) − log p_n / p_n)` reste borné par une constante explicite, pour tout `m` (Mertens aux seuls
premiers, Bertrand). Borne triviale : `O(log p_m)` ; démontré : `O(1)`. Portée : le poids `1/p_n` éteint les fluctuations
de taille `√p` ; ce n'est PAS la borne critique du résidu linéaire (`hResidualCloses`, force de RH). -/
theorem logGapResidual_cumulative_bounded (m : ℕ) :
    |∑ n ∈ Finset.range m, logGapResidual n| ≤ 2 * Real.log 2 + Real.log 4 + 6 + 1537 / Real.log 2 := by
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hC0 : 0 ≤ Real.log 4 + 6 + 1537 / Real.log 2 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num); positivity
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp; positivity
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hpos' : ∀ n, (0 : ℝ) < fnPrimeAtRank n := fun n => by exact_mod_cast (thm_primeAtRank_isPrime n).pos
  have htel : ∑ n ∈ Finset.range (k + 1), logGapResidual n =
      Real.log (fnPrimeAtRank (k + 1)) - Real.log 2 -
        ∑ n ∈ Finset.range (k + 1), Real.log (fnPrimeAtRank n) / fnPrimeAtRank n := by
    have : ∀ j, ∑ n ∈ Finset.range j, logGapResidual n =
        Real.log (fnPrimeAtRank j) - Real.log 2 -
          ∑ n ∈ Finset.range j, Real.log (fnPrimeAtRank n) / fnPrimeAtRank n := by
      intro j
      induction j with
      | zero => simp [thm_primeAtRank_zero_eq_two]
      | succ j ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
        unfold logGapResidual
        rw [Real.log_div (hpos' _).ne' (hpos' _).ne']; ring
    exact this (k + 1)
  have hmert := rank_mertens k
  -- `log p_{k+1} − log p_k ∈ [0, log 2]` (Bertrand)
  have hstep0 : Real.log (fnPrimeAtRank k) ≤ Real.log (fnPrimeAtRank (k + 1)) :=
    Real.log_le_log (hpos' k) (by exact_mod_cast (thm_primeAtRank_strictMono (Nat.lt_succ_self k)).le)
  obtain ⟨q, hq, hkq, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (fnPrimeAtRank k)
    (thm_primeAtRank_isPrime k).ne_zero
  have hQ : fnPrimeAtRank (k + 1) ≤ 2 * fnPrimeAtRank k :=
    le_trans (primeAtRank_succ_le_of_prime_gt hq hkq) hq2
  have hstep1 : Real.log (fnPrimeAtRank (k + 1)) ≤ Real.log 2 + Real.log (fnPrimeAtRank k) := by
    rw [← Real.log_mul (by norm_num) (hpos' k).ne']
    exact Real.log_le_log (hpos' _) (by exact_mod_cast hQ)
  rw [htel, abs_le]
  rw [abs_le] at hmert
  constructor <;> linarith [hmert.1, hmert.2]

/-! ## 8. (E329) Loi intermédiaire au poids `p^{−α}` : force exacte (région sans zéro)

Candidat de loi indépendante, premiers seuls : la somme pondérée `S_α(m) = Σ_{n<m} (g_n − log p_n) p_n^{−α}` reste bornée.
Au poids `1/p` (α = 1, forme logarithmique) la loi est démontrée sans RH (§7). Au poids `p^{−α}`, `1/2 < α ≤ 1`, elle donne
par sommation d'Abel `|p_m − ϑ(p_m)| ≤ C p_m^α`, donc (§3) une bande sans zéro `β ≤ α` : sa force est celle d'un
DEMI-PLAN SANS ZÉRO `Re s > α`. Pour α < 1 aucun tel demi-plan n'est démontré (ni ici, ni dans la littérature) ; pour tout
α > 1/2 à la fois, c'est RH. Ce paragraphe classe le candidat ; il ne le démontre pas. -/

/-- Somme pondérée des résidus d'écarts `S_α(m) = Σ_{n<m} r_n p_n^{−α}` (premiers seuls). -/
noncomputable def weightedResidual (α : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range m, gapResidual n * (fnPrimeAtRank n : ℝ) ^ (-α)

/-- Sommation d'Abel : `Σ_{n<m} (S_{n+1} − S_n) w_n = S_m w_m − Σ_{n<m} S_{n+1} (w_{n+1} − w_n)` (`S_0 = 0`). -/
theorem abel_partial (S w : ℕ → ℝ) (h0 : S 0 = 0) (m : ℕ) :
    ∑ n ∈ Finset.range m, (S (n + 1) - S n) * w n =
      S m * w m - ∑ n ∈ Finset.range m, S (n + 1) * (w (n + 1) - w n) := by
  induction m with
  | zero => simp [h0]
  | succ m ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]; ring

/-- `p_n^α` est croissante en `n` pour `α ≥ 0`. -/
theorem primeAtRank_rpow_mono {α : ℝ} (hα : 0 ≤ α) {a b : ℕ} (h : a ≤ b) :
    (fnPrimeAtRank a : ℝ) ^ α ≤ (fnPrimeAtRank b : ℝ) ^ α := by
  apply Real.rpow_le_rpow (by positivity) _ hα
  exact_mod_cast Nat.nth_monotone Nat.infinite_setOf_prime h

/-- **Abel** : `|S_α| ≤ B` partout ⟹ `|R_{0,m}| ≤ 2B p_m^α`. -/
theorem windowResidual_bound_of_weighted {α B : ℝ} (hα : 0 ≤ α)
    (hB : ∀ m, |weightedResidual α m| ≤ B) (m : ℕ) :
    |windowResidual 0 m| ≤ 2 * B * (fnPrimeAtRank m : ℝ) ^ α := by
  set w : ℕ → ℝ := fun n => (fnPrimeAtRank n : ℝ) ^ α with hw
  have hpos : ∀ n, 0 < (fnPrimeAtRank n : ℝ) := fun n => by
    exact_mod_cast (thm_primeAtRank_isPrime n).pos
  have hterm : ∀ n, gapResidual n = (weightedResidual α (n + 1) - weightedResidual α n) * w n := by
    intro n
    simp only [weightedResidual, Finset.sum_range_succ, add_sub_cancel_left, hw]
    rw [mul_assoc, ← Real.rpow_add (hpos n), neg_add_cancel, Real.rpow_zero, mul_one]
  have hsum : windowResidual 0 m = ∑ n ∈ Finset.range m,
      (weightedResidual α (n + 1) - weightedResidual α n) * w n := by
    unfold windowResidual; rw [← Finset.range_eq_Ico]; exact Finset.sum_congr rfl (fun n _ => hterm n)
  have hmono : ∀ n, w n ≤ w (n + 1) := fun n => primeAtRank_rpow_mono hα (Nat.le_succ n)
  have hwnn : ∀ n, 0 ≤ w n := fun n => by show 0 ≤ (fnPrimeAtRank n : ℝ) ^ α; positivity
  have hw0 : 0 ≤ w 0 := hwnn 0
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  rw [hsum, abel_partial _ w (by simp [weightedResidual])]
  have h1 : |weightedResidual α m * w m| ≤ B * w m := by
    rw [abs_mul, abs_of_nonneg (hwnn m)]
    exact mul_le_mul_of_nonneg_right (hB m) (hwnn m)
  have h2 : |∑ n ∈ Finset.range m, weightedResidual α (n + 1) * (w (n + 1) - w n)| ≤ B * (w m - w 0) := by
    calc |∑ n ∈ Finset.range m, weightedResidual α (n + 1) * (w (n + 1) - w n)|
        ≤ ∑ n ∈ Finset.range m, |weightedResidual α (n + 1) * (w (n + 1) - w n)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range m, B * (w (n + 1) - w n) := by
          apply Finset.sum_le_sum; intro n _
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hmono n))]
          exact mul_le_mul_of_nonneg_right (hB _) (sub_nonneg.mpr (hmono n))
      _ = B * (w m - w 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub (fun n => w n)]
  calc |weightedResidual α m * w m - ∑ n ∈ Finset.range m, weightedResidual α (n + 1) * (w (n + 1) - w n)|
      ≤ |weightedResidual α m * w m| + |∑ n ∈ Finset.range m, weightedResidual α (n + 1) * (w (n + 1) - w n)| :=
        abs_sub _ _
    _ ≤ B * w m + B * (w m - w 0) := add_le_add h1 h2
    _ ≤ 2 * B * w m := by nlinarith

/-- **Force exacte du candidat** : `|S_α| ≤ B` (`1/2 < α ≤ 1`) ⟹ tout vrai zéro a une partie réelle `≤ α`
(demi-plan sans zéro `Re s > α`). -/
theorem zero_free_of_weighted_residual {α B : ℝ} (hα : 1 / 2 < α) (hα1 : α ≤ 1)
    (hB : ∀ m, |weightedResidual α m| ≤ B) (w : TrueZero) : rZeroRadialPosition w.1 ≤ α := by
  have hα0 : 0 < α := by linarith
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  refine zero_free_of_rank_bound (C := 2 * B + 2 + 1 / α) hα hα1 (by positivity) (fun k => ?_) w
  have hp1 : (1 : ℝ) ≤ fnPrimeAtRank k := by
    have := (thm_primeAtRank_isPrime k).two_le; exact_mod_cast (by omega : 1 ≤ fnPrimeAtRank k)
  have hx : (1 : ℝ) ≤ (fnPrimeAtRank k : ℝ) ^ α := Real.one_le_rpow hp1 hα0.le
  have hlog0 : 0 ≤ Real.log (fnPrimeAtRank k) := Real.log_nonneg hp1
  have hlog : Real.log (fnPrimeAtRank k) ≤ (fnPrimeAtRank k : ℝ) ^ α / α :=
    Real.log_le_rpow_div (by linarith) hα0
  have hR := windowResidual_bound_of_weighted hα0.le hB k
  rw [← cumulativeResidual_shift]
  have hdiv : (fnPrimeAtRank k : ℝ) ^ α / α = 1 / α * (fnPrimeAtRank k : ℝ) ^ α := by ring
  rw [hdiv] at hlog
  obtain ⟨hR1, hR2⟩ := abs_le.mp hR
  have hpa : 0 ≤ (fnPrimeAtRank k : ℝ) ^ α := by positivity
  have hia : 0 ≤ 1 / α * (fnPrimeAtRank k : ℝ) ^ α := by positivity
  rw [abs_le]; constructor <;> nlinarith

/-- **Forme fermante de l'obligation terminale, premiers seuls** : sous un zéro `l` de partie réelle `< 1/2`, toute loi
au poids `p^{−α}` avec `1/2 < α < 1 − β_l` est fausse (le miroir de `l` a la partie réelle `1 − β_l > α`). -/
theorem weighted_law_excludes_low {α B : ℝ} (hα : 1 / 2 < α) (hB : ∀ m, |weightedResidual α m| ≤ B)
    (l : TrueZero) (hαl : α < 1 - rZeroRadialPosition l.1) : False := by
  have hm := zero_free_of_weighted_residual hα (by linarith [thm_zeroRadialPosition_positive l.1]) hB (mirrorMember l)
  rw [mirrorMember_radial] at hm
  linarith

/-- **(E329) Fermeture conditionnelle par la famille des lois intermédiaires** : si pour tout `α > 1/2` la somme
pondérée `S_α` est bornée, alors RH. Hypothèse de la force de RH ; démontrée nulle part. -/
theorem riemannHypothesis_of_weighted_residual
    (h : ∀ α : ℝ, 1 / 2 < α → α ≤ 1 → ∃ B, ∀ m, |weightedResidual α m| ≤ B) : RiemannHypothesis := by
  have hhalf : ∀ w : TrueZero, rZeroRadialPosition w.1 ≤ 1 / 2 := by
    intro w
    by_contra hgt
    push Not at hgt
    set β := rZeroRadialPosition w.1
    set α := min ((β + 1 / 2) / 2) 1
    obtain ⟨B, hB⟩ := h α (lt_min (by linarith) (by norm_num)) (min_le_right _ _)
    have := zero_free_of_weighted_residual (lt_min (by linarith) (by norm_num)) (min_le_right _ _) hB w
    have := le_trans this (min_le_left _ _)
    linarith
  refine riemannHypothesis_iff_noLowerSide.mpr (fun z hz => ?_)
  have := hhalf (mirrorMember z)
  rw [mirrorMember_radial] at this
  linarith

end RHV6Fresh

#print axioms RHV6Fresh.cumulativeResidual_eq
#print axioms RHV6Fresh.cell_control_of_rank_bound
#print axioms RHV6Fresh.zero_free_of_rank_bound
#print axioms RHV6Fresh.riemannHypothesis_of_cumulative_residual_bound
#print axioms RHV6Fresh.prime_blocks_of_riemannHypothesis
#print axioms RHV6Fresh.residual_not_function_of_transition
#print axioms RHV6Fresh.residual_not_function_of_two_gap_state
#print axioms RHV6Fresh.cross_eq_sum_classCross
#print axioms RHV6Fresh.windowResidual_sq_split
#print axioms RHV6Fresh.residualMode_energy
#print axioms RHV6Fresh.modeT_not_function_of_BO
#print axioms RHV6Fresh.nonprime_mangoldt_div_le
#print axioms RHV6Fresh.rank_mertens
#print axioms RHV6Fresh.logGapResidual_cumulative_bounded
#print axioms RHV6Fresh.windowResidual_bound_of_weighted
#print axioms RHV6Fresh.zero_free_of_weighted_residual
#print axioms RHV6Fresh.weighted_law_excludes_low
#print axioms RHV6Fresh.riemannHypothesis_of_weighted_residual
