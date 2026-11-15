/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.InversePrimeSpectral

/-!
# Matrice locale–globale des écarts, identité distributionnelle signée, transitions (E336 ; auteur, 2026-10-18)

Correction après l'audit d'E334 : la reconstruction inverse globale est confirmée, la structure locale–globale des
écarts était insuffisamment traitée. Ce module est importé et n'est pas composé dans la chaîne. Il écrit :

* §1 L'identité distributionnelle COMPLÈTE, avec ses signes, son facteur 2, ses jacobiens et sa convention de sommation. Le
  facteur de normalisation est `g(x) = −log x · e^{−log x/2}/2` (en `u = log x` : `−u e^{−u/2}/2`). Le POIDS des atomes est
  positif, `Λ(n)/√n` (`normalized_atom_weight`). Le FACTEUR appliqué est négatif. L'atome du signal normalisé vaut donc
  `−½·Λ(n)/√n` (`normalized_atom_pairing`). Le fond (terme principal `1/log x`) donne la densité `−½ e^{u/2}` en `u`
  (`normalized_background_pairing`), soustraite. Chaque paire conjuguée de zéros donne le mode
  `e^{(β−1/2)u} cos(Tu)` (`normalized_mode_pairing`). Le facteur `−2` d'une paire (`−2 Re Ei(ρ log x)` compte `ρ` et
  `ρ̄` ensemble, `counting_pair_hasDerivAt`) et le `½` du facteur se compensent : un cosinus par paire, sommé par paires.
  Jacobiens : les atomes sont transportés sans jacobien (image d'une mesure de Dirac) ; les densités reçoivent `e^u`
  (`integral_log_transport`). La somme sur une famille finie est linéaire (`normalized_modes_pairing`). La formule
  explicite du canal `J` (`CountingExplicitFormula`) reste NOMMÉE et non démontrée : le côté spectral n'est écrit que pour
  une famille finie, et le complément n'est jamais supposé petit.
* §2 La matrice. Pour une colonne (un zéro `j`) et une ligne (un écart `[p_n, p_{n+1}]`), l'entrée est
  `d_{j,n} = cellModulation z p_n p_{n+1} = −2∫ x^{β−1}cos(T log x)/log x`. Sur un écart premier, l'identité
  `D_n = S_{n,N} + R_{n,N}` est écrite avec `D_n = 1 + Σ internes − ΔF` (`gap_matrix_identity`).
* §3 Les transitions. Les colonnes sont additives sur des écarts consécutifs (`cellModulation_add`), quelle que soit la
  position radiale. Les corrections, les sommes partielles et les compléments télescopent sur toute fenêtre de nœuds
  (`window_telescope_*`). Une transition grammaticale n'impose donc aucune relation entre les entrées d'un mode à
  paramètres fixés au-delà du télescopage (`transitions_no_constraint_beyond_telescoping`). Ce qui change à un événement
  est le saut de `J₀`, porté par le complément seul (`complement_discontinuous_of_jump`, rappelé).
* §4 L'identifiabilité. Échantillonné sur une grille uniforme de pas `h` en `u`, un mode de fréquence `T` et un mode de
  fréquence `T + 2πk/h` ont les MÊMES échantillons, à une phase constante près, quelle que soit la position radiale
  (`alias_mode_samples`). C'est la cause de l'échec de la poursuite directe sur les `D_n` (E334-C v1). Sur un écart
  `[p, q]`, la condition sans repliement `T·log(q/p) < π` (moins d'un demi-tour, `halfTurnsOnGap < 1`) est impliquée par
  `T < π p/(q − p)` (`resolution_of_gap_bound`) : c'est la grandeur `T_req` d'E334.
* §5 Le raccord des canaux, membre par membre. La primitive lissée `−2 Re(x^{ρ+1}/(ρ(ρ+1)))` a pour dérivée la contribution
  brute `−2 Re(x^ρ/ρ)` (`smoothedPrimitive_hasDerivAt`). Celle-ci a pour dérivée `log x` fois la densité du canal `J`
  (`counting_modulation_eq_raw_derivative`, rappelé). Le terme lissé du dépôt vaut `x·√x·c̃ = m·primitive`
  (`smoothedPrimitive_eq_normalizedSmoothed`). Le transport de la SOMME entière, d'un canal à l'autre, n'est pas écrit : la
  convergence lissée (`smoothedCanonical_hasSum`) ne se dérive pas terme à terme.

Portée : identités vraies pour toute famille finie et toute position radiale. Aucune n'est une contrainte sur `β`. La
contrainte cherchée, « les mêmes modes sans réajustement reproduisent chaque écart et chaque transition », est satisfaite
par construction par tout mode à paramètres fixés (§3). Elle ne porte que sur le complément.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## §1 Identité distributionnelle signée -/

/-- Facteur de normalisation en `x` : `g(x) = −log x · e^{−log x/2}/2` (en `u = log x` : `−u e^{−u/2}/2`). -/
noncomputable def normalizationFactor (x : ℝ) : ℝ := -(Real.log x * Real.exp (-(Real.log x) / 2) / 2)

/-- Poids d'un atome du signal normalisé : `w(n)·g(n) = −½·Λ(n)/√n`, pour tout `n` (aux rangs `0, 1`, les deux côtés
sont nuls). Le poids `Λ(n)/√n` est positif et le facteur est négatif. -/
theorem normalized_atom_signed (n : ℕ) :
    countingWeight n * normalizationFactor n = -(1 / 2) * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp [countingWeight, normalizationFactor]
  · have h := normalized_atom_weight hn
    unfold normalizationFactor
    rw [← h]; ring

/-- **Atomes du signal normalisé** : contre une fonction test `φ`, avec `ψ = g·φ` de classe `C¹` sur `[a, b]` et `φ`
nulle aux bords, `−∫_a^b J₋ ψ' = −½·Σ_{a<n<b} Λ(n)/√n · φ(n)`. C'est l'appariement `⟨g·DJ, φ⟩`. -/
theorem normalized_atom_pairing {φ ψ' : ℝ → ℝ} {a b : ℝ} {N : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    (hψ : ∀ t ∈ Set.Icc a b, HasDerivAt (fun t => normalizationFactor t * φ t) (ψ' t) t)
    (hψ' : ContinuousOn ψ' (Set.Icc a b)) (ha : φ a = 0) (hb : φ b = 0) :
    -∫ t in a..b, countingJLeft t * ψ' t =
      -(1 / 2) * ∑ n ∈ Finset.range N,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * (if a < (n : ℝ) ∧ (n : ℝ) < b then φ n else 0) := by
  rw [counting_distributional_derivative hab hbN hψ hψ' (by simp [ha]) (by simp [hb]), neg_neg,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h := normalized_atom_signed n
  split_ifs
  · rw [← mul_assoc, h]; ring
  · ring

/-- Normalisation du terme principal du fond : `g(x)·(1/log x) = −½ e^{−log x/2}` pour `x > 1`. -/
theorem normalizationFactor_div_log {x : ℝ} (hx : 1 < x) :
    normalizationFactor x * (1 / Real.log x) = -(1 / 2) * Real.exp (-(Real.log x) / 2) := by
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  unfold normalizationFactor
  field_simp

/-- **Jacobien du transport `u = log x`** : pour `1 < a ≤ b` et `h` continue sur `[a, b]`,
`∫_a^b h(x) dx = ∫_{log a}^{log b} h(e^u) e^u du`. -/
theorem integral_log_transport {h : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hh : ContinuousOn h (Set.Icc a b)) :
    ∫ u in Real.log a..Real.log b, h (Real.exp u) * Real.exp u = ∫ x in a..b, h x := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hle : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have himg : Real.exp '' Set.uIcc (Real.log a) (Real.log b) ⊆ Set.Icc a b := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Set.uIcc_of_le hle] at hu
    constructor
    · calc a = Real.exp (Real.log a) := (Real.exp_log ha).symm
        _ ≤ Real.exp u := Real.exp_le_exp.mpr hu.1
    · calc Real.exp u ≤ Real.exp (Real.log b) := Real.exp_le_exp.mpr hu.2
        _ = b := Real.exp_log hb
  have h := intervalIntegral.integral_comp_mul_deriv' (a := Real.log a) (b := Real.log b) (f := Real.exp)
    (f' := Real.exp) (g := h) (fun u _ => Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn (hh.mono himg)
  rw [Real.exp_log ha, Real.exp_log hb] at h
  exact h

/-- **Fond du signal normalisé** : `∫_a^b g(x)·(1/log x)·φ(x) dx = −½ ∫_{log a}^{log b} e^{u/2} φ(e^u) du`, pour `1 < a ≤ b`
et `φ` continue. La densité `e^u/u` du fond, transportée et normalisée, vaut `−½ e^{u/2}` ; elle est soustraite dans `A`. -/
theorem normalized_background_pairing {φ : ℝ → ℝ} {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Set.Icc a b)) :
    ∫ x in a..b, normalizationFactor x * (1 / Real.log x) * φ x =
      -(1 / 2) * ∫ u in Real.log a..Real.log b, Real.exp (u / 2) * φ (Real.exp u) := by
  have ha0 : 0 < a := lt_trans one_pos ha
  have hcont : ContinuousOn (fun x => -(1 / 2) * Real.exp (-(Real.log x) / 2) * φ x) (Set.Icc a b) := by
    have hlog : ContinuousOn Real.log (Set.Icc a b) :=
      Real.continuousOn_log.mono fun x hx => (lt_of_lt_of_le ha0 hx.1).ne'
    exact (continuousOn_const.mul (Real.continuous_exp.comp_continuousOn (hlog.neg.div_const _))).mul hφ
  have hcongr : ∫ x in a..b, normalizationFactor x * (1 / Real.log x) * φ x =
      ∫ x in a..b, -(1 / 2) * Real.exp (-(Real.log x) / 2) * φ x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hab] at hx
    rw [normalizationFactor_div_log (lt_of_lt_of_le ha hx.1)]
  rw [hcongr, ← integral_log_transport ha0 hab hcont, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [Real.log_exp]
  have : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by rw [← Real.exp_add]; congr 1; ring
  rw [← this]; ring

/-- **Un mode** : `∫_a^b g(x)·b'_ρ(x)·φ(x) dx = ∫_{log a}^{log b} e^{(β−1/2)u} cos(Tu) φ(e^u) du`, pour `1 < a ≤ b` et `φ`
continue ; `b'_ρ = countingModulationDensity` est la densité de la paire `(ρ, ρ̄)`. -/
theorem normalized_mode_pairing (z : TrueZero) {φ : ℝ → ℝ} {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Set.Icc a b)) :
    ∫ x in a..b, normalizationFactor x * countingModulationDensity z x * φ x =
      ∫ u in Real.log a..Real.log b,
        Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * u) * Real.cos (rZeroHeight z.1 * u) * φ (Real.exp u) := by
  have ha0 : 0 < a := lt_trans one_pos ha
  have hgc : ContinuousOn normalizationFactor (Set.Icc a b) := by
    unfold normalizationFactor
    have hlog : ContinuousOn Real.log (Set.Icc a b) :=
      Real.continuousOn_log.mono fun x hx => (lt_of_lt_of_le ha0 hx.1).ne'
    exact ((hlog.mul (Real.continuous_exp.comp_continuousOn (hlog.neg.div_const _))).div_const _).neg
  have hcont : ContinuousOn (fun x => normalizationFactor x * countingModulationDensity z x * φ x) (Set.Icc a b) :=
    (hgc.mul (countingModulationDensity_continuousOn z ha)).mul hφ
  rw [← integral_log_transport ha0 hab hcont]
  have hle : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le hle] at hu
  have hu0 : 0 < u := lt_of_lt_of_le (Real.log_pos ha) hu.1
  have h := normalized_mode_density z hu0
  simp only [normalizationFactor, Real.log_exp] at h ⊢
  rw [← h]; ring

/-- **Somme finie des modes** (convention : une entrée par paire conjuguée, famille finie `s`) : l'appariement de la somme
des densités est la somme des modes normalisés. -/
theorem normalized_modes_pairing (s : Finset TrueZero) {φ : ℝ → ℝ} {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Set.Icc a b)) :
    ∫ x in a..b, normalizationFactor x * (∑ z ∈ s, countingModulationDensity z x) * φ x =
      ∑ z ∈ s, ∫ u in Real.log a..Real.log b,
        Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * u) * Real.cos (rZeroHeight z.1 * u) * φ (Real.exp u) := by
  have ha0 : 0 < a := lt_trans one_pos ha
  have hgc : ContinuousOn normalizationFactor (Set.Icc a b) := by
    unfold normalizationFactor
    have hlog : ContinuousOn Real.log (Set.Icc a b) :=
      Real.continuousOn_log.mono fun x hx => (lt_of_lt_of_le ha0 hx.1).ne'
    exact ((hlog.mul (Real.continuous_exp.comp_continuousOn (hlog.neg.div_const _))).div_const _).neg
  have hI : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hint : ∀ z ∈ s, IntervalIntegrable (fun x => normalizationFactor x * countingModulationDensity z x * φ x)
      MeasureTheory.volume a b := fun z _ =>
    (hI ▸ ((hgc.mul (countingModulationDensity_continuousOn z ha)).mul hφ)).intervalIntegrable
  have hcongr : ∫ x in a..b, normalizationFactor x * (∑ z ∈ s, countingModulationDensity z x) * φ x =
      ∫ x in a..b, ∑ z ∈ s, normalizationFactor x * countingModulationDensity z x * φ x := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [hcongr, intervalIntegral.integral_finsetSum hint]
  exact Finset.sum_congr rfl fun z _ => normalized_mode_pairing z ha hab hφ

/-! ## §2 La matrice des contributions locales -/

/-- **Identité de la matrice sur un écart premier** : `D_n = S_{n,N} + R_{n,N}`, avec `D_n = 1 + Σ internes − ΔF` (depuis `Λ`),
`S_{n,N} = Σ_{j∈s} d_{j,n}` (colonnes = intégrales des densités sur ce même écart) et `R_{n,N}` le complément. -/
theorem gap_matrix_identity (s : Finset TrueZero) {F : TrueZero → ℂ → ℂ} (Fb : ℝ → ℝ) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q)
    (hF : ∀ z ∈ s, ∀ t ∈ Set.Icc (p : ℝ) q, HasDerivAt (F z)
      (Complex.exp (zeroPoint z * (Real.log t : ℂ)) / (zeroPoint z * (Real.log t : ℂ)))
      (zeroPoint z * (Real.log t : ℂ))) :
    1 + (∑ n ∈ Finset.Ico (p + 1) q, countingWeight n) - (Fb q - Fb p) =
      (∑ z ∈ s, cellModulation z p q) + gapComplement (fun x => countingJHalf x - Fb x) s F p q := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hle : (p : ℝ) ≤ q := by exact_mod_cast hpq.le
  rw [← gapCountingCorrection_prime_gap Fb hp hq hpq, ← gapSumIncrement_eq_sum_cells s h1 hle hF]
  unfold gapComplement gapCountingCorrection
  ring

/-! ## §3 Transitions : additivité et télescopage, pour toute position radiale -/

/-- **Une colonne est additive sur deux écarts consécutifs**, pour toute position radiale : `d(a,b) + d(b,c) = d(a,c)`. -/
theorem cellModulation_add (z : TrueZero) {a b c : ℝ} (ha : 1 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    cellModulation z a b + cellModulation z b c = cellModulation z a c := by
  unfold cellModulation
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have i1 : IntervalIntegrable (countingModulationDensity z) MeasureTheory.volume a b :=
    ((Set.uIcc_of_le hab).symm ▸ countingModulationDensity_continuousOn z ha (b := b)).intervalIntegrable
  have i2 : IntervalIntegrable (countingModulationDensity z) MeasureTheory.volume b c :=
    ((Set.uIcc_of_le hbc).symm ▸ countingModulationDensity_continuousOn z hb (b := c)).intervalIntegrable
  exact intervalIntegral.integral_add_adjacent_intervals i1 i2

/-- Télescopage des corrections sur une fenêtre de nœuds `x 0, …, x m`. -/
theorem window_telescope_correction (Fb : ℝ → ℝ) (x : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range m, gapCountingCorrection Fb (x k) (x (k + 1)) = gapCountingCorrection Fb (x 0) (x m) := by
  unfold gapCountingCorrection
  rw [Finset.sum_range_sub (fun k => countingJHalf (x k) - Fb (x k))]

/-- Télescopage d'une colonne sur une fenêtre de nœuds croissants `> 1`, pour toute position radiale. -/
theorem window_telescope_column (z : TrueZero) (x : ℕ → ℝ) (m : ℕ) (h1 : 1 < x 0) (hmono : Monotone x) :
    ∑ k ∈ Finset.range m, cellModulation z (x k) (x (k + 1)) = cellModulation z (x 0) (x m) := by
  induction m with
  | zero => simp [cellModulation]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    exact cellModulation_add z h1 (hmono (Nat.zero_le m)) (hmono (Nat.le_succ m))

/-- Télescopage du complément sur une fenêtre de nœuds. -/
theorem window_telescope_complement (C : ℝ → ℝ) (s : Finset TrueZero) (F : TrueZero → ℂ → ℂ) (x : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range m, gapComplement C s F (x k) (x (k + 1)) = gapComplement C s F (x 0) (x m) := by
  induction m with
  | zero => simp [gapComplement, gapSumIncrement]
  | succ m ih => rw [Finset.sum_range_succ, ih, gapComplement_add]

/-- **Aucune contrainte de transition au-delà du télescopage** : pour toute famille finie (toutes positions radiales), toute
fenêtre de nœuds `x 0 < … < x m` au-dessus de `1` et tout fond `Fb`, si l'identité `D = S + R` vaut sur chaque écart, elle
vaut sur la fenêtre entière avec la colonne de chaque mode SANS réajustement. Les équations de transition sont des
conséquences linéaires des équations d'écart ; elles ne fixent rien de `(β, T)`. -/
theorem transitions_no_constraint_beyond_telescoping (s : Finset TrueZero) (F : TrueZero → ℂ → ℂ) (Fb : ℝ → ℝ)
    (x : ℕ → ℝ) (m : ℕ) (h1 : 1 < x 0) (hmono : Monotone x)
    (hgap : ∀ k < m, gapCountingCorrection Fb (x k) (x (k + 1)) =
      (∑ z ∈ s, cellModulation z (x k) (x (k + 1))) +
        gapComplement (fun y => countingJHalf y - Fb y) s F (x k) (x (k + 1))) :
    gapCountingCorrection Fb (x 0) (x m) =
      (∑ z ∈ s, cellModulation z (x 0) (x m)) + gapComplement (fun y => countingJHalf y - Fb y) s F (x 0) (x m) := by
  rw [← window_telescope_correction, ← window_telescope_complement]
  have hcol : ∀ z ∈ s, cellModulation z (x 0) (x m) = ∑ k ∈ Finset.range m, cellModulation z (x k) (x (k + 1)) :=
    fun z _ => (window_telescope_column z x m h1 hmono).symm
  rw [Finset.sum_congr rfl hcol, Finset.sum_comm, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k hk => hgap k (Finset.mem_range.mp hk)

/-! ## §4 Identifiabilité : repliement sur une grille uniforme, résolution d'un écart -/

/-- **Repliement** : sur la grille `u_j = u₀ + j h` (`h ≠ 0`), le mode complexe de fréquence `T + 2πk/h` est le mode de
fréquence `T` multiplié par une phase CONSTANTE `e^{2πi k u₀/h}`, pour toute amplitude `e^{(β−1/2)u}` : les échantillons ne
séparent pas les deux fréquences. -/
theorem alias_mode_samples (d T u₀ h : ℝ) (hh : h ≠ 0) (k j : ℤ) :
    Complex.exp (((d * (u₀ + j * h) : ℝ) : ℂ)) *
        Complex.exp ((((T + 2 * Real.pi * k / h) * (u₀ + j * h) : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((((2 * Real.pi * k / h) * u₀ : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (((d * (u₀ + j * h) : ℝ) : ℂ)) *
          Complex.exp ((((T * (u₀ + j * h)) : ℝ) : ℂ) * Complex.I)) := by
  have hper : Complex.exp ((((2 * Real.pi * k / h) * (j * h) : ℝ) : ℂ) * Complex.I) = 1 := by
    have : (((2 * Real.pi * k / h) * (j * h) : ℝ) : ℂ) * Complex.I = ((k * j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
      push_cast; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hsplit : (((T + 2 * Real.pi * k / h) * (u₀ + j * h) : ℝ) : ℂ) * Complex.I =
      (((2 * Real.pi * k / h) * u₀ : ℝ) : ℂ) * Complex.I + ((((T * (u₀ + j * h)) : ℝ) : ℂ) * Complex.I) +
        (((2 * Real.pi * k / h) * (j * h) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_add, hper]
  ring

/-- **Résolution d'un écart** : `T < π p/(q − p)` implique `T·log(q/p) < π` (moins d'un demi-tour sur l'écart, aucun
repliement local), pour `0 < p < q` et `T ≥ 0`. `π p/(q − p)` est la fréquence requise `T_req` d'E334. -/
theorem resolution_of_gap_bound {T p q : ℝ} (hp : 0 < p) (hpq : p < q) (hT : 0 ≤ T) (hTr : T < Real.pi * p / (q - p)) :
    T * Real.log (q / p) < Real.pi := by
  have hq : 0 < q := lt_trans hp hpq
  have hlog : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos (div_pos hq hp)
  have hlogpos : 0 < Real.log (q / p) := Real.log_pos ((one_lt_div hp).mpr hpq)
  have hqp : 0 < q - p := by linarith
  have h1 : q / p - 1 = (q - p) / p := by field_simp
  rw [h1] at hlog
  calc T * Real.log (q / p) ≤ T * ((q - p) / p) := mul_le_mul_of_nonneg_left hlog hT
    _ < Real.pi * p / (q - p) * ((q - p) / p) := mul_lt_mul_of_pos_right hTr (div_pos hqp hp)
    _ = Real.pi := by field_simp

/-- Même énoncé en demi-tours : `T < π p/(q − p)` ⟹ `halfTurnsOnGap T p q < 1`. -/
theorem halfTurns_lt_one_of_gap_bound {T p q : ℝ} (hp : 0 < p) (hpq : p < q) (hT : 0 ≤ T)
    (hTr : T < Real.pi * p / (q - p)) : halfTurnsOnGap T p q < 1 := by
  unfold halfTurnsOnGap
  rw [div_lt_one Real.pi_pos]
  exact resolution_of_gap_bound hp hpq hT hTr

/-! ## §5 Raccord des canaux, membre par membre : lissé → brut → `J` -/

/-- Primitive lissée d'une paire : `−2 Re(x^{ρ+1}/(ρ(ρ+1)))`. -/
noncomputable def smoothedPrimitive (z : TrueZero) (x : ℝ) : ℝ :=
  -2 * ((x : ℂ) ^ (zeroPoint z + 1) / (zeroPoint z * (zeroPoint z + 1))).re

/-- **Lissé → brut** : la primitive lissée a pour dérivée la contribution brute `−2 Re(x^ρ/ρ)`, pour `x > 0`. -/
theorem smoothedPrimitive_hasDerivAt (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (smoothedPrimitive z) (pairContribution z x) x := by
  have hρ := zeroPoint_ne_zero z
  have hr : zeroPoint z ≠ -1 := by
    intro h
    have := congrArg Complex.re h
    have hβ := zeroPoint_re_pos z
    simp at this; linarith
  have hd := (hasDerivAt_ofReal_cpow_const' (x := x) hx.ne' hr).div_const (zeroPoint z)
  have hfun : (fun y : ℝ => (y : ℂ) ^ (zeroPoint z + 1) / (zeroPoint z + 1) / zeroPoint z) =
      fun y : ℝ => (y : ℂ) ^ (zeroPoint z + 1) / (zeroPoint z * (zeroPoint z + 1)) := by
    funext y; rw [div_div, mul_comm]
  rw [hfun] at hd
  have hre := ((Complex.reCLM.hasFDerivAt).comp_hasDerivAt x hd).const_mul (-2)
  unfold pairContribution zeroTerm
  exact hre

/-- **Brut → `J`** (rappel, `counting_modulation_eq_raw_derivative`) : la contribution brute a pour dérivée `log x` fois
la densité du canal `J`. Chaîne complète d'un membre : primitive lissée ⟶ (dérivée) brut ⟶ (dérivée / log x) densité `J`. -/
theorem raw_to_counting_density (z : TrueZero) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (pairContribution z) (countingModulationDensity z x * Real.log x) x :=
  counting_modulation_eq_raw_derivative z hx

/-- **Le terme lissé du dépôt et la primitive** : `x·√x·c̃(x) = m·primitive(x)`, où `c̃` est la contribution lissée
normalisée (`normalizedSmoothedPairContribution`) et `m` la multiplicité. -/
theorem smoothedPrimitive_eq_normalizedSmoothed (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    x * Real.sqrt x * normalizedSmoothedPairContribution z x =
      (zetaZeroMultiplicity (zeroPoint z) : ℝ) * smoothedPrimitive z x := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hρ := zeroPoint_ne_zero z
  have hρ1 : zeroPoint z + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    have hβ := zeroPoint_re_pos z
    simp at h'; linarith
  unfold normalizedSmoothedPairContribution smoothedPrimitive
  rw [residueTerm_eq_zeroTerm]
  unfold zeroTerm
  set w : ℂ := (x : ℂ) ^ zeroPoint z / zeroPoint z / (zeroPoint z + 1) with hw
  have hpow : (x : ℂ) * (x : ℂ) ^ zeroPoint z = (x : ℂ) ^ (zeroPoint z + 1) := by
    rw [Complex.cpow_add _ _ hx', Complex.cpow_one, mul_comm]
  have hkey : (x : ℂ) ^ (zeroPoint z + 1) / (zeroPoint z * (zeroPoint z + 1)) = (x : ℂ) * w := by
    rw [← hpow, hw]; field_simp
  have hm : (-(zetaZeroMultiplicity (zeroPoint z) : ℂ) * w).re =
      -(zetaZeroMultiplicity (zeroPoint z) : ℝ) * w.re := by
    rw [show -(zetaZeroMultiplicity (zeroPoint z) : ℂ) = ((-(zetaZeroMultiplicity (zeroPoint z) : ℝ) : ℝ) : ℂ) by
      push_cast; ring, Complex.re_ofReal_mul]
  rw [hkey, Complex.re_ofReal_mul, hm]
  field_simp

end RHV6Fresh

#print axioms RHV6Fresh.normalized_atom_pairing
#print axioms RHV6Fresh.normalized_background_pairing
#print axioms RHV6Fresh.normalized_mode_pairing
#print axioms RHV6Fresh.normalized_modes_pairing
#print axioms RHV6Fresh.gap_matrix_identity
#print axioms RHV6Fresh.transitions_no_constraint_beyond_telescoping
#print axioms RHV6Fresh.alias_mode_samples
#print axioms RHV6Fresh.resolution_of_gap_bound
#print axioms RHV6Fresh.smoothedPrimitive_hasDerivAt
#print axioms RHV6Fresh.smoothedPrimitive_eq_normalizedSmoothed
