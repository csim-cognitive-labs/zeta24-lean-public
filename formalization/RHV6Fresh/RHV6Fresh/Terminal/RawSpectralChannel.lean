/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.InverseReading
import RHV6Fresh.Terminal.RawMeetingRemainder

/-!
# Le canal brut côté zéros, la décomposition fréquentielle et la cassure (E406–E410, §19.36)

Module ISOLÉ (non ajouté à `RHV6Fresh.lean`). Il relie l'objet d'E405 (`psiRemainder N = ψ(N) − N`)
au canal de cellule déjà compilé dans `InverseReading.lean` (`spectralRemainder N`, pas sur la
cellule `[N, N+1]` de la primitive absolument convergente), puis découpe ce canal par seuil de
fréquence et borne ce que les basses fréquences peuvent réaliser à une cassure.

Convention de convergence (E406) : la série brute ponctuelle des zéros n'est pas absolument
convergente ; son intégrale sur la cellule unité l'est (`channelOn_summable`). Comme l'escalier
`ψ` est constant sur `[N, N+1[`, l'intégrale de cellule de `ψ` vaut `ψ(N)` et l'identité exacte au
saut est attribuée à une somme absolument convergente, sans ordre de sommation ni convention au
point de saut. Aucune convergence ponctuelle de la série brute n'est posée ni utilisée.

1. **E406** : `psiRemainder_eq_spectral_add_correction` : `ψ(N) − N = spectralRemainder N + c(N)`,
   `‖c(N)‖ ≤ cellBackgroundConstant` (`norm_cellCorrection_le`).
2. **E407** : `lowFrequencies H` (indices de hauteur absolue au plus `H`, deux branches), fini ;
   instances du découpage compilé (`exactRemainder_split_frequency`,
   `remainderIncrement_split_frequency`).
3. **E408** : `norm_packetIncrement_finset_le` : la seconde différence de cellule d'une famille
   FINIE d'indices est bornée par la somme de leurs multiplicités (deux inégalités des
   accroissements finis) ; `break_realized_by_high_frequencies` : la part de la cassure qui
   dépasse `1 + 4τ + K(H)` est portée par les fréquences au-dessus de `H` ;
   `frequency_floor_of_low_realization` : si les fréquences au plus `H` réalisent seules la
   cassure en `p`, alors `K(H) ≥ log p − 1 − 4τ`.
4. **E410** : `off_member_forces_break_and_excess` : composition avec la lecture OFF d'E405.

Tout est axe réel (R12) : vrais premiers, vraie fonction en escalier, vrais zéros ; les constantes
de fond sont analytiques. Aucune hypothèse nommée, aucun `sorry`.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction Finset

/-! ## 1. E406 : le reste brut aux entiers et le canal de cellule -/

/-- La masse de von Mangoldt jusqu'à `N` est l'escalier de Tchebychev en `N`. -/
theorem massA_eq_psi (N : ℕ) : massA N = Chebyshev.psi (N : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  unfold massA
  rw [Nat.range_eq_Icc_zero_sub_one (N + 1) (Nat.succ_ne_zero N), Nat.add_sub_cancel]

/-- La constante compilée de la queue des zéros triviaux. -/
noncomputable def trivialTailConstant : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2

theorem trivialTailConstant_nonneg : 0 ≤ trivialTailConstant :=
  tsum_nonneg fun n => by positivity

/-- Le terme trivial pondéré par `x` reste borné par `1/(n+1)²` pour `x > 1`. -/
theorem weighted_trivialZeroResidueTerm_norm_le {x : ℝ} (hx : 1 < x) (n : ℕ) :
    ‖(x : ℂ) * trivialZeroResidueTerm x n‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  have hx0 : 0 < x := lt_trans one_pos hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0,
    trivial_zero_residue_term_eq hx, norm_neg]
  have hden : trivialZetaZeroAt n * (trivialZetaZeroAt n + 1) =
      (((2 * ((n : ℝ) + 1)) * (2 * (n : ℝ) + 1) : ℝ) : ℂ) := by
    simp only [trivialZetaZeroAt]; push_cast; ring
  have hre : (trivialZetaZeroAt n).re = -(2 * ((n : ℝ) + 1)) := by
    simp [trivialZetaZeroAt]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpow : x * x ^ (-(2 * ((n : ℝ) + 1))) ≤ 1 := by
    have hmul : x * x ^ (-(2 * ((n : ℝ) + 1))) = x ^ (1 + -(2 * ((n : ℝ) + 1))) := by
      rw [Real.rpow_add hx0, Real.rpow_one]
    rw [hmul]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx.le (by linarith)
  have hd : ((n : ℝ) + 1) ^ 2 ≤ (2 * ((n : ℝ) + 1)) * (2 * (n : ℝ) + 1) := by nlinarith
  have hdpos : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  change x * ‖(x : ℂ) ^ trivialZetaZeroAt n / (trivialZetaZeroAt n * (trivialZetaZeroAt n + 1))‖ ≤ _
  rw [norm_div, hden, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre, ← mul_div_assoc]
  calc x * x ^ (-(2 * ((n : ℝ) + 1))) / ((2 * ((n : ℝ) + 1)) * (2 * (n : ℝ) + 1))
      ≤ 1 / ((2 * ((n : ℝ) + 1)) * (2 * (n : ℝ) + 1)) :=
        div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ 1 / ((n : ℝ) + 1) ^ 2 := one_div_le_one_div_of_le hdpos hd

/-- La somme pondérée des zéros triviaux, `x · Σ' terme`. -/
noncomputable def weightedTrivialSum (x : ℝ) : ℂ := (x : ℂ) * ∑' n : ℕ, trivialZeroResidueTerm x n

theorem norm_weightedTrivialSum_le {x : ℝ} (hx : 1 < x) :
    ‖weightedTrivialSum x‖ ≤ trivialTailConstant := by
  unfold weightedTrivialSum trivialTailConstant
  rw [← tsum_mul_left]
  have hs : Summable fun n : ℕ => ‖(x : ℂ) * trivialZeroResidueTerm x n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (weighted_trivialZeroResidueTerm_norm_le hx) summable_one_div_succ_sq
  exact (norm_tsum_le_tsum_norm hs).trans
    (hs.tsum_le_tsum (weighted_trivialZeroResidueTerm_norm_le hx) summable_one_div_succ_sq)

/-- Le pas du fond sur la cellule `[N, N+1]` : `N + 1/2 + c₀ + (W(N+1) − W(N))`. -/
theorem backgroundStep_eq {N : ℕ} (hN : 1 ≤ N) :
    stepAt backgroundPrimitive N = (N : ℂ) + 1 / 2 + (-logDeriv riemannZeta 0) +
      (weightedTrivialSum ((N : ℝ) + 1) - weightedTrivialSum N) := by
  have h0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have h1 : (N : ℂ) + 1 ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  unfold stepAt backgroundPrimitive smoothedZeroBackground weightedTrivialSum
  push_cast
  field_simp
  ring

/-- **La correction de cellule** : ce qui sépare `ψ(N) − N` du canal de cellule des zéros. -/
noncomputable def cellCorrection (N : ℕ) : ℂ :=
  1 / 2 + (-logDeriv riemannZeta 0) + (weightedTrivialSum ((N : ℝ) + 1) - weightedTrivialSum N)

/-- La constante explicite de la correction. -/
noncomputable def cellBackgroundConstant : ℝ :=
  1 / 2 + ‖logDeriv riemannZeta 0‖ + 2 * trivialTailConstant

theorem norm_cellCorrection_le {N : ℕ} (hN : 2 ≤ N) :
    ‖cellCorrection N‖ ≤ cellBackgroundConstant := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN2 : (1 : ℝ) < (N : ℝ) + 1 := by linarith
  have hW1 := norm_weightedTrivialSum_le hN2
  have hW0 := norm_weightedTrivialSum_le hN1
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  unfold cellCorrection cellBackgroundConstant
  calc ‖1 / 2 + (-logDeriv riemannZeta 0) +
        (weightedTrivialSum ((N : ℝ) + 1) - weightedTrivialSum N)‖
      ≤ ‖(1 / 2 : ℂ)‖ + ‖-logDeriv riemannZeta 0‖ +
        (‖weightedTrivialSum ((N : ℝ) + 1)‖ + ‖weightedTrivialSum N‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_sub_le _ _))
    _ ≤ 1 / 2 + ‖logDeriv riemannZeta 0‖ + 2 * trivialTailConstant := by
        rw [hhalf, norm_neg]; linarith

/-- **E406.** `ψ(N) − N` est le canal de cellule des zéros plus une correction bornée. -/
theorem psiRemainder_eq_spectral_add_correction {N : ℕ} (hN : 2 ≤ N) :
    ((psiRemainder N : ℝ) : ℂ) = spectralRemainder N + cellCorrection N := by
  rw [← arithmetic_eq_spectral hN]
  unfold psiRemainder exactRemainder cellCorrection
  rw [massA_eq_psi, backgroundStep_eq (by omega)]
  push_cast
  ring

theorem abs_psiRemainder_le_spectral {N : ℕ} (hN : 2 ≤ N) :
    |psiRemainder N| ≤ ‖spectralRemainder N‖ + cellBackgroundConstant := by
  have h := psiRemainder_eq_spectral_add_correction hN
  have : ‖((psiRemainder N : ℝ) : ℂ)‖ ≤ ‖spectralRemainder N‖ + ‖cellCorrection N‖ := by
    rw [h]; exact norm_add_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  linarith [norm_cellCorrection_le hN]

/-! ## 2. E407 : la décomposition par seuil de fréquence -/

/-- Les indices de hauteur absolue au plus `H` (les deux branches). -/
def lowFrequencySet (H : ℝ) : Set ExplicitIndex := {ρ | |(ρ : ℂ).im| ≤ H}

theorem lowFrequencySet_finite (H : ℝ) : (lowFrequencySet H).Finite := by
  refine (explicitIndex_locallyFinite (H + 1)).subset ?_
  intro ρ hρ
  have hre := isNontrivialZetaZero_re_mem_Ioo ρ.property
  have him : |(ρ : ℂ).im| ≤ H := hρ
  change ‖(ρ : ℂ)‖ ≤ H + 1
  calc ‖(ρ : ℂ)‖ ≤ |(ρ : ℂ).re| + |(ρ : ℂ).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ H + 1 := by rw [abs_of_pos hre.1]; linarith [hre.2]

/-- La famille finie des basses fréquences. -/
noncomputable def lowFrequencies (H : ℝ) : Finset ExplicitIndex :=
  (lowFrequencySet_finite H).toFinset

theorem mem_lowFrequencies {H : ℝ} {ρ : ExplicitIndex} :
    ρ ∈ lowFrequencies H ↔ |(ρ : ℂ).im| ≤ H :=
  (lowFrequencySet_finite H).mem_toFinset

/-- `K(H)` : le nombre de basses fréquences, compté avec multiplicité. -/
noncomputable def lowMultiplicityCount (H : ℝ) : ℝ :=
  ∑ ρ ∈ lowFrequencies H, (zetaZeroMultiplicity (ρ : ℂ) : ℝ)

/-- **E407, au niveau du reste** : instance du découpage compilé. -/
theorem exactRemainder_split_frequency (H : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    exactRemainder N =
      localPacket (↑(lowFrequencies H)) N + localPacket (↑(lowFrequencies H))ᶜ N :=
  exactRemainder_eq_packet_add_complement _ hN

/-- **E407, au niveau de l'incrément (la cassure)** : instance du découpage compilé. -/
theorem remainderIncrement_split_frequency (H : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    remainderIncrement N =
      packetIncrement (↑(lowFrequencies H)) N + packetIncrement (↑(lowFrequencies H))ᶜ N :=
  remainderIncrement_eq_packet_add_complement _ hN

/-! ## 3. E408 : les basses fréquences ne réalisent pas une cassure plus grande que leur nombre -/

/-- La part de cellule d'un indice : `−m · y^(ρ+1) / (ρ (ρ+1))`. -/
noncomputable def cellTerm (ρ : ExplicitIndex) (y : ℝ) : ℂ :=
  -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / (ρ : ℂ) * ((y : ℂ) ^ ((ρ : ℂ) + 1) / ((ρ : ℂ) + 1))

/-- Sa pente : `−m · y^ρ / ρ`. -/
noncomputable def cellSlope (ρ : ExplicitIndex) (y : ℝ) : ℂ :=
  -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * ((y : ℂ) ^ (ρ : ℂ) / (ρ : ℂ))

theorem cellTerm_eq_mul (ρ : ExplicitIndex) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) * nontrivialZeroResidueTerm y ρ = cellTerm ρ y := by
  obtain ⟨h0, h1⟩ := explicitIndex_ne_zero ρ
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  change (y : ℂ) * (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
    ((y : ℂ) ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1)))) = _
  unfold cellTerm
  rw [Complex.cpow_add _ _ hy0, Complex.cpow_one]
  field_simp

theorem hasDerivAt_cellTerm (ρ : ExplicitIndex) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (cellTerm ρ) (cellSlope ρ y) y := by
  obtain ⟨h0, h1⟩ := explicitIndex_ne_zero ρ
  have hr : (ρ : ℂ) ≠ -1 := fun h => h1 (by rw [h]; ring)
  have h := (hasDerivAt_ofReal_cpow_const' hy.ne' hr).const_mul
    (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / (ρ : ℂ))
  refine h.congr_deriv ?_
  unfold cellSlope
  ring

theorem hasDerivAt_cellSlope (ρ : ExplicitIndex) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (cellSlope ρ)
      (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * (y : ℂ) ^ ((ρ : ℂ) - 1)) y := by
  obtain ⟨h0, _⟩ := explicitIndex_ne_zero ρ
  have hr : (ρ : ℂ) - 1 ≠ -1 := fun h => h0 (by linear_combination h)
  have h := hasDerivAt_ofReal_cpow_const' hy.ne' hr
  rw [show (ρ : ℂ) - 1 + 1 = ρ by ring] at h
  exact h.const_mul _

/-- La seconde dérivée de la part de cellule est bornée par la multiplicité pour `y ≥ 1`
(`‖y^(ρ−1)‖ = y^(β−1) ≤ 1` car `β ≤ 1`). -/
theorem norm_cellSecond_le (ρ : ExplicitIndex) {y : ℝ} (hy : 1 ≤ y) :
    ‖-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * (y : ℂ) ^ ((ρ : ℂ) - 1)‖ ≤
      zetaZeroMultiplicity (ρ : ℂ) := by
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  rw [norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
  have hre : ((ρ : ℂ) - 1).re ≤ 0 := by
    rw [Complex.sub_re, Complex.one_re]; linarith [explicitIndex_re_le_one ρ]
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hy hre)

/-- Première inégalité des accroissements finis : la pente varie d'au plus `m` sur une cellule. -/
theorem norm_cellSlope_shift_le (ρ : ExplicitIndex) {y : ℝ} (hy : 1 ≤ y) :
    ‖cellSlope ρ (y + 1) - cellSlope ρ y‖ ≤ zetaZeroMultiplicity (ρ : ℂ) := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.Icc y (y + 1))
    (f := cellSlope ρ)
    (f' := fun t => -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * (t : ℂ) ^ ((ρ : ℂ) - 1))
    (C := zetaZeroMultiplicity (ρ : ℂ))
    (fun t ht => (hasDerivAt_cellSlope ρ (by linarith [ht.1])).hasDerivWithinAt)
    (fun t ht => norm_cellSecond_le ρ (by linarith [ht.1]))
    (convex_Icc _ _) (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
  simpa using h

/-- Seconde inégalité des accroissements finis : **la seconde différence de cellule d'un indice
est bornée par sa multiplicité**, pour `y ≥ 1`. -/
theorem norm_cellTerm_second_difference_le (ρ : ExplicitIndex) {y : ℝ} (hy : 1 ≤ y) :
    ‖(cellTerm ρ (y + 1 + 1) - cellTerm ρ (y + 1)) - (cellTerm ρ (y + 1) - cellTerm ρ y)‖ ≤
      zetaZeroMultiplicity (ρ : ℂ) := by
  have hg : ∀ t ∈ Set.Icc y (y + 1), HasDerivWithinAt (fun u : ℝ => cellTerm ρ (u + 1) - cellTerm ρ u)
      (cellSlope ρ (t + 1) - cellSlope ρ t) (Set.Icc y (y + 1)) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℝ => cellTerm ρ (u + 1)) (cellSlope ρ (t + 1)) t :=
      HasDerivAt.comp_add_const t 1 (hasDerivAt_cellTerm ρ (by linarith [ht.1]))
    exact (h1.sub (hasDerivAt_cellTerm ρ (by linarith [ht.1]))).hasDerivWithinAt
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.Icc y (y + 1))
    (f := fun u : ℝ => cellTerm ρ (u + 1) - cellTerm ρ u)
    (f' := fun t => cellSlope ρ (t + 1) - cellSlope ρ t)
    (C := zetaZeroMultiplicity (ρ : ℂ)) hg
    (fun t ht => norm_cellSlope_shift_le ρ (by linarith [ht.1]))
    (convex_Icc _ _) (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
  simpa using h

/-- La primitive d'une famille finie est la somme de ses parts de cellule. -/
theorem channelPrimitive_finset (s : Finset ExplicitIndex) {y : ℝ} (hy : 0 < y) :
    channelPrimitive (↑s) y = ∑ ρ ∈ s, cellTerm ρ y := by
  unfold channelPrimitive channelOn
  rw [Finset.tsum_subtype', Finset.mul_sum]
  exact Finset.sum_congr rfl fun ρ _ => cellTerm_eq_mul ρ hy

/-- **E408, théorème central.** L'incrément de cellule (la seconde différence) d'une famille
FINIE d'indices est borné par la somme de leurs multiplicités, pour tout `N ≥ 1`. Les basses
fréquences ne peuvent réaliser à elles seules une cassure plus grande que leur nombre. -/
theorem norm_packetIncrement_finset_le (s : Finset ExplicitIndex) {N : ℕ} (hN : 1 ≤ N) :
    ‖packetIncrement (↑s) N‖ ≤ ∑ ρ ∈ s, (zetaZeroMultiplicity (ρ : ℂ) : ℝ) := by
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have e1 := channelPrimitive_finset s (y := ((N + 1 : ℕ) : ℝ) + 1) (by positivity)
  have e2 := channelPrimitive_finset s (y := ((N + 1 : ℕ) : ℝ)) (by positivity)
  have e3 := channelPrimitive_finset s (y := (N : ℝ) + 1) (by positivity)
  have e4 := channelPrimitive_finset s (y := (N : ℝ)) (by linarith)
  have hrepr : packetIncrement (↑s) N = ∑ ρ ∈ s,
      ((cellTerm ρ ((N : ℝ) + 1 + 1) - cellTerm ρ ((N : ℝ) + 1)) -
        (cellTerm ρ ((N : ℝ) + 1) - cellTerm ρ N)) := by
    unfold packetIncrement localPacket stepAt
    rw [e1, e2, e3, e4]
    push_cast
    simp only [Finset.sum_sub_distrib]
  rw [hrepr]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun ρ _ => norm_cellTerm_second_difference_le ρ h1)

/-- La seconde différence du fond vaut un, à `4τ` près. -/
theorem norm_backgroundBreak_sub_one_le {N : ℕ} (hN : 2 ≤ N) :
    ‖(stepAt backgroundPrimitive (N + 1) - stepAt backgroundPrimitive N) - 1‖ ≤
      4 * trivialTailConstant := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  rw [backgroundStep_eq (by omega), backgroundStep_eq (by omega)]
  push_cast
  have hW0 := norm_weightedTrivialSum_le hN1
  have hW1 := norm_weightedTrivialSum_le (show (1 : ℝ) < (N : ℝ) + 1 by linarith)
  have hW2 := norm_weightedTrivialSum_le (show (1 : ℝ) < (N : ℝ) + 1 + 1 by linarith)
  have heq : ((N : ℂ) + 1 + 1 / 2 + (-logDeriv riemannZeta 0) +
      (weightedTrivialSum ((N : ℝ) + 1 + 1) - weightedTrivialSum ((N : ℝ) + 1))) -
      ((N : ℂ) + 1 / 2 + (-logDeriv riemannZeta 0) +
      (weightedTrivialSum ((N : ℝ) + 1) - weightedTrivialSum N)) - 1 =
      weightedTrivialSum ((N : ℝ) + 1 + 1) - 2 * weightedTrivialSum ((N : ℝ) + 1) +
        weightedTrivialSum N := by ring
  rw [heq]
  calc ‖weightedTrivialSum ((N : ℝ) + 1 + 1) - 2 * weightedTrivialSum ((N : ℝ) + 1) +
        weightedTrivialSum N‖
      ≤ ‖weightedTrivialSum ((N : ℝ) + 1 + 1)‖ + ‖(2 : ℂ) * weightedTrivialSum ((N : ℝ) + 1)‖ +
        ‖weightedTrivialSum N‖ := (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 4 * trivialTailConstant := by
        rw [norm_mul, Complex.norm_ofNat]; linarith

/-- L'incrément du reste exact à la rencontre `N + 1` vaut au moins `Λ(N+1) − 1 − 4τ`. -/
theorem norm_remainderIncrement_ge {N : ℕ} (hN : 2 ≤ N) :
    (Λ (N + 1) : ℝ) - 1 - 4 * trivialTailConstant ≤ ‖remainderIncrement N‖ := by
  have hB := norm_backgroundBreak_sub_one_le hN
  have heq : remainderIncrement N = (((Λ (N + 1) : ℝ) - 1 : ℝ) : ℂ) -
      ((stepAt backgroundPrimitive (N + 1) - stepAt backgroundPrimitive N) - 1) := by
    rw [remainderIncrement_arithmetic]; push_cast; ring
  have h := norm_sub_norm_le (((Λ (N + 1) : ℝ) - 1 : ℝ) : ℂ)
    ((stepAt backgroundPrimitive (N + 1) - stepAt backgroundPrimitive N) - 1)
  rw [← heq, Complex.norm_real, Real.norm_eq_abs] at h
  linarith [le_abs_self ((Λ (N + 1) : ℝ) - 1)]

/-- **E408, conséquence.** La part de la cassure en `N + 1` qui dépasse `1 + 4τ + Σ m` est portée
NÉCESSAIREMENT par le complément de toute famille finie `s` : les fréquences hors de `s`. -/
theorem break_realized_by_high_frequencies (s : Finset ExplicitIndex) {N : ℕ} (hN : 2 ≤ N) :
    (Λ (N + 1) : ℝ) - 1 - 4 * trivialTailConstant -
        ∑ ρ ∈ s, (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤
      ‖packetIncrement (↑s)ᶜ N‖ := by
  have hsplit := remainderIncrement_eq_packet_add_complement (↑s) hN
  have hlow := norm_packetIncrement_finset_le s (N := N) (by omega)
  have hge := norm_remainderIncrement_ge hN
  have htri : ‖remainderIncrement N‖ ≤
      ‖packetIncrement (↑s) N‖ + ‖packetIncrement (↑s)ᶜ N‖ := by
    rw [hsplit]; exact norm_add_le _ _
  linarith

/-- À une rencontre brute `E ≥ 3`, avec le seuil `H` : la cassure moins `1 + 4τ + K(H)` est portée
par les fréquences au-dessus de `H`. -/
theorem event_break_above_threshold (H : ℝ) {E : ℕ} (hE : 3 ≤ E) :
    (Λ E : ℝ) - 1 - 4 * trivialTailConstant - lowMultiplicityCount H ≤
      ‖packetIncrement (↑(lowFrequencies H))ᶜ (E - 1)‖ := by
  have h := break_realized_by_high_frequencies (lowFrequencies H) (N := E - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at h
  exact h

/-- À un premier `p ≥ 3` : la cassure vaut `log p`. -/
theorem prime_break_above_threshold (H : ℝ) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    Real.log p - 1 - 4 * trivialTailConstant - lowMultiplicityCount H ≤
      ‖packetIncrement (↑(lowFrequencies H))ᶜ (p - 1)‖ := by
  have h := event_break_above_threshold H hp3
  rwa [vonMangoldt_apply_prime hp] at h

/-- **Plancher de fréquence.** Si les fréquences au plus `H` réalisent seules la cassure en `p`
(complément d'incrément nul), alors leur nombre vaut au moins `log p − 1 − 4τ`. -/
theorem frequency_floor_of_low_realization (H : ℝ) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (h0 : packetIncrement (↑(lowFrequencies H))ᶜ (p - 1) = 0) :
    Real.log p - 1 - 4 * trivialTailConstant ≤ lowMultiplicityCount H := by
  have h := prime_break_above_threshold H hp hp3
  rw [h0, norm_zero] at h
  linarith

/-! ## 4. E410 : composition avec la lecture OFF d'E405 -/

/-- **Composition.** Un membre à `β > θ` force (E405, `off_member_forces_raw_excess_at_event`) une
rencontre brute `E` où le reste brut dépasse `C·E^θ` d'un côté ou de l'autre ; et à cette rencontre,
pour tout seuil `H` (si `E ≥ 3`), la cassure est portée au-dessus de `H` à hauteur d'au moins
`Λ(E) − 1 − 4τ − K(H)` (E408). Les deux lectures portent sur la même rencontre. -/
theorem off_member_forces_break_and_excess {θ : ℝ} (hθ : 0 ≤ θ) (ρ : ExplicitIndex)
    (hρ : θ < (ρ : ℂ).re) (C : ℝ) :
    ∃ E : ℕ, IsRawEvent E ∧
      (C * (E : ℝ) ^ θ < |psiRemainder E| ∨ C * (E : ℝ) ^ θ < |psiRemainder (E - 1)|) ∧
      ∀ H : ℝ, 3 ≤ E →
        (Λ E : ℝ) - 1 - 4 * trivialTailConstant - lowMultiplicityCount H ≤
          ‖packetIncrement (↑(lowFrequencies H))ᶜ (E - 1)‖ := by
  obtain ⟨E, hE, hex⟩ := off_member_forces_raw_excess_at_event hθ ρ hρ C
  exact ⟨E, hE, hex, fun H hE3 => event_break_above_threshold H hE3⟩

/-- **Réduction vraie (E411, cadre).** Des bornes des deux paquets à tout entier donnent la borne
du reste brut à tout entier, donc aux rencontres. Ce n'est pas une hypothèse : c'est une implication
compilée ; ses deux prémisses sont les deux buts que la tentative E411 doit remplir. -/
theorem abs_psiRemainder_le_of_packets (H : ℝ) {θ C₁ C₂ : ℝ} (hθ : 0 ≤ θ)
    (hlow : ∀ N : ℕ, 2 ≤ N → ‖localPacket (↑(lowFrequencies H)) N‖ ≤ C₁ * (N : ℝ) ^ θ)
    (hhigh : ∀ N : ℕ, 2 ≤ N → ‖localPacket (↑(lowFrequencies H))ᶜ N‖ ≤ C₂ * (N : ℝ) ^ θ) :
    ∀ N : ℕ, 2 ≤ N →
      |psiRemainder N| ≤ (C₁ + C₂ + cellBackgroundConstant) * (N : ℝ) ^ θ := by
  intro N hN
  have h := abs_psiRemainder_le_spectral hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ θ :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) hθ
  have hsplit : ‖spectralRemainder N‖ ≤
      ‖localPacket (↑(lowFrequencies H)) N‖ + ‖localPacket (↑(lowFrequencies H))ᶜ N‖ := by
    rw [← arithmetic_eq_spectral hN, exactRemainder_split_frequency H hN]; exact norm_add_le _ _
  have hc : cellBackgroundConstant ≤ cellBackgroundConstant * (N : ℝ) ^ θ := by
    have h0 : 0 ≤ cellBackgroundConstant := by
      unfold cellBackgroundConstant; linarith [norm_nonneg (logDeriv riemannZeta 0),
        trivialTailConstant_nonneg]
    nlinarith
  linarith [hlow N hN, hhigh N hN]

#print axioms psiRemainder_eq_spectral_add_correction
#print axioms norm_packetIncrement_finset_le
#print axioms break_realized_by_high_frequencies
#print axioms prime_break_above_threshold
#print axioms frequency_floor_of_low_realization
#print axioms off_member_forces_break_and_excess
#print axioms abs_psiRemainder_le_of_packets

end RHV6Fresh
