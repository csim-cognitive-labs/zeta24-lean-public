/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FirstGainPremise

/-!
# Progression du fond et modulation d'un zéro dans le canal de comptage (auteur, 2026-10-09)

Le canal de comptage pondéré `J(x) = Σ_{p^m ≤ x} 1/m` a pour fond `li`, de dérivée `1/log x`. La contribution d'un
zéro et de son conjugué y est `b_ρ(x) = −2 Re Ei(ρ log x)` ; Mathlib ne définit pas `Ei`, la primitive locale de
`e^w/w` est donc une hypothèse explicite (`hF`), jamais un objet du dépôt.

Contenu (tout est DÉMONTRÉ, pour toute position radiale) :
* §1 dérivée de la contribution de comptage `b_ρ' = −2 x^{β−1} cos(T log x)/log x` ;
* §2 rapportée à la progression du fond `li' = 1/log x`, cette modulation EST la dérivée de la contribution brute
  `c(x) = −2 Re(x^ρ/ρ)` du canal `ψ` (`counting_modulation_eq_raw_derivative`) : normaliser le canal de comptage par
  le fond, c'est lire le canal brut ;
* §3 la stabilité relative au fond (`|b_ρ'/li'| ≤ 2x^{β−1} → 0`) vaut pour TOUTE partie réelle `< 1` : elle ne lit
  pas le régime ; la normalisation par l'échelle ON (`x^{−1/2}`) donne l'enveloppe `x^{β−1/2}`, plate ⟺ ON
  (caractérisation, non obligation) ;
* §4 extrema `D_k = exp((π/2 + kπ)/T)` de la modulation et décalage exact `log(D_k/C_k) = arctan(β/T)/T` par rapport
  aux contacts bruts `C_k` (ON : `arctan(1/(2T))/T`) : les contacts sont un repère des extrema, non ces extrema ;
* §5 par cellule : `|Δb_{ρ,k}| ≤ 2 C_k^{β−1} Δli_k`, borne individuelle ; elle ne dit rien de la somme sur tous
  les zéros.

Aucun énoncé de ce module ne relie la somme de toutes les modulations à `J − li` (aucune formule explicite du canal
`J` dans le dépôt) ; aucun ne borne le reste collectif.
-/

namespace RHV6Fresh

open RHV3Lean Filter Topology

/-- Densité de modulation du canal de comptage : `−2 t^{β−1} cos(T log t)/log t` (dérivée de `b_ρ`). -/
noncomputable def countingModulationDensity (z : TrueZero) (t : ℝ) : ℝ :=
  -2 * t ^ (rZeroRadialPosition z.1 - 1) * Real.cos (rZeroHeight z.1 * Real.log t) / Real.log t

/-- Modulation rapportée à la progression du fond : `b_ρ'/li' = −2 t^{β−1} cos(T log t)`. -/
noncomputable def backgroundRelativeModulation (z : TrueZero) (t : ℝ) : ℝ :=
  -2 * t ^ (rZeroRadialPosition z.1 - 1) * Real.cos (rZeroHeight z.1 * Real.log t)

/-- Progression du fond sur une cellule : `Δli = ∫_a^b dt/log t`. -/
noncomputable def cellBackground (a b : ℝ) : ℝ := ∫ t in a..b, 1 / Real.log t

/-- Variation de la contribution du zéro sur une cellule : `Δb_ρ = ∫_a^b b_ρ'(t) dt`. -/
noncomputable def cellModulation (z : TrueZero) (a b : ℝ) : ℝ :=
  ∫ t in a..b, countingModulationDensity z t

/-- Extremum `D_k = exp((π/2 + kπ)/T)` de la modulation de comptage. -/
noncomputable def modulationExtremum (z : TrueZero) (k : ℤ) : ℝ :=
  Real.exp ((Real.pi / 2 + (k : ℝ) * Real.pi) / rZeroHeight z.1)

/-! ## 1. Dérivée de la contribution de comptage -/

/-- `Re(x^ρ/x) = x^{β−1} cos(T log x)`. -/
theorem cpow_zeroPoint_div_re {z : TrueZero} {x : ℝ} (hx : 0 < x) :
    ((x : ℂ) ^ zeroPoint z / (x : ℂ)).re =
      x ^ (rZeroRadialPosition z.1 - 1) * Real.cos (rZeroHeight z.1 * Real.log x) := by
  rw [Complex.div_ofReal_re, cpow_zeroPoint_re hx, Real.rpow_sub_one hx.ne',
    Real.rpow_def_of_pos hx, mul_comm (Real.log x)]
  ring

/-- **Dérivée de `b_ρ`** : pour toute primitive locale `F` de `e^w/w` au point `ρ log x`, la contribution de
comptage `y ↦ −2 Re F(ρ log y)` a pour dérivée `−2 x^{β−1} cos(T log x)/log x` en `x > 1`. -/
theorem counting_pair_hasDerivAt (z : TrueZero) {F : ℂ → ℂ} {x : ℝ} (hx : 1 < x)
    (hF : HasDerivAt F
      (Complex.exp (zeroPoint z * (Real.log x : ℂ)) / (zeroPoint z * (Real.log x : ℂ)))
      (zeroPoint z * (Real.log x : ℂ))) :
    HasDerivAt (fun y : ℝ => -2 * (F (zeroPoint z * (Real.log y : ℂ))).re)
      (countingModulationDensity z x) x := by
  have hx0 : 0 < x := lt_trans one_pos hx
  have hd := counting_contribution_hasDerivAt z hx hF
  have hre := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt x hd
  have h2 := hre.const_mul (-2)
  have hval : (-2) * Complex.reCLM (zeroPoint z * zeroTerm z x / ((x : ℂ) * (Real.log x : ℂ))) =
      countingModulationDensity z x := by
    have hρ := zeroPoint_ne_zero z
    have heq : zeroPoint z * zeroTerm z x / ((x : ℂ) * (Real.log x : ℂ)) =
        ((x : ℂ) ^ zeroPoint z / (x : ℂ)) / ((Real.log x : ℝ) : ℂ) := by
      unfold zeroTerm
      field_simp
    rw [Complex.reCLM_apply, heq, Complex.div_ofReal_re, cpow_zeroPoint_div_re hx0]
    unfold countingModulationDensity
    ring
  rw [← hval]
  exact h2

/-! ## 2. Rapportée au fond, la modulation de comptage est la dérivée de la contribution brute -/

/-- La dérivée de la contribution de comptage, divisée par la progression du fond `1/log x`, est la modulation
relative `−2 x^{β−1} cos(T log x)`. -/
theorem countingModulation_over_background (z : TrueZero) {x : ℝ} (hx : 1 < x) :
    countingModulationDensity z x / (1 / Real.log x) = backgroundRelativeModulation z x := by
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  unfold countingModulationDensity backgroundRelativeModulation
  field_simp

/-- **Dérivée de la contribution brute** `c(y) = −2 Re(y^ρ/ρ)` : `c'(x) = −2 x^{β−1} cos(T log x)`. -/
theorem pairContribution_hasDerivAt (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (pairContribution z) (backgroundRelativeModulation z x) x := by
  have hρ := zeroPoint_ne_zero z
  have hr : zeroPoint z - 1 ≠ -1 := by
    intro h; apply hρ; linear_combination h
  have hd := hasDerivAt_ofReal_cpow_const' (x := x) hx.ne' hr
  have hfun : (fun y : ℝ => (y : ℂ) ^ (zeroPoint z - 1 + 1) / (zeroPoint z - 1 + 1)) =
      fun y => zeroTerm z y := by
    funext y; unfold zeroTerm; rw [sub_add_cancel]
  rw [hfun] at hd
  have hre := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt x hd
  have h2 := hre.const_mul (-2)
  have hval : (-2) * Complex.reCLM ((x : ℂ) ^ (zeroPoint z - 1)) = backgroundRelativeModulation z x := by
    have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    rw [Complex.reCLM_apply, Complex.cpow_sub _ _ hx', Complex.cpow_one, cpow_zeroPoint_div_re hx]
    unfold backgroundRelativeModulation
    ring
  rw [← hval]
  exact h2

/-- **Le couplage cherché, sous sa forme exacte** : la densité de modulation du canal de comptage est la dérivée de
la contribution brute du canal `ψ` multipliée par la progression du fond. Rapporter `b_ρ'` à `li'` ne crée aucune
lecture nouvelle : c'est lire `c'`, le canal brut. -/
theorem counting_modulation_eq_raw_derivative (z : TrueZero) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (pairContribution z) (countingModulationDensity z x * Real.log x) x := by
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have h := pairContribution_hasDerivAt z (lt_trans one_pos hx)
  have heq : countingModulationDensity z x * Real.log x = backgroundRelativeModulation z x := by
    unfold countingModulationDensity backgroundRelativeModulation
    field_simp
  rw [heq]
  exact h

/-! ## 3. Deux normalisations : par le fond (aveugle au régime), par l'échelle ON (caractérisation) -/

/-- `|b_ρ'/li'| ≤ 2 x^{β−1}`, pour toute position radiale. -/
theorem backgroundRelativeModulation_abs_le (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    |backgroundRelativeModulation z x| ≤ 2 * x ^ (rZeroRadialPosition z.1 - 1) := by
  unfold backgroundRelativeModulation
  have hp : 0 ≤ x ^ (rZeroRadialPosition z.1 - 1) := Real.rpow_nonneg hx.le _
  rw [abs_mul, abs_mul, abs_neg, abs_two, abs_of_nonneg hp]
  have := Real.abs_cos_le_one (rZeroHeight z.1 * Real.log x)
  nlinarith

/-- En ligne : `|b_ρ'/li'| ≤ 2 x^{−1/2}`. -/
theorem backgroundRelativeModulation_abs_le_onLine (z : TrueZero)
    (hOn : rZeroRadialPosition z.1 = 1 / 2) {x : ℝ} (hx : 0 < x) :
    |backgroundRelativeModulation z x| ≤ 2 * x ^ (-(1 / 2 : ℝ)) := by
  have h := backgroundRelativeModulation_abs_le z hx
  rw [hOn] at h
  convert h using 3
  norm_num

/-- **La stabilité relative au fond ne lit pas le régime** : pour TOUT zéro (toute partie réelle `< 1`), l'enveloppe
`2 x^{β−1}` de la modulation rapportée au fond tend vers zéro. Une domination par le fond est donc vraie aussi d'un
membre hors ligne : elle ne peut pas porter l'échelle ON. -/
theorem background_envelope_tendsto_zero (z : TrueZero) :
    Tendsto (fun x : ℝ => 2 * x ^ (rZeroRadialPosition z.1 - 1)) atTop (𝓝 0) := by
  have hlt : rZeroRadialPosition z.1 < 1 := thm_zeroRadialPosition_lt_one z.1
  have h := tendsto_rpow_neg_atTop (y := 1 - rZeroRadialPosition z.1) (by linarith)
  have h2 := h.const_mul 2
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards with x
  congr 2
  ring

/-- Normalisation par l'échelle ON : `(b_ρ'/li')/x^{−1/2} = −2 x^{β−1/2} cos(T log x)`. -/
theorem backgroundRelativeModulation_onScale (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    backgroundRelativeModulation z x / x ^ (-(1 / 2 : ℝ)) =
      -2 * x ^ (rZeroRadialPosition z.1 - 1 / 2) * Real.cos (rZeroHeight z.1 * Real.log x) := by
  unfold backgroundRelativeModulation
  have hne : x ^ (-(1 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have hsplit : x ^ (rZeroRadialPosition z.1 - 1) =
      x ^ (rZeroRadialPosition z.1 - 1 / 2) * x ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  rw [hsplit]
  field_simp

/-- **Caractérisation (non obligation)** : l'enveloppe à l'échelle ON `x^{β−1/2}` prend la même valeur en deux
abscisses distinctes ⟺ le zéro est en ligne. -/
theorem onScale_envelope_flat_iff (z : TrueZero) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    y ^ (rZeroRadialPosition z.1 - 1 / 2) = x ^ (rZeroRadialPosition z.1 - 1 / 2) ↔
      rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro h
    have hl := congrArg Real.log h
    rw [Real.log_rpow hy, Real.log_rpow hx] at hl
    have hlog : Real.log y ≠ Real.log x := by
      intro he
      exact hxy (Real.log_injOn_pos (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy) he.symm)
    have : (rZeroRadialPosition z.1 - 1 / 2) * (Real.log y - Real.log x) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact absurd (sub_eq_zero.mp h0) hlog
  · intro h
    rw [h, sub_self, Real.rpow_zero, Real.rpow_zero]

/-! ## 4. Extrema de la modulation et décalage exact par rapport aux contacts bruts -/

/-- La modulation rapportée au fond s'annule aux points `D_k` (extrema de `b_ρ`). -/
theorem backgroundRelativeModulation_extremum (z : TrueZero) (k : ℤ) :
    backgroundRelativeModulation z (modulationExtremum z k) = 0 := by
  have hT : 0 < rZeroHeight z.1 := z.2
  unfold backgroundRelativeModulation modulationExtremum
  rw [Real.log_exp, mul_div_cancel₀ _ hT.ne', add_comm, Real.cos_add_pi_div_two,
    Real.sin_int_mul_pi]
  ring

/-- **Décalage exact** `log D_k − log C_k = arctan(β/T)/T`. -/
theorem extremum_contact_offset (z : TrueZero) (k : ℤ) :
    Real.log (modulationExtremum z k) - Real.log (contactMinusAt z k) =
      Real.arctan (rZeroRadialPosition z.1 / rZeroHeight z.1) / rZeroHeight z.1 := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hinv : rZeroHeight z.1 / rZeroRadialPosition z.1 =
      (rZeroRadialPosition z.1 / rZeroHeight z.1)⁻¹ := (inv_div _ _).symm
  unfold modulationExtremum
  rw [contactMinusAt_eq_exp, Real.log_exp, Real.log_exp, hinv,
    Real.arctan_inv_of_pos (div_pos hβ hT)]
  field_simp
  ring

/-- En ligne : `log D_k − log C_k = arctan(1/(2T))/T`. -/
theorem extremum_contact_offset_onLine (z : TrueZero) (hOn : rZeroRadialPosition z.1 = 1 / 2) (k : ℤ) :
    Real.log (modulationExtremum z k) - Real.log (contactMinusAt z k) =
      Real.arctan (1 / (2 * rZeroHeight z.1)) / rZeroHeight z.1 := by
  rw [extremum_contact_offset, hOn]
  congr 2
  ring

/-! ## 5. Par cellule : progression du fond et variation du zéro -/

/-- La progression du fond sur `[a, b]`, `1 < a ≤ b`, est positive. -/
theorem cellBackground_nonneg {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) : 0 ≤ cellBackground a b := by
  unfold cellBackground
  refine intervalIntegral.integral_nonneg hab fun t ht => ?_
  have : 0 < Real.log t := Real.log_pos (lt_of_lt_of_le ha ht.1)
  positivity

/-- **Borne de cellule (individuelle)** : sur `[a, b]`, `1 < a ≤ b`, la variation de la contribution du zéro est
au plus `2 a^{β−1}` fois la progression du fond. Vraie pour toute position radiale ; elle ne borne aucune somme. -/
theorem cellModulation_abs_le (z : TrueZero) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    |cellModulation z a b| ≤ 2 * a ^ (rZeroRadialPosition z.1 - 1) * cellBackground a b := by
  have hlt : rZeroRadialPosition z.1 - 1 ≤ 0 := by
    have := thm_zeroRadialPosition_lt_one z.1; linarith
  have ha0 : 0 < a := lt_trans one_pos ha
  have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc a b) := by
    refine ContinuousOn.div continuousOn_const (Real.continuousOn_log.mono ?_) ?_
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact (lt_of_lt_of_le ha0 ht.1).ne'
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'
  have hint : IntervalIntegrable (fun t : ℝ => 2 * a ^ (rZeroRadialPosition z.1 - 1) * (1 / Real.log t))
      MeasureTheory.volume a b :=
    (hcont.intervalIntegrable).const_mul _
  have hle := intervalIntegral.norm_integral_le_of_norm_le (f := countingModulationDensity z) hab
    (Filter.Eventually.of_forall fun t ht => by
      have ht1 : 1 < t := lt_trans ha ht.1
      have ht0 : 0 < t := lt_trans one_pos ht1
      have hlog : 0 < Real.log t := Real.log_pos ht1
      have hpow : t ^ (rZeroRadialPosition z.1 - 1) ≤ a ^ (rZeroRadialPosition z.1 - 1) :=
        Real.rpow_le_rpow_of_nonpos ha0 ht.1.le hlt
      have hp : 0 ≤ t ^ (rZeroRadialPosition z.1 - 1) := Real.rpow_nonneg ht0.le _
      have hcos := Real.abs_cos_le_one (rZeroHeight z.1 * Real.log t)
      rw [Real.norm_eq_abs]
      unfold countingModulationDensity
      rw [abs_div, abs_of_pos hlog, abs_mul, abs_mul, abs_neg, abs_two, abs_of_nonneg hp,
        div_le_iff₀ hlog]
      field_simp
      nlinarith [Real.rpow_nonneg ha0.le (rZeroRadialPosition z.1 - 1), abs_nonneg
        (Real.cos (rZeroHeight z.1 * Real.log t))])
    hint
  rw [intervalIntegral.integral_const_mul] at hle
  unfold cellModulation cellBackground
  rw [← Real.norm_eq_abs]
  exact hle

/-- En ligne, la borne de cellule est `2 a^{−1/2} Δli`. -/
theorem cellModulation_abs_le_onLine (z : TrueZero) (hOn : rZeroRadialPosition z.1 = 1 / 2)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    |cellModulation z a b| ≤ 2 * a ^ (-(1 / 2 : ℝ)) * cellBackground a b := by
  have h := cellModulation_abs_le z ha hab
  rw [hOn] at h
  convert h using 4
  norm_num

/-- **Cellules authentiques** `[C_k, C_{k+1}]`, `k ≥ 0` : `|Δb_{ρ,k}| ≤ 2 C_k^{β−1} Δli_k`. -/
theorem cellModulation_abs_le_at_contacts (z : TrueZero) {k : ℤ} (hk : 0 ≤ k) :
    |cellModulation z (contactMinusAt z k) (contactMinusAt z (k + 1))| ≤
      2 * contactMinusAt z k ^ (rZeroRadialPosition z.1 - 1) *
        cellBackground (contactMinusAt z k) (contactMinusAt z (k + 1)) :=
  cellModulation_abs_le z (contact_gt_one z hk) (contactAt_ordered z k).le

#print axioms counting_modulation_eq_raw_derivative
#print axioms background_envelope_tendsto_zero
#print axioms extremum_contact_offset
#print axioms cellModulation_abs_le_at_contacts

end RHV6Fresh
