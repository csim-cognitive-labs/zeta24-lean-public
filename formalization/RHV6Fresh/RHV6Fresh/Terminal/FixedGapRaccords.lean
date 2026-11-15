/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.LocalPrimeGapSynchronization

/-!
# Raccords fixés par les deux bornes de chaque écart premier (E305, auteur, 2026-10-15)

Énoncé de l'auteur : « la contribution d'un même zéro à chaque intervalle `[p_n, p_{n+1}]` est fixée par les deux bornes ;
tous les intervalles sont donc soumis simultanément aux mêmes lois spectrales » ; proposition encadrée :
« zéros authentiques et contributions fixes + grammaire exacte des écarts ⟹ raccords obligatoires non déplaçables ».

Ce module démontre :
* §1 la contribution `∫_{log p_n}^{log p_{n+1}} e^{ρt} dt` est la différence d'UNE primitive aux deux bornes ; sur une
  chaîne d'écarts consécutifs elle télescope (même point, tous les écarts) ;
* §2 **non-déplaçabilité depuis les seuls écarts premiers** : deux points de partie réelle et de partie imaginaire
  strictement positives qui ont la même contribution sur tous les écarts premiers à partir d'un rang quelconque sont égaux
  (la lacune signalée par l'audit E301 dans `local_contribution_rigidity`, qui exigeait un continu de bornes, est fermée) ;
  aucune répartition des premiers n'est utilisée, seulement `log p_n → ∞` ;
* §3 portée exacte : un déplacement radial à hauteur fixée change la contribution sur des écarts au-delà de tout rang ;
  la propriété vaut pour TOUTE partie réelle `> 0` : elle identifie, elle ne contraint pas (`fixed_raccords_any_radial`,
  `exists_offline_point_with_fixed_raccords`).
-/

namespace RHV6Fresh

open RHV3Lean Complex Filter Topology

/-! ## 1. Une primitive, deux bornes -/

/-- Primitive de la densité `e^{ρt}` (variable `t = log x`). -/
noncomputable def gapPrimitive (ρ : ℂ) (u : ℝ) : ℂ := Complex.exp (ρ * u) / ρ

/-- Borne logarithmique du premier de rang `n`. -/
noncomputable def primeLogBound (n : ℕ) : ℝ := Real.log (fnPrimeAtRank n)

/-- **Contribution fixée par les deux bornes** : `gapTerm ρ a b = F_ρ(b) − F_ρ(a)`. -/
theorem gapTerm_eq_primitive_sub {ρ : ℂ} (hρ : ρ ≠ 0) (a b : ℝ) :
    gapTerm ρ a b = gapPrimitive ρ b - gapPrimitive ρ a := by
  rw [gapTerm_eq hρ]; unfold gapPrimitive; ring

/-- Contribution du point `ρ` à l'écart premier de rang `n`. -/
noncomputable def primeGapContribution (ρ : ℂ) (n : ℕ) : ℂ :=
  gapTerm ρ (primeLogBound n) (primeLogBound (n + 1))

/-- **Simultanéité** : sur toute chaîne d'écarts consécutifs, les contributions du même point télescopent ; la somme ne
dépend que des deux bornes extrêmes. -/
theorem primeGapContribution_chain {ρ : ℂ} (hρ : ρ ≠ 0) (n₀ N : ℕ) :
    ∑ j ∈ Finset.range N, primeGapContribution ρ (n₀ + j) =
      gapPrimitive ρ (primeLogBound (n₀ + N)) - gapPrimitive ρ (primeLogBound n₀) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    unfold primeGapContribution
    rw [gapTerm_eq_primitive_sub hρ, show n₀ + N + 1 = n₀ + (N + 1) by ring]
    ring

/-- Les bornes logarithmiques des premiers tendent vers l'infini. -/
theorem primeLogBound_tendsto : Tendsto primeLogBound atTop atTop := by
  have hmono : StrictMono fnPrimeAtRank := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have h1 : Tendsto (fun n => (fnPrimeAtRank n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmono.tendsto_atTop
  exact Real.tendsto_log_atTop.comp h1

/-! ## 2. Non-déplaçabilité depuis les seuls écarts premiers -/

/-- Lemme de croissance : si `e^{ρu}/ρ − e^{ρ'u}/ρ'` est constante le long d'une suite `u_n → ∞`, alors
`Re ρ' < Re ρ` est impossible (`Re ρ > 0`). -/
theorem not_re_lt_of_primitive_const {ρ ρ' : ℂ} (hβ : 0 < ρ.re) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {c : ℂ}
    (hc : ∀ n, gapPrimitive ρ (u n) - gapPrimitive ρ' (u n) = c) : ¬ ρ'.re < ρ.re := by
  intro hlt
  have hρ : ρ ≠ 0 := ne_zero_of_re_pos hβ
  have hnρ : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  -- borne : e^{βu}/‖ρ‖ ≤ ‖c‖ + e^{β'u}/‖ρ'‖
  have hbound : ∀ n, Real.exp (ρ.re * u n) / ‖ρ‖ ≤ ‖c‖ + Real.exp (ρ'.re * u n) / ‖ρ'‖ := by
    intro n
    have h1 : ‖gapPrimitive ρ (u n)‖ = Real.exp (ρ.re * u n) / ‖ρ‖ := by
      unfold gapPrimitive; rw [norm_div, Complex.norm_exp]; simp [Complex.mul_re]
    have h2 : ‖gapPrimitive ρ' (u n)‖ = Real.exp (ρ'.re * u n) / ‖ρ'‖ := by
      unfold gapPrimitive; rw [norm_div, Complex.norm_exp]; simp [Complex.mul_re]
    have h3 : gapPrimitive ρ (u n) = c + gapPrimitive ρ' (u n) := by rw [← hc n]; ring
    calc Real.exp (ρ.re * u n) / ‖ρ‖ = ‖gapPrimitive ρ (u n)‖ := h1.symm
      _ = ‖c + gapPrimitive ρ' (u n)‖ := by rw [h3]
      _ ≤ ‖c‖ + ‖gapPrimitive ρ' (u n)‖ := norm_add_le _ _
      _ = ‖c‖ + Real.exp (ρ'.re * u n) / ‖ρ'‖ := by rw [h2]
  -- après division par e^{βu} : 1/‖ρ‖ ≤ ‖c‖e^{−βu} + e^{(β'−β)u}/‖ρ'‖ → 0
  have hdiv : ∀ n, 1 / ‖ρ‖ ≤ ‖c‖ * Real.exp (-(ρ.re * u n)) +
      Real.exp ((ρ'.re - ρ.re) * u n) / ‖ρ'‖ := by
    intro n
    have hpos := Real.exp_pos (ρ.re * u n)
    have key := hbound n
    have e1 : Real.exp ((ρ'.re - ρ.re) * u n) = Real.exp (ρ'.re * u n) * Real.exp (-(ρ.re * u n)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (ρ.re * u n) * Real.exp (-(ρ.re * u n)) = 1 := by
      rw [← Real.exp_add]; simp
    rw [e1]
    have := mul_le_mul_of_nonneg_right key (Real.exp_pos (-(ρ.re * u n))).le
    calc 1 / ‖ρ‖ = Real.exp (ρ.re * u n) / ‖ρ‖ * Real.exp (-(ρ.re * u n)) := by
          rw [div_mul_eq_mul_div, e2]
      _ ≤ (‖c‖ + Real.exp (ρ'.re * u n) / ‖ρ'‖) * Real.exp (-(ρ.re * u n)) := this
      _ = ‖c‖ * Real.exp (-(ρ.re * u n)) +
            Real.exp (ρ'.re * u n) * Real.exp (-(ρ.re * u n)) / ‖ρ'‖ := by ring
  have hT1 : Tendsto (fun n => ‖c‖ * Real.exp (-(ρ.re * u n))) atTop (𝓝 0) := by
    have : Tendsto (fun n => -(ρ.re * u n)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hu.const_mul_atTop hβ)
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul ‖c‖
  have hT2 : Tendsto (fun n => Real.exp ((ρ'.re - ρ.re) * u n) / ‖ρ'‖) atTop (𝓝 0) := by
    have hneg : ρ'.re - ρ.re < 0 := by linarith
    have : Tendsto (fun n => (ρ'.re - ρ.re) * u n) atTop atBot := hu.const_mul_atTop_of_neg hneg
    simpa using (Real.tendsto_exp_atBot.comp this).div_const ‖ρ'‖
  have hlim := hT1.add hT2
  rw [add_zero] at hlim
  have hev : ∀ᶠ n in atTop, ‖c‖ * Real.exp (-(ρ.re * u n)) +
      Real.exp ((ρ'.re - ρ.re) * u n) / ‖ρ'‖ < 1 / ‖ρ‖ :=
    hlim.eventually (gt_mem_nhds (by positivity))
  obtain ⟨n, hn⟩ := hev.exists
  exact absurd (hdiv n) (not_le.mpr hn)

/-- **Identification depuis une suite de bornes `u_n → ∞`** : deux points de parties réelle et imaginaire strictement
positives dont la primitive diffère d'une constante le long de la suite sont égaux. -/
theorem eq_of_primitive_const {ρ ρ' : ℂ} (hβ : 0 < ρ.re) (hβ' : 0 < ρ'.re) (hT : 0 < ρ.im) (hT' : 0 < ρ'.im)
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {c : ℂ}
    (hc : ∀ n, gapPrimitive ρ (u n) - gapPrimitive ρ' (u n) = c) : ρ = ρ' := by
  have h1 := not_re_lt_of_primitive_const hβ hu hc
  have hc' : ∀ n, gapPrimitive ρ' (u n) - gapPrimitive ρ (u n) = -c := fun n => by rw [← hc n]; ring
  have h2 := not_re_lt_of_primitive_const hβ' hu hc'
  have hre : ρ.re = ρ'.re := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
  -- même partie réelle : les normes de 1/ρ et 1/ρ' coïncident
  have hρ : ρ ≠ 0 := ne_zero_of_re_pos hβ
  have hρ' : ρ' ≠ 0 := ne_zero_of_re_pos hβ'
  have hineq : ∀ n, |1 / ‖ρ‖ - 1 / ‖ρ'‖| ≤ ‖c‖ * Real.exp (-(ρ.re * u n)) := by
    intro n
    have h1 : ‖gapPrimitive ρ (u n)‖ = Real.exp (ρ.re * u n) * (1 / ‖ρ‖) := by
      unfold gapPrimitive; rw [norm_div, Complex.norm_exp]; simp [Complex.mul_re]; ring
    have h2 : ‖gapPrimitive ρ' (u n)‖ = Real.exp (ρ.re * u n) * (1 / ‖ρ'‖) := by
      unfold gapPrimitive; rw [norm_div, Complex.norm_exp]; simp [Complex.mul_re, ← hre]; ring
    have h3 : |‖gapPrimitive ρ (u n)‖ - ‖gapPrimitive ρ' (u n)‖| ≤ ‖c‖ := by
      rw [← hc n]; exact abs_norm_sub_norm_le _ _
    rw [h1, h2, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)] at h3
    have hpos := Real.exp_pos (ρ.re * u n)
    have e2 : Real.exp (ρ.re * u n) * Real.exp (-(ρ.re * u n)) = 1 := by rw [← Real.exp_add]; simp
    calc |1 / ‖ρ‖ - 1 / ‖ρ'‖| = Real.exp (ρ.re * u n) * |1 / ‖ρ‖ - 1 / ‖ρ'‖| * Real.exp (-(ρ.re * u n)) := by
          rw [mul_comm (Real.exp _) _, mul_assoc, e2, mul_one]
      _ ≤ ‖c‖ * Real.exp (-(ρ.re * u n)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  have hT1 : Tendsto (fun n => ‖c‖ * Real.exp (-(ρ.re * u n))) atTop (𝓝 0) := by
    have : Tendsto (fun n => -(ρ.re * u n)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hu.const_mul_atTop hβ)
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul ‖c‖
  have hzero : |1 / ‖ρ‖ - 1 / ‖ρ'‖| ≤ 0 :=
    ge_of_tendsto hT1 (Eventually.of_forall hineq)
  have hn : ‖ρ‖ = ‖ρ'‖ := by
    have h0 : 1 / ‖ρ‖ - 1 / ‖ρ'‖ = 0 := abs_nonpos_iff.mp hzero
    have hp := norm_pos_iff.mpr hρ
    have hp' := norm_pos_iff.mpr hρ'
    field_simp at h0
    linarith
  have hsq : ρ.im ^ 2 = ρ'.im ^ 2 := by
    have e : ‖ρ‖ ^ 2 = ‖ρ'‖ ^ 2 := by rw [hn]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hre] at e
    nlinarith
  have him : ρ.im = ρ'.im := by
    have := (sq_eq_sq₀ hT.le hT'.le).mp hsq
    exact this
  exact Complex.ext hre him

/-- **Non-déplaçabilité des raccords depuis les seuls écarts premiers** (forme de l'auteur) : deux points de parties
réelle et imaginaire strictement positives qui ont la même contribution sur TOUS les écarts premiers à partir d'un rang
`n₀` quelconque sont égaux. -/
theorem prime_gap_contributions_determine_point {ρ ρ' : ℂ} (hβ : 0 < ρ.re) (hβ' : 0 < ρ'.re)
    (hT : 0 < ρ.im) (hT' : 0 < ρ'.im) (n₀ : ℕ)
    (h : ∀ n, n₀ ≤ n → primeGapContribution ρ n = primeGapContribution ρ' n) : ρ = ρ' := by
  have hρ : ρ ≠ 0 := ne_zero_of_re_pos hβ
  have hρ' : ρ' ≠ 0 := ne_zero_of_re_pos hβ'
  set c := gapPrimitive ρ (primeLogBound n₀) - gapPrimitive ρ' (primeLogBound n₀)
  have hc : ∀ j, gapPrimitive ρ (primeLogBound (n₀ + j)) - gapPrimitive ρ' (primeLogBound (n₀ + j)) = c := by
    intro j
    induction j with
    | zero => simp [c]
    | succ j ih =>
      have hj := h (n₀ + j) (by omega)
      unfold primeGapContribution at hj
      rw [gapTerm_eq_primitive_sub hρ, gapTerm_eq_primitive_sub hρ'] at hj
      rw [← ih, show n₀ + (j + 1) = n₀ + j + 1 by ring]
      linear_combination hj
  have hu : Tendsto (fun j => primeLogBound (n₀ + j)) atTop atTop :=
    primeLogBound_tendsto.comp (tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩)
  exact eq_of_primitive_const hβ hβ' hT hT' hu hc

/-- Forme sur les vrais zéros : un vrai zéro est déterminé par ses contributions sur les écarts premiers au-delà de tout
rang. -/
theorem trueZero_determined_by_prime_gaps (z w : TrueZero) (n₀ : ℕ)
    (h : ∀ n, n₀ ≤ n → primeGapContribution (zeroPoint z) n = primeGapContribution (zeroPoint w) n) : z = w := by
  have hpt := prime_gap_contributions_determine_point (zeroPoint_re_pos z) (zeroPoint_re_pos w) z.2 w.2 n₀ h
  exact Subtype.ext (Subtype.ext hpt)

/-! ## 3. Portée exacte -/

/-- Deux points distincts diffèrent sur un écart premier au-delà de TOUT rang. -/
theorem distinct_points_differ_beyond_any_rank {ρ ρ' : ℂ} (hβ : 0 < ρ.re) (hβ' : 0 < ρ'.re)
    (hT : 0 < ρ.im) (hT' : 0 < ρ'.im) (hne : ρ ≠ ρ') (n₀ : ℕ) :
    ∃ n, n₀ ≤ n ∧ primeGapContribution ρ n ≠ primeGapContribution ρ' n := by
  by_contra hcon
  push Not at hcon
  exact hne (prime_gap_contributions_determine_point hβ hβ' hT hT' n₀ hcon)

/-- **Un déplacement radial à hauteur fixée change les contributions au-delà de tout rang** (« `Δβ ≠ 0` ⟹ modification »
de l'auteur, sur les écarts premiers). -/
theorem radial_displacement_changes_gaps {β β' T : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (hT : 0 < T) (hne : β ≠ β')
    (n₀ : ℕ) : ∃ n, n₀ ≤ n ∧
      primeGapContribution ((β : ℂ) + T * I) n ≠ primeGapContribution ((β' : ℂ) + T * I) n := by
  refine distinct_points_differ_beyond_any_rank (by simpa using hβ) (by simpa using hβ')
    (by simpa using hT) (by simpa using hT) ?_ n₀
  intro h
  exact hne (by simpa using congrArg Complex.re h)

/-- Propriété « raccords fixés » d'un point : tout point de quadrant ouvert qui reproduit ses contributions sur les écarts
premiers au-delà d'un rang lui est égal. -/
def FixedRaccords (ρ : ℂ) : Prop :=
  ∀ n₀ : ℕ, ∀ ρ' : ℂ, 0 < ρ'.re → 0 < ρ'.im →
    (∀ n, n₀ ≤ n → primeGapContribution ρ n = primeGapContribution ρ' n) → ρ' = ρ

/-- **Les raccords sont fixés pour TOUTE partie réelle `> 0`** : la propriété identifie, elle ne contraint pas `β`. -/
theorem fixed_raccords_any_radial {ρ : ℂ} (hβ : 0 < ρ.re) (hT : 0 < ρ.im) : FixedRaccords ρ :=
  fun n₀ _ hβ' hT' h => (prime_gap_contributions_determine_point hβ hβ' hT hT' n₀ h).symm

/-- Tout vrai zéro a ses raccords fixés. -/
theorem trueZero_fixedRaccords (z : TrueZero) : FixedRaccords (zeroPoint z) :=
  fixed_raccords_any_radial (zeroPoint_re_pos z) z.2

/-- **Un point hors ligne a lui aussi ses raccords fixés** : « contributions fixes ⟹ raccords non déplaçables » ne
donne pas `β = 1/2`. -/
theorem exists_offline_point_with_fixed_raccords :
    ∃ ρ : ℂ, ρ.re ≠ 1 / 2 ∧ FixedRaccords ρ :=
  ⟨(1 / 4 : ℂ) + 14 * I, by norm_num, fixed_raccords_any_radial (by norm_num) (by norm_num)⟩

/-- La lecture fermante sur les écarts premiers : la contribution d'un vrai zéro coïncide, sur tous les écarts au-delà
d'un rang, avec celle du point de ligne à la même hauteur ⟺ ce zéro est en ligne. Caractérisation (forme du but sur les
écarts), pas une dérivation. -/
theorem prime_gaps_line_reading_iff (z : TrueZero) :
    (∃ n₀, ∀ n, n₀ ≤ n → primeGapContribution (zeroPoint z) n =
        primeGapContribution ((1 / 2 : ℂ) + (rZeroHeight z.1 : ℂ) * I) n) ↔
      rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · rintro ⟨n₀, h⟩
    have hz : 0 < (zeroPoint z).im := z.2
    have hpt := prime_gap_contributions_determine_point (zeroPoint_re_pos z) (by norm_num)
      hz (by simpa [zeroPoint_im] using hz) n₀ h
    have := congrArg Complex.re hpt
    simpa [zeroPoint_re] using this
  · intro h
    refine ⟨0, fun n _ => ?_⟩
    congr 1
    apply Complex.ext
    · simp [zeroPoint_re, h]
    · simp [zeroPoint_im]

/-! ## 4. Hypothèse de l'auteur : la hauteur d'un OFF n'est pas celle d'un ON (non dérivée) -/

/-- **Hypothèse de l'auteur, écrite telle quelle** (non dérivée, jamais posée en hypothèse d'une fermeture) : aucun vrai
zéro hors ligne ne partage sa hauteur avec un vrai zéro en ligne. -/
def NoMixedHeight : Prop :=
  ∀ z w : TrueZero, rZeroHeight z.1 = rZeroHeight w.1 → rZeroRadialPosition w.1 = 1 / 2 →
    rZeroRadialPosition z.1 = 1 / 2

/-- Elle est impliquée par RH (au plus aussi forte que RH). -/
theorem noMixedHeight_of_riemannHypothesis (hRH : RiemannHypothesis) : NoMixedHeight :=
  fun z _ _ _ => thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1

/-- Sous elle, toute la fibre d'un membre hors ligne est hors ligne. -/
theorem noMixedHeight_offline_fiber (h : NoMixedHeight) (z : TrueZero) (hz : rZeroRadialPosition z.1 ≠ 1 / 2)
    (w : TrueZero) (hw : rZeroHeight w.1 = rZeroHeight z.1) : rZeroRadialPosition w.1 ≠ 1 / 2 :=
  fun hon => hz (h z w hw.symm hon)

/-- **Profil d'une arrivée sous la ligne, réunissant les raccords fixés et l'hypothèse de hauteur** : ses raccords sont
fixés ; elle diffère du point de ligne de même hauteur sur un écart premier au-delà de tout rang ; sous `NoMixedHeight`,
aucun vrai zéro de sa hauteur n'est en ligne. Ces trois faits sont simultanément satisfaits : aucun n'en contredit un
autre, et aucun ne mentionne une donnée qui exclurait `β_l < 1/2`. -/
theorem low_arrival_fixed_raccords_profile (h : NoMixedHeight) (l : TrueZero)
    (hlow : rZeroRadialPosition l.1 < 1 / 2) :
    FixedRaccords (zeroPoint l) ∧
      (∀ n₀ : ℕ, ∃ n, n₀ ≤ n ∧ primeGapContribution (zeroPoint l) n ≠
        primeGapContribution ((1 / 2 : ℂ) + (rZeroHeight l.1 : ℂ) * I) n) ∧
      (∀ w : TrueZero, rZeroHeight w.1 = rZeroHeight l.1 → rZeroRadialPosition w.1 ≠ 1 / 2) := by
  refine ⟨trueZero_fixedRaccords l, fun n₀ => ?_, noMixedHeight_offline_fiber h l (ne_of_lt hlow)⟩
  have hz : 0 < (zeroPoint l).im := l.2
  refine distinct_points_differ_beyond_any_rank (zeroPoint_re_pos l) (by norm_num) hz
    (by simpa [zeroPoint_im] using hz) ?_ n₀
  intro he
  have := congrArg Complex.re he
  simp [zeroPoint_re] at this
  linarith

#print axioms prime_gap_contributions_determine_point
#print axioms trueZero_determined_by_prime_gaps
#print axioms exists_offline_point_with_fixed_raccords
#print axioms prime_gaps_line_reading_iff
#print axioms low_arrival_fixed_raccords_profile

end RHV6Fresh
