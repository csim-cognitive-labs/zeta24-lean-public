/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaParameters
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# RHV6Fresh — la prémisse : aucun changement de régime n'est possible (auteur, 2026-09-30)

Décision de l'auteur : la prémisse ne porte ni sur la hauteur, ni sur une borne de taille, ni sur
un fait annexe. Elle dit une seule chose : **aucun changement de régime n'est possible**. Tout le
reste est démontré.

* **§1 Le régime vertical est engagé : théorème.** Zêta porte deux hauteurs distinctes
  (`exists_two_heights`), donc un passage vertical existe (`exists_verticalPassage`). Preuve par
  le côté arithmétique : si tous les zéros avaient la même hauteur, ils seraient en nombre fini,
  la formule explicite serait une fonction holomorphe de l'abscisse, nulle avant le premier `2`,
  donc nulle partout, alors que la somme des premiers ne l'est pas après `2`.
* **§2 La prémisse** `PNoRegimeChange` : à aucune jonction de deux passages consécutifs le régime
  ne change, dans aucun sens.
* **§3 Clôture** : `PNoRegimeChange ↔ RiemannHypothesis`
  (`noRegimeChange_iff_riemannHypothesis`), sans aucune condition annexe : ni hauteur positive,
  ni hauteur minimale, ni bas de chaîne.
* **§4 La prémisse lue sur un pas** (formulation de l'auteur) : sur un passage vertical le facteur
  radial de l'arrivée vérifie déjà `r' ≥ 1` (`arrival_radial_ge_one`, compilé) ; l'autre sens
  `r' ≤ 1` équivaut exactement à « aucun changement de régime à l'arrivée »
  (`arrival_radial_le_one_iff_regime_kept`) ; sous la prémisse il reste `r' = 1` : aucun
  déplacement radial n'est apparu pendant la progression en hauteur, `(T, 1/2) → (T', 1/2)`
  (`noRegimeChange_no_radial_displacement`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau. Une seule `def P… : Prop` : `PNoRegimeChange`.
-/

namespace RHV6Fresh

open RHV3Lean Set Filter
open scoped Topology

/-! ## 1. Le régime vertical est engagé -/

/-- Le membre typé d'un zéro de la formule explicite de hauteur strictement positive. -/
noncomputable def upperMember (ρ : ExplicitIndex) (h : 0 < (ρ : ℂ).im) : TrueZero :=
  ⟨⟨(ρ : ℂ), ρ.property.1, (isNontrivialZetaZero_re_mem_Ioo ρ.property).1,
    (isNontrivialZetaZero_re_mem_Ioo ρ.property).2⟩, h⟩

theorem upperMember_height (ρ : ExplicitIndex) (h : 0 < (ρ : ℂ).im) :
    rZeroHeight (upperMember ρ h).1 = (ρ : ℂ).im := rfl

/-- Si tous les membres avaient la même hauteur, les zéros seraient en nombre fini. -/
theorem explicitIndex_finite_of_single_height
    (h : ∀ z w : TrueZero, rZeroHeight z.1 = rZeroHeight w.1) : Finite ExplicitIndex := by
  obtain ⟨T0, hT0⟩ : ∃ T0 : ℝ, ∀ z : TrueZero, rZeroHeight z.1 = T0 := by
    by_cases hne : Nonempty TrueZero
    · obtain ⟨z0⟩ := hne
      exact ⟨rZeroHeight z0.1, fun z => h z z0⟩
    · exact ⟨0, fun z => absurd ⟨z⟩ hne⟩
  have hbound : ∀ ρ : ExplicitIndex, ‖(ρ : ℂ)‖ ≤ 1 + |T0| := by
    intro ρ
    have hre := isNontrivialZetaZero_re_mem_Ioo ρ.property
    have him : |(ρ : ℂ).im| ≤ |T0| := by
      rcases lt_trichotomy (ρ : ℂ).im 0 with hneg | hzero | hpos
      · have hc : IsNontrivialZetaZero ((starRingEnd ℂ) (ρ : ℂ)) :=
          (isNontrivialZetaZero_conj_iff _).mpr ρ.property
        have hci : 0 < ((starRingEnd ℂ) (ρ : ℂ)).im := by rw [Complex.conj_im]; linarith
        have key : ((starRingEnd ℂ) (ρ : ℂ)).im = T0 := hT0 (upperMember ⟨_, hc⟩ hci)
        rw [Complex.conj_im] at key
        rw [← key, abs_neg]
      · rw [hzero, abs_zero]; exact abs_nonneg _
      · have key : (ρ : ℂ).im = T0 := hT0 (upperMember ρ hpos)
        rw [key]
    have hre1 : |(ρ : ℂ).re| ≤ 1 := by rw [abs_of_pos hre.1]; exact hre.2.le
    calc ‖(ρ : ℂ)‖ ≤ |(ρ : ℂ).re| + |(ρ : ℂ).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 + |T0| := by linarith
  have hfin := explicitIndex_locallyFinite (1 + |T0|)
  have huniv : (Set.univ : Set ExplicitIndex) = {ρ : ExplicitIndex | ‖(ρ : ℂ)‖ ≤ 1 + |T0|} := by
    ext ρ
    simp [hbound ρ]
  exact Set.finite_univ_iff.mp (huniv ▸ hfin)

/-- Le profil complexe d'un zéro trivial : le terme de la formule explicite, l'abscisse devenue
variable complexe. -/
noncomputable def trivialProfile (n : ℕ) (z : ℂ) : ℂ :=
  -(z ^ trivialZetaZeroAt n / (trivialZetaZeroAt n * (trivialZetaZeroAt n + 1)))

theorem trivialProfile_real {x : ℝ} (hx : 1 < x) (n : ℕ) :
    trivialZeroResidueTerm x n = trivialProfile n (x : ℂ) := by
  rw [trivial_zero_residue_term_eq hx n]
  rfl

theorem trivialProfile_bound (n : ℕ) {z : ℂ} (hz : (3 / 2 : ℝ) < z.re) :
    ‖trivialProfile n z‖ ≤ ‖trivialZeroResidueTerm (3 / 2) n‖ := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hz
    linarith
  have hnorm : (3 / 2 : ℝ) ≤ ‖z‖ := hz.le.trans (Complex.re_le_norm z)
  have hre : (trivialZetaZeroAt n).re ≤ 0 := by
    simp only [trivialZetaZeroAt, Complex.mul_re, Complex.neg_re, Complex.re_ofNat,
      Complex.natCast_re, Complex.neg_im, Complex.im_ofNat, Complex.natCast_im, neg_zero,
      mul_zero, sub_zero]
    have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have him : (trivialZetaZeroAt n).im = 0 := by
    simp [trivialZetaZeroAt]
  rw [trivialProfile_real (by norm_num : (1 : ℝ) < 3 / 2) n]
  unfold trivialProfile
  rw [norm_neg, norm_neg, norm_div, norm_div]
  refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
  rw [Complex.norm_cpow_of_ne_zero hz0, him, mul_zero, Real.exp_zero, div_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) hnorm hre

theorem trivialProfile_differentiableOn (n : ℕ) :
    DifferentiableOn ℂ (trivialProfile n) {z : ℂ | (3 / 2 : ℝ) < z.re} := by
  intro z hz
  have hz' : (3 / 2 : ℝ) < z.re := hz
  have hs : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith))
  exact (((differentiableAt_id.cpow_const hs).div_const _).neg).differentiableWithinAt

/-- La formule explicite, l'abscisse devenue variable complexe, quand les zéros sont en nombre
fini. -/
noncomputable def finiteSpectralExtension [Fintype ExplicitIndex] (z : ℂ) : ℂ :=
  z / 2 + (-logDeriv riemannZeta 0) + logDeriv riemannZeta (-1) * z⁻¹
    + (∑' n : ℕ, trivialProfile n z)
    + ∑ ρ : ExplicitIndex,
        -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * (z ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1)))

theorem finiteSpectralExtension_real [Fintype ExplicitIndex] {x : ℝ} (hx : 1 < x) :
    finiteSpectralExtension (x : ℂ) = smoothedVonMangoldtSum x := by
  rw [← smoothedZeroFormula_eq_smoothedVonMangoldtSum hx]
  unfold smoothedZeroFormula finiteSpectralExtension
  rw [tsum_congr (fun n => trivialProfile_real hx n),
    tsum_fintype (f := fun ρ : ExplicitIndex => nontrivialZeroResidueTerm x ρ)]
  rfl

theorem finiteSpectralExtension_differentiableOn [Fintype ExplicitIndex] :
    DifferentiableOn ℂ finiteSpectralExtension {z : ℂ | (3 / 2 : ℝ) < z.re} := by
  have hopen : IsOpen {z : ℂ | (3 / 2 : ℝ) < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h1 : DifferentiableOn ℂ
      (fun z : ℂ => z / 2 + (-logDeriv riemannZeta 0) + logDeriv riemannZeta (-1) * z⁻¹)
      {z : ℂ | (3 / 2 : ℝ) < z.re} := by
    intro z hz
    have hz' : (3 / 2 : ℝ) < z.re := hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hz'
      linarith
    exact (((differentiableAt_id.div_const 2).add_const _).add
      ((differentiableAt_inv hz0).const_mul _)).differentiableWithinAt
  have h2 : DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, trivialProfile n z)
      {z : ℂ | (3 / 2 : ℝ) < z.re} :=
    Complex.differentiableOn_tsum_of_summable_norm
      (trivial_zero_residue_series_summable (x := 3 / 2) (by norm_num)).norm
      trivialProfile_differentiableOn hopen (fun n z hz => trivialProfile_bound n hz)
  have h3 : DifferentiableOn ℂ (fun z : ℂ => ∑ ρ : ExplicitIndex,
      -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * (z ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))))
      {z : ℂ | (3 / 2 : ℝ) < z.re} := by
    refine DifferentiableOn.fun_sum fun ρ _ => ?_
    intro z hz
    have hz' : (3 / 2 : ℝ) < z.re := hz
    have hs : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith))
    exact (((differentiableAt_id.cpow_const hs).div_const _).const_mul _).differentiableWithinAt
  exact (h1.add h2).add h3

/-- Avant le premier `2`, la somme lissée des premiers est nulle. -/
theorem smoothedVonMangoldtSum_eq_zero_of_le_two {x : ℝ} (h1 : 1 < x) (h2 : x ≤ 2) :
    smoothedVonMangoldtSum x = 0 := by
  have hceil : ⌈x⌉₊ = 2 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    exact ⟨by norm_num; exact h1, by exact_mod_cast h2⟩
  unfold smoothedVonMangoldtSum
  rw [hceil]
  simp [Finset.sum_range_succ]

/-- Après `2`, elle ne l'est pas. -/
theorem smoothedVonMangoldtSum_five_halves_ne_zero : smoothedVonMangoldtSum (5 / 2) ≠ 0 := by
  have hceil : ⌈(5 / 2 : ℝ)⌉₊ = 3 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    constructor <;> norm_num
  have hval : smoothedVonMangoldtSum (5 / 2) = ((Real.log 2 * (1 / 5) : ℝ) : ℂ) := by
    unfold smoothedVonMangoldtSum
    rw [hceil]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      ArithmeticFunction.map_zero, ArithmeticFunction.vonMangoldt_apply_one,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Complex.ofReal_zero, zero_mul]
    push_cast
    ring
  rw [hval]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact_mod_cast (mul_pos hlog (by norm_num : (0 : ℝ) < 1 / 5)).ne'

/-- **Zêta porte deux hauteurs distinctes.** Sinon les zéros seraient en nombre fini, la formule
explicite serait holomorphe en l'abscisse, nulle avant `2`, donc nulle partout ; la somme des
premiers ne l'est pas. -/
theorem exists_two_heights : ∃ z w : TrueZero, rZeroHeight z.1 < rZeroHeight w.1 := by
  by_contra hno
  have hsame : ∀ z w : TrueZero, rZeroHeight z.1 = rZeroHeight w.1 := fun z w =>
    le_antisymm (not_lt.mp fun h => hno ⟨w, z, h⟩) (not_lt.mp fun h => hno ⟨z, w, h⟩)
  have := explicitIndex_finite_of_single_height hsame
  let _ : Fintype ExplicitIndex := Fintype.ofFinite _
  have hopen : IsOpen {z : ℂ | (3 / 2 : ℝ) < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {z : ℂ | (3 / 2 : ℝ) < z.re} :=
    (convex_halfSpace_re_gt _).isPreconnected
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] (7 / 4 : ℝ), finiteSpectralExtension (x : ℂ) = 0 := by
    have hmem : ∀ᶠ x : ℝ in 𝓝 (7 / 4 : ℝ), x ∈ Ioo (3 / 2 : ℝ) 2 :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hmem] with x hx
    rw [finiteSpectralExtension_real (by linarith [hx.1])]
    exact smoothedVonMangoldtSum_eq_zero_of_le_two (by linarith [hx.1]) hx.2.le
  have htend : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (7 / 4 : ℝ)) (𝓝[≠] ((7 / 4 : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact fun h => hx (Complex.ofReal_injective h)
  have hzero : ∃ᶠ z in 𝓝[≠] ((7 / 4 : ℝ) : ℂ), finiteSpectralExtension z = 0 :=
    htend.frequently hev.frequently
  have h0 : ((7 / 4 : ℝ) : ℂ) ∈ {z : ℂ | (3 / 2 : ℝ) < z.re} := by
    change (3 / 2 : ℝ) < ((7 / 4 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    norm_num
  have h52 : ((5 / 2 : ℝ) : ℂ) ∈ {z : ℂ | (3 / 2 : ℝ) < z.re} := by
    change (3 / 2 : ℝ) < ((5 / 2 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    norm_num
  have hall := (finiteSpectralExtension_differentiableOn.analyticOnNhd
    hopen).eqOn_zero_of_preconnected_of_frequently_eq_zero hconn h0 hzero
  have hval : finiteSpectralExtension ((5 / 2 : ℝ) : ℂ) = 0 := hall h52
  rw [finiteSpectralExtension_real (by norm_num)] at hval
  exact smoothedVonMangoldtSum_five_halves_ne_zero hval

/-- Il existe un membre le plus bas. -/
theorem exists_bottom_member (z : TrueZero) :
    ∃ m : TNonTrivialZetaZero, 0 < rZeroHeight m ∧ sUpperZerosBelow m = ∅ := by
  have key : ∀ n : ℕ, ∀ w : TNonTrivialZetaZero, nZeroSourceIndex w = n → 0 < rZeroHeight w →
      ∃ m : TNonTrivialZetaZero, 0 < rZeroHeight m ∧ sUpperZerosBelow m = ∅ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hn hw
      by_cases hS : (sUpperZerosBelow w).Nonempty
      · obtain ⟨u, hu, huw⟩ := hS
        exact ih _ (hn ▸ thm_zeroSourceIndex_strictMono hu huw) u rfl hu
      · exact ⟨w, hw, Set.not_nonempty_iff_eq_empty.mp hS⟩
  exact key _ z.1 rfl z.2

/-- Si tout passage est horizontal, tous les membres ont la hauteur du plus bas. -/
theorem heights_constant_of_allHorizontal {m0 : TNonTrivialZetaZero} (h0 : 0 < rZeroHeight m0)
    (hBot : sUpperZerosBelow m0 = ∅)
    (hAll : ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → HorizontalPassage p) :
    ∀ w : TNonTrivialZetaZero, 0 < rZeroHeight w → rZeroHeight w = rZeroHeight m0 := by
  have key : ∀ n : ℕ, ∀ w : TNonTrivialZetaZero, nZeroSourceIndex w = n → 0 < rZeroHeight w →
      rZeroHeight w = rZeroHeight m0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hn hw
      by_cases hwm : w = m0
      · rw [hwm]
      · have hprec : PZeroMemberPrecedes m0 w := by
          rcases thm_distinctZeroMembers_comparable hwm with h | h
          · have hmem : w ∈ sUpperZerosBelow m0 := ⟨hw, h⟩
            rw [hBot] at hmem
            exact absurd hmem (Set.notMem_empty _)
          · exact h
        obtain ⟨m, hm, hcons, hidx⟩ := exists_consecutive_predecessor w ⟨m0, h0, hprec⟩
        have hH : HorizontalPassage ⟨m, w, hcons⟩ := hAll ⟨m, w, hcons⟩ hm
        have hmw : rZeroHeight m = rZeroHeight w := hH
        rw [← hmw]
        exact ih _ (hn ▸ hidx) m rfl hm
  exact fun w hw => key _ w rfl hw

/-- **Le régime vertical est engagé** : il existe un passage vertical. Théorème, sans hypothèse. -/
theorem exists_verticalPassage :
    ∃ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember ∧ VerticalPassage p := by
  by_contra hno
  have hAll : ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → HorizontalPassage p := by
    intro p hp
    rcases passage_regime_dichotomy p with ⟨hV, _⟩ | ⟨hH, _⟩
    · exact absurd ⟨p, hp, hV⟩ hno
    · exact hH
  obtain ⟨z, w, hlt⟩ := exists_two_heights
  obtain ⟨m0, h0, hBot⟩ := exists_bottom_member z
  have hz := heights_constant_of_allHorizontal h0 hBot hAll z.1 z.2
  have hw := heights_constant_of_allHorizontal h0 hBot hAll w.1 w.2
  rw [hz, hw] at hlt
  exact lt_irrefl _ hlt

/-! ## 2. La prémisse -/

/-- **La prémisse : aucun changement de régime n'est possible.** À aucune jonction de deux
passages consécutifs le régime ne change, dans aucun sens. -/
def PNoRegimeChange : Prop :=
  ∀ p q : TZeroPassage, p.zLaterMember = q.zEarlierMember →
    ¬ ((VerticalPassage p ∧ HorizontalPassage q) ∨ (HorizontalPassage p ∧ VerticalPassage q))

/-- Deux passages qui partent du même membre ont le même régime. -/
theorem horizontal_of_same_exit {q p : TZeroPassage} (hq : HorizontalPassage q)
    (he : p.zEarlierMember = q.zEarlierMember) : HorizontalPassage p := by
  rcases passage_regime_dichotomy p with ⟨hV, _⟩ | ⟨hH, _⟩
  · exfalso
    apply p.hConsecutive.2
    refine ⟨q.zLaterMember, ?_, ?_⟩
    · rw [he]
      exact q.hConsecutive.1
    · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
      left
      have h1 : rZeroHeight q.zLaterMember = rZeroHeight p.zEarlierMember := by
        rw [he]
        exact hq.symm
      rw [h1]
      exact hV
  · exact hH

/-- Sans changement de régime, si le passage le plus bas est horizontal, tous le sont. -/
theorem allHorizontal_of_bottom_horizontal (h : PNoRegimeChange) {q : TZeroPassage}
    (hE : 0 < rZeroHeight q.zEarlierMember) (hBot : sUpperZerosBelow q.zEarlierMember = ∅)
    (hH : HorizontalPassage q) :
    ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → HorizontalPassage p := by
  have key : ∀ n : ℕ, ∀ p : TZeroPassage, nZeroSourceIndex p.zEarlierMember = n →
      0 < rZeroHeight p.zEarlierMember → HorizontalPassage p := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p hn hp
      by_cases he : p.zEarlierMember = q.zEarlierMember
      · exact horizontal_of_same_exit hH he
      · have hprec : PZeroMemberPrecedes q.zEarlierMember p.zEarlierMember := by
          rcases thm_distinctZeroMembers_comparable he with h' | h'
          · have hmem : p.zEarlierMember ∈ sUpperZerosBelow q.zEarlierMember := ⟨hp, h'⟩
            rw [hBot] at hmem
            exact absurd hmem (Set.notMem_empty _)
          · exact h'
        obtain ⟨m, hm, hcons, hidx⟩ :=
          exists_consecutive_predecessor p.zEarlierMember ⟨q.zEarlierMember, hE, hprec⟩
        have hH' : HorizontalPassage ⟨m, p.zEarlierMember, hcons⟩ :=
          ih _ (hn ▸ hidx) ⟨m, p.zEarlierMember, hcons⟩ rfl hm
        rcases passage_regime_dichotomy p with ⟨hV, _⟩ | ⟨hHp, _⟩
        · exact absurd (Or.inr ⟨hH', hV⟩) (h ⟨m, p.zEarlierMember, hcons⟩ p rfl)
        · exact hHp
  exact fun p hp => key _ p rfl hp

/-! ## 3. Clôture -/

/-- **Aucun changement de régime ⟹ l'hypothèse de Riemann**, sans condition annexe. -/
theorem riemannHypothesis_of_noRegimeChange (h : PNoRegimeChange) : RiemannHypothesis := by
  refine riemannHypothesis_iff_no_regimeEntry.mpr ⟨?_, ?_⟩
  · rintro ⟨p, q, hJ, hp, hq⟩
    exact h p q hJ (Or.inl ⟨hp, hq⟩)
  · rintro ⟨q, hE, hBot, hH⟩
    have hAll := allHorizontal_of_bottom_horizontal h hE hBot hH
    obtain ⟨z, w, hlt⟩ := exists_two_heights
    have hz := heights_constant_of_allHorizontal hE hBot hAll z.1 z.2
    have hw := heights_constant_of_allHorizontal hE hBot hAll w.1 w.2
    rw [hz, hw] at hlt
    exact lt_irrefl _ hlt

/-- Sous l'hypothèse de Riemann, aucun changement de régime. -/
theorem noRegimeChange_of_riemannHypothesis (hRH : RiemannHypothesis) : PNoRegimeChange := by
  rintro p q _ (⟨_, hq⟩ | ⟨hp, _⟩)
  · exact no_horizontal_of_riemannHypothesis hRH q hq
  · exact no_horizontal_of_riemannHypothesis hRH p hp

/-- **La prémisse est exactement l'hypothèse de Riemann**, sans condition annexe. -/
theorem noRegimeChange_iff_riemannHypothesis : PNoRegimeChange ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_noRegimeChange, noRegimeChange_of_riemannHypothesis⟩

/-- **Sans changement de régime, tout passage est vertical** : le régime engagé est le seul. -/
theorem allVertical_of_noRegimeChange (h : PNoRegimeChange) (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) : VerticalPassage p :=
  allVertical_iff_riemannHypothesis.mpr (riemannHypothesis_of_noRegimeChange h) p hE

/-! ## 4. La prémisse lue sur un pas : aucun déplacement radial pendant la progression en hauteur -/

/-- **Le sens déjà compilé** : sur un passage vertical, le facteur radial de l'arrivée est au
moins `1` ; l'arrivée ne peut pas se trouver du côté `β > 1/2`. -/
theorem arrival_radial_ge_one (p : TZeroPassage) (hL : 0 < rZeroHeight p.zLaterMember)
    (hV : VerticalPassage p) : 1 ≤ radialFactor ⟨p.zLaterMember, hL⟩ :=
  one_le_radialFactor_of_le_half ⟨p.zLaterMember, hL⟩ (passage_entry_radial_le_half p hV)

/-- **L'autre sens est exactement l'absence de changement de régime à l'arrivée** : sur un passage
vertical, `r' ≤ 1` si et seulement si aucun passage horizontal ne part du membre d'arrivée. -/
theorem arrival_radial_le_one_iff_regime_kept (p : TZeroPassage)
    (hL : 0 < rZeroHeight p.zLaterMember) (hV : VerticalPassage p) :
    radialFactor ⟨p.zLaterMember, hL⟩ ≤ 1 ↔
      ∀ q : TZeroPassage, p.zLaterMember = q.zEarlierMember → ¬ HorizontalPassage q := by
  constructor
  · intro hr q hJ hq
    have hlt := junction_vertical_horizontal hJ hV hq
    exact absurd ((radialFactor_gt_one_iff ⟨p.zLaterMember, hL⟩).mpr hlt) (not_lt.mpr hr)
  · intro hkeep
    by_contra hr
    have hlt : rZeroRadialPosition (⟨p.zLaterMember, hL⟩ : TrueZero).1 < 1 / 2 :=
      (radialFactor_gt_one_iff ⟨p.zLaterMember, hL⟩).mp (not_le.mp hr)
    obtain ⟨z', hT', hcons'⟩ := exists_fiberSuccessor hlt
    exact hkeep ⟨p.zLaterMember, z'.1, hcons'⟩ rfl hT'.symm

/-- **Sous la prémisse, aucun déplacement radial n'est apparu pendant la progression en
hauteur** : sur tout passage vertical, `r' = 1` et l'arrivée est en ligne. Partant de la ligne :
`(T, 1/2) → (T', 1/2)`. Dérivé pas à pas, sans passer par l'énoncé global. -/
theorem noRegimeChange_no_radial_displacement (h : PNoRegimeChange) (p : TZeroPassage)
    (hL : 0 < rZeroHeight p.zLaterMember) (hV : VerticalPassage p) :
    radialFactor ⟨p.zLaterMember, hL⟩ = 1 ∧ rZeroRadialPosition p.zLaterMember = 1 / 2 := by
  have hle : radialFactor ⟨p.zLaterMember, hL⟩ ≤ 1 :=
    (arrival_radial_le_one_iff_regime_kept p hL hV).mpr
      (fun q hJ hq => h p q hJ (Or.inl ⟨hV, hq⟩))
  have heq := le_antisymm hle (arrival_radial_ge_one p hL hV)
  exact ⟨heq, (radialFactor_eq_one_iff ⟨p.zLaterMember, hL⟩).mp heq⟩

#print axioms arrival_radial_ge_one
#print axioms arrival_radial_le_one_iff_regime_kept
#print axioms noRegimeChange_no_radial_displacement
#print axioms explicitIndex_finite_of_single_height
#print axioms finiteSpectralExtension_real
#print axioms finiteSpectralExtension_differentiableOn
#print axioms exists_two_heights
#print axioms exists_bottom_member
#print axioms exists_verticalPassage
#print axioms allHorizontal_of_bottom_horizontal
#print axioms riemannHypothesis_of_noRegimeChange
#print axioms noRegimeChange_iff_riemannHypothesis
#print axioms allVertical_of_noRegimeChange

end RHV6Fresh
