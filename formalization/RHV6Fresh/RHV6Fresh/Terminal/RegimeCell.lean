/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.SpectralIdentity

/-!
# RHV6Fresh — la cellule locale complète vertical → horizontal → vertical (auteur, 2026-09-30)

Réorientation de l'auteur : confronter le changement de régime non au résidu seul, mais à ce qui
traverse la jonction, sur une cellule locale complète `a → e → l → b` :
contraction de grille, puis translation rigide de grille, puis contraction de grille.

Vocabulaire (auteur) : « contraction de grille » (la hauteur avance, le pas `π/T` se contracte) et
« translation rigide de grille » (même hauteur, `β` avance, tous les contacts sont multipliés par
un même facteur).

Ce qui est compilé ici, sans prémisse :

* **Cinématique exacte d'une paire de même hauteur** : coordonnées polaires du support
  (`zeroPoint_polar`), facteur de translation `gridTranslation`, et l'identité
  `T · (β_w − β_z) = ‖ρ_z‖ · ‖ρ_w‖ · sin(φ_z − φ_w)` (`radial_shift_eq_phase_sin`) : le déplacement
  radial est une fonction exacte de la translation des contacts.
* **Verrou de phase** (`horizontal_term_phase_lock`) : à même hauteur, pour tout `q > 0`,
  `zeroTerm w q = zeroTerm z q · transport(q) · exp(i(φ_z − φ_w))`. La translation rigide des
  contacts est la rotation constante entre les deux termes de la formule explicite ; le transport
  en est le module.
* **Le premier partagé garde sa cellule ou avance d'une cellule exactement**
  (`horizontal_pivot_shift`).
* **La cellule** `RegimeCell` et ses lois : `β_e < 1/2 < β_l`, `1/2 ≤ β_a`, `β_b ≤ 1/2` ; les deux
  membres centraux sont exactement miroirs l'un de l'autre (`central_mirror`) ; pas contracté,
  conservé, contracté (`pitch_signature`) ; aucune translation rigide, translation rigide, aucune
  (`contact_signature`) ; trois premiers consécutifs (`primes`) ; les deux variations du résidu lues
  des deux côtés et découpées en paquet et complément (`remainder_record`) ; la charge
  `(M₂²/(M₁·M₃))^d` du produit des trois transports (`transport_product`), jamais neutre
  (`charge_ne_one`), dont l'exposant est lu sur la translation (`offset_eq_translation`,
  `charge_reads_translation`).
* **Garde** : une cellule contredit RH (`not_riemannHypothesis`) ; sous RH il n'y a aucune cellule.

Borne : toutes ces identités sont satisfaites par la cellule. Aucune n'est une contradiction. Le
côté arithmétique de la cellule ne dépend que du rang (`arithmetic_depends_on_rank_only`) et le
côté Tour que des hauteurs et de `d`.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean ArithmeticFunction

/-! ## 0. Coordonnées polaires du support et cinématique d'une paire de même hauteur -/

theorem trueZero_ext {z w : TrueZero}
    (hβ : rZeroRadialPosition z.1 = rZeroRadialPosition w.1)
    (hT : rZeroHeight z.1 = rZeroHeight w.1) : z = w :=
  Subtype.ext (Subtype.ext (Complex.ext hβ hT))

private theorem sqrt_one_add_sq (z : TrueZero) :
    Real.sqrt (1 + (rZeroHeight z.1 / rZeroRadialPosition z.1) ^ 2) =
      ‖zeroPoint z‖ / rZeroRadialPosition z.1 := by
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have h : 1 + (rZeroHeight z.1 / rZeroRadialPosition z.1) ^ 2 =
      (‖zeroPoint z‖ / rZeroRadialPosition z.1) ^ 2 := by
    rw [div_pow, div_pow, zeroPoint_norm_sq]
    field_simp
  rw [h, Real.sqrt_sq (div_nonneg (norm_nonneg _) hβ.le)]

/-- `‖ρ‖ · cos φ = β`. -/
theorem zeroPoint_norm_mul_cos (z : TrueZero) :
    ‖zeroPoint z‖ * Real.cos (towerMotionOf z).phase = rZeroRadialPosition z.1 := by
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hN := zeroPoint_norm_pos z
  rw [towerMotion_phase, Real.cos_arctan, sqrt_one_add_sq]
  field_simp

/-- `‖ρ‖ · sin φ = T`. -/
theorem zeroPoint_norm_mul_sin (z : TrueZero) :
    ‖zeroPoint z‖ * Real.sin (towerMotionOf z).phase = rZeroHeight z.1 := by
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hN := zeroPoint_norm_pos z
  rw [towerMotion_phase, Real.sin_arctan, sqrt_one_add_sq]
  field_simp

/-- **Coordonnées polaires** : `ρ = ‖ρ‖ · exp(iφ)`, où `φ` est la phase de la Tour. -/
theorem zeroPoint_polar (z : TrueZero) :
    zeroPoint z =
      (‖zeroPoint z‖ : ℂ) * Complex.exp (((towerMotionOf z).phase : ℂ) * Complex.I) := by
  apply Complex.ext
  · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, zeroPoint_norm_mul_cos, zeroPoint_re]
  · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, zeroPoint_norm_mul_sin, zeroPoint_im]

/-- **Le facteur de translation de grille** de `z` vers `w` : `exp((φ_w − φ_z)/T_z)`. -/
noncomputable def gridTranslation (z w : TrueZero) : ℝ :=
  Real.exp (((towerMotionOf w).phase - (towerMotionOf z).phase) / rZeroHeight z.1)

theorem gridTranslation_pos (z w : TrueZero) : 0 < gridTranslation z w := Real.exp_pos _

/-- À même hauteur, tous les contacts de `w` sont ceux de `z` multipliés par `gridTranslation`. -/
theorem gridTranslation_contacts (z w : TrueZero) (hT : rZeroHeight z.1 = rZeroHeight w.1)
    (k : ℤ) :
    contactMinusAt w k = contactMinusAt z k * gridTranslation z w ∧
      contactPlusAt w k = contactPlusAt z k * gridTranslation z w :=
  ⟨sameHeight_grid_rigid_translation z w hT k, sameHeight_grid_rigid_translation z w hT (k + 1)⟩

theorem log_gridTranslation (z w : TrueZero) :
    rZeroHeight z.1 * Real.log (gridTranslation z w) =
      (towerMotionOf w).phase - (towerMotionOf z).phase := by
  unfold gridTranslation
  rw [Real.log_exp]
  have hT : rZeroHeight z.1 ≠ 0 := z.2.ne'
  field_simp

theorem phase_lt_of_radial_lt (z w : TrueZero) (hT : rZeroHeight z.1 = rZeroHeight w.1)
    (hβ : rZeroRadialPosition z.1 < rZeroRadialPosition w.1) :
    (towerMotionOf w).phase < (towerMotionOf z).phase := by
  have hTz : (0 : ℝ) < rZeroHeight z.1 := z.2
  have hβz : (0 : ℝ) < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  rw [towerMotion_phase, towerMotion_phase, ← hT]
  exact Real.arctan_strictMono (div_lt_div_of_pos_left hTz hβz hβ)

theorem gridTranslation_lt_one (z w : TrueZero) (hT : rZeroHeight z.1 = rZeroHeight w.1)
    (hβ : rZeroRadialPosition z.1 < rZeroRadialPosition w.1) : gridTranslation z w < 1 := by
  unfold gridTranslation
  rw [Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos (by linarith [phase_lt_of_radial_lt z w hT hβ]) z.2

/-- **Le déplacement radial, fonction exacte de la translation** : à même hauteur,
`T · (β_w − β_z) = ‖ρ_z‖ · ‖ρ_w‖ · sin(φ_z − φ_w)`. -/
theorem radial_shift_eq_phase_sin (z w : TrueZero) (hT : rZeroHeight z.1 = rZeroHeight w.1) :
    rZeroHeight z.1 * (rZeroRadialPosition w.1 - rZeroRadialPosition z.1) =
      ‖zeroPoint z‖ * ‖zeroPoint w‖ *
        Real.sin ((towerMotionOf z).phase - (towerMotionOf w).phase) := by
  rw [Real.sin_sub]
  have e : ‖zeroPoint z‖ * ‖zeroPoint w‖ *
      (Real.sin (towerMotionOf z).phase * Real.cos (towerMotionOf w).phase -
        Real.cos (towerMotionOf z).phase * Real.sin (towerMotionOf w).phase) =
      (‖zeroPoint z‖ * Real.sin (towerMotionOf z).phase) *
          (‖zeroPoint w‖ * Real.cos (towerMotionOf w).phase) -
        (‖zeroPoint z‖ * Real.cos (towerMotionOf z).phase) *
          (‖zeroPoint w‖ * Real.sin (towerMotionOf w).phase) := by ring
  rw [e, zeroPoint_norm_mul_sin, zeroPoint_norm_mul_cos, zeroPoint_norm_mul_cos,
    zeroPoint_norm_mul_sin, ← hT]
  ring

/-- **Verrou de phase du régime horizontal.** À même hauteur, pour tout `q > 0`, le terme de `w`
est le terme de `z` multiplié par le transport (réel) et tourné d'un angle constant
`φ_z − φ_w = −T · log c`, où `c` est le facteur de translation des contacts. -/
theorem horizontal_term_phase_lock (z w : TrueZero) (hT : rZeroHeight z.1 = rZeroHeight w.1)
    {q : ℝ} (hq : 0 < q) :
    zeroTerm w q = zeroTerm z q * ((energyRatio z w q : ℝ) : ℂ) *
      Complex.exp ((((towerMotionOf z).phase - (towerMotionOf w).phase : ℝ) : ℂ) *
        Complex.I) := by
  have hρ : zeroPoint w =
      zeroPoint z + ((rZeroRadialPosition w.1 - rZeroRadialPosition z.1 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.add_re, Complex.ofReal_re, zeroPoint_re, zeroPoint_re]; ring
    · rw [Complex.add_im, Complex.ofReal_im, zeroPoint_im, zeroPoint_im, hT]; ring
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hpow : (q : ℂ) ^ zeroPoint w = (q : ℂ) ^ zeroPoint z *
      ((q ^ (rZeroRadialPosition w.1 - rZeroRadialPosition z.1) : ℝ) : ℂ) := by
    rw [hρ, Complex.cpow_add _ _ hq0, Complex.ofReal_cpow hq.le]
  have pz := zeroPoint_polar z
  have pw := zeroPoint_polar w
  have hNz : ((‖zeroPoint z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zeroPoint_norm_pos z).ne'
  have hNw : ((‖zeroPoint w‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zeroPoint_norm_pos w).ne'
  have hz0 := zeroPoint_ne_zero z
  have hw0 := zeroPoint_ne_zero w
  have hexp : Complex.exp ((((towerMotionOf z).phase - (towerMotionOf w).phase : ℝ) : ℂ) *
      Complex.I) = Complex.exp (((towerMotionOf z).phase : ℂ) * Complex.I) /
        Complex.exp (((towerMotionOf w).phase : ℂ) * Complex.I) := by
    rw [← Complex.exp_sub]; congr 1; push_cast; ring
  have hEw := Complex.exp_ne_zero (((towerMotionOf w).phase : ℂ) * Complex.I)
  unfold zeroTerm
  rw [hpow, energyRatio_eq z w hq, hexp]
  push_cast
  generalize (q : ℂ) ^ zeroPoint z = X
  generalize (((q ^ (rZeroRadialPosition w.1 - rZeroRadialPosition z.1) : ℝ) : ℂ)) = r
  generalize Complex.exp (((towerMotionOf z).phase : ℂ) * Complex.I) = Ez at pz ⊢
  generalize Complex.exp (((towerMotionOf w).phase : ℂ) * Complex.I) = Ew at pw hEw ⊢
  generalize ((‖zeroPoint z‖ : ℝ) : ℂ) = Nz at pz hNz ⊢
  generalize ((‖zeroPoint w‖ : ℝ) : ℂ) = Nw at pw hNw ⊢
  field_simp
  linear_combination (X * r * Nw * Ew) * pz - (X * r * Nz * Ez) * pw

/-- **Le premier partagé garde sa cellule ou avance d'une cellule exactement.** À même hauteur,
`β_z < β_w`, pour tout `q > 0` : la cellule de `q` dans la Tour `w` est celle de `q` dans la Tour
`z`, ou la suivante. -/
theorem horizontal_pivot_shift (z w : TrueZero) (hT : rZeroHeight z.1 = rZeroHeight w.1)
    (hβ : rZeroRadialPosition z.1 < rZeroRadialPosition w.1) {q : ℝ} (hq : 0 < q) :
    pivotCoordinate w q = pivotCoordinate z q ∨ pivotCoordinate w q = pivotCoordinate z q + 1 := by
  obtain ⟨h1, h2⟩ := prime_raccord_has_unique_tower_cell z hq
  set k := pivotCoordinate z q with hk
  have hc1 := gridTranslation_lt_one z w hT hβ
  have hlow : contactMinusAt w k < q := by
    rw [(gridTranslation_contacts z w hT k).1]
    have := contactMinusAt_positive z k
    nlinarith
  by_cases hq' : q ≤ contactPlusAt w k
  · exact Or.inl (pivotCoordinate_unique w hq hlow hq').symm
  · right
    push Not at hq'
    have hhigh : q ≤ contactPlusAt w (k + 1) := by
      refine h2.trans ?_
      change contactMinusAt z (k + 1) ≤ contactMinusAt w (k + 1 + 1)
      rw [contactMinusAt_eq_exp, contactMinusAt_eq_exp, ← towerMotion_phase, ← towerMotion_phase,
        ← hT]
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ z.2.le
      have h3 := towerMotion_phase_lt_pi_div_two z
      have h4 := towerMotion_phase_pos w
      have h5 := Real.pi_pos
      push_cast
      linarith
    exact (pivotCoordinate_unique w hq hq' hhigh).symm

/-! ## 1. La cellule vertical → horizontal → vertical -/

/-- **La cellule locale complète** `a → e → l → b` : trois passages consécutifs, le premier et le
dernier à hauteur strictement croissante, le passage central à même hauteur. -/
structure RegimeCell where
  a : TrueZero
  e : TrueZero
  l : TrueZero
  b : TrueZero
  cons_ae : PZeroMembersConsecutive a.1 e.1
  cons_el : PZeroMembersConsecutive e.1 l.1
  cons_lb : PZeroMembersConsecutive l.1 b.1
  enter : rZeroHeight a.1 < rZeroHeight e.1
  level : rZeroHeight e.1 = rZeroHeight l.1
  leave : rZeroHeight l.1 < rZeroHeight b.1

namespace RegimeCell

variable (C : RegimeCell)

/-- Le passage d'entrée `a → e`. -/
def pIn : TZeroPassage := ⟨C.a.1, C.e.1, C.cons_ae⟩

/-- Le passage central `e → l`. -/
def pMid : TZeroPassage := ⟨C.e.1, C.l.1, C.cons_el⟩

/-- Le passage de sortie `l → b`. -/
def pOut : TZeroPassage := ⟨C.l.1, C.b.1, C.cons_lb⟩

/-- Les trois régimes : vertical, horizontal, vertical. -/
theorem regimes : VerticalPassage C.pIn ∧ HorizontalPassage C.pMid ∧ VerticalPassage C.pOut :=
  ⟨C.enter, C.level, C.leave⟩

/-- **Garde** : une cellule contredit RH. -/
theorem not_riemannHypothesis (C : RegimeCell) : ¬ RiemannHypothesis := fun hRH =>
  no_horizontal_of_riemannHypothesis hRH C.pMid C.level

theorem radial_e : rZeroRadialPosition C.e.1 < 1 / 2 :=
  junction_vertical_horizontal (p := C.pIn) (q := C.pMid) rfl C.enter C.level

theorem radial_l : 1 / 2 < rZeroRadialPosition C.l.1 :=
  junction_horizontal_vertical (p := C.pMid) (q := C.pOut) rfl C.level C.leave

theorem radial_a : 1 / 2 ≤ rZeroRadialPosition C.a.1 :=
  passage_exit_radial_ge_half C.pIn C.enter

theorem radial_b : rZeroRadialPosition C.b.1 ≤ 1 / 2 :=
  passage_entry_radial_le_half C.pOut C.leave

/-- **Les deux membres centraux sont exactement miroirs l'un de l'autre** : la fibre de la hauteur
centrale a exactement ces deux membres entre `a` et `b`. -/
theorem central_mirror : C.l = mirrorMember C.e := by
  have hle : rZeroRadialPosition C.l.1 ≤ 1 - rZeroRadialPosition C.e.1 :=
    fiberSuccessor_radial_le_mirror C.radial_e C.level.symm C.cons_el
  have hge : 1 - rZeroRadialPosition C.e.1 ≤ rZeroRadialPosition C.l.1 := by
    by_contra hlt
    push Not at hlt
    apply C.cons_lb.2
    refine ⟨(mirrorMember C.e).1, ?_, ?_⟩
    · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
      right
      refine ⟨C.level.symm.trans (mirrorMember_ordinate C.e).symm, ?_⟩
      rw [mirrorMember_radial]
      exact hlt
    · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
      left
      rw [mirrorMember_ordinate, C.level]
      exact C.leave
  exact trueZero_ext (by rw [mirrorMember_radial]; linarith)
    (by rw [mirrorMember_ordinate]; exact C.level.symm)

/-- **L'écart à la ligne** `d = 1/2 − β_e`. -/
noncomputable def offset : ℝ := 1 / 2 - rZeroRadialPosition C.e.1

theorem offset_pos : 0 < C.offset := by
  have := C.radial_e
  unfold offset
  linarith

theorem radial_e_eq : rZeroRadialPosition C.e.1 = 1 / 2 - C.offset := by
  unfold offset; ring

theorem radial_l_eq : rZeroRadialPosition C.l.1 = 1 / 2 + C.offset := by
  have h : rZeroRadialPosition C.l.1 = rZeroRadialPosition (mirrorMember C.e).1 := by
    rw [← C.central_mirror]
  rw [h, mirrorMember_radial]
  unfold offset; ring

theorem offset_lt_half : C.offset < 1 / 2 := by
  have := thm_zeroRadialPosition_positive C.e.1
  unfold offset
  linarith

/-! ### Tour : contraction, translation rigide, contraction -/

/-- **Signature du pas** : contracté, conservé, contracté. -/
theorem pitch_signature :
    towerPitch C.e < towerPitch C.a ∧ towerPitch C.l = towerPitch C.e ∧
      towerPitch C.b < towerPitch C.l :=
  ⟨(towerPitch_lt_iff C.a C.e).mpr C.enter, towerPitch_radial_blind C.e C.l C.level,
    (towerPitch_lt_iff C.l C.b).mpr C.leave⟩

/-- **Le facteur de translation du raccord central.** -/
noncomputable def translation : ℝ := gridTranslation C.e C.l

theorem radial_lt : rZeroRadialPosition C.e.1 < rZeroRadialPosition C.l.1 :=
  lt_trans C.radial_e C.radial_l

theorem translation_bounds : 0 < C.translation ∧ C.translation < 1 :=
  ⟨gridTranslation_pos _ _, gridTranslation_lt_one C.e C.l C.level C.radial_lt⟩

/-- **Signature des contacts** : aucune translation rigide à l'entrée ; translation rigide de
facteur `translation` au centre ; aucune translation rigide à la sortie. -/
theorem contact_signature :
    (¬ ∃ c : ℝ, ∀ k : ℤ, contactMinusAt C.e k = contactMinusAt C.a k * c) ∧
      (∀ k : ℤ, contactMinusAt C.l k = contactMinusAt C.e k * C.translation ∧
        contactPlusAt C.l k = contactPlusAt C.e k * C.translation) ∧
      (¬ ∃ c : ℝ, ∀ k : ℤ, contactMinusAt C.b k = contactMinusAt C.l k * c) :=
  ⟨no_rigid_translation_of_height_ne C.a C.e (ne_of_lt C.enter),
    gridTranslation_contacts C.e C.l C.level,
    no_rigid_translation_of_height_ne C.l C.b (ne_of_lt C.leave)⟩

/-- **L'écart à la ligne lu sur la translation** :
`2 · T · d = ‖ρ_e‖ · ‖ρ_l‖ · sin(−T · log c)`. -/
theorem offset_eq_translation :
    2 * rZeroHeight C.e.1 * C.offset =
      ‖zeroPoint C.e‖ * ‖zeroPoint C.l‖ *
        Real.sin (-(rZeroHeight C.e.1 * Real.log C.translation)) := by
  have h := radial_shift_eq_phase_sin C.e C.l C.level
  have hlog : -(rZeroHeight C.e.1 * Real.log C.translation) =
      (towerMotionOf C.e).phase - (towerMotionOf C.l).phase := by
    unfold translation
    rw [log_gridTranslation]
    ring
  rw [hlog, ← h, C.radial_l_eq, C.radial_e_eq]
  ring

/-- **Verrou de phase au centre** : pour tout `q > 0`, le terme de `l` est le terme de `e`
multiplié par le transport et tourné de l'angle constant `−T · log c`. -/
theorem central_phase_lock {q : ℝ} (hq : 0 < q) :
    zeroTerm C.l q = zeroTerm C.e q * ((energyRatio C.e C.l q : ℝ) : ℂ) *
      Complex.exp (((-(rZeroHeight C.e.1 * Real.log C.translation) : ℝ) : ℂ) * Complex.I) := by
  have hlog : -(rZeroHeight C.e.1 * Real.log C.translation) =
      (towerMotionOf C.e).phase - (towerMotionOf C.l).phase := by
    unfold translation
    rw [log_gridTranslation]
    ring
  rw [hlog]
  exact horizontal_term_phase_lock C.e C.l C.level hq

/-! ### Les trois premiers et les trois raccords -/

/-- Le premier du raccord d'entrée. -/
noncomputable def M₁ : ℕ := occurrence C.e

/-- Le premier du raccord central. -/
noncomputable def M₂ : ℕ := occurrence C.l

/-- Le premier du raccord de sortie. -/
noncomputable def M₃ : ℕ := occurrence C.b

/-- **Trois premiers consécutifs**, chacun le premier partagé de son raccord. -/
theorem primes :
    C.M₁.Prime ∧ C.M₂.Prime ∧ C.M₃.Prime ∧ C.M₁ < C.M₂ ∧ C.M₂ < C.M₃ ∧
      C.M₁ = expectedMinimumPrime C.a ∧ C.M₂ = expectedMinimumPrime C.e ∧
      C.M₃ = expectedMinimumPrime C.l ∧
      C.M₁ = fnPrimeAtRank (nZeroSourceIndex C.a.1 + 1) ∧
      C.M₂ = fnPrimeAtRank (nZeroSourceIndex C.a.1 + 2) ∧
      C.M₃ = fnPrimeAtRank (nZeroSourceIndex C.a.1 + 3) := by
  have n1 := thm_zeroSourceIndex_succ_of_consecutive C.a.2 C.cons_ae
  have n2 := thm_zeroSourceIndex_succ_of_consecutive C.e.2 C.cons_el
  have n3 := thm_zeroSourceIndex_succ_of_consecutive C.l.2 C.cons_lb
  refine ⟨occurrence_prime _, occurrence_prime _, occurrence_prime _,
    progression_strict C.cons_el, progression_strict C.cons_lb,
    progression_occurrence C.cons_ae, progression_occurrence C.cons_el,
    progression_occurrence C.cons_lb, ?_, ?_, ?_⟩
  · unfold M₁; rw [occurrence_eq_primeAtRank, n1]
  · unfold M₂; rw [occurrence_eq_primeAtRank, n2, n1]
  · unfold M₃; rw [occurrence_eq_primeAtRank, n3, n2, n1]

/-- Les trois raccords de la cellule se font aux trois premiers. -/
theorem raccords :
    (towerRaccordOf C.pIn C.a.2 C.e.2).M = C.M₁ ∧ (towerRaccordOf C.pMid C.e.2 C.l.2).M = C.M₂ ∧
      (towerRaccordOf C.pOut C.l.2 C.b.2).M = C.M₃ :=
  ⟨(towerRaccordOf C.pIn C.a.2 C.e.2).entry_eq, (towerRaccordOf C.pMid C.e.2 C.l.2).entry_eq,
    (towerRaccordOf C.pOut C.l.2 C.b.2).entry_eq⟩

/-- **Au raccord central, le premier partagé garde sa cellule ou avance d'une cellule.** -/
theorem central_cell_shift :
    pivotCoordinate C.l (C.M₂ : ℝ) = pivotCoordinate C.e (C.M₂ : ℝ) ∨
      pivotCoordinate C.l (C.M₂ : ℝ) = pivotCoordinate C.e (C.M₂ : ℝ) + 1 :=
  horizontal_pivot_shift C.e C.l C.level C.radial_lt
    (by exact_mod_cast C.primes.2.1.pos)

/-! ### La charge du produit des trois transports -/

/-- **La charge** `(M₂² / (M₁ · M₃))^d`. -/
noncomputable def charge : ℝ :=
  ((C.M₂ : ℝ) ^ 2 / ((C.M₁ : ℝ) * (C.M₃ : ℝ))) ^ C.offset

/-- **Produit des trois transports de la cellule** : le produit en ligne multiplié par la charge. -/
theorem transport_product :
    energyRatio C.a C.e C.M₁ * energyRatio C.e C.l C.M₂ * energyRatio C.l C.b C.M₃ =
      (C.M₁ : ℝ) ^ (1 / 2 - rZeroRadialPosition C.a.1) *
        (C.M₃ : ℝ) ^ (rZeroRadialPosition C.b.1 - 1 / 2) *
        (‖zeroPoint C.a‖ / ‖zeroPoint C.b‖) * C.charge := by
  obtain ⟨p1, p2, p3, _⟩ := C.primes
  exact fibre_transport_product_off C.a C.e C.l C.b (by exact_mod_cast p1.pos)
    (by exact_mod_cast p2.pos) (by exact_mod_cast p3.pos) C.radial_e_eq C.radial_l_eq

/-- **La charge n'est jamais neutre** dans une cellule. -/
theorem charge_ne_one : C.charge ≠ 1 := by
  obtain ⟨p1, p2, p3, h12, h23, _⟩ := C.primes
  intro h
  exact C.offset_pos.ne' ((fibre_charge_eq_one_iff p1 p2 p3 (ne_of_lt h12) (ne_of_lt h23) _).mp h)

/-- **La charge lit la translation** : son exposant est
`‖ρ_e‖ · ‖ρ_l‖ · sin(−T · log c) / (2T)`, où `c` est le facteur de translation des contacts ; sa
base `M₂²/(M₁·M₃)` ne contient que les trois premiers. -/
theorem charge_reads_translation :
    C.charge = ((C.M₂ : ℝ) ^ 2 / ((C.M₁ : ℝ) * (C.M₃ : ℝ))) ^
      (‖zeroPoint C.e‖ * ‖zeroPoint C.l‖ *
        Real.sin (-(rZeroHeight C.e.1 * Real.log C.translation)) / (2 * rZeroHeight C.e.1)) := by
  have hT : rZeroHeight C.e.1 ≠ 0 := C.e.2.ne'
  rw [← C.offset_eq_translation]
  unfold charge
  congr 1
  field_simp

/-! ### Le résidu entre les événements de la cellule -/

/-- **Le côté arithmétique de la cellule ne dépend que du rang** : les trois premiers et les deux
variations du résidu sont des fonctions du seul rang `n` du membre `a`. -/
theorem arithmetic_depends_on_rank_only :
    remainderBetween C.M₁ C.M₂ =
        remainderBetween (fnPrimeAtRank (nZeroSourceIndex C.a.1 + 1))
          (fnPrimeAtRank (nZeroSourceIndex C.a.1 + 2)) ∧
      remainderBetween C.M₂ C.M₃ =
        remainderBetween (fnPrimeAtRank (nZeroSourceIndex C.a.1 + 2))
          (fnPrimeAtRank (nZeroSourceIndex C.a.1 + 3)) := by
  obtain ⟨_, _, _, _, _, _, _, _, r1, r2, r3⟩ := C.primes
  rw [r1, r2, r3]
  exact ⟨rfl, rfl⟩

/-- **Enregistrement du résidu sur la cellule.** Les deux variations `ΔR(M₁, M₂)` et
`ΔR(M₂, M₃)` : côté arithmétique, côté spectral, découpage en paquet de la hauteur centrale et
complément ; les deux membres centraux sont dans le paquet, distincts ; `a` et `b` sont dans le
complément ; les variations s'enchaînent. -/
theorem remainder_record :
    remainderBetween C.M₁ C.M₂ = ((∑ n ∈ Finset.Ioc C.M₁ C.M₂, Λ n : ℝ) : ℂ) -
        (stepAt backgroundPrimitive C.M₂ - stepAt backgroundPrimitive C.M₁) ∧
      remainderBetween C.M₂ C.M₃ = ((∑ n ∈ Finset.Ioc C.M₂ C.M₃, Λ n : ℝ) : ℂ) -
        (stepAt backgroundPrimitive C.M₃ - stepAt backgroundPrimitive C.M₂) ∧
      remainderBetween C.M₁ C.M₂ = spectralBetween C.M₁ C.M₂ ∧
      remainderBetween C.M₂ C.M₃ = spectralBetween C.M₂ C.M₃ ∧
      remainderBetween C.M₁ C.M₂ =
        packetBetween (heightPacket (rZeroHeight C.e.1)) C.M₁ C.M₂ +
          packetBetween (heightPacket (rZeroHeight C.e.1))ᶜ C.M₁ C.M₂ ∧
      remainderBetween C.M₂ C.M₃ =
        packetBetween (heightPacket (rZeroHeight C.e.1)) C.M₂ C.M₃ +
          packetBetween (heightPacket (rZeroHeight C.e.1))ᶜ C.M₂ C.M₃ ∧
      memberIndex C.e ∈ heightPacket (rZeroHeight C.e.1) ∧
      memberIndex C.l ∈ heightPacket (rZeroHeight C.e.1) ∧
      memberIndex C.e ≠ memberIndex C.l ∧
      memberIndex C.a ∈ (heightPacket (rZeroHeight C.e.1))ᶜ ∧
      memberIndex C.b ∈ (heightPacket (rZeroHeight C.e.1))ᶜ ∧
      remainderBetween C.M₁ C.M₂ + remainderBetween C.M₂ C.M₃ = remainderBetween C.M₁ C.M₃ := by
  obtain ⟨p1, p2, p3, h12, h23, _⟩ := C.primes
  have t1 := p1.two_le
  have t2 := p2.two_le
  have t3 := p3.two_le
  refine ⟨remainderBetween_arithmetic h12.le, remainderBetween_arithmetic h23.le,
    remainderBetween_eq_spectral t1 t2, remainderBetween_eq_spectral t2 t3,
    remainderBetween_eq_packet_add_complement _ t1 t2,
    remainderBetween_eq_packet_add_complement _ t2 t3, memberIndex_mem_heightPacket C.e, ?_, ?_,
    ?_, ?_, remainderBetween_chain _ _ _⟩
  · have h := memberIndex_mem_heightPacket C.l
    rwa [← C.level] at h
  · intro h
    have h' := memberIndex_injective h
    have := C.radial_lt
    rw [h'] at this
    exact lt_irrefl _ this
  · intro h
    have h1 : |(zeroPoint C.a).im| = rZeroHeight C.e.1 := h
    have h2 : |(zeroPoint C.a).im| = rZeroHeight C.a.1 := memberIndex_mem_heightPacket C.a
    exact absurd (h2.symm.trans h1) (ne_of_lt C.enter)
  · intro h
    have h1 : |(zeroPoint C.b).im| = rZeroHeight C.e.1 := h
    have h2 : |(zeroPoint C.b).im| = rZeroHeight C.b.1 := memberIndex_mem_heightPacket C.b
    exact absurd (h1.symm.trans h2) (ne_of_lt (C.level ▸ C.leave))

end RegimeCell

/-- Sous RH, il n'existe aucune cellule. -/
theorem isEmpty_regimeCell_of_riemannHypothesis (hRH : RiemannHypothesis) : IsEmpty RegimeCell :=
  ⟨fun C => C.not_riemannHypothesis hRH⟩

#print axioms zeroPoint_polar
#print axioms radial_shift_eq_phase_sin
#print axioms horizontal_term_phase_lock
#print axioms horizontal_pivot_shift
#print axioms RegimeCell.not_riemannHypothesis
#print axioms RegimeCell.central_mirror
#print axioms RegimeCell.radial_l_eq
#print axioms RegimeCell.pitch_signature
#print axioms RegimeCell.contact_signature
#print axioms RegimeCell.offset_eq_translation
#print axioms RegimeCell.central_phase_lock
#print axioms RegimeCell.primes
#print axioms RegimeCell.raccords
#print axioms RegimeCell.central_cell_shift
#print axioms RegimeCell.transport_product
#print axioms RegimeCell.charge_ne_one
#print axioms RegimeCell.charge_reads_translation
#print axioms RegimeCell.arithmetic_depends_on_rank_only
#print axioms RegimeCell.remainder_record
#print axioms isEmpty_regimeCell_of_riemannHypothesis

end RHV6Fresh
