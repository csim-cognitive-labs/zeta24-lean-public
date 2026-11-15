/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.NoRegimeChange
import RHV6Fresh.Terminal.RegimeChange
import RHV6Fresh.Terminal.HeightPacket

/-!
# RHV6Fresh — énumération canonique des membres supérieurs par l'index zéro-source

Correction de l'auteur (2026-10-06, point 2) : « remplace l'énumération arbitraire par l'énumération
canonique ; construis la suite depuis l'ordre et l'index zéro-source existants ».

Tout est théorème, rien n'est choisi : l'ordre membre-sensible (`PZeroMemberPrecedes`, hauteur puis
position radiale) et l'index zéro-source (`nZeroSourceIndex`, nombre de membres supérieurs qui
précèdent) sont ceux de la base ; la suite `canonicalMember n` est l'unique membre d'index `n`.

## Ce qui est compilé

* **Infinité** : les indices de la formule explicite sont en nombre infini (sinon la formule
  explicite, l'abscisse devenue variable complexe, serait holomorphe, nulle avant `2`, donc nulle
  partout, et la somme des premiers ne l'est pas : argument déjà compilé pour deux hauteurs) ; les
  membres supérieurs sont en nombre infini (tout indice est un membre supérieur ou le conjugué d'un
  membre supérieur, aucun zéro n'ayant la hauteur zéro).
* **Surjectivité de l'index** : tout entier est l'index d'un membre supérieur (l'ensemble des index
  est infini et clos vers le bas, par le prédécesseur consécutif).
* **Suite canonique** `canonicalMember : ℕ → TrueZero` : le membre d'index `n` ; injective,
  surjective, croissante pour l'ordre des membres, consécutive de `n` à `n + 1` ; le membre d'index
  `0` n'a aucun membre supérieur en dessous (c'est l'ancre `hFirst` des théorèmes de fermeture).
* **Rangs** `canonicalZero n := canonicalMember (n - 1)` : le rang `1` a l'index `0`, le rang `n +
1`
  l'index `n`.
* **Équivalence d'indexation** `ExplicitIndex ≃ ℕ × Bool` : chaque indice est, de façon unique, le
  membre canonique de rang donné ou son conjugué ; c'est la réindexation qui regroupe un membre et
son
  conjugué dans toute somme absolument convergente.

Multiplicités : l'index compte des POINTS ; un zéro multiple est un seul membre, sa multiplicité est
le coefficient `zetaZeroMultiplicity` de l'identité arithmétique retenue
(`nontrivialZeroResidueTerm`).
La simplicité n'est supposée nulle part.
-/

namespace RHV6Fresh

open RHV3Lean Set Filter
open scoped Topology ComplexConjugate

/-! ## 1. Infinité des indices et des membres supérieurs -/

/-- **Les zéros non triviaux sont en nombre infini.** Même argument que `exists_two_heights` : si
l'index était fini, la formule explicite prolongée serait holomorphe sur un demi-plan, nulle sur
`]3/2, 2[`, donc nulle en `5/2`, où la somme lissée des premiers ne l'est pas. -/
theorem explicitIndex_infinite : Infinite ExplicitIndex := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
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

/-- Tout indice de la formule explicite est un vrai zéro de la bande ouverte. -/
noncomputable def indexMember (σ : ExplicitIndex) : TNonTrivialZetaZero :=
  ⟨(σ : ℂ), σ.property.1, (isNontrivialZetaZero_re_mem_Ioo σ.property).1,
    (isNontrivialZetaZero_re_mem_Ioo σ.property).2⟩

/-- L'indice conjugué d'un membre supérieur. -/
noncomputable def conjIndex (z : TrueZero) : ExplicitIndex :=
  ⟨conj (zeroPoint z), (isNontrivialZetaZero_conj_iff _).mpr (zeroPoint_isNontrivial z)⟩

/-- Un indice est un membre supérieur, ou le conjugué d'un membre supérieur. -/
noncomputable def upperOrConj : TrueZero ⊕ TrueZero → ExplicitIndex
  | Sum.inl z => memberIndex z
  | Sum.inr z => conjIndex z

/-- **Aucun indice n'échappe aux membres supérieurs et à leurs conjugués** : aucun zéro n'a la
hauteur zéro (`thm_zeroHeight_ne_zero`). -/
theorem upperOrConj_surjective : Function.Surjective upperOrConj := by
  intro σ
  have hne : rZeroHeight (indexMember σ) ≠ 0 := thm_zeroHeight_ne_zero _
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hc : 0 < rZeroHeight (zConjugateZero (indexMember σ)) := by
      rw [thm_conjugateZero_height]; linarith
    refine ⟨Sum.inr ⟨zConjugateZero (indexMember σ), hc⟩, Subtype.ext ?_⟩
    change conj (conj (σ : ℂ)) = (σ : ℂ)
    exact Complex.conj_conj _
  · exact ⟨Sum.inl ⟨indexMember σ, hpos⟩, Subtype.ext rfl⟩

/-- **Les membres supérieurs sont en nombre infini.** -/
theorem trueZero_infinite : Infinite TrueZero := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  have : Finite ExplicitIndex := Finite.of_surjective _ upperOrConj_surjective
  have := explicitIndex_infinite
  exact not_finite ExplicitIndex

/-! ## 2. L'index zéro-source atteint tout entier -/

/-- L'index est nul exactement pour le membre que ne précède aucun membre supérieur. -/
theorem index_zero_iff (z : TNonTrivialZetaZero) :
    nZeroSourceIndex z = 0 ↔ sUpperZerosBelow z = ∅ := by
  unfold nZeroSourceIndex
  rw [Finset.card_eq_zero, Set.Finite.toFinset_eq_empty]

/-- Les index ne sont pas bornés. -/
theorem exists_index_ge (n : ℕ) : ∃ z : TrueZero, n ≤ nZeroSourceIndex z.1 := by
  have := trueZero_infinite
  have hinj : Function.Injective (fun z : TrueZero => nZeroSourceIndex z.1) :=
    fun a b h => thm_zeroSourceIndex_injective h
  have hinf := Set.infinite_range_of_injective hinj
  obtain ⟨k, ⟨z, rfl⟩, hk⟩ := not_bddAbove_iff.mp hinf.not_bddAbove n
  exact ⟨z, hk.le⟩

/-- **Tout entier est l'index d'un membre supérieur** : l'ensemble des index est infini et clos vers
le bas (le prédécesseur consécutif a l'index précédent). -/
theorem exists_index_eq (n : ℕ) : ∃ z : TrueZero, nZeroSourceIndex z.1 = n := by
  obtain ⟨z, hz⟩ := exists_index_ge n
  obtain ⟨d, hd⟩ : ∃ d, nZeroSourceIndex z.1 = n + d := ⟨_, (Nat.add_sub_cancel' hz).symm⟩
  clear hz
  induction d generalizing z with
  | zero => exact ⟨z, by simpa using hd⟩
  | succ d ih =>
    have hne : (sUpperZerosBelow z.1).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty, ← index_zero_iff] at hemp
      omega
    obtain ⟨w, hw, hcons, _⟩ := exists_consecutive_predecessor z.1 hne
    have hidx := thm_zeroSourceIndex_succ_of_consecutive hw hcons
    exact ih ⟨w, hw⟩ (show nZeroSourceIndex w = n + d by rw [hidx] at hd; omega)

/-! ## 3. La suite canonique -/

/-- **Le membre canonique d'index `n`** : l'unique membre supérieur que précèdent exactement `n`
membres supérieurs. -/
noncomputable def canonicalMember (n : ℕ) : TrueZero := Classical.choose (exists_index_eq n)

theorem canonicalMember_index (n : ℕ) : nZeroSourceIndex (canonicalMember n).1 = n :=
  Classical.choose_spec (exists_index_eq n)

/-- **Chaque membre supérieur apparaît**, à son index. -/
theorem canonicalMember_eq_of_index (w : TrueZero) :
    canonicalMember (nZeroSourceIndex w.1) = w :=
  thm_zeroSourceIndex_injective (canonicalMember_index _)

theorem canonicalMember_surjective : Function.Surjective canonicalMember :=
  fun w => ⟨_, canonicalMember_eq_of_index w⟩

/-- **Aucun membre distinct n'est répété.** -/
theorem canonicalMember_injective : Function.Injective canonicalMember := by
  intro m n h
  have := congrArg (fun z : TrueZero => nZeroSourceIndex z.1) h
  simpa [canonicalMember_index] using this

/-- **L'ordre des membres est respecté** : précéder, c'est avoir le plus petit index. -/
theorem canonicalMember_precedes_iff (m n : ℕ) :
    PZeroMemberPrecedes (canonicalMember m).1 (canonicalMember n).1 ↔ m < n := by
  constructor
  · intro h
    have := thm_zeroSourceIndex_strictMono (canonicalMember m).2 h
    simpa [canonicalMember_index] using this
  · intro hmn
    have hne : canonicalMember m ≠ canonicalMember n :=
      fun h => absurd (canonicalMember_injective h) hmn.ne
    rcases thm_distinctZeroMembers_comparable (fun h => hne (Subtype.ext h)) with h | h
    · exact h
    · have := thm_zeroSourceIndex_strictMono (canonicalMember n).2 h
      simp [canonicalMember_index] at this
      omega

/-- La hauteur ne décroît pas le long de la suite canonique. -/
theorem canonicalMember_height_mono {m n : ℕ} (h : m ≤ n) :
    rZeroHeight (canonicalMember m).1 ≤ rZeroHeight (canonicalMember n).1 := by
  rcases h.lt_or_eq with hlt | rfl
  · have := (canonicalMember_precedes_iff m n).mpr hlt
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex] at this
    rcases this with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
  · exact le_rfl

/-- Un membre qui suit un membre supérieur est supérieur. -/
theorem height_pos_of_precedes' {w u : TNonTrivialZetaZero} (hw : 0 < rZeroHeight w)
    (h : PZeroMemberPrecedes w u) : 0 < rZeroHeight u := by
  rw [thm_zeroMemberPrecedes_iff_height_radial_lex] at h
  rcases h with h | ⟨h, _⟩
  · exact lt_trans hw h
  · exact h ▸ hw

/-- **Deux membres canoniques successifs sont consécutifs** : rien ne s'intercale. -/
theorem canonicalMember_consecutive (n : ℕ) :
    PZeroMembersConsecutive (canonicalMember n).1 (canonicalMember (n + 1)).1 := by
  refine ⟨(canonicalMember_precedes_iff n (n + 1)).mpr (Nat.lt_succ_self n), ?_⟩
  rintro ⟨u, hnu, hun⟩
  have hu : 0 < rZeroHeight u := height_pos_of_precedes' (canonicalMember n).2 hnu
  have h1 := thm_zeroSourceIndex_strictMono (canonicalMember n).2 hnu
  have h2 := thm_zeroSourceIndex_strictMono hu hun
  rw [canonicalMember_index] at h1 h2
  omega

/-- **Le membre canonique d'index `0` n'a aucun membre supérieur en dessous** : c'est l'ancre
`hFirst` des théorèmes de fermeture (`first_field_iff_riemannHypothesis`,
`individual_domination_iff_riemannHypothesis`). -/
theorem canonicalMember_zero_bottom : sUpperZerosBelow (canonicalMember 0).1 = ∅ :=
  (index_zero_iff _).mp (canonicalMember_index 0)

/-- Le membre d'index `0` précède tout autre membre supérieur. -/
theorem canonicalMember_zero_precedes (w : TrueZero) (hw : w ≠ canonicalMember 0) :
    PZeroMemberPrecedes (canonicalMember 0).1 w.1 := by
  obtain ⟨n, rfl⟩ := canonicalMember_surjective w
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => hw (by rw [h])
  exact (canonicalMember_precedes_iff 0 n).mpr hn

/-! ## 4. Les rangs : le rang `1` a l'index `0`, le rang `n + 1` l'index `n` -/

/-- **Le membre canonique de rang `n`** (`n ≥ 1`) : le membre d'index `n - 1`. -/
noncomputable def canonicalZero (n : ℕ) : TrueZero := canonicalMember (n - 1)

theorem canonicalZero_one : canonicalZero 1 = canonicalMember 0 := rfl

theorem canonicalZero_succ (n : ℕ) : canonicalZero (n + 1) = canonicalMember n := rfl

/-- Le membre de rang un possède l'index zéro-source zéro. -/
theorem canonicalZero_one_index : nZeroSourceIndex (canonicalZero 1).1 = 0 :=
  canonicalMember_index 0

/-- Le membre de rang `n + 1` possède l'index zéro-source `n`. -/
theorem canonicalZero_succ_index (n : ℕ) : nZeroSourceIndex (canonicalZero (n + 1)).1 = n :=
  canonicalMember_index n

/-- Chaque vrai membre supérieur apparaît à un rang `≥ 1`. -/
theorem canonicalZero_surjective (w : TrueZero) : ∃ n : ℕ, 1 ≤ n ∧ canonicalZero n = w :=
  ⟨nZeroSourceIndex w.1 + 1, Nat.le_add_left _ _, canonicalMember_eq_of_index w⟩

/-- Aucun membre distinct n'est répété aux rangs `≥ 1`. -/
theorem canonicalZero_injOn {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : canonicalZero m = canonicalZero n) : m = n := by
  have := canonicalMember_injective h
  omega

/-- L'ordre des membres est respecté aux rangs `≥ 1`. -/
theorem canonicalZero_precedes_iff {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    PZeroMemberPrecedes (canonicalZero m).1 (canonicalZero n).1 ↔ m < n := by
  unfold canonicalZero
  rw [canonicalMember_precedes_iff]
  omega

/-- Les rangs successifs `≥ 1` sont des membres consécutifs. -/
theorem canonicalZero_consecutive {n : ℕ} (hn : 1 ≤ n) :
    PZeroMembersConsecutive (canonicalZero n).1 (canonicalZero (n + 1)).1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact canonicalMember_consecutive k

/-- **Le premier membre canonique est l'ancre des théorèmes de fermeture.** -/
theorem canonicalZero_one_bottom : sUpperZerosBelow (canonicalZero 1).1 = ∅ :=
  canonicalMember_zero_bottom

/-! ## 5. Équivalence d'indexation : chaque indice est un membre canonique ou son conjugué -/

/-- Le membre supérieur porté par un indice : lui-même ou son conjugué. -/
noncomputable def indexUpper (σ : ExplicitIndex) : TrueZero :=
  ⟨zUpperRepresentativeMember (indexMember σ), thm_upperRepresentativeMember_heightPositive _⟩

theorem indexUpper_of_pos {σ : ExplicitIndex} (h : 0 < (σ : ℂ).im) :
    (indexUpper σ).1 = indexMember σ := by
  have h' : 0 < rZeroHeight (indexMember σ) := h
  unfold indexUpper zUpperRepresentativeMember
  simp only
  rw [if_pos h']

theorem indexUpper_of_neg {σ : ExplicitIndex} (h : (σ : ℂ).im < 0) :
    (indexUpper σ).1 = zConjugateZero (indexMember σ) := by
  have h' : ¬ 0 < rZeroHeight (indexMember σ) := not_lt.mpr (show (σ : ℂ).im ≤ 0 from h.le)
  unfold indexUpper zUpperRepresentativeMember
  simp only
  rw [if_neg h']

theorem memberIndex_canonical_of_pos {σ : ExplicitIndex} (h : 0 < (σ : ℂ).im) :
    memberIndex (canonicalMember (nZeroSourceIndex (indexUpper σ).1)) = σ := by
  rw [canonicalMember_eq_of_index]
  apply Subtype.ext
  change (indexUpper σ).1.1 = (σ : ℂ)
  rw [indexUpper_of_pos h]
  rfl

theorem conjIndex_canonical_of_neg {σ : ExplicitIndex} (h : (σ : ℂ).im < 0) :
    conjIndex (canonicalMember (nZeroSourceIndex (indexUpper σ).1)) = σ := by
  rw [canonicalMember_eq_of_index]
  apply Subtype.ext
  change conj (indexUpper σ).1.1 = (σ : ℂ)
  rw [indexUpper_of_neg h]
  exact Complex.conj_conj _

/-- **Équivalence d'indexation** : `(n, true)` est le membre canonique d'index `n`, `(n, false)` son
conjugué. -/
noncomputable def indexEquiv : ExplicitIndex ≃ ℕ × Bool where
  toFun σ := (nZeroSourceIndex (indexUpper σ).1, decide (0 < (σ : ℂ).im))
  invFun p := if p.2 then memberIndex (canonicalMember p.1) else conjIndex (canonicalMember p.1)
  left_inv σ := by
    have hne : rZeroHeight (indexMember σ) ≠ 0 := thm_zeroHeight_ne_zero _
    change (σ : ℂ).im ≠ 0 at hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · simp only [not_lt.mpr hneg.le, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact conjIndex_canonical_of_neg hneg
    · simp only [hpos, decide_true, ↓reduceIte]
      exact memberIndex_canonical_of_pos hpos
  right_inv p := by
    obtain ⟨n, b⟩ := p
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hneg : ((conjIndex (canonicalMember n) : ExplicitIndex) : ℂ).im < 0 := by
        change (conj (zeroPoint (canonicalMember n))).im < 0
        rw [Complex.conj_im]
        exact neg_neg_of_pos (canonicalMember n).2
      have hup : (indexUpper (conjIndex (canonicalMember n))).1 = (canonicalMember n).1 := by
        rw [indexUpper_of_neg hneg]
        apply Subtype.ext
        exact Complex.conj_conj _
      simp only [Prod.mk.injEq, decide_eq_false_iff_not, not_lt]
      exact ⟨by rw [hup, canonicalMember_index], hneg.le⟩
    · simp only [↓reduceIte]
      have hpos : ((memberIndex (canonicalMember n) : ExplicitIndex) : ℂ).im > 0 :=
        (canonicalMember n).2
      have hup : (indexUpper (memberIndex (canonicalMember n))).1 = (canonicalMember n).1 := by
        rw [indexUpper_of_pos hpos]; rfl
      simp only [Prod.mk.injEq, decide_eq_true_eq]
      exact ⟨by rw [hup, canonicalMember_index], hpos⟩

theorem indexEquiv_symm_true (n : ℕ) :
    indexEquiv.symm (n, true) = memberIndex (canonicalMember n) :=
  rfl

theorem indexEquiv_symm_false (n : ℕ) :
    indexEquiv.symm (n, false) = conjIndex (canonicalMember n) := rfl

#print axioms explicitIndex_infinite
#print axioms trueZero_infinite
#print axioms exists_index_eq
#print axioms canonicalMember_index
#print axioms canonicalMember_eq_of_index
#print axioms canonicalMember_injective
#print axioms canonicalMember_precedes_iff
#print axioms canonicalMember_consecutive
#print axioms canonicalZero_one_bottom
#print axioms indexEquiv

end RHV6Fresh
