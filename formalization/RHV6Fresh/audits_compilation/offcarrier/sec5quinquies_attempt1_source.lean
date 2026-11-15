/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-! ## 5quinquies. Signature intégrée de la paire OFF/miroir sur trois écarts premiers consécutifs (§19.12, 2026-10-30)

Changement d'objet intermédiaire (relecture du 2026-10-30) : la continuation forcée (§6) reste la caractérisation
terminale, mais n'est plus l'objectif de recherche. L'objet étudié est la **signature exacte de la paire** `(β + iT,
(1 − β) + iT)` sur les trois écarts `[p_{n−1}, p_n]`, `[p_n, p_{n+1}]`, `[p_{n+1}, p_{n+2}]`, dans le cas (a).

Compilé ici, exact et local, sans moyenne ni borne :
* **A. Identité hyperbolique de la paire** (canal de comptage, `countingGapTerm_mirror_pair` réutilisé, aucune nouvelle
  définition de reconstruction) : la paire moins deux signaux de ligne de même fréquence est l'intégrale d'un facteur
  d'amplitude `2(cosh(dt) − 1) > 0` fois le signal de ligne ; forme réelle de l'auteur
  `−4 ∫ e^{t/2}(cosh(dt) − 1) cos(Tt)/t dt`. Le facteur d'amplitude est strictement positif, le cosinus change de signe :
  la différence intégrée sur un écart donné n'est PAS automatiquement non nulle (consigné, pas affirmé).
* **B. Transport sur les trois écarts** : quatre premiers consécutifs strictement croissants ; télescopage exact de la
  signature de la paire ; dans le cas (a), profil des trois écarts : montée, gel, montée, avec les trois événements
  canoniques `p_n = Occ(z)`, `p_{n+1} = Occ(z*)`, `p_{n+2} = Occ(membre n+2)`.
* **D. Raccord au canal arithmétique compilé** (choix explicite : transport vers le canal LISSÉ, seul canal dont la
  reconstruction est compilée ; la reconstruction du canal de COMPTAGE n'est PAS formalisée, audit E301) : pour tout
  écart, la cible lissée se découpe exactement en « paquet de la fréquence `T` » plus « autres fréquences »
  (`target_split`) ; dans le cas (a), le paquet est exactement quatre indices (`z`, `z*` et leurs conjugués) et sa
  contribution à chaque écart est la paire lissée plus la paire conjuguée (`target_split_of_mirror`).

Ce que cela ne dit pas : l'identité `target_split_of_mirror` vaut pour toute famille de zéros ; la part « autres
fréquences » n'est pas contrainte ici. L'incompatibilité de la signature avec les trois raccords est la question
ouverte de §19.12, pas un théorème. -/

/-- Le point de ligne à la fréquence du zéro OFF : `1/2 + iT`. -/
noncomputable def linePoint : ℂ := (1 / 2 : ℂ) + (rZeroHeight C.zero.1 : ℂ) * Complex.I

theorem linePoint_re : C.linePoint.re = 1 / 2 := by simp [linePoint]

theorem linePoint_im : C.linePoint.im = rZeroHeight C.zero.1 := by simp [linePoint]

/-- `ρ = (1/2 + iT) − d`, `d = 1/2 − β`. -/
theorem zeroPoint_eq_line_sub_shift : zeroPoint C.zero = C.linePoint - (C.radialShift : ℂ) := by
  apply Complex.ext
  · rw [Complex.sub_re, Complex.ofReal_re, C.linePoint_re, zeroPoint_re]
    exact C.zero_radial_eq
  · rw [Complex.sub_im, Complex.ofReal_im, C.linePoint_im, zeroPoint_im, sub_zero]

/-- `ρ* = (1/2 + iT) + d`. -/
theorem mirrorPoint_eq_line_add_shift :
    zeroPoint (mirrorMember C.zero) = C.linePoint + (C.radialShift : ℂ) := by
  apply Complex.ext
  · rw [Complex.add_re, Complex.ofReal_re, C.linePoint_re, zeroPoint_re]
    exact C.mirror_radial_eq
  · rw [Complex.add_im, Complex.ofReal_im, C.linePoint_im, zeroPoint_im, add_zero]
    exact mirrorMember_ordinate C.zero

theorem gap_b_pos (I : PrimeGapInterval) : 0 < I.b := lt_trans I.a_pos I.a_lt_b

/-! ### A. La signature intégrée de la paire (canal de comptage) -/

/-- Contribution de la paire (zéro OFF, miroir) à l'écart `I`, canal de comptage : `C_ρ(I) + C_{ρ*}(I)`. -/
noncomputable def pairCounting (I : PrimeGapInterval) : ℂ :=
  countingGapTerm (zeroPoint C.zero) I.a I.b + countingGapTerm (zeroPoint (mirrorMember C.zero)) I.a I.b

/-- Contribution d'un signal de ligne de même fréquence à l'écart `I`. -/
noncomputable def lineCounting (I : PrimeGapInterval) : ℂ := countingGapTerm C.linePoint I.a I.b

/-- **Identité hyperbolique de la paire** : `P_ρ(I) − 2 C_{1/2+iT}(I) = ∫_a^b 2(cosh(dt) − 1) e^{(1/2+iT)t}/t dt`.
Même fréquence (même facteur oscillant), facteur d'amplitude `2(cosh(dt) − 1) > 0` pour `t > 0`, bornes exactes de
l'écart premier. -/
theorem pair_hyperbolic_signature (I : PrimeGapInterval) :
    C.pairCounting I - 2 * C.lineCounting I =
      ∫ t in I.a..I.b, 2 * (Complex.cosh ((C.radialShift : ℂ) * t) - 1) * Complex.exp (C.linePoint * t) / t := by
  unfold pairCounting lineCounting
  rw [C.zeroPoint_eq_line_sub_shift, C.mirrorPoint_eq_line_add_shift]
  exact countingGapTerm_mirror_pair C.linePoint C.radialShift I.a_pos (gap_b_pos I)

/-- Contribution signée réelle de la paire (chaque membre regroupé avec son conjugué). -/
noncomputable def pairReal (I : PrimeGapInterval) : ℝ :=
  zeroLocalContribution (zeroPoint C.zero) I + zeroLocalContribution (zeroPoint (mirrorMember C.zero)) I

/-- Contribution signée réelle d'un signal de ligne de même fréquence. -/
noncomputable def lineReal (I : PrimeGapInterval) : ℝ := zeroLocalContribution C.linePoint I

/-- Forme réelle : la différence `D_OFF − D_ON` est `−2` fois la partie réelle de l'intégrale hyperbolique. -/
theorem pair_real_signature (I : PrimeGapInterval) :
    C.pairReal I - 2 * C.lineReal I =
      -2 * (∫ t in I.a..I.b,
        2 * (Complex.cosh ((C.radialShift : ℂ) * t) - 1) * Complex.exp (C.linePoint * t) / t).re := by
  rw [← C.pair_hyperbolic_signature I]
  unfold pairReal lineReal zeroLocalContribution pairCounting lineCounting
  have h2 : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp
  rw [Complex.sub_re, Complex.add_re, h2]
  ring

theorem realCountingDensity_intervalIntegrable (ρ : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (realCountingDensity ρ) volume a b := by
  have h := countingDensity_intervalIntegrable ρ ha hb
  have h2 : IntervalIntegrable (fun t => (countingDensity ρ t).re) volume a b := ⟨h.1.re, h.2.re⟩
  have h3 := h2.const_mul (-2)
  have hfun : realCountingDensity ρ = fun t => -2 * (countingDensity ρ t).re :=
    funext (realCountingDensity_eq ρ)
  rw [hfun]
  exact h3

/-- **Formule réelle de l'auteur** : `D_OFF(a, b) − D_ON(a, b) = −4 ∫_a^b e^{t/2} (cosh(dt) − 1) cos(Tt)/t dt`. Fréquence
`T` commune, amplitude `e^{t/2}(cosh(dt) − 1) > 0` pour `t > 0`, bornes exactes. Le cosinus change de signe : le signe de
la différence sur un écart donné n'est pas décidé par cette identité. -/
theorem pair_real_signature_explicit (I : PrimeGapInterval) :
    C.pairReal I - 2 * C.lineReal I =
      ∫ t in I.a..I.b, -4 * (Real.exp (t / 2) * (Real.cosh (C.radialShift * t) - 1) *
        Real.cos (rZeroHeight C.zero.1 * t) / t) := by
  have ha := I.a_pos
  have hb := gap_b_pos I
  unfold pairReal lineReal zeroLocalContribution
  rw [zeroLocalContribution_eq_real_integral _ ha hb, zeroLocalContribution_eq_real_integral _ ha hb,
    zeroLocalContribution_eq_real_integral _ ha hb, C.zeroPoint_eq_line_sub_shift,
    C.mirrorPoint_eq_line_add_shift]
  have hI1 := realCountingDensity_intervalIntegrable (C.linePoint - (C.radialShift : ℂ)) ha hb
  have hI2 := realCountingDensity_intervalIntegrable (C.linePoint + (C.radialShift : ℂ)) ha hb
  have hI3 := realCountingDensity_intervalIntegrable C.linePoint ha hb
  rw [← intervalIntegral.integral_const_mul, ← integral_add hI1 hI2,
    ← integral_sub (hI1.add hI2) (hI3.const_mul 2)]
  congr 1
  funext t
  have hre1 : (C.linePoint - (C.radialShift : ℂ)).re = 1 / 2 - C.radialShift := by
    rw [Complex.sub_re, Complex.ofReal_re, C.linePoint_re]
  have hre2 : (C.linePoint + (C.radialShift : ℂ)).re = 1 / 2 + C.radialShift := by
    rw [Complex.add_re, Complex.ofReal_re, C.linePoint_re]
  have him1 : (C.linePoint - (C.radialShift : ℂ)).im = rZeroHeight C.zero.1 := by
    rw [Complex.sub_im, Complex.ofReal_im, C.linePoint_im, sub_zero]
  have him2 : (C.linePoint + (C.radialShift : ℂ)).im = rZeroHeight C.zero.1 := by
    rw [Complex.add_im, Complex.ofReal_im, C.linePoint_im, add_zero]
  simp only [realCountingDensity, hre1, hre2, him1, him2, C.linePoint_re, C.linePoint_im]
  have e1 : Real.exp ((1 / 2 - C.radialShift) * t) = Real.exp (t / 2) * Real.exp (-(C.radialShift * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp ((1 / 2 + C.radialShift) * t) = Real.exp (t / 2) * Real.exp (C.radialShift * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (1 / 2 * t) = Real.exp (t / 2) := by congr 1; ring
  rw [e1, e2, e3, Real.cosh_eq]
  ring

/-! ### B. Les trois écarts consécutifs et les quatre premiers -/

/-- L'écart suivant `[p_{n+1}, p_{n+2}]`. -/
def nextGap : PrimeGapInterval := ⟨C.n + 1⟩

theorem previousGap_upper_eq_gap_lower : C.previousGap.upper = C.gap.lower := by
  have := C.one_le_n
  show fnPrimeAtRank (C.n - 1 + 1) = fnPrimeAtRank C.n
  congr 1
  omega

theorem gap_upper_eq_nextGap_lower : C.gap.upper = C.nextGap.lower := rfl

theorem previousGap_b_eq_gap_a : C.previousGap.b = C.gap.a := by
  unfold PrimeGapInterval.b PrimeGapInterval.a
  rw [C.previousGap_upper_eq_gap_lower]

theorem gap_b_eq_nextGap_a : C.gap.b = C.nextGap.a := rfl

/-- **Quatre premiers consécutifs strictement croissants** : `p_{n−1} < p_n < p_{n+1} < p_{n+2}`. -/
theorem four_primes :
    fnPrimeAtRank (C.n - 1) < fnPrimeAtRank C.n ∧ fnPrimeAtRank C.n < fnPrimeAtRank (C.n + 1) ∧
      fnPrimeAtRank (C.n + 1) < fnPrimeAtRank (C.n + 1 + 1) := by
  have := C.one_le_n
  exact ⟨thm_primeAtRank_strictMono (by omega), thm_primeAtRank_strictMono (by omega),
    thm_primeAtRank_strictMono (by omega)⟩

/-- **Télescopage exact** de la signature de la paire sur les trois écarts : la somme des trois contributions est la
contribution à la fenêtre `[p_{n−1}, p_{n+2}]`. Cohérence de la formalisation, pas une contradiction. -/
theorem pairCounting_three_gaps :
    C.pairCounting C.previousGap + C.pairCounting C.gap + C.pairCounting C.nextGap =
      countingGapTerm (zeroPoint C.zero) C.previousGap.a C.nextGap.b +
        countingGapTerm (zeroPoint (mirrorMember C.zero)) C.previousGap.a C.nextGap.b := by
  have h1 : ∀ ρ : ℂ, countingGapTerm ρ C.previousGap.a C.previousGap.b +
      countingGapTerm ρ C.gap.a C.gap.b + countingGapTerm ρ C.nextGap.a C.nextGap.b =
        countingGapTerm ρ C.previousGap.a C.nextGap.b := by
    intro ρ
    rw [C.previousGap_b_eq_gap_a, C.gap_b_eq_nextGap_a,
      countingGapTerm_add ρ C.previousGap.a_pos C.gap.a_pos C.nextGap.a_pos,
      countingGapTerm_add ρ C.previousGap.a_pos C.nextGap.a_pos (gap_b_pos C.nextGap)]
  unfold pairCounting
  rw [← h1 (zeroPoint C.zero), ← h1 (zeroPoint (mirrorMember C.zero))]
  ring

/-- L'occurrence du membre de rang `n + 2` est le point de rencontre de l'écart suivant, `p_{n+2}`. -/
theorem postPassage_later_occurrence :
    (occurrence ⟨C.postPassage.zLaterMember, C.postPassage_later_pos⟩ : ℝ) = meetingPoint C.nextGap := by
  show (occurrence (canonicalMember (C.n + 1 + 1)) : ℝ) = _
  rw [occurrence_eq_primeAtRank, canonicalMember_index, meetingPoint_eq_upper]
  rfl

/-- Le point de rencontre de l'écart précédent est l'occurrence du zéro OFF, `p_n`. -/
theorem previousGap_meeting_eq_zero_occurrence :
    meetingPoint C.previousGap = (occurrence C.zero : ℝ) := by
  rw [C.previous_liaison, C.arrivalRaccord_M, C.zero_occurrence]

/-- **Profil des trois écarts dans le cas (a)** : montée (l'écart précédent apporte `T`), gel (l'écart du zéro OFF est
reconstitué à la fréquence `T`), montée (l'écart suivant apporte une fréquence strictement supérieure) ; et les trois
événements premiers canoniques portés : `p_n = Occ(z)`, `p_{n+1} = Occ(z*)`, `p_{n+2} = Occ(membre n+2)`. -/
theorem three_gap_profile_of_mirror (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    VerticalPassage C.arrival ∧ HorizontalPassage C.outgoing ∧ VerticalPassage C.postPassage ∧
      meetingPoint C.previousGap = (occurrence C.zero : ℝ) ∧
      meetingPoint C.gap = (occurrence (mirrorMember C.zero) : ℝ) ∧
      meetingPoint C.nextGap = (occurrence ⟨C.postPassage.zLaterMember, C.postPassage_later_pos⟩ : ℝ) :=
  ⟨C.arrival_vertical, C.outgoing_horizontal, C.post_mirror_vertical h,
    C.previousGap_meeting_eq_zero_occurrence, (C.mirror_occurrence_eq_meeting h).symm,
    C.postPassage_later_occurrence.symm⟩

/-! ### D. Raccord au canal arithmétique compilé (canal lissé) -/

/-- Identité hyperbolique pour le terme lissé (sans le facteur `1/t`). -/
theorem gapTerm_mirror_pair (ρ₀ : ℂ) (d : ℝ) (a b : ℝ) :
    gapTerm (ρ₀ - d) a b + gapTerm (ρ₀ + d) a b - 2 * gapTerm ρ₀ a b =
      ∫ t in a..b, 2 * (Complex.cosh (d * t) - 1) * Complex.exp (ρ₀ * t) := by
  unfold gapTerm
  have hc : ∀ σ : ℂ, IntervalIntegrable (fun t : ℝ => Complex.exp (σ * t)) volume a b :=
    fun σ => (by fun_prop : Continuous fun t : ℝ => Complex.exp (σ * t)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_const_mul, ← integral_add (hc _) (hc _),
    ← integral_sub ((hc _).add (hc _)) ((hc ρ₀).const_mul 2)]
  congr 1
  funext t
  exact mirror_pair_density ρ₀ d t

/-- Signature hyperbolique de la paire dans le canal lissé (termes non pondérés). -/
theorem pair_gapTerm_signature (I : PrimeGapInterval) :
    gapTerm (zeroPoint C.zero) I.a I.b + gapTerm (zeroPoint (mirrorMember C.zero)) I.a I.b -
        2 * gapTerm C.linePoint I.a I.b =
      ∫ t in I.a..I.b, 2 * (Complex.cosh ((C.radialShift : ℂ) * t) - 1) * Complex.exp (C.linePoint * t) := by
  rw [C.zeroPoint_eq_line_sub_shift, C.mirrorPoint_eq_line_add_shift]
  exact gapTerm_mirror_pair C.linePoint C.radialShift I.a I.b

/-- Le paquet de la fréquence du zéro OFF : tous les indices de hauteur absolue `T`. -/
def packet : Set ExplicitIndex := heightPacket (rZeroHeight C.zero.1)

/-- Contribution du paquet de fréquence `T` à l'écart `I` (canal lissé). -/
noncomputable def packetContribution (I : PrimeGapInterval) : ℂ :=
  channelOn C.packet I.upper - channelOn C.packet I.lower

/-- Contribution des autres fréquences à l'écart `I` (canal lissé). -/
noncomputable def otherFrequenciesContribution (I : PrimeGapInterval) : ℂ :=
  channelOn C.packetᶜ I.upper - channelOn C.packetᶜ I.lower

/-- **Découpage exact de la cible lissée** : pour tout écart, l'incrément du reste lissé des premiers est la part de la
fréquence `T` plus la part des autres fréquences. Identité, valable pour toute famille de zéros. -/
theorem target_split (I : PrimeGapInterval) :
    localArithmeticTarget I = C.packetContribution I + C.otherFrequenciesContribution I := by
  unfold localArithmeticTarget packetContribution otherFrequenciesContribution
  rw [smoothedRemainder_eq_tsum_residueTerm I.one_lt_upper,
    smoothedRemainder_eq_tsum_residueTerm I.one_lt_lower,
    channel_eq_packet_add_complement C.packet I.one_lt_upper,
    channel_eq_packet_add_complement C.packet I.one_lt_lower]
  ring

theorem zero_off : PIsOffCriticalLine C.zero.1 := by
  unfold PIsOffCriticalLine
  exact ne_of_lt C.zero_low

theorem memberIndex_ne_mirrorIndex : memberIndex C.zero ≠ memberIndex (mirrorMember C.zero) :=
  (off_packet_mirror_distinct C.zero_off).symm

theorem conjIndex_ne_memberIndex (w w' : TrueZero) : conjIndex w ≠ memberIndex w' := by
  intro h
  have him := congrArg (fun σ : ExplicitIndex => (σ : ℂ).im) h
  simp only [conjIndex, memberIndex, Complex.conj_im, zeroPoint_im] at him
  linarith [w.2, w'.2]

theorem conjIndex_ne_mirrorConjIndex : conjIndex C.zero ≠ conjIndex (mirrorMember C.zero) := by
  intro h
  apply C.memberIndex_ne_mirrorIndex
  have h1 : conj (zeroPoint C.zero) = conj (zeroPoint (mirrorMember C.zero)) :=
    congrArg (fun σ : ExplicitIndex => (σ : ℂ)) h
  have h2 : zeroPoint C.zero = zeroPoint (mirrorMember C.zero) := by
    have := congrArg conj h1
    rwa [Complex.conj_conj, Complex.conj_conj] at this
  exact Subtype.ext h2

theorem conjIndex_mem_packet (w : TrueZero) (hw : rZeroHeight w.1 = rZeroHeight C.zero.1) :
    conjIndex w ∈ C.packet := by
  show |(conj (zeroPoint w)).im| = rZeroHeight C.zero.1
  rw [Complex.conj_im, abs_neg, zeroPoint_im, abs_of_pos w.2, hw]

/-- Dans le cas (a), tout indice du paquet est l'un des quatre : `z`, `z*`, ou leurs conjugués. -/
theorem packet_mem_cases (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) (σ : ExplicitIndex)
    (hσ : σ ∈ C.packet) :
    σ = memberIndex C.zero ∨ σ = memberIndex (mirrorMember C.zero) ∨
      σ = conjIndex C.zero ∨ σ = conjIndex (mirrorMember C.zero) := by
  obtain ⟨w, rfl⟩ := upperOrConj_surjective σ
  cases w with
  | inl w =>
    have hw : rZeroHeight w.1 = rZeroHeight C.zero.1 := by
      have h0 : |(zeroPoint w).im| = rZeroHeight C.zero.1 := hσ
      rwa [zeroPoint_im, abs_of_pos w.2] at h0
    rcases C.fiber_eq_pair_of_mirror h w hw with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  | inr w =>
    have hw : rZeroHeight w.1 = rZeroHeight C.zero.1 := by
      have h0 : |(conj (zeroPoint w)).im| = rZeroHeight C.zero.1 := hσ
      rwa [Complex.conj_im, abs_neg, zeroPoint_im, abs_of_pos w.2] at h0
    rcases C.fiber_eq_pair_of_mirror h w hw with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- **Dans le cas (a), le paquet de la fréquence `T` est exactement quatre indices.** -/
theorem packet_eq_four_of_mirror (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    C.packet = {memberIndex C.zero, memberIndex (mirrorMember C.zero),
      conjIndex C.zero, conjIndex (mirrorMember C.zero)} := by
  ext σ
  constructor
  · intro hσ
    rcases C.packet_mem_cases h σ hσ with rfl | rfl | rfl | rfl <;> simp
  · intro hσ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl | rfl | rfl
    · exact memberIndex_mem_heightPacket C.zero
    · exact mirrorMember_mem_heightPacket C.zero
    · exact C.conjIndex_mem_packet C.zero rfl
    · exact C.conjIndex_mem_packet (mirrorMember C.zero) (mirrorMember_ordinate C.zero)

theorem four_sdiff_two {α : Type*} {a b c d : α} (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    ({a, b, c, d} : Set α) \ {a, b} = {c, d} := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    push_neg at h2
    rcases h1 with rfl | rfl | rfl | rfl
    · exact absurd rfl h2.1
    · exact absurd rfl h2.2
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hca, hcb⟩
    · exact ⟨Or.inr (Or.inr (Or.inr rfl)), hda, hdb⟩

theorem channelOn_empty (x : ℝ) : channelOn (∅ : Set ExplicitIndex) x = 0 := by
  unfold channelOn
  simp

/-- **Le canal du paquet, explicité dans le cas (a)** : exactement les quatre termes. -/
theorem packet_channel_four_of_mirror (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) {x : ℝ}
    (hx : 1 < x) :
    channelOn C.packet x =
      nontrivialZeroResidueTerm x (memberIndex C.zero) +
        nontrivialZeroResidueTerm x (memberIndex (mirrorMember C.zero)) +
        nontrivialZeroResidueTerm x (conjIndex C.zero) +
        nontrivialZeroResidueTerm x (conjIndex (mirrorMember C.zero)) := by
  rw [C.packet_eq_four_of_mirror h]
  have hA := packet_two_members (S := {memberIndex C.zero, memberIndex (mirrorMember C.zero),
      conjIndex C.zero, conjIndex (mirrorMember C.zero)}) (a := memberIndex C.zero)
    (b := memberIndex (mirrorMember C.zero)) (by simp) (by simp) C.memberIndex_ne_mirrorIndex hx
  rw [hA, four_sdiff_two (conjIndex_ne_memberIndex _ _) (conjIndex_ne_memberIndex _ _)
    (conjIndex_ne_memberIndex _ _) (conjIndex_ne_memberIndex _ _)]
  have hB := packet_two_members (S := {conjIndex C.zero, conjIndex (mirrorMember C.zero)})
    (a := conjIndex C.zero) (b := conjIndex (mirrorMember C.zero)) (by simp) (by simp)
    C.conjIndex_ne_mirrorConjIndex hx
  rw [hB, Set.diff_self, channelOn_empty]
  ring

/-- Contribution lissée de la paire (branche supérieure). -/
noncomputable def smoothedPair (I : PrimeGapInterval) : ℂ :=
  smoothedLocalContribution (memberIndex C.zero) I +
    smoothedLocalContribution (memberIndex (mirrorMember C.zero)) I

/-- Contribution lissée de la paire conjuguée (branche inférieure). -/
noncomputable def smoothedConjPair (I : PrimeGapInterval) : ℂ :=
  smoothedLocalContribution (conjIndex C.zero) I +
    smoothedLocalContribution (conjIndex (mirrorMember C.zero)) I

/-- **Transport exact de la signature vers le canal lissé compilé, cas (a)** : pour TOUT écart premier, la cible
arithmétique lissée est la paire lissée, plus la paire conjuguée, plus les autres fréquences. Aucune autre contribution
à la fréquence `T`. Identité de reconstruction : elle ne contraint pas, à elle seule, la part des autres fréquences. -/
theorem target_split_of_mirror (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1)
    (I : PrimeGapInterval) :
    localArithmeticTarget I = C.smoothedPair I + C.smoothedConjPair I + C.otherFrequenciesContribution I := by
  rw [C.target_split I]
  congr 1
  unfold packetContribution smoothedPair smoothedConjPair
  rw [C.packet_channel_four_of_mirror h I.one_lt_upper, C.packet_channel_four_of_mirror h I.one_lt_lower,
    smoothedLocalContribution_eq, smoothedLocalContribution_eq, smoothedLocalContribution_eq,
    smoothedLocalContribution_eq]
  ring

