/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-! ## 5septies. Ce que le prochain point de rencontre exige : compilé et ouvert (§19.14, 2026-10-30)

Demande de l'auteur : prouver que le prochain point de rencontre et le prochain pic exigent une fréquence strictement
supérieure, sans être trop grande, donc exactement une fréquence ON, et non une seconde paire OFF/miroir, trop forte.

Compilé ici (cas (a), le membre porté par `p_{n+2}` est `nextMember`, celui qui suit le miroir) :
* `next_meeting_higher_frequency` : **le membre porté par `p_{n+2}` a une fréquence strictement supérieure à `T`.**
  Source : l'ordre canonique et la bande de la fibre (`post_mirror_vertical`) — pas la rencontre elle-même.
* `nextMember_radial_le_half`, `nextMember_onLine_or_low` : **ce membre est ON, ou sous un demi** ; au-dessus d'un demi,
  son propre miroir s'intercalerait entre le miroir du zéro OFF et lui, contre la consécutivité.
* `second_off_freezes_again` : **s'il est sous un demi, le pas qui le quitte gèle de nouveau** (son miroir attend à la
  même fréquence) ; `second_pair_amplitude_exceeds_line`, `second_pair_relativeAmplitude_unbounded` : **cette seconde
  paire dépasse strictement la ligne en tout point, et son amplitude relative aux rencontres n'est pas bornée.**

Non compilé, consigné : aucune borne supérieure sur la fréquence suivante (« sans être trop grande ») n'existe dans le
corpus ; « exactement une fréquence ON » pour `nextMember` est la même frontière un pas plus loin (une seconde paire OFF
n'est contredite par rien de compilé : elle coûte un pas gelé et une amplitude relative non bornée, qui ne contredisent
la demande que sous un fait sur son niveau, absent du corpus). -/

/-- Le membre porté par le point de rencontre suivant `p_{n+2}`. -/
noncomputable def nextMember : TrueZero := ⟨C.postPassage.zLaterMember, C.postPassage_later_pos⟩

theorem nextMember_occurrence : (occurrence C.nextMember : ℝ) = meetingPoint C.nextGap :=
  C.postPassage_later_occurrence

/-- **Le prochain point de rencontre porte une fréquence strictement supérieure** (cas (a)). -/
theorem next_meeting_higher_frequency (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    zeroFrequency C.zero.1 < zeroFrequency C.nextMember.1 := by
  have hv : rZeroHeight C.postPassage.zEarlierMember < rZeroHeight C.postPassage.zLaterMember :=
    C.post_mirror_vertical h
  rw [C.postPassage_earlier_height] at hv
  exact hv

/-- **Le membre porté par `p_{n+2}` n'est pas au-dessus d'un demi** : sinon son miroir, de même hauteur et de position
radiale strictement inférieure, s'intercalerait entre le miroir du zéro OFF et lui. -/
theorem nextMember_radial_le_half (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    rZeroRadialPosition C.nextMember.1 ≤ 1 / 2 := by
  by_contra hgt
  have hgt' : 1 / 2 < rZeroRadialPosition C.nextMember.1 := lt_of_not_ge hgt
  have hv : rZeroHeight C.postPassage.zEarlierMember < rZeroHeight C.postPassage.zLaterMember :=
    C.post_mirror_vertical h
  have hm_h : rZeroHeight (mirrorMember C.nextMember).1 = rZeroHeight C.nextMember.1 :=
    mirrorMember_ordinate _
  have hm_r : rZeroRadialPosition (mirrorMember C.nextMember).1 = 1 - rZeroRadialPosition C.nextMember.1 :=
    mirrorMember_radial _
  have h1 : PZeroMemberPrecedes C.postPassage.zEarlierMember (mirrorMember C.nextMember).1 := by
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    left
    rw [hm_h]
    exact hv
  have h2 : PZeroMemberPrecedes (mirrorMember C.nextMember).1 C.nextMember.1 := by
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    exact ⟨hm_h, by rw [hm_r]; linarith⟩
  exact (canonicalMember_consecutive (C.n + 1)).2 ⟨_, h1, h2⟩

/-- **Dichotomie du membre suivant** : ON, ou sous un demi (une seconde paire OFF). -/
theorem nextMember_onLine_or_low (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    rZeroRadialPosition C.nextMember.1 = 1 / 2 ∨ rZeroRadialPosition C.nextMember.1 < 1 / 2 := by
  rcases lt_or_eq_of_le (C.nextMember_radial_le_half h) with hlt | heq
  · exact Or.inr hlt
  · exact Or.inl heq

/-- **Une seconde paire OFF gèle de nouveau** : si le membre porté par `p_{n+2}` est sous un demi, le passage qui le
quitte garde sa fréquence (son miroir attend). -/
theorem second_off_freezes_again (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1)
    (hlow : rZeroRadialPosition C.nextMember.1 < 1 / 2) :
    HorizontalPassage (canonicalPassage (C.n + 1 + 1)) :=
  (low_arrival_freezes_cascade (p := C.postPassage) (q := canonicalPassage (C.n + 1 + 1)) rfl
    (C.post_mirror_vertical h) hlow C.postPassage_later_pos (canonicalMember (C.n + 1 + 1 + 1)).2).1

/-- **La seconde paire dépasse strictement la ligne** en tout point `x > 1`. -/
theorem second_pair_amplitude_exceeds_line (hlow : rZeroRadialPosition C.nextMember.1 < 1 / 2) {x : ℝ}
    (hx : 1 < x) :
    2 * x ^ (-(1 / 2) : ℝ) <
      ‖(x : ℂ) ^ (zeroPoint C.nextMember - 1)‖ + ‖(x : ℂ) ^ (zeroPoint (mirrorMember C.nextMember) - 1)‖ :=
  off_pair_density_exceeds_line C.nextMember (mirrorMember C.nextMember) hx
    (d := 1 / 2 - rZeroRadialPosition C.nextMember.1) (by linarith : (0 : ℝ) < _).ne' (by ring)
    (by rw [mirrorMember_radial]; ring)

/-- **L'amplitude relative de la seconde paire aux rencontres n'est pas bornée.** -/
theorem second_pair_relativeAmplitude_unbounded (hlow : rZeroRadialPosition C.nextMember.1 < 1 / 2) (c : ℝ) :
    ∃ I : PrimeGapInterval, c < pairRelativeAmplitude C.nextMember (meetingPoint I) :=
  pairRelativeAmplitude_unbounded C.nextMember hlow c

