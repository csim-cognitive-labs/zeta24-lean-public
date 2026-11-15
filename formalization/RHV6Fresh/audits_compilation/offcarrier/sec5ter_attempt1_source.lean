/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-! ## 5ter. Le membre sortant est pris dans la bande du zéro OFF et de son miroir (cible §19.9.5, 2026-10-30)

Composition de la cible avec l'ordre canonique et la rencontre obligatoire. Faits exacts, locaux, sans moyenne :
le membre qui rencontre `p_{n+1}` est consécutif au zéro OFF, à sa fréquence, et sa position radiale est prise dans
`]β, 1 − β]` ; au-dessus d'un demi il ne peut être que le miroir (sinon son propre miroir s'intercalerait, contre la
consécutivité). Trichotomie compilée : le miroir lui-même, un zéro ON à la fréquence du zéro OFF, ou un second zéro OFF
strictement entre `β` et un demi. Dans le premier cas, l'occurrence du miroir est exactement le point de rencontre de
l'écart du zéro OFF. Enfin, le zéro OFF et le membre sortant, à fréquence partagée, n'ont aucune rencontre lissée commune,
alors que l'écart leur impose une rencontre unique à `p_{n+1}` : la rencontre lissée n'est pas la rencontre arithmétique,
et cette non-coïncidence est consignée, pas transformée en contradiction. -/

/-- Le membre sortant est le membre canonique suivant : consécutif au zéro OFF. -/
theorem outgoing_consecutive : PZeroMembersConsecutive C.zero.1 C.outgoing.zLaterMember :=
  canonicalMember_consecutive C.n

/-- Le membre sortant a la hauteur du zéro OFF (lecture directe du gel). -/
theorem outgoing_same_height : rZeroHeight C.outgoing.zLaterMember = rZeroHeight C.zero.1 :=
  C.outgoing_horizontal.symm

/-- Le membre sortant comme vrai zéro. -/
noncomputable def outgoingMember : TrueZero := ⟨C.outgoing.zLaterMember, C.outgoing_later_pos⟩

theorem outgoingMember_val : (C.outgoingMember).1 = C.outgoing.zLaterMember := rfl

/-- **Le membre sortant ne dépasse pas le miroir** : `β < β' ≤ 1 − β`. -/
theorem outgoing_radial_le_mirror :
    rZeroRadialPosition C.outgoing.zLaterMember ≤ rZeroRadialPosition (mirrorMember C.zero).1 := by
  rw [mirrorMember_radial]
  exact fiberSuccessor_radial_le_mirror (z := C.zero) (z' := C.outgoingMember) C.low C.outgoing_same_height
    C.outgoing_consecutive

/-- **Au-dessus d'un demi, le membre sortant est le miroir** : sinon le miroir du membre sortant, de même hauteur et de
position radiale strictement entre `β` et `β'`, s'intercalerait entre le zéro OFF et lui. -/
theorem outgoing_eq_mirror_of_high (h : 1 / 2 < rZeroRadialPosition C.outgoing.zLaterMember) :
    C.outgoing.zLaterMember = (mirrorMember C.zero).1 := by
  by_contra hne
  have hle := C.outgoing_radial_le_mirror
  rw [mirrorMember_radial] at hle
  have hlt : rZeroRadialPosition C.outgoing.zLaterMember < 1 - rZeroRadialPosition C.zero.1 := by
    rcases lt_or_eq_of_le hle with h' | h'
    · exact h'
    · exfalso
      apply hne
      apply thm_zero_identity_of_sameSupport
      apply Complex.ext
      · show rZeroRadialPosition C.outgoing.zLaterMember = rZeroRadialPosition (mirrorMember C.zero).1
        rw [mirrorMember_radial]; exact h'
      · show rZeroHeight C.outgoing.zLaterMember = rZeroHeight (mirrorMember C.zero).1
        rw [mirrorMember_ordinate]; exact C.outgoing_same_height
  have hmR : rZeroRadialPosition (mirrorMember C.outgoingMember).1 = 1 - rZeroRadialPosition C.outgoing.zLaterMember :=
    mirrorMember_radial C.outgoingMember
  have hmH : rZeroHeight (mirrorMember C.outgoingMember).1 = rZeroHeight C.outgoing.zLaterMember :=
    mirrorMember_ordinate C.outgoingMember
  apply C.outgoing_consecutive.2
  refine ⟨(mirrorMember C.outgoingMember).1, ?_, ?_⟩
  · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    refine ⟨?_, ?_⟩
    · rw [hmH]; exact C.outgoing_same_height.symm
    · rw [hmR]; linarith
  · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    refine ⟨hmH, ?_⟩
    rw [hmR]; linarith

/-- **Trichotomie du membre sortant** : le miroir, ou un zéro ON à la fréquence du zéro OFF, ou un second zéro OFF
strictement entre `β` et un demi. -/
theorem outgoing_trichotomy :
    C.outgoing.zLaterMember = (mirrorMember C.zero).1 ∨
    rZeroRadialPosition C.outgoing.zLaterMember = 1 / 2 ∨
    (rZeroRadialPosition C.zero.1 < rZeroRadialPosition C.outgoing.zLaterMember ∧
      rZeroRadialPosition C.outgoing.zLaterMember < 1 / 2) := by
  rcases lt_trichotomy (rZeroRadialPosition C.outgoing.zLaterMember) (1 / 2) with h | h | h
  · exact Or.inr (Or.inr ⟨C.outgoing_radial_lt, h⟩)
  · exact Or.inr (Or.inl h)
  · exact Or.inl (C.outgoing_eq_mirror_of_high h)

/-- **Si le membre sortant est le miroir, l'occurrence du miroir est le point de rencontre de l'écart du zéro OFF** :
`p_{n+1}` exactement. -/
theorem mirror_occurrence_eq_meeting (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    (occurrence (mirrorMember C.zero) : ℝ) = meetingPoint C.gap := by
  have hEq : mirrorMember C.zero = canonicalMember (C.n + 1) := Subtype.ext h.symm
  rw [hEq, occurrence_eq_primeAtRank, canonicalMember_index, meetingPoint_eq_upper]
  rfl

/-- Dans les deux autres cas, l'occurrence du miroir est strictement au-delà du point de rencontre. -/
theorem mirror_occurrence_gt_meeting (h : C.outgoing.zLaterMember ≠ (mirrorMember C.zero).1) :
    meetingPoint C.gap < (occurrence (mirrorMember C.zero) : ℝ) := by
  have hpre : PZeroMemberPrecedes C.outgoing.zLaterMember (mirrorMember C.zero).1 := by
    have hle := C.outgoing_radial_le_mirror
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
      right
      exact ⟨by rw [mirrorMember_ordinate]; exact C.outgoing_same_height, hlt⟩
    · exfalso
      apply h
      apply thm_zero_identity_of_sameSupport
      apply Complex.ext
      · exact heq
      · show rZeroHeight C.outgoing.zLaterMember = rZeroHeight (mirrorMember C.zero).1
        rw [mirrorMember_ordinate]; exact C.outgoing_same_height
  have hidx := thm_zeroSourceIndex_strictMono C.outgoing_later_pos hpre
  rw [show C.outgoing.zLaterMember = (canonicalMember (C.n + 1)).1 from rfl, canonicalMember_index] at hidx
  rw [occurrence_eq_primeAtRank, meetingPoint_eq_upper]
  exact_mod_cast thm_primeAtRank_strictMono hidx

/-- **Aucune rencontre lissée commune** : le zéro OFF et le membre sortant, à fréquence partagée, n'ont aucun point de
rencontre lissée en commun, à aucun couple d'indices — alors que l'écart `[p_n, p_{n+1}]` leur impose à tous deux la
rencontre arithmétique unique à `p_{n+1}` (`liaison`). Les deux notions de rencontre ne coïncident pas ; ce fait est
consigné, il n'est pas une contradiction. -/
theorem outgoing_no_common_smoothed_meeting (k k' : ℤ) :
    smoothedMeeting (zeroPoint C.zero) k ≠ smoothedMeeting (zeroPoint C.outgoingMember) k' :=
  shared_frequency_no_common_meeting C.zero C.outgoingMember C.outgoing_same_height.symm C.outgoing_radial_lt

/-- **Amplitude du membre sortant au point de rencontre** : strictement au-dessus de celle du zéro OFF, à la même
fréquence (position radiale strictement plus grande, point strictement supérieur à un). -/
theorem outgoing_amplitude_gt_zero_at_meeting :
    ‖(meetingPoint C.gap : ℂ) ^ (zeroPoint C.zero - 1)‖ <
      ‖(meetingPoint C.gap : ℂ) ^ (zeroPoint C.outgoingMember - 1)‖ := by
  have hx : 0 < meetingPoint C.gap := by linarith [one_lt_meetingPoint C.gap]
  rw [zeroTerm_density_norm C.zero hx, zeroTerm_density_norm C.outgoingMember hx]
  exact Real.rpow_lt_rpow_of_exponent_lt (one_lt_meetingPoint C.gap) (by linarith [C.outgoing_radial_lt])

