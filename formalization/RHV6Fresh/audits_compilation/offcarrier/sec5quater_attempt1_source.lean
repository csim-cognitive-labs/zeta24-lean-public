/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-! ## 5quater. La fibre de la fréquence du zéro OFF ; reprise de la cascade après le miroir (cas (a), 2026-10-30)

Confirmation de l'auteur : la position radiale au-dessus d'un demi est déjà exclue pour le premier zéro hors ligne
(`later_le_half_of_history_onLine`, `exists_first_regime_break`), et « un OFF reproduit un ON » est réfuté au
compilateur (§5bis). Le régime ON est engagé et certifié jusqu'au zéro OFF (`history_onLine`, `arrival_vertical`).

Compilé ici, exact et local : (i) tout zéro à la fréquence du zéro OFF a sa position radiale dans `[β, 1 − β]` (à gauche,
il précéderait le zéro OFF et serait ON ; à droite, son miroir le ferait) ; (ii) dans le cas (a), la fibre de la fréquence
est exactement la paire `{z, z*}` ; (iii) dans le cas (a), le passage qui quitte le miroir **remonte** : la cascade
reprend, les décalages décroissent de nouveau strictement, la hiérarchie tient de nouveau (dès la hauteur 2) — le gel est
exactement un pas, l'écart `[p_n, p_{n+1}]` est le seul écart reconstitué sans fréquence nouvelle entre deux écarts qui
en apportent une ; (iv) hors du cas (a), le passage qui quitte le membre sortant est encore gelé (le miroir attend) :
le gel dure au moins deux pas. Le cas (a) est donc exactement « le gel dure un seul pas ». -/

/-- Aucun zéro à la fréquence du zéro OFF n'est strictement à sa gauche : il le précéderait et serait ON. -/
theorem fiber_radial_ge (w : TrueZero) (hw : rZeroHeight w.1 = rZeroHeight C.zero.1) :
    rZeroRadialPosition C.zero.1 ≤ rZeroRadialPosition w.1 := by
  by_contra hlt
  push_neg at hlt
  have hpre : PZeroMemberPrecedes w.1 C.zero.1 := by
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    exact ⟨hw, hlt⟩
  have hOn := C.history_onLine w hpre
  linarith [C.zero_low]

/-- Aucun zéro à cette fréquence n'est strictement à droite du miroir : son propre miroir serait à gauche du zéro OFF. -/
theorem fiber_radial_le (w : TrueZero) (hw : rZeroHeight w.1 = rZeroHeight C.zero.1) :
    rZeroRadialPosition w.1 ≤ rZeroRadialPosition (mirrorMember C.zero).1 := by
  rw [mirrorMember_radial]
  have h := C.fiber_radial_ge (mirrorMember w) (by rw [mirrorMember_ordinate]; exact hw)
  rw [mirrorMember_radial] at h
  linarith

/-- **La bande de la fibre** : tout zéro à la fréquence du zéro OFF a sa position radiale entre `β` et `1 − β`. -/
theorem fiber_band (w : TrueZero) (hw : rZeroHeight w.1 = rZeroHeight C.zero.1) :
    rZeroRadialPosition C.zero.1 ≤ rZeroRadialPosition w.1 ∧
      rZeroRadialPosition w.1 ≤ 1 - rZeroRadialPosition C.zero.1 := by
  refine ⟨C.fiber_radial_ge w hw, ?_⟩
  have := C.fiber_radial_le w hw
  rwa [mirrorMember_radial] at this

/-- **Cas (a) : la fibre de la fréquence est exactement la paire** zéro OFF et miroir. -/
theorem fiber_eq_pair_of_mirror (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1)
    (w : TrueZero) (hw : rZeroHeight w.1 = rZeroHeight C.zero.1) :
    w = C.zero ∨ w = mirrorMember C.zero := by
  rcases lt_trichotomy (rZeroRadialPosition w.1) (rZeroRadialPosition C.zero.1) with hlt | heq | hgt
  · exact absurd hlt (not_lt.mpr (C.fiber_radial_ge w hw))
  · left
    exact Subtype.ext (thm_zero_identity_of_sameSupport (Complex.ext heq hw))
  · have hle := C.fiber_radial_le w hw
    rcases lt_or_eq_of_le hle with hlt' | heq'
    · exfalso
      apply C.outgoing_consecutive.2
      refine ⟨w.1, ?_, ?_⟩
      · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
        right
        exact ⟨hw.symm, hgt⟩
      · rw [thm_zeroMemberPrecedes_iff_height_radial_lex, h]
        right
        exact ⟨by rw [mirrorMember_ordinate]; exact hw, hlt'⟩
    · right
      exact Subtype.ext (thm_zero_identity_of_sameSupport
        (Complex.ext heq' (by show rZeroHeight w.1 = rZeroHeight (mirrorMember C.zero).1
                               rw [mirrorMember_ordinate]; exact hw)))

/-- Le passage qui quitte le membre sortant : du membre de rang `n + 1` au membre de rang `n + 2`. -/
noncomputable def postPassage : TZeroPassage := canonicalPassage (C.n + 1)

theorem postPassage_earlier : C.postPassage.zEarlierMember = C.outgoing.zLaterMember := rfl

theorem postPassage_earlier_pos : 0 < rZeroHeight C.postPassage.zEarlierMember := C.outgoing_later_pos

theorem postPassage_later_pos : 0 < rZeroHeight C.postPassage.zLaterMember :=
  (canonicalMember (C.n + 1 + 1)).2

theorem postPassage_earlier_height : rZeroHeight C.postPassage.zEarlierMember = rZeroHeight C.zero.1 :=
  C.outgoing_same_height

/-- Hors du cas (a), le membre sortant précède le miroir. -/
theorem outgoing_precedes_mirror_of_ne (h : C.outgoing.zLaterMember ≠ (mirrorMember C.zero).1) :
    PZeroMemberPrecedes C.outgoing.zLaterMember (mirrorMember C.zero).1 := by
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

/-- **Cas (a) : après le miroir, la fréquence remonte.** Le passage qui quitte le miroir est vertical : s'il gardait la
hauteur, son membre postérieur serait à la fréquence du zéro OFF et strictement à droite du miroir, hors de la bande. -/
theorem post_mirror_vertical (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    VerticalPassage C.postPassage := by
  rcases passage_regime_dichotomy C.postPassage with ⟨hV, _⟩ | ⟨hH, _⟩
  · exact hV
  · exfalso
    have hr := horizontalPassage_radial_lt hH
    have hH' : rZeroHeight C.postPassage.zEarlierMember = rZeroHeight C.postPassage.zLaterMember := hH
    have hw : rZeroHeight C.postPassage.zLaterMember = rZeroHeight C.zero.1 := by
      rw [← hH']; exact C.postPassage_earlier_height
    have hle := C.fiber_radial_le ⟨C.postPassage.zLaterMember, C.postPassage_later_pos⟩ hw
    rw [postPassage_earlier, h] at hr
    exact absurd hle (not_le.mpr hr)

/-- **Hors du cas (a), le gel continue** : le passage qui quitte le membre sortant garde encore la hauteur, car le miroir,
à la même fréquence, suit le membre sortant et précéderait tout membre de hauteur supérieure. -/
theorem post_horizontal_of_ne (h : C.outgoing.zLaterMember ≠ (mirrorMember C.zero).1) :
    HorizontalPassage C.postPassage := by
  rcases passage_regime_dichotomy C.postPassage with ⟨hV, _⟩ | ⟨hH, _⟩
  · exfalso
    apply (canonicalMember_consecutive (C.n + 1)).2
    refine ⟨(mirrorMember C.zero).1, C.outgoing_precedes_mirror_of_ne h, ?_⟩
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    left
    have hV' : rZeroHeight C.postPassage.zEarlierMember < rZeroHeight C.postPassage.zLaterMember := hV
    rw [C.postPassage_earlier_height] at hV'
    rw [mirrorMember_ordinate]
    exact hV'
  · exact hH

/-- **Le cas (a) est exactement « le gel dure un seul pas »** : le passage qui quitte le membre sortant remonte si et
seulement si le membre sortant est le miroir. -/
theorem post_vertical_iff_mirror :
    VerticalPassage C.postPassage ↔ C.outgoing.zLaterMember = (mirrorMember C.zero).1 := by
  constructor
  · intro hV
    by_contra hne
    exact absurd (C.post_horizontal_of_ne hne) (ne_of_lt hV)
  · exact C.post_mirror_vertical

/-- **Cas (a) : la cascade reprend après le miroir** : les décalages d'entrelacement décroissent de nouveau strictement. -/
theorem post_mirror_cascade_resumes (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) (k : ℤ) :
    interlacingOffset ⟨C.postPassage.zEarlierMember, C.postPassage_earlier_pos⟩
        ⟨C.postPassage.zLaterMember, C.postPassage_later_pos⟩ (k + 1) <
      interlacingOffset ⟨C.postPassage.zEarlierMember, C.postPassage_earlier_pos⟩
        ⟨C.postPassage.zLaterMember, C.postPassage_later_pos⟩ k :=
  (cascade_step_rises_iff C.postPassage C.postPassage_earlier_pos C.postPassage_later_pos k).mpr
    (C.post_mirror_vertical h)

/-- **Cas (a) : la hiérarchie tient de nouveau au raccord qui quitte le miroir** (dès la hauteur 2). -/
theorem post_mirror_hierarchy (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1)
    (hT2 : 2 ≤ rZeroHeight C.zero.1) :
    RaccordHierarchy C.postPassage C.postPassage_earlier_pos C.postPassage_later_pos := by
  have hV := C.post_mirror_vertical h
  have hV' : rZeroHeight C.postPassage.zEarlierMember < rZeroHeight C.postPassage.zLaterMember := hV
  have he := C.postPassage_earlier_height
  exact raccordHierarchy_of_height_advance C.postPassage C.postPassage_earlier_pos C.postPassage_later_pos hV
    (by linarith)

/-- **Cas (a), profil complet du gel d'un pas** : arrivée verticale, pas sortant horizontal, pas suivant vertical. La
hiérarchie tient avant et après, elle est brisée sur le seul pas du zéro OFF vers son miroir. -/
theorem single_frozen_step_of_mirror (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1)
    (hT2 : 2 ≤ rZeroHeight C.zero.1) :
    VerticalPassage C.arrival ∧ HorizontalPassage C.outgoing ∧ VerticalPassage C.postPassage ∧
    RaccordHierarchy C.arrival C.arrival_earlier_pos C.arrival_later_pos ∧
    ¬ RaccordHierarchy C.outgoing C.outgoing_earlier_pos C.outgoing_later_pos ∧
    RaccordHierarchy C.postPassage C.postPassage_earlier_pos C.postPassage_later_pos :=
  ⟨C.arrival_vertical, C.outgoing_horizontal, C.post_mirror_vertical h, C.arrival_hierarchy hT2,
    C.outgoing_signature.2.2, C.post_mirror_hierarchy h hT2⟩

