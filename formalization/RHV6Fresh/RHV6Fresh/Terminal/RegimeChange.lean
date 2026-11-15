/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.InverseReading

/-!
# RHV6Fresh — deux régimes et le changement de régime (auteur, 2026-09-30)

Énoncé de l'auteur : même si un zéro hors ligne peut passer inaperçu de la somme, il **exige un
changement de régime** ; l'alignement vertical des zéros sur la ligne est un régime différent.

* **Deux régimes de passage**, exclusifs et exhaustifs (`passage_regime_dichotomy`) :
  vertical (`VerticalPassage`, la hauteur avance) et horizontal (`HorizontalPassage`, même hauteur).
* **Signature du régime vertical** (`vertical_regime`) : `β_l ≤ 1/2 ≤ β_e`, raccord orienté,
  passage séparé par un préfixe, et le membre d'entrée quitte le paquet de hauteur du membre de
  sortie.
* **Signature du régime horizontal** (`horizontal_regime`) : `β_e < β_l`, une extrémité hors
  ligne, raccord renversé, aucun préfixe séparateur, les deux membres dans le même paquet.
* **Lois de jonction** sur un membre `m` entre deux passages consécutifs `p` puis `q` :
  vertical–vertical ⟹ `β_m = 1/2` (`junction_vertical_vertical`) ;
  vertical–horizontal ⟹ `β_m < 1/2` (`junction_vertical_horizontal`) ;
  horizontal–vertical ⟹ `1/2 < β_m` (`junction_horizontal_vertical`).
* **Le changement de régime est impossible sur la ligne** : un membre en ligne garde le régime
  (`onLine_keeps_regime`) ; tout changement a lieu sur un membre hors ligne
  (`regimeChange_offLine`).
* **Un hors-ligne exige le changement** (`off_forces_regime_entry`) : il existe, à sa hauteur, un
  membre `β < 1/2` d'où part un passage horizontal, et ce membre est soit atteint par un passage
  vertical, soit le plus bas de tous.
* **Caractérisation** (`riemannHypothesis_iff_no_regimeEntry`) : RH équivaut à « aucune entrée
  vertical → horizontal, et la suite ne commence pas par un passage horizontal ».

* **Le régime dans la lecture inverse** (`passage_split_by_regime`) : sur tout passage,
  `ΔR = paquet + complément` ; le membre d'entrée tombe dans le paquet exactement en régime
  horizontal, dans le complément exactement en régime vertical.

Borne : l'impossibilité de l'entrée en régime horizontal est donc RH elle-même ; elle est compilée
comme équivalence, pas comme théorème.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Les deux régimes d'un passage -/

/-- **Régime vertical** : la hauteur avance strictement. -/
def VerticalPassage (p : TZeroPassage) : Prop :=
  rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember

/-- **Régime horizontal** : la hauteur n'avance pas. -/
def HorizontalPassage (p : TZeroPassage) : Prop :=
  rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember

/-- **Les deux régimes sont exclusifs et exhaustifs.** -/
theorem passage_regime_dichotomy (p : TZeroPassage) :
    (VerticalPassage p ∧ ¬ HorizontalPassage p) ∨ (HorizontalPassage p ∧ ¬ VerticalPassage p) := by
  rcases (passage_height_le p).lt_or_eq with h | h
  · exact Or.inl ⟨h, ne_of_lt h⟩
  · exact Or.inr ⟨h, fun h' => absurd h (ne_of_lt h')⟩

theorem horizontalPassage_radial_lt {p : TZeroPassage} (h : HorizontalPassage p) :
    rZeroRadialPosition p.zEarlierMember < rZeroRadialPosition p.zLaterMember :=
  (nullPassage_horizontal p ((thm_zeroPassage_null_iff_sameHeight p).mpr h)).2.1

/-- **Signature du régime vertical.** -/
theorem vertical_regime (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hV : VerticalPassage p) :
    rZeroRadialPosition p.zLaterMember ≤ 1 / 2 ∧ 1 / 2 ≤ rZeroRadialPosition p.zEarlierMember ∧
      (2 ≤ rZeroHeight p.zLaterMember → (towerRaccordOf p hE hL).Oriented) ∧
      (∃ C : ℝ, cZeroSupport p.zEarlierMember ∈ finsetSymmetricZeroWindow C ∧
        cZeroSupport p.zLaterMember ∉ finsetSymmetricZeroWindow C) ∧
      memberIndex ⟨p.zLaterMember, hL⟩ ∈ (heightPacket (rZeroHeight p.zEarlierMember))ᶜ := by
  refine ⟨passage_entry_radial_le_half p hV, passage_exit_radial_ge_half p hV,
    towerRaccord_oriented_of_height_lt p hE hL hV,
    (passage_separated_by_window_iff p hE hL).mpr hV, ?_⟩
  intro h
  have h1 : |(zeroPoint ⟨p.zLaterMember, hL⟩).im| = rZeroHeight p.zEarlierMember := h
  have h2 : |(zeroPoint ⟨p.zLaterMember, hL⟩).im| = rZeroHeight p.zLaterMember :=
    memberIndex_mem_heightPacket ⟨p.zLaterMember, hL⟩
  exact absurd (h1.symm.trans h2) (ne_of_lt hV)

/-- **Signature du régime horizontal.** -/
theorem horizontal_regime (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hH : HorizontalPassage p) :
    rZeroRadialPosition p.zEarlierMember < rZeroRadialPosition p.zLaterMember ∧
      (PIsOffCriticalLine p.zEarlierMember ∨ PIsOffCriticalLine p.zLaterMember) ∧
      (2 ≤ rZeroHeight p.zEarlierMember → ¬ (towerRaccordOf p hE hL).Oriented) ∧
      (¬ ∃ C : ℝ, cZeroSupport p.zEarlierMember ∈ finsetSymmetricZeroWindow C ∧
        cZeroSupport p.zLaterMember ∉ finsetSymmetricZeroWindow C) ∧
      memberIndex ⟨p.zLaterMember, hL⟩ ∈ heightPacket (rZeroHeight p.zEarlierMember) := by
  refine ⟨horizontalPassage_radial_lt hH, nullPassage_offLine p hH,
    globalRigidSystem.detectorFlat p hE hL hH, ?_, ?_⟩
  · intro hSep
    exact absurd ((passage_separated_by_window_iff p hE hL).mp hSep) (by rw [hH]; exact lt_irrefl _)
  · have h2 := memberIndex_mem_heightPacket ⟨p.zLaterMember, hL⟩
    rwa [show rZeroHeight p.zLaterMember = rZeroHeight p.zEarlierMember from hH.symm] at h2

/-! ## 2. Les lois de jonction : ce qu'un membre entre deux passages peut être -/

/-- **Vertical puis vertical** : le membre de jonction est sur la ligne. L'alignement sur la ligne
est exactement l'intérieur du régime vertical. -/
theorem junction_vertical_vertical {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hp : VerticalPassage p) (hq : VerticalPassage q) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 :=
  le_antisymm (passage_entry_radial_le_half p hp) (hJ ▸ passage_exit_radial_ge_half q hq)

/-- **Vertical puis horizontal** : l'entrée en régime horizontal se fait sur un membre du côté
`β < 1/2`, strictement. -/
theorem junction_vertical_horizontal {p q : TZeroPassage}
    (hJ : p.zLaterMember = q.zEarlierMember) (hp : VerticalPassage p) (hq : HorizontalPassage q) :
    rZeroRadialPosition p.zLaterMember < 1 / 2 := by
  have hle := passage_entry_radial_le_half p hp
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    have hβ := horizontalPassage_radial_lt hq
    have hT : rZeroHeight q.zLaterMember = rZeroHeight p.zLaterMember := by rw [hJ]; exact hq.symm
    rw [← hJ, h] at hβ
    apply p.hConsecutive.2
    refine ⟨zMirrorZero q.zLaterMember, ?_, ?_⟩
    · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
      left
      rw [thm_mirror_sameHeight, hT]
      exact hp
    · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
      right
      refine ⟨by rw [thm_mirror_sameHeight, hT], ?_⟩
      rw [thm_mirror_radialPosition, h]
      linarith

/-- **Horizontal puis vertical** : la sortie du régime horizontal se fait sur un membre du côté
`β > 1/2`, strictement. -/
theorem junction_horizontal_vertical {p q : TZeroPassage}
    (hJ : p.zLaterMember = q.zEarlierMember) (hp : HorizontalPassage p) (hq : VerticalPassage q) :
    1 / 2 < rZeroRadialPosition p.zLaterMember := by
  have hge : 1 / 2 ≤ rZeroRadialPosition p.zLaterMember := hJ ▸ passage_exit_radial_ge_half q hq
  rcases hge.lt_or_eq with h | h
  · exact h
  · exfalso
    have hβ := horizontalPassage_radial_lt hp
    have hT : rZeroHeight p.zEarlierMember = rZeroHeight q.zEarlierMember := by rw [← hJ]; exact hp
    apply q.hConsecutive.2
    refine ⟨zMirrorZero p.zEarlierMember, ?_, ?_⟩
    · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
      right
      refine ⟨by rw [thm_mirror_sameHeight, hT], ?_⟩
      rw [thm_mirror_radialPosition, ← hJ]
      linarith
    · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
      left
      rw [thm_mirror_sameHeight, hT]
      exact hq

/-- **Tout changement de régime a lieu sur un membre hors ligne.** -/
theorem regimeChange_offLine {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (h : (VerticalPassage p ∧ HorizontalPassage q) ∨ (HorizontalPassage p ∧ VerticalPassage q)) :
    PIsOffCriticalLine p.zLaterMember := by
  rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact ne_of_lt (junction_vertical_horizontal hJ hp hq)
  · exact ne_of_gt (junction_horizontal_vertical hJ hp hq)

/-- **Le changement de régime est impossible sur la ligne** : un membre en ligne sort dans le
régime par lequel il est entré. -/
theorem onLine_keeps_regime {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hOn : rZeroRadialPosition p.zLaterMember = 1 / 2) :
    VerticalPassage p ↔ VerticalPassage q := by
  constructor
  · intro hp
    rcases passage_regime_dichotomy q with ⟨hq, _⟩ | ⟨hq, _⟩
    · exact hq
    · exact absurd hOn (ne_of_lt (junction_vertical_horizontal hJ hp hq))
  · intro hq
    rcases passage_regime_dichotomy p with ⟨hp, _⟩ | ⟨hp, _⟩
    · exact hp
    · exact absurd hOn (ne_of_gt (junction_horizontal_vertical hJ hp hq))

/-! ## 3. Un zéro hors ligne exige l'entrée en régime horizontal -/

private theorem height_pos_of_precedes {w u : TNonTrivialZetaZero}
    (hw : 0 < rZeroHeight w) (h : PZeroMemberPrecedes w u) : 0 < rZeroHeight u := by
  rcases (thm_zeroMemberPrecedes_iff_height_radial_lex w u).mp h with h1 | ⟨h1, _⟩
  · linarith
  · linarith

/-- Tout membre qui n'est pas le plus bas a un prédécesseur consécutif authentique. -/
theorem exists_consecutive_predecessor (z : TNonTrivialZetaZero)
    (hne : (sUpperZerosBelow z).Nonempty) :
    ∃ w : TNonTrivialZetaZero, 0 < rZeroHeight w ∧ PZeroMembersConsecutive w z ∧
      nZeroSourceIndex w < nZeroSourceIndex z := by
  classical
  have hfin := thm_upperZerosBelow_finite z
  obtain ⟨w, hwS, hmax⟩ := Finset.exists_max_image hfin.toFinset nZeroSourceIndex
    (by simpa [Set.Finite.toFinset_nonempty] using hne)
  rw [Set.Finite.mem_toFinset] at hwS
  obtain ⟨hw, hwz⟩ := hwS
  refine ⟨w, hw, ⟨hwz, ?_⟩, thm_zeroSourceIndex_strictMono hw hwz⟩
  rintro ⟨u, hwu, huz⟩
  have hu : 0 < rZeroHeight u := height_pos_of_precedes hw hwu
  have hle := hmax u ((Set.Finite.mem_toFinset hfin).mpr ⟨hu, huz⟩)
  exact absurd (thm_zeroSourceIndex_strictMono hw hwu) (not_lt.mpr hle)

/-- **Un membre du côté `β < 1/2` exige l'entrée en régime horizontal** : à sa hauteur, il existe
un membre `m` du côté `β < 1/2` d'où part un passage horizontal, et `m` est soit le plus bas de
tous les membres, soit atteint par un passage vertical. -/
theorem lowerSide_enters_horizontal (z : TrueZero) (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    ∃ m : TrueZero, rZeroHeight m.1 = rZeroHeight z.1 ∧ rZeroRadialPosition m.1 < 1 / 2 ∧
      (∃ q : TZeroPassage, q.zEarlierMember = m.1 ∧ HorizontalPassage q) ∧
      (sUpperZerosBelow m.1 = ∅ ∨
        ∃ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember ∧ p.zLaterMember = m.1 ∧
          VerticalPassage p) := by
  have key : ∀ n : ℕ, ∀ z : TrueZero, nZeroSourceIndex z.1 = n →
      rZeroRadialPosition z.1 < 1 / 2 →
      ∃ m : TrueZero, rZeroHeight m.1 = rZeroHeight z.1 ∧ rZeroRadialPosition m.1 < 1 / 2 ∧
        (∃ q : TZeroPassage, q.zEarlierMember = m.1 ∧ HorizontalPassage q) ∧
        (sUpperZerosBelow m.1 = ∅ ∨
          ∃ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember ∧ p.zLaterMember = m.1 ∧
            VerticalPassage p) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z hz hβ
      obtain ⟨z', hT', hcons'⟩ := exists_fiberSuccessor hβ
      have hq : ∃ q : TZeroPassage, q.zEarlierMember = z.1 ∧ HorizontalPassage q :=
        ⟨⟨z.1, z'.1, hcons'⟩, rfl, hT'.symm⟩
      by_cases hS : (sUpperZerosBelow z.1).Nonempty
      · obtain ⟨w, hw, hcons, hlt⟩ := exists_consecutive_predecessor z.1 hS
        rcases passage_regime_dichotomy ⟨w, z.1, hcons⟩ with ⟨hV, _⟩ | ⟨hH, _⟩
        · exact ⟨z, rfl, hβ, hq, Or.inr ⟨⟨w, z.1, hcons⟩, hw, rfl, hV⟩⟩
        · have hβw : rZeroRadialPosition w < 1 / 2 := lt_trans (horizontalPassage_radial_lt hH) hβ
          obtain ⟨m, hm, hmβ, hmq, hmp⟩ := ih _ (hz ▸ hlt) ⟨w, hw⟩ rfl hβw
          exact ⟨m, hm.trans hH, hmβ, hmq, hmp⟩
      · exact ⟨z, rfl, hβ, hq, Or.inl (Set.not_nonempty_iff_eq_empty.mp hS)⟩
  exact key _ z rfl hβ

/-- **Un zéro hors ligne exige le changement de régime** : à sa hauteur, un membre `β < 1/2` porte
un passage horizontal sortant, et il est soit le plus bas de tous, soit atteint par un passage
vertical (jonction vertical → horizontal). -/
theorem off_forces_regime_entry {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    ∃ m : TrueZero, rZeroHeight m.1 = rZeroHeight z.1 ∧ rZeroRadialPosition m.1 < 1 / 2 ∧
      (∃ q : TZeroPassage, q.zEarlierMember = m.1 ∧ HorizontalPassage q) ∧
      (sUpperZerosBelow m.1 = ∅ ∨
        ∃ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember ∧ p.zLaterMember = m.1 ∧
          VerticalPassage p) := by
  rcases lt_or_gt_of_ne hOff with h | h
  · exact lowerSide_enters_horizontal z h
  · obtain ⟨m, hm, rest⟩ := lowerSide_enters_horizontal (mirrorMember z)
      (by rw [mirrorMember_radial]; linarith)
    exact ⟨m, hm.trans (mirrorMember_ordinate z), rest⟩

/-! ## 4. Les deux mondes et la caractérisation -/

/-- Sous RH, aucun passage n'est horizontal. -/
theorem no_horizontal_of_riemannHypothesis (hRH : RiemannHypothesis) (q : TZeroPassage) :
    ¬ HorizontalPassage q := by
  intro h
  rcases nullPassage_offLine q h with hOff | hOff
  · exact hOff (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _)
  · exact hOff (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _)

/-- **Le monde aligné** : tout passage est vertical si et seulement si RH. -/
theorem allVertical_iff_riemannHypothesis :
    (∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    refine riemannHypothesis_of_noOff fun z hOff => ?_
    obtain ⟨p, hE, _, _, hSame, _⟩ := off_event_increment_without_height hOff
    exact absurd hSame (ne_of_lt (h p hE))
  · intro hRH p _
    rcases passage_regime_dichotomy p with ⟨hV, _⟩ | ⟨hH, _⟩
    · exact hV
    · exact absurd hH (no_horizontal_of_riemannHypothesis hRH p)

/-- **Le monde mixte** : RH est fausse si et seulement si un passage horizontal existe. -/
theorem not_riemannHypothesis_iff_horizontal :
    ¬ RiemannHypothesis ↔
      ∃ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember ∧ HorizontalPassage p := by
  rw [← allVertical_iff_riemannHypothesis]
  constructor
  · intro h
    by_contra hNo
    apply h
    intro p hE
    rcases passage_regime_dichotomy p with ⟨hV, _⟩ | ⟨hH, _⟩
    · exact hV
    · exact absurd ⟨p, hE, hH⟩ hNo
  · rintro ⟨p, hE, hH⟩ h
    exact absurd hH (ne_of_lt (h p hE))

/-- **Caractérisation par le changement de régime** : RH équivaut à « aucune jonction vertical →
horizontal, et le plus bas membre ne porte pas de passage horizontal ». L'impossibilité de l'entrée
en régime horizontal est RH elle-même. -/
theorem riemannHypothesis_iff_no_regimeEntry :
    RiemannHypothesis ↔
      (¬ ∃ p q : TZeroPassage, p.zLaterMember = q.zEarlierMember ∧ VerticalPassage p ∧
        HorizontalPassage q) ∧
      (¬ ∃ q : TZeroPassage, 0 < rZeroHeight q.zEarlierMember ∧
        sUpperZerosBelow q.zEarlierMember = ∅ ∧ HorizontalPassage q) := by
  constructor
  · intro hRH
    exact ⟨fun ⟨_, q, _, _, hq⟩ => no_horizontal_of_riemannHypothesis hRH q hq,
      fun ⟨q, _, _, hq⟩ => no_horizontal_of_riemannHypothesis hRH q hq⟩
  · rintro ⟨hEntry, hBottom⟩
    refine riemannHypothesis_iff_noLowerSide.mpr fun z hβ => ?_
    obtain ⟨m, _, _, ⟨q, hq, hHq⟩, hBot | ⟨p, _, hp, hVp⟩⟩ := lowerSide_enters_horizontal z hβ
    · exact hBottom ⟨q, by rw [hq]; exact m.2, by rw [hq]; exact hBot, hHq⟩
    · exact hEntry ⟨p, q, hp.trans hq.symm, hVp, hHq⟩

/-! ## 5. Le régime dans la lecture inverse -/

/-- **Le régime décide seulement du côté du découpage.** Sur tout passage, entre les deux premiers
consécutifs de son raccord, `ΔR = paquet + complément` pour le paquet de hauteur du membre de
sortie ; le membre d'entrée tombe dans le paquet exactement en régime horizontal, dans le
complément exactement en régime vertical. L'identité elle-même ne dépend pas du régime. -/
theorem passage_split_by_regime (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    remainderBetween (occurrence ⟨p.zEarlierMember, hE⟩) (grammaticalRaccordOf p hE hL).M =
        packetBetween (heightPacket (rZeroHeight p.zEarlierMember))
            (occurrence ⟨p.zEarlierMember, hE⟩) (grammaticalRaccordOf p hE hL).M +
          packetBetween (heightPacket (rZeroHeight p.zEarlierMember))ᶜ
            (occurrence ⟨p.zEarlierMember, hE⟩) (grammaticalRaccordOf p hE hL).M ∧
      (HorizontalPassage p ↔
        memberIndex ⟨p.zLaterMember, hL⟩ ∈ heightPacket (rZeroHeight p.zEarlierMember)) ∧
      (VerticalPassage p ↔
        memberIndex ⟨p.zLaterMember, hL⟩ ∈ (heightPacket (rZeroHeight p.zEarlierMember))ᶜ) := by
  have hM : (grammaticalRaccordOf p hE hL).M = occurrence ⟨p.zLaterMember, hL⟩ :=
    (grammaticalRaccordOf p hE hL).entry_eq
  have ha : 2 ≤ occurrence ⟨p.zEarlierMember, hE⟩ := (occurrence_prime _).two_le
  have hb : 2 ≤ (grammaticalRaccordOf p hE hL).M := by
    rw [hM]; exact (occurrence_prime _).two_le
  have hHiff : HorizontalPassage p ↔
      memberIndex ⟨p.zLaterMember, hL⟩ ∈ heightPacket (rZeroHeight p.zEarlierMember) := by
    constructor
    · intro hH
      exact (horizontal_regime p hE hL hH).2.2.2.2
    · intro h
      have h1 : |(zeroPoint ⟨p.zLaterMember, hL⟩).im| = rZeroHeight p.zEarlierMember := h
      have h2 : |(zeroPoint ⟨p.zLaterMember, hL⟩).im| = rZeroHeight p.zLaterMember :=
        memberIndex_mem_heightPacket ⟨p.zLaterMember, hL⟩
      exact h1.symm.trans h2
  refine ⟨remainderBetween_eq_packet_add_complement _ ha hb, hHiff, ?_⟩
  constructor
  · intro hV
    exact (vertical_regime p hE hL hV).2.2.2.2
  · intro h
    rcases passage_regime_dichotomy p with ⟨hV, _⟩ | ⟨hH, _⟩
    · exact hV
    · exact absurd (hHiff.mp hH) h

#print axioms passage_regime_dichotomy
#print axioms vertical_regime
#print axioms horizontal_regime
#print axioms junction_vertical_vertical
#print axioms junction_vertical_horizontal
#print axioms junction_horizontal_vertical
#print axioms regimeChange_offLine
#print axioms onLine_keeps_regime
#print axioms lowerSide_enters_horizontal
#print axioms off_forces_regime_entry
#print axioms not_riemannHypothesis_iff_horizontal
#print axioms allVertical_iff_riemannHypothesis
#print axioms riemannHypothesis_iff_no_regimeEntry
#print axioms passage_split_by_regime

end RHV6Fresh
