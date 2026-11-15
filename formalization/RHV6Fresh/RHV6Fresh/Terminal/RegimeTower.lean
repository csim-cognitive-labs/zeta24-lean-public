/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RegimeChange
import RHV6Fresh.Terminal.MirrorDegeneracy

/-!
# RHV6Fresh — le régime lu sur la Tour, et la verticalité sur la ligne (auteur, 2026-09-30)

Deux énoncés de l'auteur, rendus exacts.

1. **Sur la ligne, la poussée horizontale vaut zéro, donc la poussée est verticale.** Pour un membre
   `β = 1/2` : le miroir est le membre lui-même, `Δβ = 0`, `Δφ = 0`, tous les contacts coïncident et
   l'action énergétique horizontale est nulle pour tout `q` (`onLine_horizontal_push_zero`). Tout
   passage entre deux membres en ligne est vertical, avec sa signature complète
   (`onLine_passage_vertical`, `onLine_passage_vertical_signature`). Un passage horizontal qui
   touche un membre en ligne est porté par l'autre extrémité, hors ligne (`onLine_exit`,
   `onLine_entry`).

2. **Le régime se lit sur le déplacement de la Tour.** `T` contrôle le pas `π/T` de la Tour ; `β`
   n'y entre pas (`towerPitch_eq_contacts`, `towerPitch_radial_blind`). À même hauteur, un
   changement de `β` translate rigidement tous les contacts par un facteur unique `0 < c < 1`
   (`rigid_translation_of_sameHeight_radial_lt`). À hauteurs différentes, aucune translation rigide
   ne relie les deux grilles (`no_rigid_translation_of_height_ne`). Donc, sur tout passage :
   horizontal ⟺ pas conservé ⟺ la grille d'entrée est une translatée rigide de la grille de sortie
   (`horizontal_iff_pitch_kept`, `horizontal_iff_tower_translation`) ; vertical ⟺ le pas se
   contracte strictement (`vertical_iff_pitch_contracts`). L'entrée en régime horizontal se lit
   donc sur les contacts (`regime_entry_read_on_towers`).

Borne : lire le régime sur la Tour ne l'interdit pas. Les énoncés du point 2 valent pour tout
passage, hors ligne compris ; l'impossibilité de l'entrée en régime horizontal reste
`riemannHypothesis_iff_no_regimeEntry`.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Le pas de la Tour : `T` seul -/

/-- **Le pas de la Tour** : `π/T`. -/
noncomputable def towerPitch (z : TrueZero) : ℝ := Real.pi / rZeroHeight z.1

/-- Le pas est l'écart logarithmique entre deux contacts consécutifs, pour toute cellule. -/
theorem towerPitch_eq_contacts (z : TrueZero) (k : ℤ) :
    Real.log (contactPlusAt z k) - Real.log (contactMinusAt z k) = towerPitch z :=
  contactAt_consecutive_logWidth z k

theorem towerPitch_pos (z : TrueZero) : 0 < towerPitch z :=
  div_pos Real.pi_pos z.2

/-- **`β` n'entre pas dans le pas** : deux Tours de même hauteur ont le même pas, quelles que soient
leurs positions radiales. -/
theorem towerPitch_radial_blind (z w : TrueZero) (hT : rZeroHeight z.1 = rZeroHeight w.1) :
    towerPitch w = towerPitch z := by
  unfold towerPitch; rw [hT]

/-- **Le pas se contracte strictement ⟺ la hauteur avance strictement.** -/
theorem towerPitch_lt_iff (z w : TrueZero) :
    towerPitch w < towerPitch z ↔ rZeroHeight z.1 < rZeroHeight w.1 :=
  div_lt_div_iff_of_pos_left Real.pi_pos w.2 z.2

/-- **Le pas est conservé ⟺ la hauteur est la même.** -/
theorem towerPitch_eq_iff (z w : TrueZero) :
    towerPitch w = towerPitch z ↔ rZeroHeight z.1 = rZeroHeight w.1 := by
  constructor
  · intro h
    rcases lt_trichotomy (rZeroHeight z.1) (rZeroHeight w.1) with hlt | heq | hgt
    · exact absurd h (ne_of_lt ((towerPitch_lt_iff z w).mpr hlt))
    · exact heq
    · exact absurd h.symm (ne_of_lt ((towerPitch_lt_iff w z).mpr hgt))
  · exact towerPitch_radial_blind z w

/-! ## 2. `β` translate, `T` change le pas -/

/-- **À même hauteur, un déplacement radial `β_z < β_w` translate rigidement la grille** : tous les
contacts de `w` sont ceux de `z` multipliés par un facteur unique `c`, `0 < c < 1`. -/
theorem rigid_translation_of_sameHeight_radial_lt (z w : TrueZero)
    (hT : rZeroHeight z.1 = rZeroHeight w.1)
    (hβ : rZeroRadialPosition z.1 < rZeroRadialPosition w.1) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ k : ℤ,
      contactMinusAt w k = contactMinusAt z k * c ∧
        contactPlusAt w k = contactPlusAt z k * c := by
  refine ⟨Real.exp (((towerMotionOf w).phase - (towerMotionOf z).phase) / rZeroHeight z.1),
    Real.exp_pos _, ?_, fun k => ⟨sameHeight_grid_rigid_translation z w hT k,
      sameHeight_grid_rigid_translation z w hT (k + 1)⟩⟩
  rw [Real.exp_lt_one_iff]
  have hTz : (0 : ℝ) < rZeroHeight z.1 := z.2
  have hβz : (0 : ℝ) < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hphase : (towerMotionOf w).phase < (towerMotionOf z).phase := by
    rw [towerMotion_phase, towerMotion_phase, ← hT]
    exact Real.arctan_strictMono (div_lt_div_of_pos_left hTz hβz hβ)
  exact div_neg_of_neg_of_pos (by linarith) hTz

/-- **À hauteurs différentes, aucune translation rigide ne relie les deux grilles** : le rapport
des contacts dépend du rang. -/
theorem no_rigid_translation_of_height_ne (z w : TrueZero)
    (hT : rZeroHeight z.1 ≠ rZeroHeight w.1) :
    ¬ ∃ c : ℝ, ∀ k : ℤ, contactMinusAt w k = contactMinusAt z k * c := by
  rintro ⟨c, hc⟩
  have h0 := hc 0
  have h1 := hc (0 + 1)
  have hz0 := contactMinusAt_positive z 0
  have hz1 := contactMinusAt_positive z (0 + 1)
  have hw0 := contactMinusAt_positive w 0
  have hcpos : 0 < c := by
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_nonneg hz0.le (neg_nonneg.mpr hneg)]
  refine sameRadial_height_changes_pitch z w hT 0 ?_
  rw [show contactPlusAt w 0 = contactMinusAt w (0 + 1) from rfl,
    show contactPlusAt z 0 = contactMinusAt z (0 + 1) from rfl, h1, h0,
    Real.log_mul hz1.ne' hcpos.ne', Real.log_mul hz0.ne' hcpos.ne']
  ring

/-! ## 3. Le régime d'un passage, lu sur les deux Tours -/

/-- **Horizontal ⟺ le pas est conservé.** -/
theorem horizontal_iff_pitch_kept (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    HorizontalPassage p ↔
      towerPitch ⟨p.zLaterMember, hL⟩ = towerPitch ⟨p.zEarlierMember, hE⟩ :=
  (towerPitch_eq_iff ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩).symm

/-- **Vertical ⟺ le pas se contracte strictement.** -/
theorem vertical_iff_pitch_contracts (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    VerticalPassage p ↔
      towerPitch ⟨p.zLaterMember, hL⟩ < towerPitch ⟨p.zEarlierMember, hE⟩ :=
  (towerPitch_lt_iff ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩).symm

/-- **Régime horizontal : translation rigide stricte de tous les contacts**, facteur unique
`0 < c < 1`, pas inchangé. -/
theorem horizontal_tower_translation (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hH : HorizontalPassage p) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ k : ℤ,
      contactMinusAt ⟨p.zLaterMember, hL⟩ k = contactMinusAt ⟨p.zEarlierMember, hE⟩ k * c ∧
        contactPlusAt ⟨p.zLaterMember, hL⟩ k = contactPlusAt ⟨p.zEarlierMember, hE⟩ k * c :=
  rigid_translation_of_sameHeight_radial_lt ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hH
    (horizontalPassage_radial_lt hH)

/-- **Horizontal ⟺ la grille d'entrée est une translatée rigide de la grille de sortie.** Le régime
se lit sur les contacts seuls. -/
theorem horizontal_iff_tower_translation (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    HorizontalPassage p ↔
      ∃ c : ℝ, ∀ k : ℤ,
        contactMinusAt ⟨p.zLaterMember, hL⟩ k = contactMinusAt ⟨p.zEarlierMember, hE⟩ k * c := by
  constructor
  · intro hH
    obtain ⟨c, _, _, hc⟩ := horizontal_tower_translation p hE hL hH
    exact ⟨c, fun k => (hc k).1⟩
  · intro h
    by_contra hne
    exact no_rigid_translation_of_height_ne ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hne h

/-- **Vertical ⟺ aucune translation rigide ne relie les deux grilles.** -/
theorem vertical_iff_no_tower_translation (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    VerticalPassage p ↔
      ¬ ∃ c : ℝ, ∀ k : ℤ,
        contactMinusAt ⟨p.zLaterMember, hL⟩ k = contactMinusAt ⟨p.zEarlierMember, hE⟩ k * c := by
  rw [← horizontal_iff_tower_translation p hE hL]
  rcases passage_regime_dichotomy p with ⟨hV, hnH⟩ | ⟨hH, hnV⟩
  · exact ⟨fun _ => hnH, fun _ => hV⟩
  · exact ⟨fun hV => absurd hV hnV, fun hnH => absurd hH hnH⟩

/-- **L'entrée en régime horizontal se lit sur les Tours.** À une jonction vertical puis horizontal
sur le membre `m` : le pas s'est contracté strictement en arrivant sur `m`, puis il est conservé et
tous les contacts sont translatés par un facteur unique `0 < c < 1` ; le membre `m` a `β < 1/2`. -/
theorem regime_entry_read_on_towers {p q : TZeroPassage}
    (hJ : p.zLaterMember = q.zEarlierMember)
    (hEp : 0 < rZeroHeight p.zEarlierMember) (hLp : 0 < rZeroHeight p.zLaterMember)
    (hEq : 0 < rZeroHeight q.zEarlierMember) (hLq : 0 < rZeroHeight q.zLaterMember)
    (hp : VerticalPassage p) (hq : HorizontalPassage q) :
    towerPitch ⟨p.zLaterMember, hLp⟩ < towerPitch ⟨p.zEarlierMember, hEp⟩ ∧
      towerPitch ⟨q.zLaterMember, hLq⟩ = towerPitch ⟨q.zEarlierMember, hEq⟩ ∧
      (∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ k : ℤ,
        contactMinusAt ⟨q.zLaterMember, hLq⟩ k = contactMinusAt ⟨q.zEarlierMember, hEq⟩ k * c ∧
          contactPlusAt ⟨q.zLaterMember, hLq⟩ k =
            contactPlusAt ⟨q.zEarlierMember, hEq⟩ k * c) ∧
      rZeroRadialPosition p.zLaterMember < 1 / 2 :=
  ⟨(vertical_iff_pitch_contracts p hEp hLp).mp hp, (horizontal_iff_pitch_kept q hEq hLq).mp hq,
    horizontal_tower_translation q hEq hLq hq, junction_vertical_horizontal hJ hp hq⟩

/-! ## 4. Sur la ligne : la poussée horizontale vaut zéro, le régime est vertical -/

/-- **Sur la ligne, tout le mécanisme horizontal vaut zéro** : le miroir est le membre lui-même,
`Δβ = 0`, `Δφ = 0`, tous les contacts coïncident, le terme explicite coïncide et l'action
énergétique horizontale est nulle pour tout `q`. -/
theorem onLine_horizontal_push_zero {z : TrueZero} (hβ : rZeroRadialPosition z.1 = 1 / 2) :
    mirrorMember z = z ∧
      rZeroRadialPosition (mirrorMember z).1 - rZeroRadialPosition z.1 = 0 ∧
      (towerMotionOf (mirrorMember z)).phase - (towerMotionOf z).phase = 0 ∧
      (∀ k : ℤ, contactMinusAt (mirrorMember z) k = contactMinusAt z k ∧
        contactPlusAt (mirrorMember z) k = contactPlusAt z k) ∧
      (∀ q : ℝ, zeroTerm (mirrorMember z) q = zeroTerm z q) ∧
      (∀ q : ℝ, Real.log ‖zeroTerm (mirrorMember z) q‖ - Real.log ‖zeroTerm z q‖ = 0) :=
  ⟨mirrorMember_eq_self_of_onLine hβ, (mirror_degeneracy_of_onLine hβ).1,
    (mirror_degeneracy_of_onLine hβ).2.1, (mirror_degeneracy_of_onLine hβ).2.2.1,
    (mirror_degeneracy_of_onLine hβ).2.2.2, horizontal_energy_action_zero_of_onLine hβ⟩

/-- **Tout passage entre deux membres en ligne est vertical.** -/
theorem onLine_passage_vertical (p : TZeroPassage)
    (hβe : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hβl : rZeroRadialPosition p.zLaterMember = 1 / 2) : VerticalPassage p := by
  rcases passage_regime_dichotomy p with ⟨hV, _⟩ | ⟨hH, _⟩
  · exact hV
  · have := horizontalPassage_radial_lt hH
    rw [hβe, hβl] at this
    exact absurd this (lt_irrefl _)

/-- **Signature complète du passage en ligne** : vertical, pas strictement contracté, aucune
translation rigide des contacts, raccord orienté dès la hauteur 2, passage séparé par un préfixe. -/
theorem onLine_passage_vertical_signature (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hβe : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hβl : rZeroRadialPosition p.zLaterMember = 1 / 2) :
    VerticalPassage p ∧
      towerPitch ⟨p.zLaterMember, hL⟩ < towerPitch ⟨p.zEarlierMember, hE⟩ ∧
      (¬ ∃ c : ℝ, ∀ k : ℤ,
        contactMinusAt ⟨p.zLaterMember, hL⟩ k = contactMinusAt ⟨p.zEarlierMember, hE⟩ k * c) ∧
      (2 ≤ rZeroHeight p.zLaterMember → (towerRaccordOf p hE hL).Oriented) ∧
      (∃ C : ℝ, cZeroSupport p.zEarlierMember ∈ finsetSymmetricZeroWindow C ∧
        cZeroSupport p.zLaterMember ∉ finsetSymmetricZeroWindow C) := by
  have hV := onLine_passage_vertical p hβe hβl
  have hsig := vertical_regime p hE hL hV
  exact ⟨hV, (vertical_iff_pitch_contracts p hE hL).mp hV,
    (vertical_iff_no_tower_translation p hE hL).mp hV, hsig.2.2.1, hsig.2.2.2.1⟩

/-- **Sortie d'un membre en ligne** : verticale, ou horizontale vers un membre `β > 1/2`. La
poussée horizontale ne vient jamais du membre en ligne. -/
theorem onLine_exit (p : TZeroPassage) (hβe : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    VerticalPassage p ∨ (HorizontalPassage p ∧ 1 / 2 < rZeroRadialPosition p.zLaterMember) := by
  rcases passage_regime_dichotomy p with ⟨hV, _⟩ | ⟨hH, _⟩
  · exact Or.inl hV
  · exact Or.inr ⟨hH, by have := horizontalPassage_radial_lt hH; rwa [hβe] at this⟩

/-- **Arrivée sur un membre en ligne** : verticale, ou horizontale depuis un membre `β < 1/2`. -/
theorem onLine_entry (p : TZeroPassage) (hβl : rZeroRadialPosition p.zLaterMember = 1 / 2) :
    VerticalPassage p ∨ (HorizontalPassage p ∧ rZeroRadialPosition p.zEarlierMember < 1 / 2) := by
  rcases passage_regime_dichotomy p with ⟨hV, _⟩ | ⟨hH, _⟩
  · exact Or.inl hV
  · exact Or.inr ⟨hH, by have := horizontalPassage_radial_lt hH; rwa [hβl] at this⟩

#print axioms towerPitch_eq_contacts
#print axioms towerPitch_radial_blind
#print axioms towerPitch_lt_iff
#print axioms towerPitch_eq_iff
#print axioms rigid_translation_of_sameHeight_radial_lt
#print axioms no_rigid_translation_of_height_ne
#print axioms horizontal_iff_pitch_kept
#print axioms vertical_iff_pitch_contracts
#print axioms horizontal_tower_translation
#print axioms horizontal_iff_tower_translation
#print axioms vertical_iff_no_tower_translation
#print axioms regime_entry_read_on_towers
#print axioms onLine_horizontal_push_zero
#print axioms onLine_passage_vertical
#print axioms onLine_passage_vertical_signature
#print axioms onLine_exit
#print axioms onLine_entry

end RHV6Fresh
