/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.EngagedNoTranslation
import RHV6Fresh.Direct.MirrorCount
import RHV6Fresh.Terminal.LocalRaccordCaptivity

/-!
# La place d'une Tour parmi TOUTES les autres, bloquée par le haut et par le bas

Paramètre de l'auteur (2026-10-04) : une Tour s'enroule dans toutes celles qui la précèdent (bloquée par le haut)
et laisse la place à toutes celles qui la suivent, jusqu'à l'infini (bloquée par le bas). L'ordre est l'ordre
des membres : hauteur d'abord, position radiale ensuite.

- `TowerRoom z` : objet, la double obstruction sur tous les membres, pas une prémisse ;
- nécessaire : sous RH toute Tour a sa place (`towerRoom_of_riemannHypothesis`) ;
- encadrement par toutes les autres (`towerRoom_squeeze`) ;
- le miroir d'un membre bas le suit à la même hauteur, s'enroule dans lui, pas inchangé
  (`mirror_takes_room_below`) ;
- enroulement à l'infini de toutes les Tours, sans prémisse (`WindingNestedAtInfinity`, `windingNestedAtInfinity_of_precedes`,
  `towerRoomAtInfinity`) : à partir d'un indice, toute Tour qui en suit une s'enroule en elle, toutes positions radiales ;
  `TowerRoom` (tout `k ≥ 1`) reste non dérivé ;
- capture renouvelée au raccord suivant ⟺ grille d'arrivée non translatée (`renewed_captivity_iff_no_translation`) ;
- monde des paramètres `(β, T)` : quatre Tours, dont une paire miroir à la même hauteur, chacune bloquée par
  le haut et par le bas par toutes les autres, au-dessus du plancher `1` (`room_parameter_model_with_mirror_pair`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse `def P… : Prop`. Sondes hors build :
`experiments/tower_two_sided_room_probe/`.
-/

namespace RHV6Fresh

open RHV3Lean

/-- Contact d'un vrai zéro = contact de la Tour de paramètres `(β, T)`. -/
theorem contactMinusAt_eq_windingContact (z : TrueZero) (k : ℤ) :
    contactMinusAt z k = windingContact (rZeroRadialPosition z.1) (rZeroHeight z.1) k := by
  rw [contactMinusAt_eq_exp]; rfl

/-- **La place d'une Tour parmi toutes les autres.** Bloquée par le haut : elle s'enroule dans toute Tour qui
la précède. Bloquée par le bas : toute Tour qui la suit, jusqu'à l'infini, s'enroule en elle. -/
def TowerRoom (z : TrueZero) : Prop :=
  (∀ w : TrueZero, PZeroMemberPrecedes w.1 z.1 → WindingNested w z) ∧
    (∀ w : TrueZero, PZeroMemberPrecedes z.1 w.1 → WindingNested z w)

/-- **Nécessaire : sous RH, toute Tour a sa place, par le haut et par le bas.** -/
theorem towerRoom_of_riemannHypothesis (hRH : RiemannHypothesis) (z : TrueZero) : TowerRoom z := by
  have hOn : ∀ w : TrueZero, rZeroRadialPosition w.1 = 1 / 2 := fun w =>
    thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1
  have hLt : ∀ a b : TrueZero, PZeroMemberPrecedes a.1 b.1 → rZeroHeight a.1 < rZeroHeight b.1 := by
    intro a b h
    rcases (thm_zeroMemberPrecedes_iff_height_radial_lex a.1 b.1).mp h with h | ⟨_, h⟩
    · exact h
    · rw [hOn a, hOn b] at h; exact absurd h (lt_irrefl _)
  exact ⟨fun w h => windingNested_of_onLine w z (hOn w) (hOn z) (hLt w z h),
    fun w h => windingNested_of_onLine z w (hOn z) (hOn w) (hLt z w h)⟩

/-- **Encadrement par toutes les autres.** Une Tour qui a sa place est, à tout indice `k ≥ 1`, strictement
entre toute Tour qui la suit et toute Tour qui la précède, et toute Tour est au-dessus du plancher `1`. -/
theorem towerRoom_squeeze {e l b : TrueZero} (hR : TowerRoom l) (he : PZeroMemberPrecedes e.1 l.1)
    (hb : PZeroMemberPrecedes l.1 b.1) {k : ℤ} (hk : 1 ≤ k) :
    1 < contactMinusAt b k ∧ contactMinusAt b k < contactMinusAt l k ∧
      contactMinusAt l k < contactMinusAt e k :=
  ⟨contact_gt_one b (by omega), hR.2 b hb k hk, hR.1 e he k hk⟩

/-- À hauteur égale, la Tour de position radiale plus grande s'enroule dans l'autre. -/
theorem windingContact_lt_of_radial_lt {β β' T k : ℝ} (hβ : 0 < β) (hββ' : β < β') (hT : 0 < T) :
    windingContact β' T k < windingContact β T k := by
  unfold windingContact
  apply Real.exp_lt_exp.mpr
  apply div_lt_div_of_pos_right _ hT
  have := Real.arctan_strictMono ((div_lt_div_iff_of_pos_left hT (hβ.trans hββ') hβ).mpr hββ')
  linarith

/-- **Le miroir d'un membre bas prend la place sous lui.** Position radiale `< 1/2` : le membre miroir le suit
dans l'ordre (même hauteur, position radiale plus grande), s'enroule en lui à tout indice, et garde son pas. -/
theorem mirror_takes_room_below (z : TrueZero) (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    PZeroMemberPrecedes z.1 (mirrorMember z).1 ∧
      (∀ k : ℤ, contactMinusAt (mirrorMember z) k < contactMinusAt z k) ∧
      towerPitch (mirrorMember z) = towerPitch z := by
  have hT := mirrorMember_ordinate z
  have hR := mirrorMember_radial z
  have hpos := thm_zeroRadialPosition_positive z.1
  have hlt : rZeroRadialPosition z.1 < rZeroRadialPosition (mirrorMember z).1 := by rw [hR]; linarith
  refine ⟨(thm_zeroMemberPrecedes_iff_height_radial_lex z.1 (mirrorMember z).1).mpr
    (Or.inr ⟨hT.symm, hlt⟩), ?_, ?_⟩
  · intro k
    rw [contactMinusAt_eq_windingContact, contactMinusAt_eq_windingContact, hT]
    exact windingContact_lt_of_radial_lt hpos hlt z.2
  · unfold towerPitch; rw [hT]

/-- **Monde des paramètres : la double obstruction n'exclut pas une paire miroir.** Quatre Tours
`(1/2, 1)`, `(1/4, 4)`, `(3/4, 4)`, `(1/2, 8)`, dans l'ordre des membres. À tout indice réel `k ≥ 1`, chacune
s'enroule dans toutes celles qui la précèdent et toutes celles qui la suivent s'enroulent en elle, toutes au-dessus
du plancher `1` ; la paire `(1/4, 4)`, `(3/4, 4)` est hors ligne, à la même hauteur. Ce monde ne contient que les
contacts : il ne lit ni les premiers ni le poids exact. -/
theorem room_parameter_model_with_mirror_pair {k : ℝ} (hk : 1 ≤ k) :
    1 < windingContact (1 / 2) 8 k ∧
      windingContact (1 / 2) 8 k < windingContact (3 / 4) 4 k ∧
      windingContact (3 / 4) 4 k < windingContact (1 / 4) 4 k ∧
      windingContact (1 / 4) 4 k < windingContact (1 / 2) 1 k ∧
      windingContact (1 / 2) 8 k < windingContact (1 / 4) 4 k ∧
      windingContact (3 / 4) 4 k < windingContact (1 / 2) 1 k ∧
      windingContact (1 / 2) 8 k < windingContact (1 / 2) 1 k := by
  have hπ := Real.pi_pos
  have hkπ : Real.pi ≤ k * Real.pi := by nlinarith
  have hgap48 : (4 : ℝ) * (Real.pi / 2 + k * Real.pi) ≤ 8 * (k * Real.pi) := by nlinarith
  have hgap14 : (1 : ℝ) * (Real.pi / 2 + k * Real.pi) ≤ 4 * (k * Real.pi) := by nlinarith
  have hgap18 : (1 : ℝ) * (Real.pi / 2 + k * Real.pi) ≤ 8 * (k * Real.pi) := by nlinarith
  have h1 : 1 < windingContact (1 / 2) 8 k := by
    unfold windingContact
    rw [Real.one_lt_exp_iff]
    have := Real.arctan_pos.mpr (show (0 : ℝ) < 8 / (1 / 2) by norm_num)
    apply div_pos _ (by norm_num); nlinarith
  have h2 : windingContact (1 / 2) 8 k < windingContact (3 / 4) 4 k :=
    prime_axis_nesting_any_depth (by norm_num) (by norm_num) (by norm_num) hgap48
  have h3 : windingContact (3 / 4) 4 k < windingContact (1 / 4) 4 k :=
    windingContact_lt_of_radial_lt (by norm_num) (by norm_num) (by norm_num)
  have h4 : windingContact (1 / 4) 4 k < windingContact (1 / 2) 1 k :=
    prime_axis_nesting_any_depth (by norm_num) (by norm_num) (by norm_num) hgap14
  exact ⟨h1, h2, h3, h4, h2.trans h3, h3.trans h4,
    prime_axis_nesting_any_depth (by norm_num) (by norm_num) (by norm_num) hgap18⟩

/-- **Capture renouvelée au raccord suivant ⟺ grille d'arrivée non translatée.** Pas `e → l` où la hauteur avance,
pas suivant `l → b`, hauteur de `l` au moins `2`. La Tour `b` est captive de `l` au premier de l'événement
(captivité locale du raccord `l → b`, et non celle du raccord `e → l`) si et seulement si la grille de `l` n'est
pas translatée. Aucun des deux côtés n'est dérivé ici. -/
theorem renewed_captivity_iff_no_translation {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hp : VerticalPassage p) (hL : 0 < rZeroHeight p.zLaterMember)
    (hE' : 0 < rZeroHeight q.zEarlierMember) (hB : 0 < rZeroHeight q.zLaterMember)
    (hT2 : 2 ≤ rZeroHeight q.zEarlierMember) :
    LocalCaptivity q hE' hB ↔ radialFactor ⟨p.zLaterMember, hL⟩ = 1 :=
  (local_captivity_computed q hE' hB hT2).2.trans
    ((vertical_iff_pitch_contracts q hE' hB).trans (no_translation_iff_next_winds hJ hp hL hE' hB))

#print axioms renewed_captivity_iff_no_translation
#print axioms contactMinusAt_eq_windingContact
#print axioms towerRoom_of_riemannHypothesis
#print axioms towerRoom_squeeze
#print axioms mirror_takes_room_below
#print axioms windingContact_lt_of_radial_lt
#print axioms room_parameter_model_with_mirror_pair

/-! ## Enroulement à l'infini, pour TOUTES les Tours -/

/-- **Enroulement à l'infini de `l` dans `e`** : à partir d'un indice, le contact de `l` est en deçà de celui de
`e`. C'est la forme de l'enroulement que la profondeur de hauteur compile, par opposition à `WindingNested`
(tout indice `k ≥ 1`). -/
def WindingNestedAtInfinity (e l : TrueZero) : Prop :=
  ∃ K : ℤ, ∀ k : ℤ, K ≤ k → contactMinusAt l k < contactMinusAt e k

/-- **Toute Tour qui en suit une s'enroule en elle à l'infini**, sans aucune prémisse, pour toutes positions
radiales : hauteur plus grande par la profondeur, même hauteur par la translation vers l'intérieur. -/
theorem windingNestedAtInfinity_of_precedes (e l : TrueZero) (h : PZeroMemberPrecedes e.1 l.1) :
    WindingNestedAtInfinity e l := by
  rcases (thm_zeroMemberPrecedes_iff_height_radial_lex e.1 l.1).mp h with hT | ⟨hT, hβ⟩
  · obtain ⟨n, hn⟩ := exists_nat_gt (rZeroHeight e.1 / (rZeroHeight l.1 - rZeroHeight e.1))
    refine ⟨(n : ℤ) + 1, fun k hk => windingNested_index_of_depth e l k ?_⟩
    have hd : 0 < rZeroHeight l.1 - rZeroHeight e.1 := by linarith
    have hkR : (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk
    have h1 : rZeroHeight e.1 < (n : ℝ) * (rZeroHeight l.1 - rZeroHeight e.1) := by
      rwa [div_lt_iff₀ hd] at hn
    have he0 : 0 < rZeroHeight e.1 := e.2
    have h2 : rZeroHeight e.1 < (k : ℝ) * (rZeroHeight l.1 - rZeroHeight e.1) := by nlinarith
    nlinarith [Real.pi_pos]
  · refine ⟨1, fun k _ => ?_⟩
    rw [contactMinusAt_eq_windingContact, contactMinusAt_eq_windingContact, hT]
    exact windingContact_lt_of_radial_lt (thm_zeroRadialPosition_positive e.1) hβ l.2

/-- **La Tour d'un zéro est prise par toutes les autres à l'infini** : par le haut et par le bas. -/
def TowerRoomAtInfinity (z : TrueZero) : Prop :=
  (∀ w : TrueZero, PZeroMemberPrecedes w.1 z.1 → WindingNestedAtInfinity w z) ∧
    (∀ w : TrueZero, PZeroMemberPrecedes z.1 w.1 → WindingNestedAtInfinity z w)

/-- **Toute Tour a sa place à l'infini, sans prémisse** (la sonde 1, énoncée avec l'enroulement que le code
compile). -/
theorem towerRoomAtInfinity (z : TrueZero) : TowerRoomAtInfinity z :=
  ⟨fun w h => windingNestedAtInfinity_of_precedes w z h,
    fun w h => windingNestedAtInfinity_of_precedes z w h⟩

#print axioms towerRoomAtInfinity

end RHV6Fresh
