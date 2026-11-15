/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.DiagonalPassage

/-!
# RHV6Fresh — la progression depuis l'état engagé sur la ligne (auteur, 2026-09-30)

Inversion demandée par l'auteur : ne plus accorder un hors-ligne pour en mesurer les effets. Partir
uniquement de l'état effectivement engagé (`β = 1/2`, miroir dégénéré, poussée horizontale nulle,
Tour déterminée par `T`), appliquer uniquement les lois de progression disponibles jusqu'à la
hauteur suivante, et regarder si ces lois possèdent un terme capable de créer `Δβ ≠ 0`.

Aucune hypothèse de ce fichier ne pose un membre hors ligne.

* **§1 L'état engagé** (`EngagedState`, `engagedState_iff_onLine`) : en ligne, miroir égal au
  membre, poussée horizontale nulle, contacts déterminés par la hauteur seule, fonction réelle
  nulle à sa hauteur.
* **§2 La progression est déterministe** : le membre suivant est unique
  (`passage_successor_unique`) et, depuis un membre en ligne, il est une fonction de la hauteur de
  départ seule (`engaged_successor_determined_by_height`).
* **§3 Ce que les lois de progression donnent depuis l'état engagé** (`engaged_progression`) :
  passage vertical, rang avancé d'un cran, pas contracté, aucune annulation de la fonction réelle
  entre les deux hauteurs, événement premier reproduit, raccord orienté, et sur la position
  radiale une seule inégalité : `Δβ ≤ 0`, facteur radial `≥ 1`.
* **§4 Le pas de propagation** (`engaged_propagates`) : si la fibre de la hauteur suivante est
  réduite à un membre, le membre suivant est engagé à son tour et son passage de sortie est
  vertical.

Borne compilée : depuis l'état engagé, `Δβ = 0` ⟺ facteur radial `= 1` ⟺ fibre suivante réduite à
un membre ⟺ passage suivant vertical (`engaged_progression`, dernier point). Les lois de
progression disponibles donnent `Δβ ≤ 0` ; aucune ne donne `Δβ ≥ 0`.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean Set

/-! ## 1. L'état engagé -/

/-- **L'état engagé sur la ligne** : tout ce que porte un membre en ligne, sans référence à un
autre membre. -/
structure EngagedState (z : TrueZero) : Prop where
  /-- Le membre est en ligne. -/
  onLine : rZeroRadialPosition z.1 = 1 / 2
  /-- Le miroir est dégénéré : il est le membre lui-même. -/
  mirror_self : mirrorMember z = z
  /-- La poussée horizontale est nulle à tout `q`. -/
  push_zero : ∀ q : ℝ, Real.log ‖zeroTerm (mirrorMember z) q‖ - Real.log ‖zeroTerm z q‖ = 0
  /-- La Tour est déterminée par la hauteur seule. -/
  contacts : ∀ k : ℤ, contactMinusAt z k = lineContact (rZeroHeight z.1) k
  /-- Le facteur radial vaut `1`. -/
  radial_one : radialFactor z = 1
  /-- La fonction réelle de la hauteur s'annule à sa hauteur. -/
  detector : lineValue (rZeroHeight z.1) = 0

/-- Un membre est engagé si et seulement s'il est en ligne. -/
theorem engagedState_iff_onLine (z : TrueZero) :
    EngagedState z ↔ rZeroRadialPosition z.1 = 1 / 2 :=
  ⟨fun h => h.onLine, fun h =>
    ⟨h, mirrorMember_eq_self_of_onLine h, (onLine_horizontal_push_zero h).2.2.2.2.2,
      (contacts_height_determined_iff_onLine z).mpr h, (radialFactor_eq_one_iff z).mpr h,
      lineValue_member_onLine z.1 h⟩⟩

/-! ## 2. La progression est déterministe -/

/-- **Le membre suivant est unique** : deux passages de même départ ont la même arrivée. -/
theorem passage_successor_unique {p p' : TZeroPassage}
    (h : p.zEarlierMember = p'.zEarlierMember) : p.zLaterMember = p'.zLaterMember := by
  by_contra hNe
  have h₂ : PZeroMembersConsecutive p.zEarlierMember p'.zLaterMember := by
    rw [h]
    exact p'.hConsecutive
  rcases thm_distinctZeroMembers_comparable hNe with hlt | hlt
  · exact h₂.2 ⟨p.zLaterMember, p.hConsecutive.1, hlt⟩
  · exact p.hConsecutive.2 ⟨p'.zLaterMember, h₂.1, hlt⟩

/-- **Depuis un membre en ligne, le membre suivant est une fonction de la hauteur de départ
seule** : deux passages partis de la ligne à la même hauteur ont la même arrivée. -/
theorem engaged_successor_determined_by_height {p p' : TZeroPassage}
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hOn' : rZeroRadialPosition p'.zEarlierMember = 1 / 2)
    (hT : rZeroHeight p.zEarlierMember = rZeroHeight p'.zEarlierMember) :
    p.zLaterMember = p'.zLaterMember :=
  passage_successor_unique (fibre_onLine_unique hT hOn hOn')

/-! ## 3. Ce que les lois de progression donnent depuis l'état engagé -/

/-- Sous la ligne ou en ligne, le facteur radial est au moins `1`. -/
theorem one_le_radialFactor_of_le_half (z : TrueZero) (h : rZeroRadialPosition z.1 ≤ 1 / 2) :
    1 ≤ radialFactor z := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact ((radialFactor_gt_one_iff z).mpr hlt).le
  · exact ((radialFactor_eq_one_iff z).mpr heq).ge

/-- **La progression depuis l'état engagé, sans accorder aucun hors-ligne.** Un passage vertical
`o` arrive sur un membre en ligne `e` ; `p` est le passage qui part de `e`. Les lois de progression
disponibles donnent, en même temps :

1. `p` est vertical, jamais horizontal : la hauteur avance ;
2. le rang avance d'exactement un ;
3. le pas se contracte strictement et vaut `π/T'` ;
4. les contacts de l'arrivée sont ceux de la Tour de ligne à la hauteur `T'`, multipliés par un
   facteur radial unique ;
5. la fonction réelle ne s'annule nulle part strictement entre les deux hauteurs ;
6. l'événement premier est reproduit exactement au raccord ;
7. le raccord est orienté dès la hauteur 2 ;
8. sur la position radiale, une seule inégalité : `β' ≤ 1/2`, facteur radial `≥ 1` ;
9. `β' = 1/2` ⟺ facteur radial `= 1` ⟺ la fibre de `T'` est réduite à l'arrivée ⟺ tout passage
   qui part de l'arrivée est vertical. -/
theorem engaged_progression {o p : TZeroPassage} (hJ : o.zLaterMember = p.zEarlierMember)
    (ho : VerticalPassage o) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    (VerticalPassage p ∧ ¬ HorizontalPassage p) ∧
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
    (towerPitch ⟨p.zLaterMember, hL⟩ = Real.pi / rZeroHeight p.zLaterMember ∧
      towerPitch ⟨p.zLaterMember, hL⟩ < towerPitch ⟨p.zEarlierMember, hE⟩) ∧
    (∀ k : ℤ, contactMinusAt ⟨p.zLaterMember, hL⟩ k =
      lineContact (rZeroHeight p.zLaterMember) k * radialFactor ⟨p.zLaterMember, hL⟩) ∧
    (∀ t : ℝ, rZeroHeight p.zEarlierMember < t → t < rZeroHeight p.zLaterMember →
      lineValue t ≠ 0) ∧
    (∃ G : GrammaticalRaccord ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩,
      G.event = reconstructedEventAt (nZeroSourceIndex p.zLaterMember) ∧
      primalHistory (nZeroSourceIndex p.zLaterMember) =
        primalHistory (nZeroSourceIndex p.zEarlierMember) ++ [G.event]) ∧
    (2 ≤ rZeroHeight p.zLaterMember → (towerRaccordOf p hE hL).Oriented) ∧
    (rZeroRadialPosition p.zLaterMember ≤ 1 / 2 ∧ 1 ≤ radialFactor ⟨p.zLaterMember, hL⟩) ∧
    ((rZeroRadialPosition p.zLaterMember = 1 / 2 ↔ radialFactor ⟨p.zLaterMember, hL⟩ = 1) ∧
      (rZeroRadialPosition p.zLaterMember = 1 / 2 ↔
        ∀ w : TNonTrivialZetaZero, rZeroHeight w = rZeroHeight p.zLaterMember →
          w = p.zLaterMember) ∧
      (∀ q : TZeroPassage, p.zLaterMember = q.zEarlierMember →
        (VerticalPassage q ↔ rZeroRadialPosition p.zLaterMember = 1 / 2))) := by
  have hOnO : rZeroRadialPosition o.zLaterMember = 1 / 2 := by rw [hJ]; exact hOn
  obtain ⟨hV, hnH⟩ := engaged_regime_kept hJ ho hOnO
  have hβ := passage_entry_radial_le_half p hV
  obtain ⟨G, _, hRec, hHist⟩ := globalRigidSystem.raccord p hE hL
  exact ⟨⟨hV, hnH⟩, thm_zeroSourceIndex_succ_of_passage p hE,
    ⟨rfl, (vertical_iff_pitch_contracts p hE hL).mp hV⟩,
    fun k => contact_eq_line_mul_radial ⟨p.zLaterMember, hL⟩ k,
    fun t h1 h2 => lineValue_ne_zero_between p h1 h2, ⟨G, hRec, hHist⟩,
    fun hT2 => towerRaccord_oriented_of_height_lt p hE hL hV hT2,
    ⟨hβ, one_le_radialFactor_of_le_half ⟨p.zLaterMember, hL⟩ hβ⟩,
    (radialFactor_eq_one_iff ⟨p.zLaterMember, hL⟩).symm,
    vertical_arrival_onLine_iff_fibre_singleton p hV,
    fun q hq => (vertical_arrival_characterizes hq hV).1⟩

/-! ## 4. Le pas de propagation -/

/-- **Pas de propagation du régime engagé.** Depuis l'état engagé, si la fibre de la hauteur
suivante est réduite à un membre, le membre suivant est engagé à son tour, il a été atteint
verticalement, et tout passage qui en part est vertical. -/
theorem engaged_propagates {o p : TZeroPassage} (hJ : o.zLaterMember = p.zEarlierMember)
    (ho : VerticalPassage o) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hL : 0 < rZeroHeight p.zLaterMember)
    (hFibre : ∀ w : TNonTrivialZetaZero, rZeroHeight w = rZeroHeight p.zLaterMember →
      w = p.zLaterMember) :
    VerticalPassage p ∧ EngagedState ⟨p.zLaterMember, hL⟩ ∧
      ∀ q : TZeroPassage, p.zLaterMember = q.zEarlierMember →
        VerticalPassage q ∧ ¬ HorizontalPassage q := by
  have hOnO : rZeroRadialPosition o.zLaterMember = 1 / 2 := by rw [hJ]; exact hOn
  have hV := (engaged_regime_kept hJ ho hOnO).1
  have hOnL := (vertical_arrival_onLine_iff_fibre_singleton p hV).mpr hFibre
  exact ⟨hV, (engagedState_iff_onLine ⟨p.zLaterMember, hL⟩).mpr hOnL,
    fun q hq => engaged_regime_kept hq hV hOnL⟩

#print axioms engagedState_iff_onLine
#print axioms passage_successor_unique
#print axioms engaged_successor_determined_by_height
#print axioms one_le_radialFactor_of_le_half
#print axioms engaged_progression
#print axioms engaged_propagates

end RHV6Fresh
