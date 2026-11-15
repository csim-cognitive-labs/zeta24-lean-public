/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.LocalRaccordCaptivity
import RHV6Fresh.Terminal.TowerHierarchy
import RHV6Fresh.Terminal.EngagedPersistence
import RHV6Fresh.Terminal.RegimeTrigger

/-!
# RHV6Fresh — le plancher radial de l'arrivée depuis un départ engagé (revue de l'auteur, 2026-10-04)

Troisième revue de l'auteur : le trou n'est pas le passage de même hauteur. Le code possède déjà
« membre engagé sur la ligne ⟹ le passage qui le quitte fait avancer la hauteur » (`engaged_regime_kept`,
`raccordHierarchy_of_engaged_departure`), et toute entrée en régime horizontal est précédée d'une arrivée hors ligne
(`regime_entry_diagonal`). Un membre n'a que deux coordonnées, `β` et `T` : il n'y a aucune « diagonale »
dans zêta (réalignement de l'auteur, 2026-10-04). L'arrivée hypothétique à exclure d'abord est

    (T, 1/2) ⟶ (T', β' < 1/2),  T' > T   (hauteur qui avance, grille d'arrivée translatée),

avant tout passage de même hauteur. La cible alignée est la non-translation de la grille d'arrivée
(`Terminal/EngagedNoTranslation.lean`). Sur un passage parti d'un membre engagé on a déjà
`β_l ≤ 1/2` (`passage_entry_radial_le_half`) ; il ne manque que le plancher `1/2 ≤ β_l`.

* **§1 Le lemme atomique** : depuis un départ engagé, arrivée en ligne ⟺ plancher radial `1/2 ≤ β_l`
  (`engaged_arrival_onLine_iff_radial_floor`).
* **§2 Inventaire des planchers radiaux compilés** : le seul plancher sur l'arrivée d'un passage où la
  hauteur avance est celui que donne le passage SUIVANT quand il fait avancer la hauteur
  (`arrival_radial_floor_iff_next_vertical`) ; il lit le passage d'après, pas le raccord du passage même.
* **§3 L'arrivée translatée (hypothétique), lue au raccord exact** : la transition première exacte existe
  entière, le coût de sortie est strictement négatif, le budget est tenu avec excédent, la captivité locale
  tient (`translated_arrival_complete_and_captive`). L'énergie au raccord ne donne aucun plancher : elle
  est du côté de la descente radiale.
* **§4 Le lemme cible, mesuré** : « départ engagé + transition première exacte ⟹ plancher » ⟺ loi locale
  de conservation depuis l'état engagé (`engaged_radial_floor_target_iff`) ; plancher ⟺ « seule la hauteur
  évolue » (`radial_floor_iff_heightOnly`) ; nécessaire (`radial_floor_of_riemannHypothesis`).
* **§5 On recommence** : sous le plancher, tout membre au-dessus d'un membre engagé est en ligne, atteint
  et quitté par un passage où la hauteur avance (`engaged_persists_of_radial_floor`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse `def P… : Prop` : le plancher n'apparaît
qu'en hypothèse de théorème ou en membre d'équivalence.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Le lemme atomique -/

/-- **Depuis un départ engagé, arrivée en ligne ⟺ plancher radial.** Un passage `o` où la hauteur avance
arrive sur un membre en ligne ; `p` en part. Alors `p` fait avancer la hauteur, `β_l ≤ 1/2` est acquis, et
l'arrivée est en ligne si et seulement si `1/2 ≤ β_l`. -/
theorem engaged_arrival_onLine_iff_radial_floor {o p : TZeroPassage}
    (hJ : o.zLaterMember = p.zEarlierMember) (ho : VerticalPassage o)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    VerticalPassage p ∧ rZeroRadialPosition p.zLaterMember ≤ 1 / 2 ∧
      (rZeroRadialPosition p.zLaterMember = 1 / 2 ↔ 1 / 2 ≤ rZeroRadialPosition p.zLaterMember) := by
  have hV : VerticalPassage p := (engaged_regime_kept hJ ho (by rw [hJ]; exact hOn)).1
  have hLe := passage_entry_radial_le_half p hV
  exact ⟨hV, hLe, fun h => h.ge, fun h => le_antisymm hLe h⟩

/-! ## 2. Inventaire des planchers radiaux compilés -/

/-- **Le seul plancher compilé sur une arrivée lit le passage suivant.** Sur l'arrivée d'un passage où la
hauteur avance, `1/2 ≤ β_l` ⟺ le passage qui quitte cette arrivée fait avancer la hauteur. Les deux
formulations (plancher radial de l'arrivée, départ vertical de l'arrivée) sont la même propriété. -/
theorem arrival_radial_floor_iff_next_vertical {p q : TZeroPassage}
    (hJ : p.zLaterMember = q.zEarlierMember) (hp : VerticalPassage p) :
    1 / 2 ≤ rZeroRadialPosition p.zLaterMember ↔ VerticalPassage q := by
  have hChar := vertical_arrival_characterizes hJ hp
  have hLe := passage_entry_radial_le_half p hp
  exact ⟨fun h => hChar.1.mpr (le_antisymm hLe h), fun hq => (hChar.1.mp hq).ge⟩

/-! ## 3. L'arrivée translatée (hypothétique), lue au raccord exact -/

/-- **Une arrivée translatée, si elle existait, satisferait tout ce que le raccord sait calculer.** Départ en
ligne, la hauteur avance, arrivée strictement sous la ligne, hauteur d'arrivée au moins 2 : la transition
première exacte existe avec tous ses champs, le coût de sortie est strictement négatif, le budget est tenu
avec l'excédent des deux supports, la captivité locale tient. Rien de ce que contient le raccord ne donne
un plancher radial : l'énergie au premier partagé est du côté de la descente. -/
theorem translated_arrival_complete_and_captive (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) (hV : VerticalPassage p)
    (hlt : rZeroRadialPosition p.zLaterMember < 1 / 2) (hT2 : 2 ≤ rZeroHeight p.zLaterMember) :
    Nonempty (ExactPrimeTransition p hE hL) ∧
      exitCost ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) < 0 ∧
      exitCost ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) +
          (rZeroRadialPosition p.zEarlierMember - rZeroRadialPosition p.zLaterMember) *
            (Real.log 2 - 1 / 4) ≤ raccordAvailable ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ ∧
      LocalCaptivity p hE hL := by
  have hM := raccordPrime_two_le ⟨p.zEarlierMember, hE⟩
  have hB := (height_advance_local_budget p hE hL hV).2 hT2
  refine ⟨⟨exactPrimeTransitionOf p hE hL⟩, ?_, hB.1, hB.2⟩
  unfold exitCost
  exact mul_neg_of_neg_of_pos (by change rZeroRadialPosition p.zLaterMember - rZeroRadialPosition p.zEarlierMember < 0; linarith)
    (Real.log_pos (by linarith))

/-! ## 4. Le lemme cible, mesuré -/

/-- **Le lemme cible** : « départ engagé + transition première exacte ⟹ `1/2 ≤ β_l` » équivaut à la loi
locale de conservation depuis l'état engagé. La transition, faite de faits démontrés, existe sur tout passage, quelle que soit la position radiale d'arrivée : comme hypothèse elle n'apporte rien. -/
theorem engaged_radial_floor_target_iff :
    (∀ (o p : TZeroPassage), o.zLaterMember = p.zEarlierMember → VerticalPassage o →
        rZeroRadialPosition p.zEarlierMember = 1 / 2 →
        ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
          ExactPrimeTransition p hE hL → 1 / 2 ≤ rZeroRadialPosition p.zLaterMember) ↔
      ∀ (o p : TZeroPassage), o.zLaterMember = p.zEarlierMember → VerticalPassage o →
        rZeroRadialPosition p.zEarlierMember = 1 / 2 → 0 < rZeroHeight p.zEarlierMember →
        rZeroRadialPosition p.zLaterMember = 1 / 2 := by
  constructor
  · intro h o p hJ ho hOn hE
    have hL : 0 < rZeroHeight p.zLaterMember := hE.trans_le (passage_height_le p)
    exact (engaged_arrival_onLine_iff_radial_floor hJ ho hOn).2.2.mpr
      (h o p hJ ho hOn hE hL (exactPrimeTransitionOf p hE hL))
  · intro h o p hJ ho hOn hE _ _
    exact (h o p hJ ho hOn hE).ge

/-- **Plancher radial ⟺ « seule la hauteur évolue »** sur les passages où la hauteur avance partis de la
ligne. -/
theorem radial_floor_iff_heightOnly :
    (∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
        1 / 2 ≤ rZeroRadialPosition p.zLaterMember) ↔
      ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
        rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember := by
  constructor
  · intro h p hV hOn
    exact (le_antisymm (passage_entry_radial_le_half p hV) (h p hV hOn)).trans hOn.symm
  · intro h p hV hOn
    rw [h p hV hOn, hOn]

/-- **Borne.** Le plancher radial est nécessaire : il est vrai sous l'hypothèse de Riemann. -/
theorem radial_floor_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      1 / 2 ≤ rZeroRadialPosition p.zLaterMember :=
  fun _ _ _ => (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _).ge

/-! ## 5. On recommence -/

/-- **Sous le plancher radial, le régime engagé perdure** : un passage où la hauteur avance arrive sur un
membre en ligne ; alors tout membre au-dessus est en ligne, atteint par un passage où la hauteur avance, et
tout passage qui en part fait avancer la hauteur. Le plancher (`hFloor`) est une hypothèse, non dérivée. -/
theorem engaged_persists_of_radial_floor
    (hFloor : ∀ p : TZeroPassage, VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 → 1 / 2 ≤ rZeroRadialPosition p.zLaterMember)
    {o : TZeroPassage} (hE : 0 < rZeroHeight o.zLaterMember) (ho : VerticalPassage o)
    (hOn : rZeroRadialPosition o.zLaterMember = 1 / 2) :
    ∀ w : TNonTrivialZetaZero, PZeroMemberPrecedes o.zLaterMember w →
      rZeroRadialPosition w = 1 / 2 ∧
      (∃ q : TZeroPassage, q.zLaterMember = w ∧ VerticalPassage q) ∧
      (∀ q : TZeroPassage, q.zEarlierMember = w → VerticalPassage q ∧ ¬ HorizontalPassage q) :=
  engaged_persists_to_infinity (radial_floor_iff_heightOnly.mp hFloor) hE ho hOn

#print axioms engaged_arrival_onLine_iff_radial_floor
#print axioms arrival_radial_floor_iff_next_vertical
#print axioms translated_arrival_complete_and_captive
#print axioms engaged_radial_floor_target_iff
#print axioms radial_floor_iff_heightOnly
#print axioms radial_floor_of_riemannHypothesis
#print axioms engaged_persists_of_radial_floor

end RHV6Fresh
