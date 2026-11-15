/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.EngagedProgression

/-!
# RHV6Fresh — zêta produit les zéros, ils sont liés (auteur, 2026-09-30)

Correction de l'auteur : « la production d'un zéro n'est pas induite par le zéro précédent mais
liée ; zêta produit les zéros ; les liaisons ont déjà été définies, prends-les en considération ».

Ce fichier ne cherche donc plus une loi qui ferait produire un zéro par le précédent. Il part de
l'état engagé sur la ligne, sans accorder aucun hors-ligne, et applique au membre d'arrivée les
liaisons déjà compilées, ensemble :

1. **l'ordre** : le membre suivant est unique ;
2. **le miroir** : son réfléchi est un zéro de même hauteur, égal à lui-même ⟺ en ligne ;
3. **la grammaire première** : il pointe l'événement premier reconstruit de son rang ;
4. **la somme** : il figure, avec sa position radiale, sa hauteur et un poids non nul, dans toute
   représentation du reste arithmétique, et il n'en est pas retirable ;
5. **le côté arithmétique** : sa position radiale est écrite dans le reste arithmétique
   (`vertical_arrival_written_in_arithmetic`) ;
6. **la fonction réelle de la ligne** : en ligne, elle s'annule à sa hauteur.

Conséquence compilée : la position radiale du membre d'arrivée n'est pas un degré de liberté. Elle
est fixée par le côté arithmétique seul, dans toute représentation. Le régime ne peut pas changer
« au hasard ».

Borne : le point 5 est une équivalence. Il dit où le régime de l'arrivée est écrit, pas ce qui y
est écrit.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse, aucune hypothèse de hors-ligne.
-/

namespace RHV6Fresh

open RHV3Lean Set

/-- **La position radiale de l'arrivée est écrite dans le côté arithmétique.** Sur un passage
vertical, l'arrivée est en ligne si et seulement si, dans toute représentation du reste
arithmétique, tout exposant de poids non nul à la hauteur d'arrivée est sur la ligne. -/
theorem vertical_arrival_written_in_arithmetic {ι : Type*} (Rep : SpectralRepresentation ι)
    (p : TZeroPassage) (hV : VerticalPassage p) (hL : 0 < rZeroHeight p.zLaterMember) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ↔
      ∀ i, Rep.weight i ≠ 0 → (Rep.point i).im = rZeroHeight p.zLaterMember →
        (Rep.point i).re = 1 / 2 := by
  constructor
  · intro hOn i hw hIm
    have hNT : IsNontrivialZetaZero (Rep.point i) := by
      by_contra h
      exact hw (Rep.no_intruder i h)
    have hIoo := isNontrivialZetaZero_re_mem_Ioo hNT
    let w : TNonTrivialZetaZero := ⟨Rep.point i, hNT.1, hIoo.1, hIoo.2⟩
    have hw' : w = p.zLaterMember :=
      (vertical_arrival_onLine_iff_fibre_singleton p hV).mp hOn w hIm
    have hβ : rZeroRadialPosition w = 1 / 2 := by rw [hw']; exact hOn
    exact hβ
  · intro h
    obtain ⟨i, hre, him, _, hne⟩ := Rep.recovers_member ⟨p.zLaterMember, hL⟩
    rw [← hre]
    exact h i hne him

/-- **Le membre d'arrivée, produit par zêta et lié, depuis l'état engagé.** Un passage vertical `o`
arrive sur un membre en ligne `e` ; `p` est le passage qui part de `e`. Les liaisons compilées
tiennent ensemble sur l'arrivée, dans toute représentation `Rep` du reste arithmétique :

1. ordre : tout passage parti de `e` a la même arrivée ;
2. miroir : le réfléchi de l'arrivée a sa hauteur, et il est l'arrivée elle-même ⟺ en ligne ;
3. grammaire première : l'arrivée pointe l'événement premier reconstruit de son rang ;
4. somme : l'arrivée figure dans `Rep` avec sa position radiale, sa hauteur, un poids non nul ;
5. somme : l'arrivée n'est pas retirable ;
6. côté arithmétique : arrivée en ligne ⟺ tout exposant de `Rep` à cette hauteur est sur la ligne ;
7. fonction réelle : en ligne, elle s'annule à la hauteur d'arrivée. -/
theorem engaged_linked_production {ι : Type*} (Rep : SpectralRepresentation ι)
    {o p : TZeroPassage} (hJ : o.zLaterMember = p.zEarlierMember)
    (ho : VerticalPassage o) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    (∀ p' : TZeroPassage, p'.zEarlierMember = p.zEarlierMember →
      p'.zLaterMember = p.zLaterMember) ∧
    (rZeroHeight (mirrorMember ⟨p.zLaterMember, hL⟩).1 = rZeroHeight p.zLaterMember ∧
      (rZeroRadialPosition p.zLaterMember = 1 / 2 ↔
        mirrorMember ⟨p.zLaterMember, hL⟩ = ⟨p.zLaterMember, hL⟩)) ∧
    (∃ G : GrammaticalRaccord ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩,
      G.event = reconstructedEventAt (nZeroSourceIndex p.zLaterMember)) ∧
    (∃ i, (Rep.point i).re = rZeroRadialPosition p.zLaterMember ∧
      (Rep.point i).im = rZeroHeight p.zLaterMember ∧ Rep.weight i ≠ 0) ∧
    (∀ x : ℝ, 1 < x → channelOn {memberIndex ⟨p.zLaterMember, hL⟩}ᶜ x ≠
      ∑' σ : ExplicitIndex, nontrivialZeroResidueTerm x σ) ∧
    (rZeroRadialPosition p.zLaterMember = 1 / 2 ↔
      ∀ i, Rep.weight i ≠ 0 → (Rep.point i).im = rZeroHeight p.zLaterMember →
        (Rep.point i).re = 1 / 2) ∧
    (rZeroRadialPosition p.zLaterMember = 1 / 2 →
      lineValue (rZeroHeight p.zLaterMember) = 0) := by
  obtain ⟨⟨hV, _⟩, _, _, _, _, ⟨G, hRec, _⟩, _⟩ := engaged_progression hJ ho hOn hE hL
  refine ⟨fun p' h => passage_successor_unique h,
    ⟨mirrorMember_ordinate ⟨p.zLaterMember, hL⟩,
      fun h => mirrorMember_eq_self_of_onLine (z := ⟨p.zLaterMember, hL⟩) h, fun h => ?_⟩,
    ⟨G, hRec⟩, ?_, fun x hx => (no_member_removable (memberIndex ⟨p.zLaterMember, hL⟩) hx).2,
    vertical_arrival_written_in_arithmetic Rep p hV hL,
    fun h => lineValue_member_onLine p.zLaterMember h⟩
  · have hm := mirrorMember_radial ⟨p.zLaterMember, hL⟩
    rw [h] at hm
    have hm' : rZeroRadialPosition p.zLaterMember = 1 - rZeroRadialPosition p.zLaterMember := hm
    linarith
  · obtain ⟨i, hre, him, _, hne⟩ := Rep.recovers_member ⟨p.zLaterMember, hL⟩
    exact ⟨i, hre, him, hne⟩

#print axioms vertical_arrival_written_in_arithmetic
#print axioms engaged_linked_production

end RHV6Fresh
