/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.SymmetricWinding
import RHV6Fresh.Terminal.TowerTwoSidedRoom
import RHV6Fresh.Terminal.ReadingArithmetic
import RHV6Fresh.Voyage.FiberSuccessor

/-!
# RHV6Fresh — l'obligation d'enroulement entier comme hypothèse de suffisance (ancienne prémisse,
auteur, 2026-10-06)

Depuis la directive de l'auteur du 2026-10-06, l'UNIQUE prémisse du dépôt est `hGain` (premier gain
collectif maximal à tout rang, `Terminal/FirstGainPremise.lean`) ; l'obligation ci-dessous n'est
plus une prémisse : hypothèse ⟺ RH de théorèmes de caractérisation, conséquence de la domination
individuelle (`whole_winding_all_passages_of_individual_domination`).

TDD de SUFFISANCE, pas de dérivation. Une hypothèse analytique, écrite en hypothèse
explicite (aucune `def P… : Prop` nouvelle, conformément à la règle du dépôt) :

> Pour chaque passage `p` et chaque réel `x > 0`, la norme de `zeroTerm` du membre atteint
> est inférieure ou égale à celle du membre précédent, au même `x`.

Les positivités `0 < rZeroHeight` des deux membres sont les données structurelles de la branche
supérieure (elles construisent les `TrueZero`), pas des hypothèses analytiques. Aucune hypothèse
ON, aucune progression stricte de hauteur, aucune symétrie, aucun budget collectif, aucune borne
basse n'entre dans la prémisse.

Composition (chaque raccord démontré) :

1. **Conservation** : sur un passage à enroulement entier, la partie réelle est conservée et les
   supports sont ordonnés (`whole_winding_conserves_radial`, par `whole_tower_inside_iff`).
2. **Réflexion + succession** : un membre sous la ligne a un successeur consécutif de même
   hauteur strictement à sa droite (le miroir, de même hauteur et à droite, garantit la fibre
   non réduite à un point ; `exists_fiberSuccessor`, `horizontalPassage_radial_lt`) ; le passage
   vers lui ne conserve pas la partie réelle (`low_member_passage_breaks_conservation`).
3. **Fermeture** : aucun membre sous la ligne, donc RH par la caractérisation compilée
   `riemannHypothesis_iff_noLowerSide` (`riemannHypothesis_of_whole_winding_all_passages`).

Deux sens du mot « s'enrouler », à ne pas échanger :

* **acquis** : ordre des contacts à partir d'un seuil (`WindingNestedAtInfinity`), vrai sur tout
  passage pour toute position radiale (`acquired_winding_all_passages`) ;
* **posé ici** : domination entière sur tout l'axe positif, `x < 1` compris.

L'implication « acquis ⟹ posé », sur tout passage, équivaut à RH : son antécédent est toujours
vrai (`contact_order_implies_whole_winding_iff_riemannHypothesis`). Elle n'est pas démontrée ici.

Portées des dominations : la domination entière (`x > 0`) implique la domination sur `x ≥ 1`
(`whole_winding_implies_prisoner`) ; sur un passage donné la réciproque n'est pas une conséquence
(une Tour basse de support plus grand est sous la Tour ON sur `x ≥ 1` sans conserver la partie
réelle) ; les deux obligations GLOBALES sont chacune équivalentes à RH
(`prison_iff_riemannHypothesis`, `riemannHypothesis_iff_passage_whole_winding`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau. Ce fichier n'importe pas
`Terminal/OnLineBetaEqPrevious.lean` (module sans `.olean` tant que son but est ouvert) : la
chaîne conditionnelle ci-dessous est entièrement vérifiée par le compilateur.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Conservation de la partie réelle sur un passage à enroulement entier -/

/-- **Sur un passage à enroulement entier, la partie réelle est conservée et les supports sont
ordonnés.** Lecture exacte de la domination entière (`whole_tower_inside_iff`). -/
theorem whole_winding_conserves_radial (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (h : ∀ x : ℝ, 0 < x →
      ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖) :
    rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember ∧
      ‖zeroPoint ⟨p.zEarlierMember, hE⟩‖ ≤ ‖zeroPoint ⟨p.zLaterMember, hL⟩‖ :=
  (whole_tower_inside_iff ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩).mp h

/-! ## 2. Réflexion et succession : un membre bas est quitté par un passage qui ne conserve pas -/

/-- **Un membre sous la ligne est quitté par un passage de même hauteur dont l'arrivée est
strictement à droite.** La réflexion fournit le miroir, de même hauteur et à droite ; la succession fournit le
membre consécutif de la fibre ; l'ordre lexicographique donne la partie réelle strictement plus
grande. -/
theorem low_member_passage_breaks_conservation {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    ∃ p : TZeroPassage, p.zEarlierMember = z.1 ∧ HorizontalPassage p ∧
      rZeroRadialPosition p.zEarlierMember < rZeroRadialPosition p.zLaterMember := by
  obtain ⟨z', hT, hCons⟩ := exists_fiberSuccessor hβ
  have hH : HorizontalPassage ⟨z.1, z'.1, hCons⟩ := hT.symm
  exact ⟨⟨z.1, z'.1, hCons⟩, rfl, hH, horizontalPassage_radial_lt hH⟩

/-! ## 3. Théorème conditionnel de fermeture -/

/-- **Obligation globale d'enroulement entier ⟹ hypothèse de Riemann.** Hypothèse (ancienne prémisse,
⟺ RH) :
sur chaque passage, la Tour du membre atteint reste sous la Tour du membre précédent en tout point
de l'axe positif. Preuve : la prémisse conserve la partie réelle sur chaque passage ; un membre
sous la ligne serait quitté par un passage qui ne la conserve pas ; donc aucun membre sous la
ligne ; donc RH (`riemannHypothesis_iff_noLowerSide`). Aucune amorce, aucune hypothèse ON, aucune
progression de hauteur. -/
theorem riemannHypothesis_of_whole_winding_all_passages
    (hWind : ∀ p : TZeroPassage, ∀ (hE : 0 < rZeroHeight p.zEarlierMember)
        (hL : 0 < rZeroHeight p.zLaterMember), ∀ x : ℝ, 0 < x →
        ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_noLowerSide.mpr fun z hβ => ?_
  obtain ⟨p, hpe, _, hlt⟩ := low_member_passage_breaks_conservation hβ
  have hE : 0 < rZeroHeight p.zEarlierMember := by rw [hpe]; exact z.2
  have hL : 0 < rZeroHeight p.zLaterMember := lt_of_lt_of_le hE (passage_height_le p)
  exact absurd (whole_winding_conserves_radial p hE hL (hWind p hE hL)).1 (ne_of_gt hlt)

/-- **La prémisse est aussi nécessaire** : la fermeture ci-dessus est l'un des deux sens de
`riemannHypothesis_iff_passage_whole_winding`, dont l'autre sens est acquis. La route de preuve
diffère (ici : conservation + réflexion + succession ; là : absence de passage de même hauteur). -/
theorem whole_winding_all_passages_iff_riemannHypothesis :
    (∀ p : TZeroPassage, ∀ (hE : 0 < rZeroHeight p.zEarlierMember)
        (hL : 0 < rZeroHeight p.zLaterMember), ∀ x : ℝ, 0 < x →
        ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖) ↔
      RiemannHypothesis :=
  ⟨riemannHypothesis_of_whole_winding_all_passages,
    riemannHypothesis_iff_passage_whole_winding.mpr⟩

/-! ## 4. Les deux sens de « s'enrouler » : acquis (ordre des contacts) et posé (domination
entière) -/

/-- **L'enroulement acquis tient sur tout passage, pour toute position radiale** : à partir d'un
indice, les contacts du membre atteint sont en deçà de ceux du membre précédent. Cet ordre
éventuel ne suffit pas à fixer la partie réelle. -/
theorem acquired_winding_all_passages (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    WindingNestedAtInfinity ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ :=
  windingNestedAtInfinity_of_precedes _ _ p.hConsecutive.1

/-- **L'implication « ordre des contacts ⟹ domination entière », sur tout passage, équivaut à RH.**
Son antécédent étant toujours vrai, elle n'est pas plus faible que la prémisse elle-même : c'est
l'implication manquante entre l'enroulement acquis et l'enroulement posé. -/
theorem contact_order_implies_whole_winding_iff_riemannHypothesis :
    (∀ p : TZeroPassage, ∀ (hE : 0 < rZeroHeight p.zEarlierMember)
        (hL : 0 < rZeroHeight p.zLaterMember),
        WindingNestedAtInfinity ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ →
        ∀ x : ℝ, 0 < x →
          ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_whole_winding_all_passages fun p hE hL =>
      h p hE hL (acquired_winding_all_passages p hE hL)
  · intro hRH p hE hL _
    exact riemannHypothesis_iff_passage_whole_winding.mpr hRH p hE hL

/-! ## 5. Portées : domination sur tout l'axe positif et domination sur `x ≥ 1` -/

/-- **La domination entière implique la domination sur `x ≥ 1`** (`TowerPrisoner`). -/
theorem whole_winding_implies_prisoner (p : TZeroPassage)
    (h : ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
      ∀ x : ℝ, 0 < x →
        ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖) :
    TowerPrisoner p :=
  fun hE hL x hx => h hE hL x (lt_of_lt_of_le one_pos hx)

/-- **Sur un passage donné, la domination sur `x ≥ 1` ne donne pas la conservation de la partie
réelle** : elle se lit sur les supports dès que la partie réelle ne monte pas
(`inside_iff_support`), sans rien dire de plus. La domination entière, elle, la donne
(`whole_winding_conserves_radial`). Énoncé de portée : sous `β_l ≤ β_e`, prisonnière sur `x ≥ 1` ⟺
supports ordonnés. -/
theorem prisoner_reads_support_only (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hβ : rZeroRadialPosition p.zLaterMember ≤ rZeroRadialPosition p.zEarlierMember) :
    InsideField ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ ↔
      ‖zeroPoint ⟨p.zEarlierMember, hE⟩‖ ≤ ‖zeroPoint ⟨p.zLaterMember, hL⟩‖ :=
  inside_iff_support (z := ⟨p.zEarlierMember, hE⟩) (w := ⟨p.zLaterMember, hL⟩) hβ

#print axioms whole_winding_conserves_radial
#print axioms low_member_passage_breaks_conservation
#print axioms riemannHypothesis_of_whole_winding_all_passages
#print axioms whole_winding_all_passages_iff_riemannHypothesis
#print axioms acquired_winding_all_passages
#print axioms contact_order_implies_whole_winding_iff_riemannHypothesis
#print axioms whole_winding_implies_prisoner
#print axioms prisoner_reads_support_only

end RHV6Fresh
