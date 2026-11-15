/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Tower.CanonicalOrigin
import RHV6Fresh.Direct.PivotCell
import RHV6Fresh.Direct.PairTowers
import RHV6Fresh.Direct.Reached
import RHV6Fresh.Voyage.Progression
import RHV6Fresh.Grammar.ExpectedMinimum

/-!
# Démonstration SANS l'hypothèse de Riemann (ordre de l'auteur, 2026-09-22 ; maîtres finaux 2026-09-23)

Anciennement la bibliothèque séparée `RHV6Demonstration` (racine `RHV6Demonstration.lean`, cible par défaut avec
`RHV6Fresh`). Déplacée mot pour mot dans la bibliothèque unique le 2026-10-09 (auteur : un seul code Lean, une seule
chaîne, une seule commande `lake build RHV6Fresh` ; aucune cible séparée) ; la bibliothèque et la cible `RHV6Demonstration`
sont supprimées du lakefile. Ce module n'appartient pas à la chaîne active (`Terminal/DemonstrationChain.lean`) : il
conserve onze théorèmes compilés de la règle du pivot. L'hypothèse de Riemann est
retirée de la boucle : ce fichier n'énonce ni `RiemannHypothesis`, ni un zéro hors ligne, ni un miroir,
ni la contradiction.  Il écrit la démonstration « jusqu'au bout » telle que les maîtres finaux la
décrivent pour TOUT vrai zéro (SEM §4–§7, §9 ; MATH §4–§7, §9 ; LEAN §4–§7, §9), chaque étape étant
un théorème sur la Tour produite par la règle du pivot (`firstTowerOf z`) :

1. la géométrie : origine canonique, demi-tours, alternance de côté (`Tower/CanonicalOrigin.lean`) ;
2. l'état propre : la règle du pivot arrête le parcours au premier anneau qui atteint `p_min(z)`,
   la cellule contient `p_min(z)`, `k` et `m = 1` sont lus, l'inversion rend `(T, β)` ;
3. la lecture arithmétique : l'occurrence et le minimum attendu sont atteints (R₁, C_lecture) ; les
   deux informations : `p_min(z) ≤ cible` ;
4. la progression déjà démontrée : sur un passage consécutif `a ▷ b`, `Occ(b) = p_min(a)`, et le test
   de vérification passe à l'état propre de `b` (`verification_passes`).

Aucune hypothèse, aucun `sorry`, aucun `P…Law`, aucun recul, aucun miroir.  Les fichiers autrefois cités pour le
raccord à l'hypothèse de Riemann (`Terminal/PairContradiction.lean`, `Terminal/Universalization.lean`, `RHV6Closure.lean`)
sont retirés du code ; la seule chaîne vers RH est `Terminal/DemonstrationChain.lean`.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Géométrie : le parcours part de l'origine canonique, un demi-tour par croisement -/

/-- L'origine canonique est le premier croisement après l'abscisse 1, et le côté du passage alterne
à chaque croisement. -/
theorem geometry_of_tower (z : TrueZero) :
    IsLeast {k : ℤ | 1 < (towerMotionOf z).incidence k} 0 ∧
      ∀ k : ℤ, Real.cos (rZeroHeight z.1 * Real.log ((towerMotionOf z).incidence (k + 1)) -
          (towerMotionOf z).phase) =
        - Real.cos (rZeroHeight z.1 * Real.log ((towerMotionOf z).incidence k) -
          (towerMotionOf z).phase) :=
  ⟨canonicalOrigin_isLeast z, crossing_side_alternates z⟩

/-! ## 2. L'état propre : la règle du pivot, la cellule, les lectures, l'inversion -/

/-- Le parcours s'arrête au PREMIER croisement dont le suivant atteint `p_min(z)`. -/
theorem stop_event (z : TrueZero) :
    IsLeast {k : ℤ | (expectedMinimumPrime z : ℝ) ≤ contactPlusAt z k}
      (firstTowerOf z).properState.entryCoordinate := by
  rw [(firstTower_readings z).1]
  exact pivotCoordinate_isLeast z (by exact_mod_cast expectedMinimumPrime_pos z)

/-- La cellule de l'état propre contient le minimum attendu : `C⁻ < p_min(z) ≤ C⁺`. -/
theorem cell_contains_expected (z : TrueZero) :
    (firstTowerOf z).entryContact < (expectedMinimumPrime z : ℝ) ∧
      (expectedMinimumPrime z : ℝ) ≤ (firstTowerOf z).lastRayContact :=
  ⟨entry_lt_pivot z (by exact_mod_cast expectedMinimumPrime_pos z),
    pivot_le_lastRay z (by exact_mod_cast expectedMinimumPrime_pos z)⟩

theorem expected_mem_cell (z : TrueZero) :
    ((expectedMinimumPrime z : ℕ) : ℝ) ∈ (firstTowerOf z).properState.cell :=
  ⟨le_of_lt (cell_contains_expected z).1, (cell_contains_expected z).2⟩

/-- Les lectures de l'état propre : `k` (demi-tours depuis l'origine) et `m = 1`. -/
theorem readings (z : TrueZero) :
    (firstTowerOf z).properState.entryCoordinate = pivotCoordinate z (expectedMinimumPrime z) ∧
      (firstTowerOf z).properState.stageCount = 1 :=
  firstTower_readings z

/-- L'inversion : les deux contacts de l'état propre rendent `T` puis `β`. -/
theorem inversion (z : TrueZero) :
    rZeroHeight z.1 =
        (firstTowerOf z).properState.stageReading * Real.pi /
          (firstTowerOf z).properState.logDiameter ∧
      rZeroRadialPosition z.1 =
        rZeroHeight z.1 /
          Real.tan (rZeroHeight z.1 * Real.log (firstTowerOf z).properState.entryContact) :=
  ⟨(firstTowerOf z).properState.recovers_T, (firstTowerOf z).properState.recovers_beta⟩

/-! ## 3. Lecture arithmétique : R₁, C_lecture, les deux informations -/

/-- R₁ : le minimum attendu est atteint à l'état propre (théorème de la règle). -/
theorem reaches_expected (z : TrueZero) :
    reaches (firstTowerOf z).properState (expectedMinimumPrime z) :=
  firstTower_reaches_expected z

/-- C_lecture : l'occurrence est atteinte à l'état propre. -/
theorem reaches_occurrence (z : TrueZero) :
    reaches (firstTowerOf z).properState (occurrence z) :=
  firstTower_reaches_occurrence z

/-- Les deux informations : la cible constatée est au moins la référence. -/
theorem expected_le_counted (z : TrueZero) :
    expectedMinimumPrime z ≤ countedPrime (firstTowerOf z).properState :=
  pivot_le_counted z (expectedMinimumPrime_prime z)

/-! ## 4. La progression et le test de vérification -/

/-- **Progression des premiers atteints** (SEM §7, §9) : sur un passage consécutif, l'occurrence de
`b` est le minimum attendu de `a`, et elle est atteinte à l'état propre de `b`. -/
theorem reached_progression {a b : TrueZero} (hab : PZeroMembersConsecutive a.1 b.1) :
    occurrence b = expectedMinimumPrime a ∧
      reaches (firstTowerOf b).properState (occurrence b) :=
  ⟨progression_occurrence hab, firstTower_reaches_occurrence b⟩

/-- **Test de vérification**, pour tout vrai zéro `b` de prédécesseur consécutif `a`, sur ou hors
ligne, sans distinction : le minimum attendu de `a` est atteint à l'état propre porté par la Tour
de `b`. -/
theorem verification_passes {a b : TrueZero} (hab : PZeroMembersConsecutive a.1 b.1) :
    reaches (firstTowerOf b).properState (expectedMinimumPrime a) :=
  reaches_expected_of_reaches_occurrence hab _ (firstTower_reaches_occurrence b)

#print axioms RHV6Fresh.geometry_of_tower
#print axioms RHV6Fresh.stop_event
#print axioms RHV6Fresh.cell_contains_expected
#print axioms RHV6Fresh.inversion
#print axioms RHV6Fresh.expected_le_counted
#print axioms RHV6Fresh.reached_progression
#print axioms RHV6Fresh.verification_passes

end RHV6Fresh
