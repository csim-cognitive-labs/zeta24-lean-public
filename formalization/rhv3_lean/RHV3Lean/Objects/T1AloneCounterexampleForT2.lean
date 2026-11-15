/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.PrimeSuccessionBridge

/-!
# RHV3Lean — preuve concrète : T1 seul (compté membre par membre) ne force pas
l'écart de comptage un entre deux premiers centraux quelconques

    TRACE_ID              : RHV3-T1-ALONE-COUNTEREXAMPLE
    SEMANTIC_OBJECT       : démonstration, par construction explicite, que la
                            seule répétition de « la cellule d'un membre
                            contient exactement un premier » (T1, appliqué
                            séparément à deux cellules quelconques) ne suffit
                            PAS, en toute généralité, à forcer que l'écart de
                            comptage entre les deux premiers ainsi trouvés
                            vaille un. Ce n'est pas une absence de preuve : `
                            c'est une preuve, avec témoin numérique explicite.
    SEMANTIC_STATEMENT    : deux cellules disjointes, chacune de cardinal
                            trouvé un (T1 vrai sur chacune séparément), peuvent
                            laisser un troisième premier dans l'espace qui les
                            sépare. Le témoin ci-dessous exhibe exactement ce
                            cas : la cellule `(1,2]` (T1 vrai, premier trouvé
                            2) et la cellule `(4,5]` (T1 vrai, premier trouvé
                            5), avec le premier 3 strictement entre les deux,
                            hors des deux cellules. L'écart de comptage entre
                            5 et 2 vaut deux, pas un.
    MATHEMATICAL_STATEMENT: il existe deux intervalles algébriques I1, I2 avec
                            nCellFoundCount I1 = nCellFoundCount I2 = 1, mais
                            nPrimeCountRank (nCellCentralPrime I2) -
                              nPrimeCountRank (nCellCentralPrime I1) = 2 ≠ 1.
    MATHEMATICAL_PARENT   : O2 (axe algébrique), O10 (rigidité de comptage,
                            déjà produits) -- ce module n'ajoute aucune
                            primitive de comptage, il instancie seulement les
                            objets déjà là sur des bords numériques concrets.
    PROOF_STRATEGY        : construction directe de deux `TAlgebraicInterval`
                            à bords entiers, calcul de leurs cardinaux trouvés
                            et premiers centraux par arithmétique pure
                            (`omega`), puis calcul des deux rangs de comptage
                            par évaluation décidable de `Nat.count Nat.Prime`.
    REQUIRED_LEMMAS       : thm_cellFoundCount_eq_one_iff_existsUniquePrime,
                            thm_cellCentralPrime_mem_found, thm_mem_foundPrimes_iff,
                            thm_nPrimeCountRank_eq_count
    WHY_EACH_LEMME_EXISTS : les trois premiers donnent le premier central
                            exact de chaque cellule concrète depuis son
                            cardinal ; le dernier convertit le rang de comptage
                            en un `Nat.count` calculable.
    LEAN_DEFINITION       : tCounterexampleCellEarlier, tCounterexampleCellLater
    LEAN_THEOREM          : thm_counterexample_bothCellsUnique,
                            thm_counterexample_centralPrimes,
                            thm_counterexample_countDiff_is_two,
                            thm_T1_alone_does_not_force_T2_countDiff
    SAME_MEMBER_CHECK     : sans objet -- aucun zéro, aucune Tour ; uniquement
                            deux intervalles concrets de l'axe algébrique.
    SAME_PASSAGE_CHECK    : sans objet.
    SAME_MIDDLE_CHECK     : sans objet.
    SAME_HISTORY_CHECK    : le comptage lu est le même `Nat.count Nat.Prime`
                            que partout ailleurs dans ce corpus -- aucune
                            deuxième énumération.
    FORBIDDEN_PREMISES    : aucune -- ce module ne reçoit aucune hypothèse
                            libre ; les deux intervalles sont des témoins
                            numériques fermés, sans paramètre.
    NEXT_CONSUMER         : le statut architectural de `PT2CountingSuccession`
                            (CanonicalT2.lean) -- ce module établit que cette
                            prémisse n'est PAS une conséquence de T1 seul
                            répété deux fois ; elle reste une prémisse propre,
                            distincte de T1, tant qu'aucun fait de contiguïté
                            entre cellules de membres consécutifs n'est établi.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED -- démonstration complète, aucun `sorry`.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau. Les deux intervalles sont
des témoins numériques concrets, fermés, sans paramètre libre.
-/

namespace RHV3Lean

open Finset

/-! ## 1. Les deux témoins numériques -/

/-- **Le témoin antérieur** : la cellule `(1,2]`. Contient exactement le
premier 2 -- T1 y est vrai. -/
noncomputable def tCounterexampleCellEarlier : TAlgebraicInterval where
  rLeftEndpoint := 1
  rRightEndpoint := 2
  hLeftPositive := by norm_num
  hOrdered := by norm_num

/-- **Le témoin postérieur** : la cellule `(4,5]`. Contient exactement le
premier 5 -- T1 y est vrai. Le premier 3, strictement entre les deux
cellules, n'appartient à AUCUNE des deux. -/
noncomputable def tCounterexampleCellLater : TAlgebraicInterval where
  rLeftEndpoint := 4
  rRightEndpoint := 5
  hLeftPositive := by norm_num
  hOrdered := by norm_num

/-! ## 2. T1 est vrai séparément sur chacune des deux cellules -/

theorem thm_counterexample_earlier_uniquePrime :
    ∃! p : ℕ,
      Nat.Prime p ∧
        tCounterexampleCellEarlier.rLeftEndpoint < (p : ℝ) ∧
          (p : ℝ) ≤ tCounterexampleCellEarlier.rRightEndpoint := by
  unfold tCounterexampleCellEarlier
  refine ⟨2, ⟨by decide, by norm_num, by norm_num⟩, ?_⟩
  rintro q ⟨-, hLeft, hRight⟩
  simp only at hLeft hRight
  have hLeft' : 1 < q := by exact_mod_cast hLeft
  have hRight' : q ≤ 2 := by exact_mod_cast hRight
  omega

theorem thm_counterexample_later_uniquePrime :
    ∃! p : ℕ,
      Nat.Prime p ∧
        tCounterexampleCellLater.rLeftEndpoint < (p : ℝ) ∧
          (p : ℝ) ≤ tCounterexampleCellLater.rRightEndpoint := by
  unfold tCounterexampleCellLater
  refine ⟨5, ⟨by decide, by norm_num, by norm_num⟩, ?_⟩
  rintro q ⟨-, hLeft, hRight⟩
  simp only at hLeft hRight
  have hLeft' : 4 < q := by exact_mod_cast hLeft
  have hRight' : q ≤ 5 := by exact_mod_cast hRight
  omega

/-- **T1 vaut sur les deux cellules, séparément, sans aucune autre
hypothèse.** -/
theorem thm_counterexample_bothCellsUnique :
    nCellFoundCount tCounterexampleCellEarlier = 1 ∧
      nCellFoundCount tCounterexampleCellLater = 1 :=
  ⟨(thm_cellFoundCount_eq_one_iff_existsUniquePrime _).mpr
      thm_counterexample_earlier_uniquePrime,
    (thm_cellFoundCount_eq_one_iff_existsUniquePrime _).mpr
      thm_counterexample_later_uniquePrime⟩

/-! ## 3. Les deux premiers centraux exacts -/

theorem thm_counterexample_centralPrimes :
    nCellCentralPrime tCounterexampleCellEarlier = 2 ∧
      nCellCentralPrime tCounterexampleCellLater = 5 := by
  obtain ⟨hFoundEarlier, hFoundLater⟩ := thm_counterexample_bothCellsUnique
  constructor
  · have hMem := thm_cellCentralPrime_mem_found tCounterexampleCellEarlier
      (by rw [hFoundEarlier]; norm_num)
    obtain ⟨-, hLeft, hRight⟩ := (thm_mem_foundPrimes_iff _ _).mp hMem
    simp only [tCounterexampleCellEarlier] at hLeft hRight
    have hLeft' : 1 < nCellCentralPrime tCounterexampleCellEarlier := by exact_mod_cast hLeft
    have hRight' : nCellCentralPrime tCounterexampleCellEarlier ≤ 2 := by exact_mod_cast hRight
    omega
  · have hMem := thm_cellCentralPrime_mem_found tCounterexampleCellLater
      (by rw [hFoundLater]; norm_num)
    obtain ⟨-, hLeft, hRight⟩ := (thm_mem_foundPrimes_iff _ _).mp hMem
    simp only [tCounterexampleCellLater] at hLeft hRight
    have hLeft' : 4 < nCellCentralPrime tCounterexampleCellLater := by exact_mod_cast hLeft
    have hRight' : nCellCentralPrime tCounterexampleCellLater ≤ 5 := by exact_mod_cast hRight
    omega

/-! ## 4. L'écart de comptage entre les deux premiers centraux vaut DEUX,
pas un -/

theorem thm_counterexample_countDiff_is_two :
    nPrimeCountRank (nCellCentralPrime tCounterexampleCellLater) -
        nPrimeCountRank (nCellCentralPrime tCounterexampleCellEarlier) = 2 := by
  obtain ⟨hEarlier, hLater⟩ := thm_counterexample_centralPrimes
  rw [hEarlier, hLater, thm_nPrimeCountRank_eq_count, thm_nPrimeCountRank_eq_count]
  decide

/-- **CONCLUSION : T1, appliqué séparément à deux cellules quelconques, ne
force PAS que l'écart de comptage entre leurs deux premiers centraux vaille
un.**  Témoin numérique explicite : deux cellules de cardinal trouvé un
chacune (`(1,2]` et `(4,5]`), dont l'écart de comptage des premiers centraux
vaut deux. Sans un fait supplémentaire liant les deux cellules (par exemple,
qu'elles ne laissent passer aucun premier étranger entre elles), la répétition
de T1 seul sur deux membres quelconques ne produit pas `PT2CountingSuccession`. -/
theorem thm_T1_alone_does_not_force_T2_countDiff :
    ∃ tEarlier tLater : TAlgebraicInterval,
      nCellFoundCount tEarlier = 1 ∧
        nCellFoundCount tLater = 1 ∧
          nPrimeCountRank (nCellCentralPrime tLater) -
              nPrimeCountRank (nCellCentralPrime tEarlier) ≠ 1 := by
  refine ⟨tCounterexampleCellEarlier, tCounterexampleCellLater,
    thm_counterexample_bothCellsUnique.1, thm_counterexample_bothCellsUnique.2, ?_⟩
  rw [thm_counterexample_countDiff_is_two]
  omega

/-! ## 5. LA MÊME COMPARAISON, formulée comme ÉGALITÉ DE RANGS -- jamais
comme une soustraction sur `ℕ`

`PT2CountingSuccession` (`CanonicalT2.lean`) compare les deux comptages par
soustraction tronquée de `ℕ`. Reformulation demandée : comparer les deux
rangs directement, par une égalité `rang(p(n+1)) = rang(p(n)) + 1`, sans
passer par la soustraction. Le témoin numérique ci-dessus réfute ENCORE cette
forme, avec les mêmes deux cellules, sans aucun changement de construction. -/

/-- **LA COMPARAISON PAR ÉGALITÉ DE RANGS, sur le même témoin.**  Le rang de
comptage du second premier central (3) n'est PAS le rang de comptage du
premier plus un (1+1=2) : 3 ≠ 2. Aucune soustraction n'intervient ici ; c'est
une comparaison directe des deux rangs. -/
theorem thm_counterexample_rankEquality_fails :
    nPrimeCountRank (nCellCentralPrime tCounterexampleCellLater) ≠
      nPrimeCountRank (nCellCentralPrime tCounterexampleCellEarlier) + 1 := by
  obtain ⟨hEarlier, hLater⟩ := thm_counterexample_centralPrimes
  rw [hEarlier, hLater, thm_nPrimeCountRank_eq_count, thm_nPrimeCountRank_eq_count]
  decide

/-- **CONCLUSION, sous la forme d'égalité de rangs demandée.** T1, appliqué
séparément à deux cellules quelconques, ne force PAS que le rang de comptage
du second premier central soit le rang de comptage du premier plus un --
comparaison directe des deux rangs, sans soustraction sur `ℕ`. Même témoin,
même construction que `thm_T1_alone_does_not_force_T2_countDiff` : la
soustraction tronquée n'était responsable d'aucune perte d'information dans
ce cas (`3 - 1 = 2` est la vraie différence, pas un artefact de troncature),
et la reformulation en égalité confirme exactement la même réfutation. -/
theorem thm_T1_alone_does_not_force_T2_rankEquality :
    ∃ tEarlier tLater : TAlgebraicInterval,
      nCellFoundCount tEarlier = 1 ∧
        nCellFoundCount tLater = 1 ∧
          nPrimeCountRank (nCellCentralPrime tLater) ≠
            nPrimeCountRank (nCellCentralPrime tEarlier) + 1 := by
  refine ⟨tCounterexampleCellEarlier, tCounterexampleCellLater,
    thm_counterexample_bothCellsUnique.1, thm_counterexample_bothCellsUnique.2, ?_⟩
  exact thm_counterexample_rankEquality_fails

/-! Surface audit. -/

#check @tCounterexampleCellEarlier
#check @tCounterexampleCellLater
#check @thm_counterexample_bothCellsUnique
#check @thm_counterexample_centralPrimes
#check @thm_counterexample_countDiff_is_two
#check @thm_T1_alone_does_not_force_T2_countDiff
#check @thm_counterexample_rankEquality_fails
#check @thm_T1_alone_does_not_force_T2_rankEquality

end RHV3Lean
