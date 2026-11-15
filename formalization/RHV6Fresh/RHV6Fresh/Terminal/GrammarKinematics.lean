/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.NoRegimeChange
import RHV6Fresh.Grammar.Mod6Rigidity

/-!
# RHV6Fresh — composition de la grammaire première et de la cinématique des Tours
(auteur, 2026-09-30)

Correction de l'auteur : le verrou en amont n'est pas « trouver `r' ≤ 1` », c'est **composer la
progression grammaticale obligatoire avec la cinématique exacte des Tours**, sur une chaîne
d'événements et non sur un seul, puis seulement regarder ce que cette composition laisse à la
position radiale. Le membre gauche doit utiliser réellement `EV+1`, `p_n`, `g_n`, la classe
modulo 6 et l'alternance `2, 4` ; le membre droit doit utiliser réellement `T_n`, `T_{n+1}`, `φ`,
les contacts et le pas `π/T`.

Ce fichier compile cette composition, exacte, sans rien poser.

* **§1 La position de l'occurrence dans sa propre Tour** (`occurrencePosition`) : `T·log(Occ) − φ`,
  et son découpage `T·log(Occ) − φ_ligne(T) − T·log r` (`occurrencePosition_decomposed`) : la part
  que la hauteur détermine, et la part radiale.
* **§2 Le registre d'un passage** (`passage_ledger`) : sur tout passage, le déplacement de la
  position de l'occurrence est exactement le déplacement au raccord (`raccordShift`, cinématique :
  `ΔT·log M − Δφ`) plus la progression continue de l'événement (`phaseIncrement`, grammaire :
  `T·log(p_{n+1}/p_n)`). Le déplacement en hauteur s'en lit exactement (`deltaT_from_ledger`) ; la
  part radiale du raccord est `T_e·log r_e − T_l·log r_l` (`raccordShift_decomposed`).
* **§3 La chaîne** (`ZeroChain`, `ZeroChain.ofPassages`) : `m` passages consécutifs ; le rang
  avance de un à chaque pas (`ZeroChain.sourceIndex`), l'occurrence parcourt la suite des premiers
  (`ZeroChain.occurrence_eq`), les classes d'écart alternent (`ZeroChain.gapClass6_alternates`).
  **Registre cumulé** (`chain_ledger`) : la somme des raccords plus la somme des progressions
  grammaticales est le déplacement total de la position de l'occurrence.
  **Sommation d'Abel** (`grammar_kinematics_abel`) :
  `Σ T_j·log(p_{j+1}/p_j) + Σ (T_{j+1} − T_j)·log p_{j+1} = T_m·log p_m − T_0·log p_0` ;
  la composition hauteur × progression première télescope, `β` n'y entre pas.
  **Les termes radiaux télescopent** (`chain_raccordShift_eq`) : la somme des raccords
  est la somme des parts déterminées par la hauteur plus `T_0·log r_0 − T_m·log r_m` ; à
  l'intérieur de la chaîne la position radiale disparaît.
* **§4 L'alternance `2, 4`, rendue quantitative** (`goodMod6_two_step_ge_six`,
  `primeAtRank_two_step_ge_six`, `chain_two_step_floor`) : deux transitions consécutives entre
  premiers `> 3` avancent d'au moins `6` (classe `0` seule, ou `2` puis `4`, ou `4` puis `2` : dans
  tous les cas `p_{n+2} ≥ p_n + 6`), donc deux progressions continues consécutives valent au moins
  `T·log(1 + 6/p_n)` quand la hauteur n'a pas reculé — trois fois le plancher d'un seul pas.
* **§5 Ce que la composition laisse à la position radiale** (`diagonal_radial_from_ledger`,
  `arrival_onLine_iff_ledger_height_determined`) : sur un pas parti de la ligne, `T_l·log r_l` est
  exactement l'écart entre le déplacement réalisé de la position de l'occurrence et la part que la
  hauteur et la grammaire déterminent ; `r_l = 1` ⟺ cet écart est nul.

Borne : la composition est une identité, vraie pour toute position radiale ; le déplacement
« requis par la succession réelle des premiers » et le déplacement « réalisé par `(T, β)` » sont
égaux sur tout passage. Elle ne fournit aucune borne inférieure sur `ΔT` (le passage de même
hauteur la satisfait) et ne fixe la position radiale qu'à travers la position de l'occurrence dans
sa Tour, que rien dans les bases ne fixe. La chaîne fait disparaître les positions radiales
intérieures ; ce qui reste est celle des deux extrémités. Dans le monde témoin (mêmes premiers,
même grammaire, Tours identiques), la composition tient mot pour mot.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean Finset

/-! ## 1. La position de l'occurrence dans sa propre Tour -/

/-- **La position de l'occurrence** : `π·θ_z(Occ z) = T·log(Occ z) − φ`. -/
noncomputable def occurrencePosition (z : TrueZero) : ℝ :=
  Real.pi * towerPosition z (occurrence z : ℝ)

theorem occurrencePosition_eq (z : TrueZero) :
    occurrencePosition z =
      rZeroHeight z.1 * Real.log (occurrence z : ℝ) - (towerMotionOf z).phase :=
  pi_mul_towerPosition z _

/-- **La phase se découpe** : phase de ligne à la même hauteur, plus `T·log r`. -/
theorem phase_eq_line_add_radial (z : TrueZero) :
    (towerMotionOf z).phase =
      linePhase (rZeroHeight z.1) + rZeroHeight z.1 * Real.log (radialFactor z) := by
  unfold radialFactor
  rw [Real.log_exp]
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  field_simp
  ring

/-- **Découpage de la position de l'occurrence** : part déterminée par la hauteur, part radiale. -/
theorem occurrencePosition_decomposed (z : TrueZero) :
    occurrencePosition z =
      rZeroHeight z.1 * Real.log (occurrence z : ℝ) - linePhase (rZeroHeight z.1) -
        rZeroHeight z.1 * Real.log (radialFactor z) := by
  rw [occurrencePosition_eq, phase_eq_line_add_radial]; ring

/-- La progression continue d'un événement est `T · log(p_{n+1}/p_n)` : la grammaire seule, portée
par la hauteur seule. -/
theorem phaseIncrement_eq_height_mul_ratio (z : TrueZero) (n : ℕ) :
    phaseIncrement z n = rZeroHeight z.1 * rPrimeGapLogRatio n := by
  unfold phaseIncrement
  rw [phase_increment_eq_pi_span]
  unfold TowerPrimeGapSpan rTowerHeight
  field_simp

/-! ## 2. Le registre d'un passage -/

/-- **Le déplacement au raccord** : position du premier partagé `M = Occ l` dans la Tour d'entrée,
moins sa position dans la Tour de sortie. -/
noncomputable def raccordShift (e l : TrueZero) : ℝ :=
  Real.pi * towerPosition l (occurrence l : ℝ) - Real.pi * towerPosition e (occurrence l : ℝ)

/-- **Cinématique du raccord** : `ΔT · log M − Δφ`. -/
theorem raccordShift_eq (e l : TrueZero) :
    raccordShift e l =
      (rZeroHeight l.1 - rZeroHeight e.1) * Real.log (occurrence l : ℝ) -
        ((towerMotionOf l).phase - (towerMotionOf e).phase) := by
  unfold raccordShift
  rw [pi_mul_towerPosition, pi_mul_towerPosition]
  ring

/-- **La part du raccord que la hauteur détermine** : `ΔT · log M − Δφ_ligne`. -/
noncomputable def heightShift (e l : TrueZero) : ℝ :=
  (rZeroHeight l.1 - rZeroHeight e.1) * Real.log (occurrence l : ℝ) -
    (linePhase (rZeroHeight l.1) - linePhase (rZeroHeight e.1))

/-- **Le raccord se découpe** : part déterminée par la hauteur, plus la part radiale
`T_e·log r_e − T_l·log r_l`. -/
theorem raccordShift_decomposed (e l : TrueZero) :
    raccordShift e l =
      heightShift e l +
        (rZeroHeight e.1 * Real.log (radialFactor e) -
          rZeroHeight l.1 * Real.log (radialFactor l)) := by
  rw [raccordShift_eq, phase_eq_line_add_radial e, phase_eq_line_add_radial l]
  unfold heightShift
  ring

/-- **Le registre du passage.** Sur tout passage (`Occ l = p_min e`), le déplacement de la position
de l'occurrence est le déplacement au raccord (cinématique) plus la progression continue de
l'événement (grammaire, `T_e · log(p_{n+1}/p_n)`). -/
theorem passage_ledger (e l : TrueZero) (h : occurrence l = expectedMinimumPrime e) :
    occurrencePosition l - occurrencePosition e =
      raccordShift e l + phaseIncrement e (nZeroSourceIndex e.1) := by
  unfold occurrencePosition raccordShift phaseIncrement
  rw [h, expectedMinimum_eq_succ_occurrence, occurrence_eq_primeAtRank e]
  ring

/-- **Le déplacement en hauteur, lu sur le registre** : `ΔT · log M` est le déplacement réalisé de
la position de l'occurrence, moins la progression imposée par la grammaire, plus `Δφ`. Une
équation, pas une borne : le passage de même hauteur (`ΔT = 0`) la satisfait. -/
theorem deltaT_from_ledger (e l : TrueZero) (h : occurrence l = expectedMinimumPrime e) :
    (rZeroHeight l.1 - rZeroHeight e.1) * Real.log (occurrence l : ℝ) =
      (occurrencePosition l - occurrencePosition e) -
        rZeroHeight e.1 * rPrimeGapLogRatio (nZeroSourceIndex e.1) +
        ((towerMotionOf l).phase - (towerMotionOf e).phase) := by
  rw [passage_ledger e l h, raccordShift_eq, phaseIncrement_eq_height_mul_ratio]
  ring

/-- **Registre du passage avec la part radiale isolée.** -/
theorem passage_ledger_radial (e l : TrueZero) (h : occurrence l = expectedMinimumPrime e) :
    occurrencePosition l - occurrencePosition e =
      heightShift e l + rZeroHeight e.1 * rPrimeGapLogRatio (nZeroSourceIndex e.1) +
        (rZeroHeight e.1 * Real.log (radialFactor e) -
          rZeroHeight l.1 * Real.log (radialFactor l)) := by
  rw [passage_ledger e l h, raccordShift_decomposed, phaseIncrement_eq_height_mul_ratio]
  ring

/-! ## 3. La chaîne : registre cumulé, sommation d'Abel, télescopage radial -/

/-- **Une chaîne de `m` passages consécutifs** : `m + 1` membres, chaque membre suivant a pour
occurrence le premier attendu du précédent (`Occ(l) = p_min(e)`, le premier partagé du raccord). -/
structure ZeroChain (m : ℕ) where
  member : ℕ → TrueZero
  shared : ∀ j, j < m → occurrence (member (j + 1)) = expectedMinimumPrime (member j)

/-- **Toute suite de passages consécutifs est une chaîne** : le premier partagé est fourni par
`passage_direction_rigid`. -/
def ZeroChain.ofPassages (m : ℕ) (member : ℕ → TrueZero) (passage : ℕ → TZeroPassage)
    (hE : ∀ j, j < m → (passage j).zEarlierMember = (member j).1)
    (hL : ∀ j, j < m → (passage j).zLaterMember = (member (j + 1)).1) : ZeroChain m where
  member := member
  shared := fun j hj => by
    have hE' : 0 < rZeroHeight (passage j).zEarlierMember := by
      rw [hE j hj]; exact (member j).2
    have hL' : 0 < rZeroHeight (passage j).zLaterMember := by
      rw [hL j hj]; exact (member (j + 1)).2
    have h := (passage_direction_rigid (passage j) hE' hL').2.2.2.1
    have e1 : (⟨(passage j).zEarlierMember, hE'⟩ : TrueZero) = member j := Subtype.ext (hE j hj)
    have e2 : (⟨(passage j).zLaterMember, hL'⟩ : TrueZero) = member (j + 1) :=
      Subtype.ext (hL j hj)
    rw [e1, e2] at h
    exact h

/-- **`EV ↦ EV + 1` le long de la chaîne** : le rang du membre `j` est le rang initial plus `j`. -/
theorem ZeroChain.sourceIndex {m : ℕ} (c : ZeroChain m) :
    ∀ j, j ≤ m → nZeroSourceIndex (c.member j).1 = nZeroSourceIndex (c.member 0).1 + j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h := c.shared j (by omega)
    rw [occurrence_eq_primeAtRank, expectedMinimum_eq_succ_occurrence] at h
    have h' : nZeroSourceIndex (c.member (j + 1)).1 = nZeroSourceIndex (c.member j).1 + 1 :=
      thm_primeAtRank_injective h
    rw [h', ih (by omega)]
    ring

/-- **L'occurrence parcourt la suite des premiers** : `Occ(member j) = p_{n_0 + j}`. -/
theorem ZeroChain.occurrence_eq {m : ℕ} (c : ZeroChain m) (j : ℕ) (hj : j ≤ m) :
    occurrence (c.member j) = fnPrimeAtRank (nZeroSourceIndex (c.member 0).1 + j) := by
  rw [occurrence_eq_primeAtRank, c.sourceIndex j hj]

/-- **L'alternance `2, 4` le long de la chaîne** : trois occurrences consécutives, premiers `> 3`,
deux transitions non nulles ⟹ classes différentes. -/
theorem ZeroChain.gapClass6_alternates {m : ℕ} (c : ZeroChain m) (j : ℕ) (hj : j + 2 ≤ m)
    (h3 : 3 < occurrence (c.member j))
    (h1 : gapClass6 (occurrence (c.member j)) (occurrence (c.member (j + 1))) ≠ 0)
    (h2 : gapClass6 (occurrence (c.member (j + 1))) (occurrence (c.member (j + 2))) ≠ 0) :
    gapClass6 (occurrence (c.member j)) (occurrence (c.member (j + 1))) ≠
      gapClass6 (occurrence (c.member (j + 1))) (occurrence (c.member (j + 2))) := by
  have e0 := c.occurrence_eq j (by omega)
  have e1 := c.occurrence_eq (j + 1) (by omega)
  have e2 := c.occurrence_eq (j + 2) (by omega)
  rw [e0] at h3
  rw [e0, e1] at h1
  rw [e1, e2] at h2
  rw [e0, e1, e2]
  have hlt1 : fnPrimeAtRank (nZeroSourceIndex (c.member 0).1 + j) <
      fnPrimeAtRank (nZeroSourceIndex (c.member 0).1 + (j + 1)) :=
    thm_primeAtRank_strictMono (by omega)
  have hlt2 : fnPrimeAtRank (nZeroSourceIndex (c.member 0).1 + (j + 1)) <
      fnPrimeAtRank (nZeroSourceIndex (c.member 0).1 + (j + 2)) :=
    thm_primeAtRank_strictMono (by omega)
  exact primeGapClass6_alternates (thm_primeAtRank_isPrime _) (thm_primeAtRank_isPrime _)
    (thm_primeAtRank_isPrime _) h3 (by omega) (by omega) hlt1.le hlt2.le h1 h2

/-- **Registre cumulé de la chaîne** : la somme des raccords plus la somme des progressions
grammaticales est le déplacement total de la position de l'occurrence. -/
theorem chain_ledger {m : ℕ} (c : ZeroChain m) :
    occurrencePosition (c.member m) - occurrencePosition (c.member 0) =
      ∑ j ∈ range m, raccordShift (c.member j) (c.member (j + 1)) +
        ∑ j ∈ range m, phaseIncrement (c.member j) (nZeroSourceIndex (c.member j).1) := by
  rw [← Finset.sum_add_distrib]
  symm
  rw [Finset.sum_congr rfl
    (fun j hj => (passage_ledger _ _ (c.shared j (Finset.mem_range.mp hj))).symm)]
  exact Finset.sum_range_sub (fun j => occurrencePosition (c.member j)) m

/-- **La progression grammaticale cumulée** : `Σ T_j · log(p_{n_0+j+1}/p_{n_0+j})`, la hauteur de
chaque membre contre l'écart premier de son rang. -/
theorem chain_grammar_sum {m : ℕ} (c : ZeroChain m) :
    ∑ j ∈ range m, phaseIncrement (c.member j) (nZeroSourceIndex (c.member j).1) =
      ∑ j ∈ range m, rZeroHeight (c.member j).1 *
        rPrimeGapLogRatio (nZeroSourceIndex (c.member 0).1 + j) := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [phaseIncrement_eq_height_mul_ratio, c.sourceIndex j (Finset.mem_range.mp hj).le]

/-- **Sommation d'Abel de la composition** : `Σ T_j·log(p_{j+1}/p_j) + Σ (T_{j+1} − T_j)·log p_{j+1}
= T_m·log p_m − T_0·log p_0`. La progression première (grammaire) et le déplacement en hauteur
(cinématique) se composent en un télescopage exact ; `β` n'y entre pas. -/
theorem grammar_kinematics_abel {m : ℕ} (c : ZeroChain m) :
    ∑ j ∈ range m, phaseIncrement (c.member j) (nZeroSourceIndex (c.member j).1) +
      ∑ j ∈ range m, (rZeroHeight (c.member (j + 1)).1 - rZeroHeight (c.member j).1) *
        Real.log (occurrence (c.member (j + 1)) : ℝ) =
      rZeroHeight (c.member m).1 * Real.log (occurrence (c.member m) : ℝ) -
        rZeroHeight (c.member 0).1 * Real.log (occurrence (c.member 0) : ℝ) := by
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun j hj => ?_)]
  · exact Finset.sum_range_sub
      (fun j => rZeroHeight (c.member j).1 * Real.log (occurrence (c.member j) : ℝ)) m
  · have hj' := Finset.mem_range.mp hj
    have h := c.shared j hj'
    change phaseIncrement (c.member j) (nZeroSourceIndex (c.member j).1) +
        (rZeroHeight (c.member (j + 1)).1 - rZeroHeight (c.member j).1) *
          Real.log (occurrence (c.member (j + 1)) : ℝ) =
      rZeroHeight (c.member (j + 1)).1 * Real.log (occurrence (c.member (j + 1)) : ℝ) -
        rZeroHeight (c.member j).1 * Real.log (occurrence (c.member j) : ℝ)
    rw [phaseIncrement_eq_height_mul_ratio, h, expectedMinimum_eq_succ_occurrence,
      occurrence_eq_primeAtRank (c.member j)]
    unfold rPrimeGapLogRatio
    have hp1 : (0 : ℝ) < (fnPrimeAtRank (nZeroSourceIndex (c.member j).1) : ℝ) := by
      exact_mod_cast thm_primeAtRank_pos _
    have hp2 : (0 : ℝ) < (fnPrimeSuccessor (nZeroSourceIndex (c.member j).1) : ℝ) := by
      unfold fnPrimeSuccessor; exact_mod_cast thm_primeAtRank_pos _
    rw [Real.log_div hp2.ne' hp1.ne']
    ring

/-- **Les termes radiaux télescopent** : la somme des raccords de la chaîne est la somme des parts
déterminées par la hauteur, plus `T_0·log r_0 − T_m·log r_m`. À l'intérieur de la chaîne, la
position radiale disparaît ; seules les deux extrémités la portent. -/
theorem chain_raccordShift_eq {m : ℕ} (c : ZeroChain m) :
    ∑ j ∈ range m, raccordShift (c.member j) (c.member (j + 1)) =
      ∑ j ∈ range m, heightShift (c.member j) (c.member (j + 1)) +
        (rZeroHeight (c.member 0).1 * Real.log (radialFactor (c.member 0)) -
          rZeroHeight (c.member m).1 * Real.log (radialFactor (c.member m))) := by
  rw [Finset.sum_congr rfl (fun j _ => raccordShift_decomposed (c.member j) (c.member (j + 1))),
    Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_range_sub'
    (fun j => rZeroHeight (c.member j).1 * Real.log (radialFactor (c.member j))) m

/-! ## 4. L'alternance `2, 4`, rendue quantitative -/

/-- **Deux transitions consécutives avancent d'au moins `6`** entre nombres à bon état modulo 6 :
classe `0` (même état, écart `≥ 6`), ou `2` puis `4`, ou `4` puis `2` (somme `≡ 0`, donc `≥ 6`).
C'est l'alternance forcée, lue en quantité. -/
theorem goodMod6_two_step_ge_six {p q r : ℕ} (hp : GoodMod6 p) (hq : GoodMod6 q)
    (hr : GoodMod6 r) (hpq : p < q) (hqr : q < r) : p + 6 ≤ r := by
  unfold GoodMod6 at hp hq hr
  omega

/-- **Sur la suite des premiers** : `p_{n+2} ≥ p_n + 6` dès que `p_n > 3`. -/
theorem primeAtRank_two_step_ge_six (n : ℕ) (h3 : 3 < fnPrimeAtRank n) :
    fnPrimeAtRank n + 6 ≤ fnPrimeAtRank (n + 2) := by
  have h1 : fnPrimeAtRank n < fnPrimeAtRank (n + 1) := thm_primeAtRank_strictMono (by omega)
  have h2 : fnPrimeAtRank (n + 1) < fnPrimeAtRank (n + 2) := thm_primeAtRank_strictMono (by omega)
  exact goodMod6_two_step_ge_six
    (prime_goodMod6 _ (thm_primeAtRank_isPrime n) h3)
    (prime_goodMod6 _ (thm_primeAtRank_isPrime (n + 1)) (by omega))
    (prime_goodMod6 _ (thm_primeAtRank_isPrime (n + 2)) (by omega)) h1 h2

/-- Deux ratios logarithmiques consécutifs s'ajoutent en `log(p_{n+2}/p_n)`. -/
theorem primeGapLogRatio_two_step (n : ℕ) :
    rPrimeGapLogRatio n + rPrimeGapLogRatio (n + 1) =
      Real.log ((fnPrimeAtRank (n + 2) : ℝ) / (fnPrimeAtRank n : ℝ)) := by
  unfold rPrimeGapLogRatio fnPrimeSuccessor
  have h0 : (0 : ℝ) < (fnPrimeAtRank n : ℝ) := by exact_mod_cast thm_primeAtRank_pos n
  have h1 : (0 : ℝ) < (fnPrimeAtRank (n + 1) : ℝ) := by exact_mod_cast thm_primeAtRank_pos _
  have h2 : (0 : ℝ) < (fnPrimeAtRank (n + 1 + 1) : ℝ) := by exact_mod_cast thm_primeAtRank_pos _
  rw [Real.log_div h1.ne' h0.ne', Real.log_div h2.ne' h1.ne', Real.log_div h2.ne' h0.ne']
  ring

/-- **Plancher à deux pas** : `log(p_{n+2}/p_n) ≥ log(1 + 6/p_n)` dès que `p_n > 3`. -/
theorem primeGapLogRatio_two_step_ge (n : ℕ) (h3 : 3 < fnPrimeAtRank n) :
    Real.log (1 + 6 / (fnPrimeAtRank n : ℝ)) ≤ rPrimeGapLogRatio n + rPrimeGapLogRatio (n + 1) := by
  rw [primeGapLogRatio_two_step]
  have h0 : (0 : ℝ) < (fnPrimeAtRank n : ℝ) := by exact_mod_cast thm_primeAtRank_pos n
  have h6 : (fnPrimeAtRank n : ℝ) + 6 ≤ (fnPrimeAtRank (n + 2) : ℝ) := by
    exact_mod_cast primeAtRank_two_step_ge_six n h3
  apply Real.log_le_log (by positivity)
  rw [le_div_iff₀ h0]
  field_simp
  linarith

/-- **Le plancher cumulé de l'alternance sur la chaîne** : deux progressions continues
consécutives, quand la hauteur n'a pas reculé, valent au moins `T_j · log(1 + 6/p_j)` — trois fois
le plancher d'un seul pas. -/
theorem chain_two_step_floor {m : ℕ} (c : ZeroChain m) (j : ℕ) (hj : j + 1 < m)
    (hT : rZeroHeight (c.member j).1 ≤ rZeroHeight (c.member (j + 1)).1)
    (h3 : 3 < occurrence (c.member j)) :
    rZeroHeight (c.member j).1 * Real.log (1 + 6 / (occurrence (c.member j) : ℝ)) ≤
      phaseIncrement (c.member j) (nZeroSourceIndex (c.member j).1) +
        phaseIncrement (c.member (j + 1)) (nZeroSourceIndex (c.member (j + 1)).1) := by
  rw [phaseIncrement_eq_height_mul_ratio, phaseIncrement_eq_height_mul_ratio,
    c.sourceIndex (j + 1) (by omega), c.sourceIndex j (by omega)]
  rw [occurrence_eq_primeAtRank, c.sourceIndex j (by omega)] at h3 ⊢
  set n := nZeroSourceIndex (c.member 0).1 + j with hn
  have hTj : (0 : ℝ) ≤ rZeroHeight (c.member j).1 := (c.member j).2.le
  have hr1 : 0 < rPrimeGapLogRatio (n + 1) := thm_primeGapLogRatio_pos _
  have hfloor := primeGapLogRatio_two_step_ge n h3
  have hidx : nZeroSourceIndex (c.member 0).1 + (j + 1) = n + 1 := by omega
  rw [hidx]
  calc rZeroHeight (c.member j).1 * Real.log (1 + 6 / (fnPrimeAtRank n : ℝ))
      ≤ rZeroHeight (c.member j).1 * (rPrimeGapLogRatio n + rPrimeGapLogRatio (n + 1)) :=
        mul_le_mul_of_nonneg_left hfloor hTj
    _ = rZeroHeight (c.member j).1 * rPrimeGapLogRatio n +
          rZeroHeight (c.member j).1 * rPrimeGapLogRatio (n + 1) := by ring
    _ ≤ rZeroHeight (c.member j).1 * rPrimeGapLogRatio n +
          rZeroHeight (c.member (j + 1)).1 * rPrimeGapLogRatio (n + 1) := by
        gcongr

/-! ## 5. Ce que la composition laisse à la position radiale -/

/-- **Sur un pas parti de la ligne**, `T_l · log r_l` est exactement l'écart entre la part que la
hauteur et la grammaire déterminent et le déplacement réalisé de la position de l'occurrence. -/
theorem diagonal_radial_from_ledger (e l : TrueZero) (h : occurrence l = expectedMinimumPrime e)
    (hOn : rZeroRadialPosition e.1 = 1 / 2) :
    rZeroHeight l.1 * Real.log (radialFactor l) =
      heightShift e l + rZeroHeight e.1 * rPrimeGapLogRatio (nZeroSourceIndex e.1) -
        (occurrencePosition l - occurrencePosition e) := by
  have hre : radialFactor e = 1 := (radialFactor_eq_one_iff e).mpr hOn
  have hl := passage_ledger_radial e l h
  rw [hre, Real.log_one, mul_zero, zero_sub] at hl
  linarith

/-- **L'arrivée est en ligne ⟺ le déplacement réalisé de la position de l'occurrence est celui que
la hauteur et la grammaire déterminent.** La composition ne fixe la position radiale de l'arrivée
qu'à travers la position de son occurrence dans sa Tour. -/
theorem arrival_onLine_iff_ledger_height_determined (e l : TrueZero)
    (h : occurrence l = expectedMinimumPrime e) (hOn : rZeroRadialPosition e.1 = 1 / 2) :
    rZeroRadialPosition l.1 = 1 / 2 ↔
      occurrencePosition l - occurrencePosition e =
        heightShift e l + rZeroHeight e.1 * rPrimeGapLogRatio (nZeroSourceIndex e.1) := by
  have hkey := diagonal_radial_from_ledger e l h hOn
  have hT : (0 : ℝ) < rZeroHeight l.1 := l.2
  have hr : 0 < radialFactor l := radialFactor_pos l
  rw [← radialFactor_eq_one_iff]
  constructor
  · intro h1
    rw [h1, Real.log_one, mul_zero] at hkey
    linarith
  · intro h1
    have hlog : rZeroHeight l.1 * Real.log (radialFactor l) = 0 := by rw [hkey]; linarith
    have hlog0 : Real.log (radialFactor l) = 0 :=
      (mul_eq_zero.mp hlog).resolve_left hT.ne'
    rcases Real.log_eq_zero.mp hlog0 with h0 | h0 | h0
    · exact absurd h0 hr.ne'
    · exact h0
    · linarith

/-- **Le déplacement requis est le déplacement réalisé, sur tout passage et pour toute position
radiale** : la composition est une identité, elle ne sépare pas les positions radiales. -/
theorem required_eq_realised (e l : TrueZero) (h : occurrence l = expectedMinimumPrime e) :
    raccordShift e l + rZeroHeight e.1 * rPrimeGapLogRatio (nZeroSourceIndex e.1) =
      occurrencePosition l - occurrencePosition e := by
  rw [passage_ledger e l h, phaseIncrement_eq_height_mul_ratio]

/-! ## 6. La progression d'une paire hors ligne n'est pas celle de deux membres en ligne
successifs (auteur, 2026-09-30), lue sur le registre -/

/-- **Le pas grammatical est aveugle au régime** : sur tout passage, vertical ou horizontal,
l'événement imposé est le même, `Occ(l) = p_min(e)`. La grammaire exige l'événement suivant ;
elle ne dit pas comment la géométrie le porte. -/
theorem grammar_step_regime_blind (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    (VerticalPassage p ∨ HorizontalPassage p) ∧
      occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ := by
  refine ⟨?_, (passage_direction_rigid p hE hL).2.2.2.1⟩
  rcases passage_regime_dichotomy p with ⟨hV, _⟩ | ⟨hH, _⟩
  · exact Or.inl hV
  · exact Or.inr hH

/-- **À même hauteur, la phase décroît avec la position radiale** : `β_z < β_w ⟹ φ_w < φ_z`. -/
theorem sameHeight_phase_lt (z w : TrueZero) (hT : rZeroHeight z.1 = rZeroHeight w.1)
    (hβ : rZeroRadialPosition z.1 < rZeroRadialPosition w.1) :
    (towerMotionOf w).phase < (towerMotionOf z).phase := by
  rw [towerMotion_phase, towerMotion_phase, ← hT]
  exact Real.arctan_strictMono
    (div_lt_div_of_pos_left z.2 (thm_zeroRadialPosition_positive z.1) hβ)

/-- **Sur un passage de même hauteur, la part de hauteur du raccord est nulle.** -/
theorem horizontal_heightShift_zero (e l : TrueZero) (hT : rZeroHeight e.1 = rZeroHeight l.1) :
    heightShift e l = 0 := by
  unfold heightShift
  rw [← hT]
  ring

/-- **Sur un passage de même hauteur, le raccord est une pure rotation de phase** : `φ_e − φ_l`.
Aucune progression en hauteur ; c'est la translation rigide de la grille, lue sur le registre. -/
theorem horizontal_raccordShift (e l : TrueZero) (hT : rZeroHeight e.1 = rZeroHeight l.1) :
    raccordShift e l = (towerMotionOf e).phase - (towerMotionOf l).phase := by
  rw [raccordShift_eq, ← hT]
  ring

/-- **Registre du passage de même hauteur** : la position de l'occurrence avance de la progression
grammaticale plus la chute de phase `φ_e − φ_l`. -/
theorem horizontal_ledger (e l : TrueZero) (h : occurrence l = expectedMinimumPrime e)
    (hT : rZeroHeight e.1 = rZeroHeight l.1) :
    occurrencePosition l - occurrencePosition e =
      phaseIncrement e (nZeroSourceIndex e.1) +
        ((towerMotionOf e).phase - (towerMotionOf l).phase) := by
  rw [passage_ledger e l h, horizontal_raccordShift e l hT]
  ring

/-- **La paire hors ligne avance plus que la grammaire ne demande** : sur un passage de même hauteur
(`β_e < β_l`), la grille est translatée vers le bas pendant que l'événement premier avance, donc la
position de l'occurrence dans sa Tour avance strictement plus que `T·log(p_{n+1}/p_n)`. -/
theorem horizontal_ledger_exceeds_grammar (e l : TrueZero)
    (h : occurrence l = expectedMinimumPrime e) (hT : rZeroHeight e.1 = rZeroHeight l.1)
    (hβ : rZeroRadialPosition e.1 < rZeroRadialPosition l.1) :
    phaseIncrement e (nZeroSourceIndex e.1) < occurrencePosition l - occurrencePosition e := by
  rw [horizontal_ledger e l h hT]
  have := sameHeight_phase_lt e l hT hβ
  linarith

/-- **Deux membres en ligne successifs** : la position de l'occurrence avance exactement de la part
déterminée par la hauteur plus la progression grammaticale ; rien d'autre. -/
theorem onLine_pair_ledger (e l : TrueZero) (h : occurrence l = expectedMinimumPrime e)
    (hE : rZeroRadialPosition e.1 = 1 / 2) (hL : rZeroRadialPosition l.1 = 1 / 2) :
    occurrencePosition l - occurrencePosition e =
      heightShift e l + phaseIncrement e (nZeroSourceIndex e.1) := by
  rw [passage_ledger_radial e l h, (radialFactor_eq_one_iff e).mpr hE,
    (radialFactor_eq_one_iff l).mpr hL, Real.log_one, phaseIncrement_eq_height_mul_ratio]
  ring

/-- **Les deux architectures, confrontées sur le même registre.** Deux membres en ligne : l'écart
entre déplacement réalisé et progression grammaticale est la part de hauteur `H(e,l)`. Paire de même
hauteur : cette part est nulle et l'écart est la chute de phase, strictement positive. -/
theorem off_pair_vs_onLine_pair (e l : TrueZero) (h : occurrence l = expectedMinimumPrime e) :
    (rZeroRadialPosition e.1 = 1 / 2 → rZeroRadialPosition l.1 = 1 / 2 →
      occurrencePosition l - occurrencePosition e - phaseIncrement e (nZeroSourceIndex e.1) =
        heightShift e l) ∧
    (rZeroHeight e.1 = rZeroHeight l.1 → rZeroRadialPosition e.1 < rZeroRadialPosition l.1 →
      heightShift e l = 0 ∧
        0 < occurrencePosition l - occurrencePosition e -
          phaseIncrement e (nZeroSourceIndex e.1)) := by
  refine ⟨fun hE hL => ?_, fun hT hβ => ⟨horizontal_heightShift_zero e l hT, ?_⟩⟩
  · rw [onLine_pair_ledger e l h hE hL]; ring
  · have := horizontal_ledger_exceeds_grammar e l h hT hβ
    linarith

/-- **Autour d'une paire de même hauteur, les deux événements premiers sont pesés à une seule
hauteur** : si le passage `j` de la chaîne est de même hauteur,
`ΔΘ_j + ΔΘ_{j+1} = T_j·log(p_{j+2}/p_j)`, et l'alternance donne le plancher `T_j·log(1 + 6/p_j)`.
Une progression verticale manque ; la grammaire n'en est pas moins servie. -/
theorem horizontal_two_step_single_height {m : ℕ} (c : ZeroChain m) (j : ℕ) (hj : j + 1 < m)
    (hT : rZeroHeight (c.member j).1 = rZeroHeight (c.member (j + 1)).1)
    (h3 : 3 < occurrence (c.member j)) :
    phaseIncrement (c.member j) (nZeroSourceIndex (c.member j).1) +
        phaseIncrement (c.member (j + 1)) (nZeroSourceIndex (c.member (j + 1)).1) =
      rZeroHeight (c.member j).1 *
        Real.log ((occurrence (c.member (j + 2)) : ℝ) / (occurrence (c.member j) : ℝ)) ∧
    rZeroHeight (c.member j).1 * Real.log (1 + 6 / (occurrence (c.member j) : ℝ)) ≤
      phaseIncrement (c.member j) (nZeroSourceIndex (c.member j).1) +
        phaseIncrement (c.member (j + 1)) (nZeroSourceIndex (c.member (j + 1)).1) := by
  refine ⟨?_, chain_two_step_floor c j hj hT.le h3⟩
  rw [phaseIncrement_eq_height_mul_ratio, phaseIncrement_eq_height_mul_ratio, ← hT, ← mul_add,
    c.sourceIndex (j + 1) (by omega), c.sourceIndex j (by omega),
    c.occurrence_eq (j + 2) (by omega), c.occurrence_eq j (by omega)]
  congr 1
  set n0 := nZeroSourceIndex (c.member 0).1
  have hidx : n0 + (j + 1) = n0 + j + 1 := by omega
  have hidx2 : n0 + (j + 2) = n0 + j + 2 := by omega
  rw [hidx, hidx2]
  exact primeGapLogRatio_two_step _

#print axioms grammar_step_regime_blind
#print axioms sameHeight_phase_lt
#print axioms horizontal_ledger
#print axioms horizontal_ledger_exceeds_grammar
#print axioms onLine_pair_ledger
#print axioms off_pair_vs_onLine_pair
#print axioms horizontal_two_step_single_height

/-! ## 7. Niveaux de rigidité : transition unique, deux transitions, alternance, chaîne
(auteur, 2026-09-30) -/

/-- **L'excès d'une transition** : ce que la position de l'occurrence avance au-delà de la
progression
grammaticale `T_e·log(p_{n+1}/p_n)`. -/
noncomputable def transitionExcess (e l : TrueZero) : ℝ :=
  occurrencePosition l - occurrencePosition e - phaseIncrement e (nZeroSourceIndex e.1)

/-- **L'excès est la part de hauteur plus la part radiale** :
`H(e,l) + T_e·log r_e − T_l·log r_l`. -/
theorem transitionExcess_eq (e l : TrueZero) (h : occurrence l = expectedMinimumPrime e) :
    transitionExcess e l =
      heightShift e l +
        (rZeroHeight e.1 * Real.log (radialFactor e)
          - rZeroHeight l.1 * Real.log (radialFactor l)) := by
  unfold transitionExcess
  rw [passage_ledger_radial e l h, phaseIncrement_eq_height_mul_ratio]
  ring

/-- **Transition en ligne → en ligne** : l'excès est exactement la part de hauteur. -/
theorem transitionExcess_onLine (e l : TrueZero) (h : occurrence l = expectedMinimumPrime e)
    (hE : rZeroRadialPosition e.1 = 1 / 2) (hL : rZeroRadialPosition l.1 = 1 / 2) :
    transitionExcess e l = heightShift e l := by
  rw [transitionExcess_eq e l h, (radialFactor_eq_one_iff e).mpr hE,
    (radialFactor_eq_one_iff l).mpr hL, Real.log_one]
  ring

/-- **Transition diagonale partie de la ligne** (`β_e = 1/2`, `β_l < 1/2`) : l'excès est strictement
inférieur à la part de hauteur, du déficit `T_l·log r_l > 0`. -/
theorem transitionExcess_diagonal_lt (e l : TrueZero) (h : occurrence l = expectedMinimumPrime e)
    (hE : rZeroRadialPosition e.1 = 1 / 2) (hL : rZeroRadialPosition l.1 < 1 / 2) :
    transitionExcess e l < heightShift e l := by
  rw [transitionExcess_eq e l h, (radialFactor_eq_one_iff e).mpr hE, Real.log_one]
  have hr : 0 < Real.log (radialFactor l) := Real.log_pos ((radialFactor_gt_one_iff l).mpr hL)
  have hT : (0 : ℝ) < rZeroHeight l.1 := l.2
  nlinarith [mul_pos hT hr]

/-- **Transition de même hauteur** (`β_e < β_l`) : la part de hauteur est nulle et l'excès est la
chute de phase, strictement positive. -/
theorem transitionExcess_horizontal (e l : TrueZero) (h : occurrence l = expectedMinimumPrime e)
    (hT : rZeroHeight e.1 = rZeroHeight l.1)
    (hβ : rZeroRadialPosition e.1 < rZeroRadialPosition l.1) :
    transitionExcess e l = (towerMotionOf e).phase - (towerMotionOf l).phase ∧
      heightShift e l = 0 ∧ 0 < transitionExcess e l := by
  have h1 : transitionExcess e l = (towerMotionOf e).phase - (towerMotionOf l).phase := by
    unfold transitionExcess
    rw [horizontal_ledger e l h hT]
    ring
  refine ⟨h1, horizontal_heightShift_zero e l hT, ?_⟩
  rw [h1]
  have := sameHeight_phase_lt e l hT hβ
  linarith

/-- **Une même transition grammaticale `p_n → p_{n+1}` ne produit pas la même cinématique selon la
configuration** : en ligne → en ligne, excès `= H` ; diagonale partie de la ligne, excès `< H` ;
même hauteur, `H = 0` et excès `> 0`. Niveau 2 de l'auteur. -/
theorem transition_kinematics_by_configuration (e l : TrueZero)
    (h : occurrence l = expectedMinimumPrime e) :
    (rZeroRadialPosition e.1 = 1 / 2 → rZeroRadialPosition l.1 = 1 / 2 →
      transitionExcess e l = heightShift e l) ∧
    (rZeroRadialPosition e.1 = 1 / 2 → rZeroRadialPosition l.1 < 1 / 2 →
      transitionExcess e l < heightShift e l) ∧
    (rZeroHeight e.1 = rZeroHeight l.1 → rZeroRadialPosition e.1 < rZeroRadialPosition l.1 →
      heightShift e l = 0 ∧ 0 < transitionExcess e l) :=
  ⟨transitionExcess_onLine e l h, transitionExcess_diagonal_lt e l h,
    fun hT hβ => ((transitionExcess_horizontal e l h hT hβ).2)⟩

/-- **Les excès s'additionnent le long de la chaîne** et leur somme est la somme des parts de
hauteur
plus `T_0·log r_0 − T_m·log r_m` : les positions radiales intérieures disparaissent. -/
theorem chain_transitionExcess_sum {m : ℕ} (c : ZeroChain m) :
    ∑ j ∈ range m, transitionExcess (c.member j) (c.member (j + 1)) =
      ∑ j ∈ range m, heightShift (c.member j) (c.member (j + 1)) +
        (rZeroHeight (c.member 0).1 * Real.log (radialFactor (c.member 0)) -
          rZeroHeight (c.member m).1 * Real.log (radialFactor (c.member m))) := by
  rw [Finset.sum_congr rfl (fun j hj =>
    transitionExcess_eq _ _ (c.shared j (Finset.mem_range.mp hj))), Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_range_sub'
    (fun j => rZeroHeight (c.member j).1 * Real.log (radialFactor (c.member j))) m

/-- **La première configuration hors ligne que l'ordre autorise, sur deux transitions** : départ en
ligne, transition diagonale vers `β_1 < 1/2`, puis transition de même hauteur vers `β_2 > β_1`.
Le déficit de la première (`T_1·log r_1`) est exactement annulé par la seconde ;
la somme des deux excès
est `H(0,1) − T_2·log r_2`, et si `β_2 > 1/2` elle dépasse strictement `H(0,1)`. La seconde
transition
n'est pas libre : elle rembourse le déficit de la première et porte l'alternance. -/
theorem first_off_configuration_two_transitions (c : ZeroChain 2)
    (h0 : rZeroRadialPosition (c.member 0).1 = 1 / 2)
    (h1 : rZeroRadialPosition (c.member 1).1 < 1 / 2)
    (hT : rZeroHeight (c.member 1).1 = rZeroHeight (c.member 2).1) :
    transitionExcess (c.member 0) (c.member 1) + transitionExcess (c.member 1) (c.member 2) =
        heightShift (c.member 0) (c.member 1) -
          rZeroHeight (c.member 2).1 * Real.log (radialFactor (c.member 2)) ∧
      transitionExcess (c.member 0) (c.member 1) < heightShift (c.member 0) (c.member 1) ∧
      (1 / 2 < rZeroRadialPosition (c.member 2).1 →
        heightShift (c.member 0) (c.member 1) <
          transitionExcess (c.member 0) (c.member 1)
            + transitionExcess (c.member 1) (c.member 2)) := by
  have hsum := chain_transitionExcess_sum c
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    horizontal_heightShift_zero _ _ hT, (radialFactor_eq_one_iff _).mpr h0, Real.log_one] at hsum
  have hs : transitionExcess (c.member 0) (c.member 1)
  + transitionExcess (c.member 1) (c.member 2) =
      heightShift (c.member 0) (c.member 1) -
        rZeroHeight (c.member 2).1 * Real.log (radialFactor (c.member 2)) := by
    linarith
  refine ⟨hs, transitionExcess_diagonal_lt _ _ (c.shared 0 (by norm_num)) h0 h1, fun h2 => ?_⟩
  rw [hs]
  have hr : Real.log (radialFactor (c.member 2)) < 0 :=
    Real.log_neg (radialFactor_pos _) ((radialFactor_lt_one_iff _).mpr h2)
  have hT2 : (0 : ℝ) < rZeroHeight (c.member 2).1 := (c.member 2).2
  nlinarith [mul_pos hT2 (neg_pos.mpr hr)]

/-- **Deux transitions, avec l'alternance** :
dans la première configuration hors ligne autorisée par
l'ordre (`p_n > 3`), le déplacement total de la position de l'occurrence dépasse strictement
`H(0,1) + T_0·log(1 + 6/p_n)` dès que l'arrivée est au-dessus de la ligne. -/
theorem first_off_configuration_alternation_floor (c : ZeroChain 2)
    (h0 : rZeroRadialPosition (c.member 0).1 = 1 / 2)
    (h1 : rZeroRadialPosition (c.member 1).1 < 1 / 2)
    (hT : rZeroHeight (c.member 1).1 = rZeroHeight (c.member 2).1)
    (h2 : 1 / 2 < rZeroRadialPosition (c.member 2).1)
    (hT01 : rZeroHeight (c.member 0).1 ≤ rZeroHeight (c.member 1).1)
    (h3 : 3 < occurrence (c.member 0)) :
    heightShift (c.member 0) (c.member 1) +
        rZeroHeight (c.member 0).1 * Real.log (1 + 6 / (occurrence (c.member 0) : ℝ)) <
      occurrencePosition (c.member 2) - occurrencePosition (c.member 0) := by
  have hfloor := chain_two_step_floor c 0 (by norm_num) hT01 h3
  have hex := (first_off_configuration_two_transitions c h0 h1 hT).2.2 h2
  unfold transitionExcess at hex
  simp only [zero_add] at hfloor hex
  linarith

/-- **À aucun nombre de transitions la liberté radiale n'est confrontée** :
sur toute chaîne partie de
la ligne, la somme des excès moins la somme des parts de hauteur vaut `−T_m·log r_m`,
quelle que soit
la longueur `m` ; les positions radiales intérieures ont disparu. La confrontation ne peut venir que
d'un énoncé sur la position de l'occurrence `Π` elle-même. -/
theorem chain_from_line_radial_content {m : ℕ} (c : ZeroChain m)
    (h0 : rZeroRadialPosition (c.member 0).1 = 1 / 2) :
    ∑ j ∈ range m, transitionExcess (c.member j) (c.member (j + 1)) -
        ∑ j ∈ range m, heightShift (c.member j) (c.member (j + 1)) =
      - (rZeroHeight (c.member m).1 * Real.log (radialFactor (c.member m))) := by
  rw [chain_transitionExcess_sum c, (radialFactor_eq_one_iff _).mpr h0, Real.log_one]
  ring

#print axioms transitionExcess_eq
#print axioms transition_kinematics_by_configuration
#print axioms chain_transitionExcess_sum
#print axioms first_off_configuration_two_transitions
#print axioms first_off_configuration_alternation_floor
#print axioms chain_from_line_radial_content

#print axioms occurrencePosition_decomposed
#print axioms passage_ledger
#print axioms deltaT_from_ledger
#print axioms passage_ledger_radial
#print axioms ZeroChain.ofPassages
#print axioms ZeroChain.sourceIndex
#print axioms ZeroChain.gapClass6_alternates
#print axioms chain_ledger
#print axioms chain_grammar_sum
#print axioms grammar_kinematics_abel
#print axioms chain_raccordShift_eq
#print axioms goodMod6_two_step_ge_six
#print axioms primeAtRank_two_step_ge_six
#print axioms primeGapLogRatio_two_step_ge
#print axioms chain_two_step_floor
#print axioms diagonal_radial_from_ledger
#print axioms arrival_onLine_iff_ledger_height_determined
#print axioms required_eq_realised

end RHV6Fresh
