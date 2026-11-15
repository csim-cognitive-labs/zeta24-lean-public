/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ChangePredictor

/-!
# RHV6Fresh — la flèche entre deux événements canoniques successifs (auteur, 2026-10-01)

Correction de l'auteur : « c'est E140 qui avait correctement isolé le problème : les mécanismes
connus au départ engagé ont une composante radiale nulle, mais nous n'avons pas encore démontré que
la transition conserve cette nullité. La piste course / fonction réelle / comptage de fenêtre n'est
pas confirmée comme bonne démarche. Le travail revient exclusivement à
`(Tour_n, p_n, EV_n, β_n = 1/2) ⟶ (Tour_{n+1}, p_{n+1}, EV_n + 1)` et cherche dans cette flèche,
notamment dans la liaison Tour–grammaire première déjà compilée, ce qui détermine la composante
radiale de la Tour suivante. »

Ce fichier ne quitte pas la flèche : deux Tours consécutives, le premier partagé, le rang.

* **L'objet** (§1) : `CanonicalTransition e l` (départ engagé, rang + 1, premier partagé) ; il
  existe sur tout passage parti de la ligne (`canonicalTransition_of_passage`).
* **Ce que la liaison fixe avant l'arrivée** (§2) : la position du premier partagé dans la Tour de
  départ est celle de la Tour de ligne à la hauteur de départ (`exit_position_fixed_by_departure`).
* **Ce qui, dans la Tour d'arrivée, ne lit pas la composante radiale** (§3) : toute position
  relative de deux réels dans une même Tour vaut `T·log(q/q')/π` (`tower_relative_position`) ; la
  cellule d'entrée du premier partagé est celle de la Tour de ligne à la hauteur d'arrivée, hors
  d'une marge de `1/(πT)` cellule (`entry_cell_eq_line_cell_of_margin`).
* **Ce qui la porte** (§4) : la position du premier partagé dans la Tour d'arrivée est sa position
  de ligne plus `D/π` (`towerPosition_eq_line_add_residue`), écart strictement compris entre
  `−1/(2πT)` et `1/(πT)` (`entry_position_window`) ; à hauteur égale cette position détermine la
  position radiale (`entry_position_determines_radial`) ; sur la flèche, le déplacement du premier
  partagé d'une Tour à l'autre est sa part de hauteur plus `D` (`transition_shared_prime_shift`),
  sans aucun terme de grammaire, et la nullité radiale est conservée si et seulement si ce
  déplacement est sa part de hauteur (`transition_conserves_iff_shared_prime_shift`).
* **Bilan** (`canonical_transition_radial_carrier`) : les cinq lectures ensemble.

Borne : la liaison Tour–grammaire compilée lit la position d'entrée du premier partagé, elle ne la
fixe pas ; les deux membres de l'équivalence sont des données de l'arrivée. Le verrou est écrit sur
un seul premier et deux Tours : « le premier partagé entre dans la Tour suivante à sa position de
ligne ». Aucun énoncé de ce fichier ne pose un membre hors ligne ni la prémisse `PNoRegimeChange`.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune `def` de prémisse.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. L'objet : la flèche -/

/-- **La flèche entre deux événements canoniques successifs**, partie de l'état engagé : le départ
est en ligne, le rang avance d'un cran, le premier partagé est le minimum attendu du départ et
l'occurrence de l'arrivée. Aucun champ ne porte sur la position radiale de l'arrivée. -/
structure CanonicalTransition (e l : TrueZero) : Prop where
  engaged : rZeroRadialPosition e.1 = 1 / 2
  rank_step : nZeroSourceIndex l.1 = nZeroSourceIndex e.1 + 1
  shared : occurrence l = expectedMinimumPrime e

/-- La flèche existe sur tout passage parti de la ligne. -/
theorem canonicalTransition_of_passage (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    CanonicalTransition ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ :=
  ⟨hOn, thm_zeroSourceIndex_succ_of_passage p hE, (passage_direction_rigid p hE hL).2.2.2.1⟩

/-! ## 2. Ce que la liaison fixe avant l'arrivée -/

/-- **Position d'un réel dans la Tour de ligne à la hauteur `T`**, en cellules. -/
noncomputable def linePosition (T q : ℝ) : ℝ :=
  (T * Real.log q - linePhase T) / Real.pi

/-- La phase d'un membre en ligne est la phase de ligne à sa hauteur. -/
theorem phase_eq_linePhase_of_onLine (z : TrueZero) (h : rZeroRadialPosition z.1 = 1 / 2) :
    (towerMotionOf z).phase = linePhase (rZeroHeight z.1) := by
  rw [towerMotion_phase, h]
  rfl

/-- **Côté départ.** La position du premier partagé dans la Tour de départ est sa position dans la
Tour de ligne à la hauteur de départ : fixée par la hauteur de départ et le rang. -/
theorem exit_position_fixed_by_departure {e l : TrueZero} (t : CanonicalTransition e l) :
    towerPosition e (occurrence l : ℝ) =
      linePosition (rZeroHeight e.1) (expectedMinimumPrime e : ℝ) := by
  rw [t.shared]
  unfold towerPosition linePosition
  rw [phase_eq_linePhase_of_onLine e t.engaged]

/-! ## 3. Ce qui, dans la Tour d'arrivée, ne lit pas la composante radiale -/

/-- **Les positions relatives ne lisent que la hauteur.** Dans une même Tour, l'écart de position
de deux réels vaut `T·(log q − log q')/π` : la grille mesure les écarts par la hauteur seule. -/
theorem tower_relative_position (z : TrueZero) (q q' : ℝ) :
    towerPosition z q - towerPosition z q' =
      rZeroHeight z.1 * (Real.log q - Real.log q') / Real.pi := by
  unfold towerPosition
  ring

/-- **La position dans la Tour est la position de ligne plus `D/π`.** -/
theorem towerPosition_eq_line_add_residue (z : TrueZero) (q : ℝ) :
    towerPosition z q = linePosition (rZeroHeight z.1) q + changeResidue z.1 / Real.pi := by
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  unfold linePosition
  rw [← changeResidue_eq_position_sub z q, ← add_div, eq_div_iff hπ]
  ring

/-- **Fenêtre de la position d'entrée.** L'écart entre la position dans la Tour et la position de
ligne à la même hauteur est strictement compris entre `−1/(2πT)` et `1/(πT)` cellule. -/
theorem entry_position_window (z : TrueZero) (q : ℝ) :
    -(1 / (2 * rZeroHeight z.1)) / Real.pi <
        towerPosition z q - linePosition (rZeroHeight z.1) q ∧
      towerPosition z q - linePosition (rZeroHeight z.1) q < 1 / rZeroHeight z.1 / Real.pi := by
  have hw := changeResidueAt_window (thm_zeroRadialPosition_positive z.1)
    (thm_zeroRadialPosition_lt_one z.1) z.2
  have e : towerPosition z q - linePosition (rZeroHeight z.1) q =
      changeResidue z.1 / Real.pi := by
    rw [towerPosition_eq_line_add_residue z q]
    ring
  rw [e]
  exact ⟨(div_lt_div_iff_of_pos_right Real.pi_pos).mpr hw.1,
    (div_lt_div_iff_of_pos_right Real.pi_pos).mpr hw.2⟩

/-- **La cellule ne lit pas la composante radiale, hors d'une marge.** Si la position de ligne du
réel `q` à la hauteur du membre est à plus de `1/(2πT)` au-dessus du bord `k` et à plus de `1/(πT)`
sous le bord `k + 1`, la cellule de `q` dans la Tour du membre est `k`, quelle que soit la position
radiale du membre. -/
theorem entry_cell_eq_line_cell_of_margin (z : TrueZero) (q : ℝ) (k : ℤ)
    (hlow : (k : ℝ) + 1 / (2 * rZeroHeight z.1) / Real.pi ≤ linePosition (rZeroHeight z.1) q)
    (hhigh : linePosition (rZeroHeight z.1) q + 1 / rZeroHeight z.1 / Real.pi ≤ (k : ℝ) + 1) :
    pivotCoordinate z q = k := by
  obtain ⟨h1, h2⟩ := entry_position_window z q
  have hneg : -(1 / (2 * rZeroHeight z.1)) / Real.pi = -(1 / (2 * rZeroHeight z.1) / Real.pi) :=
    neg_div _ _
  rw [hneg] at h1
  unfold pivotCoordinate
  have hceil : ⌈towerPosition z q⌉ = k + 1 := by
    rw [Int.ceil_eq_iff]
    push_cast
    constructor <;> linarith
  omega

/-! ## 4. Ce qui porte la composante radiale de la Tour suivante -/

/-- **À hauteur égale, la position d'un même réel détermine la position radiale.** Deux Tours de
même hauteur qui placent un même réel à la même position ont la même position radiale. -/
theorem entry_position_determines_radial (l l' : TrueZero)
    (hT : rZeroHeight l.1 = rZeroHeight l'.1) (q : ℝ)
    (hpos : towerPosition l q = towerPosition l' q) :
    rZeroRadialPosition l.1 = rZeroRadialPosition l'.1 := by
  have h1 := pi_mul_towerPosition l q
  rw [hpos, pi_mul_towerPosition l' q, hT] at h1
  have hφ : (towerMotionOf l).phase = (towerMotionOf l').phase := by linarith
  rw [towerMotion_phase, towerMotion_phase, hT] at hφ
  have h := Real.arctan_injective hφ
  rw [div_eq_div_iff (thm_zeroRadialPosition_positive l.1).ne'
    (thm_zeroRadialPosition_positive l'.1).ne'] at h
  exact (mul_left_cancel₀ (ne_of_gt l'.2) h).symm

/-- **Le déplacement du premier partagé d'une Tour à l'autre**, depuis l'état engagé : sa part de
hauteur plus le résidu de l'arrivée. Aucun terme de grammaire n'y figure. -/
theorem transition_shared_prime_shift {e l : TrueZero} (t : CanonicalTransition e l) :
    raccordShift e l = heightShift e l + changeResidue l.1 := by
  have hre : radialFactor e = 1 := (radialFactor_eq_one_iff e).mpr t.engaged
  rw [raccordShift_decomposed, hre, Real.log_one, mul_zero, zero_sub, changeResidue_eq_radial]

/-- **La transition conserve la nullité radiale si et seulement si le premier partagé se déplace,
d'une Tour à l'autre, de sa seule part de hauteur.** -/
theorem transition_conserves_iff_shared_prime_shift {e l : TrueZero}
    (t : CanonicalTransition e l) :
    rZeroRadialPosition l.1 = 1 / 2 ↔ raccordShift e l = heightShift e l := by
  rw [transition_shared_prime_shift t, ← changeResidue_eq_zero_iff l.1]
  constructor
  · intro h
    rw [h, add_zero]
  · intro h
    linarith

/-- **La transition conserve la nullité radiale si et seulement si le premier partagé entre dans la
Tour suivante à sa position de ligne.** -/
theorem transition_conserves_iff_entry_position {e l : TrueZero}
    (_t : CanonicalTransition e l) :
    rZeroRadialPosition l.1 = 1 / 2 ↔
      towerPosition l (occurrence l : ℝ) =
        linePosition (rZeroHeight l.1) (occurrence l : ℝ) := by
  rw [towerPosition_eq_line_add_residue l, ← changeResidue_eq_zero_iff l.1]
  constructor
  · intro h
    rw [h, zero_div, add_zero]
  · intro h
    have h0 : changeResidue l.1 / Real.pi = 0 := by linarith
    rcases div_eq_zero_iff.mp h0 with h1 | h1
    · exact h1
    · exact absurd h1 Real.pi_pos.ne'

/-! ## 5. Bilan de la flèche -/

/-- **Ce qui, dans la flèche, porte la composante radiale de la Tour suivante.** Sur la flèche
partie de l'état engagé, tenus ensemble :

1. la position du premier partagé dans la Tour de départ est fixée par la hauteur de départ et le
   rang ;
2. dans la Tour d'arrivée, l'écart de position entre son minimum attendu et son occurrence ne lit
   que la hauteur ;
3. la position d'entrée du premier partagé est sa position de ligne plus `D/π`, dans la fenêtre ;
4. le déplacement du premier partagé d'une Tour à l'autre est sa part de hauteur plus `D` ;
5. la nullité radiale est conservée si et seulement si la position d'entrée est la position de
   ligne. -/
theorem canonical_transition_radial_carrier {e l : TrueZero} (t : CanonicalTransition e l) :
    towerPosition e (occurrence l : ℝ) =
        linePosition (rZeroHeight e.1) (expectedMinimumPrime e : ℝ) ∧
    towerPosition l (expectedMinimumPrime l : ℝ) - towerPosition l (occurrence l : ℝ) =
        rZeroHeight l.1 *
          (Real.log (expectedMinimumPrime l : ℝ) - Real.log (occurrence l : ℝ)) / Real.pi ∧
    (towerPosition l (occurrence l : ℝ) =
        linePosition (rZeroHeight l.1) (occurrence l : ℝ) + changeResidue l.1 / Real.pi ∧
      -(1 / (2 * rZeroHeight l.1)) / Real.pi <
        towerPosition l (occurrence l : ℝ) - linePosition (rZeroHeight l.1) (occurrence l : ℝ) ∧
      towerPosition l (occurrence l : ℝ) - linePosition (rZeroHeight l.1) (occurrence l : ℝ) <
        1 / rZeroHeight l.1 / Real.pi) ∧
    raccordShift e l = heightShift e l + changeResidue l.1 ∧
    (rZeroRadialPosition l.1 = 1 / 2 ↔
      towerPosition l (occurrence l : ℝ) =
        linePosition (rZeroHeight l.1) (occurrence l : ℝ)) :=
  ⟨exit_position_fixed_by_departure t, tower_relative_position l _ _,
    ⟨towerPosition_eq_line_add_residue l _, entry_position_window l _⟩,
    transition_shared_prime_shift t, transition_conserves_iff_entry_position t⟩

#print axioms canonicalTransition_of_passage
#print axioms exit_position_fixed_by_departure
#print axioms tower_relative_position
#print axioms towerPosition_eq_line_add_residue
#print axioms entry_position_window
#print axioms entry_cell_eq_line_cell_of_margin
#print axioms entry_position_determines_radial
#print axioms transition_shared_prime_shift
#print axioms transition_conserves_iff_shared_prime_shift
#print axioms transition_conserves_iff_entry_position
#print axioms canonical_transition_radial_carrier

end RHV6Fresh
