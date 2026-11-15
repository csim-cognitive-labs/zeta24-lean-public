/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ConstantAmplitudeNeed
import RHV6Fresh.Terminal.DiagonalPassage
import RHV6Fresh.Terminal.FirstZeroContactComparison
import RHV6Fresh.Terminal.RegimeTower
import RHV6Fresh.Terminal.TangentialInversion

/-!
# Le verrou du couple (fréquence, amplitude) sur la Tour normalisée (auteur, 2026-10-16)

Démarche validée par l'auteur (2026-10-16) : « c'est le couple amplitude, fréquence, donc `(T, β)`, qui doit disqualifier le OFF,
pas seulement le changement d'amplitude ». Les conclusions des expériences historiques à OFF fabriqués sont écartées ; seule la
géométrie compilée de la Tour normalisée et de sa projection sur l'axe algébrique est utilisée.

Le signal d'un zéro, ramené à l'échelle de la ligne et projeté sur l'axe algébrique, est une seule courbe en coordonnée
logarithmique. Trois grandeurs s'y lisent, sur le même objet, et elles ne sont pas indépendantes :

1. **l'espacement des rencontres** (points où la projection coupe l'axe : les contacts `C_k`) : `π/T`, hauteur seule ;
2. **la position des rencontres** : celles de la ligne à la même hauteur, multipliées par un facteur unique `λ`, `λ = 1 ⟺ β = 1/2` ;
3. **le besoin aux rencontres** (amplitude à l'échelle de la ligne, `pairAmplitude`) : rapport `e^{(β − 1/2)π/T}` entre deux
   rencontres consécutives, `1 ⟺ β = 1/2`.

Démontré ici (axiomes standard, tout vrai pour toute position radiale, aucune valeur présupposée) :
- l'espacement lit la fréquence et ne voit pas `β` (`frequency_of_spacing`, `spacing_blind_to_radial`) ;
- à fréquence égale, la position d'une seule rencontre fixe `β` (`radial_of_meeting_point`) ; le rapport des besoins à deux
  rencontres consécutives fixe `β` (`radial_of_need_ratio`) ; les deux lectures de `β` coïncident (`two_radial_readings_agree`) ;
- **on ne peut pas changer l'amplitude sans déplacer les points de passage obligés** : à fréquence fixée, besoin constant aux
  rencontres ⟺ rencontres non translatées (`need_constant_iff_not_shifted`) ; une dérive du besoin déplace toutes les rencontres
  hors des positions de la ligne (`need_change_moves_meeting_points`) ;
- **on ne peut pas réaligner les rencontres en changeant la fréquence** : un changement de hauteur change l'espacement et
  n'est jamais une translation rigide (`vertical_change_contracts_spacing`) ; un changement de `β` à hauteur fixe est une
  translation rigide de facteur `≠ 1` avec dérive du besoin (`horizontal_change_shifts_and_drifts`) ;
- **le couple est verrouillé** : même espacement et même rencontre ⟹ même `(T, β)` (`couple_locked`) ; même espacement et même
  rapport de besoins ⟹ même `(T, β)` (`couple_locked_by_amplitude`) : aucune solution diagonale ne satisfait à la fois
  l'espacement, la position et le besoin d'un autre signal ;
- fermeture par le couple : deux rencontres consécutives à besoin égal excluent un signal décroissant (`couple_lock_closes`) ;
  la loi quantifiée sur tous les signaux a la force de RH (`meeting_need_law_iff_riemannHypothesis`).

Ce que ce verrou laisse ouvert : la DEMANDE, c'est-à-dire ce que la courbe des premiers impose au signal placé à la hauteur du
zéro suivant (positions des rencontres, besoin aux rencontres). Aucun énoncé compilé ne va des écarts exacts vers ces points de
passage obligés ; la chaîne affiche cette demande comme son but.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. L'espacement des rencontres lit la fréquence -/

/-- L'espacement logarithmique de deux rencontres consécutives est `π/T`. -/
theorem spacing_eq_pitch (z : TrueZero) (k : ℤ) :
    Real.log (contactMinusAt z (k + 1)) - Real.log (contactMinusAt z k) = Real.pi / rZeroHeight z.1 :=
  contactAt_consecutive_logWidth z k

/-- **Même espacement ⟹ même fréquence** : l'espacement des rencontres détermine la hauteur. -/
theorem frequency_of_spacing (z w : TrueZero)
    (h : Real.log (contactMinusAt w (0 + 1)) - Real.log (contactMinusAt w 0) =
      Real.log (contactMinusAt z (0 + 1)) - Real.log (contactMinusAt z 0)) :
    rZeroHeight w.1 = rZeroHeight z.1 := by
  rw [spacing_eq_pitch, spacing_eq_pitch] at h
  have hz : (0 : ℝ) < rZeroHeight z.1 := z.2
  have hw : (0 : ℝ) < rZeroHeight w.1 := w.2
  rw [div_eq_div_iff hw.ne' hz.ne'] at h
  exact (mul_left_cancel₀ Real.pi_pos.ne' h).symm

/-- **L'espacement ne voit pas `β`** : à même hauteur, même espacement pour toute position radiale. -/
theorem spacing_blind_to_radial (z w : TrueZero) (hT : rZeroHeight z.1 = rZeroHeight w.1) (k : ℤ) :
    Real.log (contactMinusAt w (k + 1)) - Real.log (contactMinusAt w k) =
      Real.log (contactMinusAt z (k + 1)) - Real.log (contactMinusAt z k) := by
  rw [spacing_eq_pitch, spacing_eq_pitch, hT]

/-! ## 2. La position des rencontres et le besoin lisent `β`, et s'accordent -/

/-- **Une seule rencontre fixe `β` à fréquence égale** (inversion compilée `β = T·cot(T log C_k)`). -/
theorem radial_of_meeting_point (z w : TrueZero) (hT : rZeroHeight z.1 = rZeroHeight w.1) (k : ℤ)
    (h : contactMinusAt w k = contactMinusAt z k) :
    rZeroRadialPosition w.1 = rZeroRadialPosition z.1 := by
  rw [← inversion_radial w k, ← inversion_radial z k, ← hT, h]

/-- **Le rapport des besoins à deux rencontres consécutives fixe `β` à fréquence égale.** -/
theorem radial_of_need_ratio (z w : TrueZero) (hT : rZeroHeight z.1 = rZeroHeight w.1) (k : ℤ)
    (h : pairAmplitude w (contactMinusAt w (k + 1)) / pairAmplitude w (contactMinusAt w k) =
      pairAmplitude z (contactMinusAt z (k + 1)) / pairAmplitude z (contactMinusAt z k)) :
    rZeroRadialPosition w.1 = rZeroRadialPosition z.1 := by
  rw [need_ratio_meeting_points, need_ratio_meeting_points, Real.exp_eq_exp, ← hT] at h
  have hpos : Real.pi / rZeroHeight z.1 ≠ 0 := (div_pos Real.pi_pos z.2).ne'
  have := mul_right_cancel₀ hpos h
  linarith

/-- **Les deux lectures de `β` coïncident** : la position de la rencontre `C_k` et le rapport des besoins entre `C_k` et
`C_{k+1}` donnent la même valeur. -/
theorem two_radial_readings_agree (w : TrueZero) (k : ℤ) :
    rZeroHeight w.1 * Real.cot (rZeroHeight w.1 * Real.log (contactMinusAt w k)) =
      rZeroHeight w.1 / Real.pi *
        Real.log (pairAmplitude w (contactMinusAt w (k + 1)) / pairAmplitude w (contactMinusAt w k)) + 1 / 2 := by
  rw [inversion_radial, need_ratio_meeting_points, Real.log_exp]
  have hT : rZeroHeight w.1 ≠ 0 := w.2.ne'
  field_simp
  ring

/-! ## 3. On ne peut pas changer l'amplitude sans déplacer les points de passage obligés -/

/-- **À fréquence fixée, besoin constant aux rencontres ⟺ rencontres non translatées** (facteur `λ = 1`). -/
theorem need_constant_iff_not_shifted (w : TrueZero) (k : ℤ) :
    pairAmplitude w (contactMinusAt w (k + 1)) = pairAmplitude w (contactMinusAt w k) ↔ radialFactor w = 1 := by
  rw [constantNeed_meeting_points, radialFactor_eq_one_iff]

/-- Un facteur `λ ≠ 1` déplace toutes les rencontres hors des positions de la ligne à cette hauteur. -/
theorem shift_moves_meeting_points (w : TrueZero) (h : radialFactor w ≠ 1) (k : ℤ) :
    contactMinusAt w k ≠ lineContact (rZeroHeight w.1) k := by
  intro hc
  rw [contact_eq_line_mul_radial] at hc
  have hL : lineContact (rZeroHeight w.1) k ≠ 0 := (lineContact_pos _ k).ne'
  exact h ((mul_eq_left₀ hL).mp hc)

/-- **Une dérive du besoin déplace tous les points de passage** : si le besoin change entre deux rencontres consécutives, aucune
rencontre n'est à la position de la ligne à cette hauteur. -/
theorem need_change_moves_meeting_points (w : TrueZero) (k : ℤ)
    (h : pairAmplitude w (contactMinusAt w (k + 1)) ≠ pairAmplitude w (contactMinusAt w k)) (j : ℤ) :
    contactMinusAt w j ≠ lineContact (rZeroHeight w.1) j :=
  shift_moves_meeting_points w (fun h1 => h ((need_constant_iff_not_shifted w k).mpr h1)) j

/-! ## 4. Les deux mouvements : changer la fréquence change l'espacement ; changer `β` translate et fait dériver -/

/-- **Changement de fréquence** : la hauteur monte ⟹ l'espacement se contracte strictement, et aucune translation rigide ne relie
les deux grilles de rencontres. On ne réaligne pas les rencontres en changeant la fréquence. -/
theorem vertical_change_contracts_spacing (z w : TrueZero) (hT : rZeroHeight z.1 < rZeroHeight w.1) :
    towerPitch w < towerPitch z ∧ ¬ ∃ c : ℝ, ∀ k : ℤ, contactMinusAt w k = contactMinusAt z k * c :=
  ⟨(towerPitch_lt_iff z w).mpr hT, no_rigid_translation_of_height_ne z w hT.ne⟩

/-- **Changement de `β` à fréquence fixe** : translation rigide de toutes les rencontres par un facteur unique, différent de `1`,
et rapports de besoins différents aux rencontres consécutives. On ne change pas l'amplitude sans déplacer les rencontres. -/
theorem horizontal_change_shifts_and_drifts (z w : TrueZero) (hT : rZeroHeight z.1 = rZeroHeight w.1)
    (hβ : rZeroRadialPosition z.1 ≠ rZeroRadialPosition w.1) :
    (∃ c : ℝ, c ≠ 1 ∧ ∀ k : ℤ, contactMinusAt w k = contactMinusAt z k * c) ∧
    ∀ k : ℤ, pairAmplitude w (contactMinusAt w (k + 1)) / pairAmplitude w (contactMinusAt w k) ≠
      pairAmplitude z (contactMinusAt z (k + 1)) / pairAmplitude z (contactMinusAt z k) := by
  refine ⟨⟨Real.exp (((towerMotionOf w).phase - (towerMotionOf z).phase) / rZeroHeight z.1), ?_,
    fun k => sameHeight_grid_rigid_translation z w hT k⟩, fun k h => hβ (radial_of_need_ratio z w hT k h).symm⟩
  intro hc
  apply hβ
  have h0 := sameHeight_grid_rigid_translation z w hT 0
  rw [hc, mul_one] at h0
  exact (radial_of_meeting_point z w hT 0 h0).symm

/-! ## 5. Le couple est verrouillé : aucune solution diagonale -/

/-- **Verrou du couple** : même espacement des rencontres et une rencontre commune ⟹ même fréquence et même `β`. -/
theorem couple_locked (z w : TrueZero)
    (hS : Real.log (contactMinusAt w (0 + 1)) - Real.log (contactMinusAt w 0) =
      Real.log (contactMinusAt z (0 + 1)) - Real.log (contactMinusAt z 0))
    (hP : contactMinusAt w 0 = contactMinusAt z 0) :
    rZeroHeight w.1 = rZeroHeight z.1 ∧ rZeroRadialPosition w.1 = rZeroRadialPosition z.1 := by
  have hT := frequency_of_spacing z w hS
  exact ⟨hT, radial_of_meeting_point z w hT.symm 0 hP⟩

/-- **Verrou du couple par l'amplitude** : même espacement et même rapport de besoins ⟹ même fréquence et même `β`. -/
theorem couple_locked_by_amplitude (z w : TrueZero)
    (hS : Real.log (contactMinusAt w (0 + 1)) - Real.log (contactMinusAt w 0) =
      Real.log (contactMinusAt z (0 + 1)) - Real.log (contactMinusAt z 0))
    (hA : pairAmplitude w (contactMinusAt w (0 + 1)) / pairAmplitude w (contactMinusAt w 0) =
      pairAmplitude z (contactMinusAt z (0 + 1)) / pairAmplitude z (contactMinusAt z 0)) :
    rZeroHeight w.1 = rZeroHeight z.1 ∧ rZeroRadialPosition w.1 = rZeroRadialPosition z.1 := by
  have hT := frequency_of_spacing z w hS
  exact ⟨hT, radial_of_need_ratio z w hT.symm 0 hA⟩

/-- **Aucune solution diagonale** : un signal qui satisfait l'espacement et le besoin constant d'un autre signal à une de ses
rencontres a la même fréquence et est sur la ligne. -/
theorem no_diagonal_solution (z w : TrueZero)
    (hS : Real.log (contactMinusAt w (0 + 1)) - Real.log (contactMinusAt w 0) =
      Real.log (contactMinusAt z (0 + 1)) - Real.log (contactMinusAt z 0))
    (hN : pairAmplitude w (contactMinusAt w (0 + 1)) = pairAmplitude w (contactMinusAt w 0)) :
    rZeroHeight w.1 = rZeroHeight z.1 ∧ rZeroRadialPosition w.1 = 1 / 2 :=
  ⟨frequency_of_spacing z w hS, (constantNeed_meeting_points w 0).mp hN⟩

/-! ## 6. Fermeture par le couple -/

/-- **Fermeture par deux rencontres consécutives à besoin égal** : un signal d'amplitude strictement décroissante le long des
premiers est exclu dès que son besoin est le même à deux rencontres consécutives (positions ET amplitude, à la fréquence donnée). -/
theorem couple_lock_closes (w : TrueZero)
    (hDecr : ∀ x y : ℝ, 1 ≤ x → x < y → pairAmplitude w y < pairAmplitude w x)
    (hJoint : ∃ k : ℤ, pairAmplitude w (contactMinusAt w (k + 1)) = pairAmplitude w (contactMinusAt w k)) : False := by
  obtain ⟨k, hk⟩ := hJoint
  exact decreasing_breaks_constantNeed w hDecr
    (constantNeed_of_onLine w ((constantNeed_meeting_points w k).mp hk))

/-- **La loi « tout signal a le même besoin à deux rencontres consécutives » ⟺ RH.** -/
theorem meeting_need_law_iff_riemannHypothesis :
    (∀ z : TrueZero, ∃ k : ℤ, pairAmplitude z (contactMinusAt z (k + 1)) = pairAmplitude z (contactMinusAt z k)) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    refine riemannHypothesis_iff_noLowerSide.mpr (fun z hlt => ?_)
    obtain ⟨k, hk⟩ := h z
    rw [(constantNeed_meeting_points z k).mp hk] at hlt
    linarith
  · intro hRH z
    exact ⟨0, (constantNeed_meeting_points z 0).mpr (thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1)⟩

#print axioms frequency_of_spacing
#print axioms radial_of_meeting_point
#print axioms radial_of_need_ratio
#print axioms two_radial_readings_agree
#print axioms need_constant_iff_not_shifted
#print axioms need_change_moves_meeting_points
#print axioms vertical_change_contracts_spacing
#print axioms horizontal_change_shifts_and_drifts
#print axioms couple_locked
#print axioms couple_locked_by_amplitude
#print axioms no_diagonal_solution
#print axioms couple_lock_closes
#print axioms meeting_need_law_iff_riemannHypothesis

end RHV6Fresh
