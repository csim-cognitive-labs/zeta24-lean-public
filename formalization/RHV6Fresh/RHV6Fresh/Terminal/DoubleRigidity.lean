/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FirstTowerHorizon
import RHV6Fresh.Terminal.GrammarKinematics
import RHV6Fresh.Terminal.PointedPrimeComparison
import RHV6Fresh.Terminal.TowerWinding
import RHV6Fresh.Terminal.ArithmeticReading

/-!
# RHV6Fresh — la double rigidité : emprisonnement des Tours et écarts reproduits par la hauteur seule
(auteur, 2026-10-04)

Énoncé de l'auteur : « la relation indéfectible entre les premiers et chaque Tour (confirmée par von
Mangoldt), la rigidité double entre l'emprisonnement des Tours et la rigidité de reproduire les écarts
UNIQUEMENT par la hauteur, empêche la Tour de sortir de la Tour précédente ; la hauteur qui progresse fait
varier des paramètres clés qui concourent tous à accentuer la situation ; `M^Z = M` est en contrainte ».

* **§1 La liaison premiers–Tour sur un passage** (`prime_tower_bond`, `passage_prime_tower_bond`) : `M^Z = M`
  (l'occurrence de l'arrivée est le minimum attendu du départ, premier, strictement au-dessus de l'occurrence
  du départ), poids de von Mangoldt `Λ(M) = log M`, formule tangentielle
  `π·Π_l(M) = T_l·log M − arctan(T_l/β_l)`, registre du passage.
* **§2 Les écarts sont reproduits par la hauteur seule** : dans toute Tour, l'écart de position entre deux
  réels vaut `T·(log q' − log q)/π` (`gap_reading_height_only`) ; deux Tours lisent un écart de la même façon
  ⟺ elles ont la même hauteur (`gap_readings_agree_iff_height`).
* **§3 La hauteur qui avance : tous les paramètres concourent** (`height_advance_concurs`,
  `vertical_passage_concurs`) : pas contracté, phase plus grande, support plus grand, amplitude plus faible en
  tout point, chaque écart lu sur plus de cellules, contacts d'indice fixé rapprochés ; sur un passage où la
  hauteur avance, hiérarchie au raccord et côtés radiaux.
* **§4 Ce que la compilation établit sur le passage de même hauteur** (`sameHeight_satisfies_both_rigidities`) :
  `M^Z = M`, le poids de von Mangoldt, la lecture de tous les écarts (identique à celle de la Tour de départ),
  le pas et le registre tiennent ; l'énergie au raccord est renversée et la Tour d'arrivée n'est pas
  prisonnière. Modèle de paramètres sans zéro (`parameter_model_twin_escapes`).
* **§5 Ce qui ferme** : « aucun passage de même hauteur » ⟺ hypothèse de Riemann
  (`no_sameHeight_iff_riemannHypothesis`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse `def P… : Prop`.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. La liaison premiers–Tour sur un passage -/

/-- **Liaison premiers–Tour** sous `M^Z = M` : le premier partagé `M = Occ l` est premier, strictement
au-dessus de l'occurrence du départ, son poids de von Mangoldt est `log M`, sa position dans la Tour
d'arrivée est donnée par la formule tangentielle, et le registre du passage tient. -/
theorem prime_tower_bond (e l : TrueZero) (h : occurrence l = expectedMinimumPrime e) :
    Nat.Prime (occurrence l) ∧ occurrence e < occurrence l ∧
    ArithmeticFunction.vonMangoldt (occurrence l) = Real.log (occurrence l : ℝ) ∧
    Real.pi * towerPosition l (occurrence l : ℝ) =
      rZeroHeight l.1 * Real.log (occurrence l : ℝ) -
        Real.arctan (rZeroHeight l.1 / rZeroRadialPosition l.1) ∧
    occurrencePosition l - occurrencePosition e =
      raccordShift e l + rZeroHeight e.1 * rPrimeGapLogRatio (nZeroSourceIndex e.1) := by
  refine ⟨occurrence_prime l, ?_, ArithmeticFunction.vonMangoldt_apply_prime (occurrence_prime l), ?_, ?_⟩
  · rw [h]; exact occurrence_lt_expectedMinimumPrime e
  · rw [pi_mul_towerPosition, towerMotion_phase]
  · rw [passage_ledger e l h, phaseIncrement_eq_height_mul_ratio]

/-- **La liaison tient sur tout passage**, sans hypothèse : `M^Z = M` y est un théorème. -/
theorem passage_prime_tower_bond (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
    Nat.Prime (occurrence ⟨p.zLaterMember, hL⟩) ∧
    occurrence ⟨p.zEarlierMember, hE⟩ < occurrence ⟨p.zLaterMember, hL⟩ ∧
    ArithmeticFunction.vonMangoldt (occurrence ⟨p.zLaterMember, hL⟩) =
      Real.log (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) ∧
    Real.pi * towerPosition ⟨p.zLaterMember, hL⟩ (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) =
      rZeroHeight p.zLaterMember * Real.log (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) -
        Real.arctan (rZeroHeight p.zLaterMember / rZeroRadialPosition p.zLaterMember) ∧
    occurrencePosition ⟨p.zLaterMember, hL⟩ - occurrencePosition ⟨p.zEarlierMember, hE⟩ =
      raccordShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ +
        rZeroHeight p.zEarlierMember * rPrimeGapLogRatio (nZeroSourceIndex p.zEarlierMember) :=
  have h := (passage_direction_rigid p hE hL).2.2.2.1
  ⟨h, prime_tower_bond ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ h⟩

/-! ## 2. Les écarts sont reproduits par la hauteur seule -/

/-- **Lecture d'un écart dans une Tour** : `Π(q') − Π(q) = T·(log q' − log q)/π`. Ni la position radiale ni
la phase n'y figurent. -/
theorem gap_reading_height_only (z : TrueZero) (q q' : ℝ) :
    towerPosition z q' - towerPosition z q =
      rZeroHeight z.1 * (Real.log q' - Real.log q) / Real.pi :=
  tower_relative_position z q' q

/-- **Deux Tours lisent un écart de la même façon ⟺ elles ont la même hauteur.** -/
theorem gap_readings_agree_iff_height (z w : TrueZero) {q q' : ℝ} (hq : 0 < q) (hqq' : q < q') :
    towerPosition z q' - towerPosition z q = towerPosition w q' - towerPosition w q ↔
      rZeroHeight z.1 = rZeroHeight w.1 := by
  rw [gap_reading_height_only, gap_reading_height_only]
  have hlog : 0 < Real.log q' - Real.log q := sub_pos.mpr (Real.log_lt_log hq hqq')
  constructor
  · intro h
    have h' := (div_left_inj' Real.pi_ne_zero).mp h
    exact mul_right_cancel₀ hlog.ne' h'
  · intro h; rw [h]

/-- **La hauteur est retrouvée depuis la lecture d'un seul écart.** -/
theorem height_recovered_from_gap_reading (z : TrueZero) {q q' : ℝ} (hq : 0 < q) (hqq' : q < q') :
    rZeroHeight z.1 =
      Real.pi * (towerPosition z q' - towerPosition z q) / (Real.log q' - Real.log q) := by
  have hlog : 0 < Real.log q' - Real.log q := sub_pos.mpr (Real.log_lt_log hq hqq')
  rw [gap_reading_height_only]
  field_simp

/-! ## 3. La hauteur qui avance : tous les paramètres concourent -/

/-- **À position radiale fixée, la hauteur qui avance** contracte le pas, augmente la phase et le support,
affaiblit l'amplitude en tout point, fait lire chaque écart sur plus de demi-tours et rapproche les contacts
d'indice fixé. -/
theorem height_advance_concurs {β T T' : ℝ} (hβ : 0 < β) (hT : 0 < T) (hTT' : T < T') :
    Real.pi / T' < Real.pi / T ∧
    Real.arctan (T / β) < Real.arctan (T' / β) ∧
    β ^ 2 + T ^ 2 < β ^ 2 + T' ^ 2 ∧
    (∀ x : ℝ, 0 < x → x ^ β / Real.sqrt (β ^ 2 + T' ^ 2) < x ^ β / Real.sqrt (β ^ 2 + T ^ 2)) ∧
    (∀ q q' : ℝ, 0 < q → q < q' → T * Real.log (q' / q) < T' * Real.log (q' / q)) ∧
    (∀ k : ℝ, 1 ≤ k → windingContact β T' k < windingContact β T k) := by
  have hsq : β ^ 2 + T ^ 2 < β ^ 2 + T' ^ 2 := by nlinarith
  have hpos : 0 < β ^ 2 + T ^ 2 := by positivity
  refine ⟨div_lt_div_of_pos_left Real.pi_pos hT hTT',
    Real.arctan_strictMono (div_lt_div_of_pos_right hTT' hβ), hsq, fun x hx => ?_,
    fun q q' hq hqq' => mul_lt_mul_of_pos_right hTT' (Real.log_pos ((one_lt_div hq).mpr hqq')),
    fun k hk => windingContact_strictAnti_height hβ hT hTT' hk⟩
  exact div_lt_div_of_pos_left (Real.rpow_pos_of_pos hx β) (Real.sqrt_pos.mpr hpos)
    (Real.sqrt_lt_sqrt hpos.le hsq)

/-- **Sur un passage où la hauteur avance**, la hiérarchie tient au raccord (énergie non croissante au premier
partagé, pas contracté), la position radiale ne monte pas (`β_l ≤ 1/2 ≤ β_e`), et chaque écart est lu sur
strictement plus de cellules par la Tour d'arrivée. -/
theorem vertical_passage_concurs (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hV : VerticalPassage p)
    (hT2 : 2 ≤ rZeroHeight p.zLaterMember) :
    RaccordHierarchy p hE hL ∧
    rZeroRadialPosition p.zLaterMember ≤ 1 / 2 ∧ 1 / 2 ≤ rZeroRadialPosition p.zEarlierMember ∧
    (∀ q q' : ℝ, 0 < q → q < q' →
      towerPosition ⟨p.zEarlierMember, hE⟩ q' - towerPosition ⟨p.zEarlierMember, hE⟩ q <
        towerPosition ⟨p.zLaterMember, hL⟩ q' - towerPosition ⟨p.zLaterMember, hL⟩ q) := by
  refine ⟨raccordHierarchy_of_height_advance p hE hL hV hT2, passage_entry_radial_le_half p hV,
    passage_exit_radial_ge_half p hV, fun q q' hq hqq' => ?_⟩
  have a : towerPosition ⟨p.zLaterMember, hL⟩ q' - towerPosition ⟨p.zLaterMember, hL⟩ q =
      rZeroHeight p.zLaterMember * (Real.log q' - Real.log q) / Real.pi := gap_reading_height_only _ q q'
  have b : towerPosition ⟨p.zEarlierMember, hE⟩ q' - towerPosition ⟨p.zEarlierMember, hE⟩ q =
      rZeroHeight p.zEarlierMember * (Real.log q' - Real.log q) / Real.pi := gap_reading_height_only _ q q'
  rw [a, b]
  have hlog : 0 < Real.log q' - Real.log q := sub_pos.mpr (Real.log_lt_log hq hqq')
  have hV' : rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember := hV
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hV' hlog) Real.pi_pos

/-! ## 4. Le passage de même hauteur : ce que la compilation établit -/

/-- **Sur un passage de même hauteur, les deux rigidités tiennent, et la Tour d'arrivée sort** : `M^Z = M`,
poids de von Mangoldt, tous les écarts lus exactement comme par la Tour de départ, pas conservé, registre
équilibré par la chute de phase ; l'énergie au premier partagé est renversée dès la hauteur 2 et la Tour
d'arrivée n'est pas prisonnière de la Tour de départ. -/
theorem sameHeight_satisfies_both_rigidities (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hH : HorizontalPassage p) :
    occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
    ArithmeticFunction.vonMangoldt (occurrence ⟨p.zLaterMember, hL⟩) =
      Real.log (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) ∧
    (∀ q q' : ℝ,
      towerPosition ⟨p.zLaterMember, hL⟩ q' - towerPosition ⟨p.zLaterMember, hL⟩ q =
        towerPosition ⟨p.zEarlierMember, hE⟩ q' - towerPosition ⟨p.zEarlierMember, hE⟩ q) ∧
    towerPitch ⟨p.zLaterMember, hL⟩ = towerPitch ⟨p.zEarlierMember, hE⟩ ∧
    occurrencePosition ⟨p.zLaterMember, hL⟩ - occurrencePosition ⟨p.zEarlierMember, hE⟩ =
      rZeroHeight p.zEarlierMember * rPrimeGapLogRatio (nZeroSourceIndex p.zEarlierMember) +
        ((towerMotionOf ⟨p.zEarlierMember, hE⟩).phase - (towerMotionOf ⟨p.zLaterMember, hL⟩).phase) ∧
    (towerMotionOf ⟨p.zLaterMember, hL⟩).phase < (towerMotionOf ⟨p.zEarlierMember, hE⟩).phase ∧
    (2 ≤ rZeroHeight p.zEarlierMember →
      ‖zeroTerm ⟨p.zEarlierMember, hE⟩ (towerRaccordOf p hE hL).M‖ <
        ‖zeroTerm ⟨p.zLaterMember, hL⟩ (towerRaccordOf p hE hL).M‖) ∧
    ¬ TowerPrisoner p := by
  have h := (passage_direction_rigid p hE hL).2.2.2.1
  have hT : rZeroHeight (⟨p.zEarlierMember, hE⟩ : TrueZero).1 =
      rZeroHeight (⟨p.zLaterMember, hL⟩ : TrueZero).1 := hH
  have hβ : rZeroRadialPosition (⟨p.zEarlierMember, hE⟩ : TrueZero).1 <
      rZeroRadialPosition (⟨p.zLaterMember, hL⟩ : TrueZero).1 := horizontalPassage_radial_lt hH
  refine ⟨h, ArithmeticFunction.vonMangoldt_apply_prime (occurrence_prime _), fun q q' => ?_,
    (horizontal_iff_pitch_kept p hE hL).mp hH, ?_, sameHeight_phase_lt _ _ hT hβ,
    (sameHeight_breaks_hierarchy p hE hL hH).2.1,
    fun hP => absurd hH (ne_of_lt (prisoner_forces_height hP hE hL))⟩
  · have a : towerPosition ⟨p.zLaterMember, hL⟩ q' - towerPosition ⟨p.zLaterMember, hL⟩ q =
        rZeroHeight p.zLaterMember * (Real.log q' - Real.log q) / Real.pi := gap_reading_height_only _ q q'
    have b : towerPosition ⟨p.zEarlierMember, hE⟩ q' - towerPosition ⟨p.zEarlierMember, hE⟩ q =
        rZeroHeight p.zEarlierMember * (Real.log q' - Real.log q) / Real.pi := gap_reading_height_only _ q q'
    have hT' : rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember := hH
    rw [a, b, hT']
  · have c : phaseIncrement ⟨p.zEarlierMember, hE⟩ (nZeroSourceIndex p.zEarlierMember) =
        rZeroHeight p.zEarlierMember * rPrimeGapLogRatio (nZeroSourceIndex p.zEarlierMember) :=
      phaseIncrement_eq_height_mul_ratio _ _
    exact (horizontal_ledger ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ h hT).trans
      (congrArg (· + ((towerMotionOf ⟨p.zEarlierMember, hE⟩).phase -
        (towerMotionOf ⟨p.zLaterMember, hL⟩).phase)) c)

/-- **Modèle de paramètres, sans aucun zéro** : la paire `(1/4, 2)`, `(3/4, 2)` est miroir, lit tout écart de
la même façon, a un registre de pas équilibré par la seule chute de phase, et l'énergie de son membre haut
dépasse celle du membre bas en `q = 16`. Les formules en `(β, T, q)` admettent donc la paire qui sort. -/
theorem parameter_model_twin_escapes :
    (3 / 4 : ℝ) = 1 - 1 / 4 ∧
    (∀ q q' : ℝ, 0 < q → 0 < q' →
      pointedPosition (3 / 4) 2 q' - pointedPosition (3 / 4) 2 q =
        pointedPosition (1 / 4) 2 q' - pointedPosition (1 / 4) 2 q) ∧
    (∀ p p' : ℝ, 0 < p → 0 < p' →
      pointedPosition (3 / 4) 2 p' - pointedPosition (1 / 4) 2 p =
        (2 * Real.log (p' / p) + (Real.arctan (2 / (1 / 4)) - Real.arctan (2 / (3 / 4)))) / Real.pi) ∧
    ((16 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * ((3 / 4 : ℝ) ^ 2 + 2 ^ 2) <
      ((16 : ℝ) ^ (3 / 4 : ℝ)) ^ 2 * ((1 / 4 : ℝ) ^ 2 + 2 ^ 2) := by
  have h16 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
    rw [h16, ← Real.rpow_mul (by norm_num)]
    rw [show (4 : ℝ) * (1 / 4) = ((1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h3 : (16 : ℝ) ^ (3 / 4 : ℝ) = 8 := by
    rw [h16, ← Real.rpow_mul (by norm_num)]
    rw [show (4 : ℝ) * (3 / 4) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  refine ⟨by norm_num, fun q q' hq hq' => ?_, fun p p' hp hp' => ?_, ?_⟩
  · rw [pointedPosition_step _ _ _ _ hq hq', pointedPosition_step _ _ _ _ hq hq']
  · have := pair_step_position (1 / 4) 2 p p' hp hp'
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] at this
    exact this
  · rw [h1, h3]; norm_num

/-! ## 5. Ce qui ferme -/

/-- **« Aucun passage de même hauteur » équivaut à l'hypothèse de Riemann.** -/
theorem no_sameHeight_iff_riemannHypothesis :
    (∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → ¬ HorizontalPassage p) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    refine riemannHypothesis_of_height_always_advances fun p hE => ?_
    rcases passage_regime_dichotomy p with ⟨hV, -⟩ | ⟨hH, -⟩
    · exact hV
    · exact absurd hH (h p hE)
  · intro hRH p _ hH
    exact absurd hH (ne_of_lt (passage_height_lt_of_riemannHypothesis hRH p))

#print axioms prime_tower_bond
#print axioms passage_prime_tower_bond
#print axioms gap_reading_height_only
#print axioms gap_readings_agree_iff_height
#print axioms height_recovered_from_gap_reading
#print axioms height_advance_concurs
#print axioms vertical_passage_concurs
#print axioms sameHeight_satisfies_both_rigidities
#print axioms parameter_model_twin_escapes
#print axioms no_sameHeight_iff_riemannHypothesis

end RHV6Fresh
