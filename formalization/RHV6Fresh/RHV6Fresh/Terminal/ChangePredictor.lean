/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PrimeWeightResponse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# RHV6Fresh — le résidu de changement et son prédicteur, E141 à E145 (auteur, 2026-10-01)

Énoncé de l'auteur : « le bon objet est le résidu de changement
`D = X_réel − X_ligne = −T·log r`. Nous cherchons une quantité arithmétique antérieure à l'arrivée
qui mesure le changement radial, et il faut démontrer qu'elle vaut zéro pour le générateur exact de
zêta. Le théorème recherché est une loi de conservation de l'état engagé, pas une loi
d'incompatibilité. » Aucun énoncé de ce fichier ne pose un membre hors ligne ni la prémisse
`PNoRegimeChange`.

Numérotation (dernière en date, elle remplace les précédentes) :

* **E141, détectabilité du changement** (§1) : le résidu `changeResidue`, position réelle moins
  position de la Tour de ligne à la même hauteur ; le terme premier disparaît
  (`changeResidue_eq_position_sub`) ; `D = −T·log r` (`changeResidue_eq_radial`) ; toutes les
  représentations du changement (position radiale, phase, facteur radial, contacts, position de
  l'occurrence, déplacement radial sur le passage, régime du passage suivant) sont équivalentes à
  `D = 0` (`change_detector`, `passage_change_detector`) ; fenêtre `−1/(2T) < D < 1/T`
  (`changeResidueAt_window`) ; équation du registre `D_l − D_e = ΔΠ − H − T_e·log(p_{n+1}/p_n)`
  (`changeResidue_ledger`).
* **E142, prédiction arithmétique** (§2) : un prédicteur est une fonction de la hauteur de départ
  et du rang (les premiers, `Λ` et l'histoire grammaticale sont des fonctions du rang). Il en
  existe un qui est exact (`predictor_exists`), par l'existence du générateur : la signature ne
  suffit donc pas à faire une prédiction, il faut une formule. Candidats : réponse différentielle
  aux poids (`Terminal/PrimeWeightResponse.lean`, nulle aussi pour `regimeWitness`) ; exposant de
  croissance du reste arithmétique (`changeResidue_enclosed_by_remainder_growth`), qui encadre `D`
  sans lire aucun zéro.
* **E143, exactitude** et **E144, évaluation dans l'état engagé** : pour l'encadrement par la
  croissance, l'exactitude est compilée ; l'évaluation à zéro est la borne en `√x`
  (`changeResidue_vanishes_iff_remainder_sqrt_growth`), non dérivée.
* **E145, propagation** (`predictor_closes`, `engaged_persists_of_predictor`) : exactitude et
  valeur nulle dans l'état engagé donnent la loi « seule la hauteur évolue », puis la persistance.

* **Le bit de changement** (§4) : sur un passage vertical, `D = 0` ⟺ aucun membre hors ligne n'est
  atteint avant que la fonction réelle sur la ligne ne s'annule (`change_bit_iff_race`) ; un
  changement de signe de cette fonction fixe l'échéance de l'arrivée (`arrival_before_sign_change`).
  Avis de l'auteur (2026-10-01) : cette démarche n'est pas confirmée ; elle compare des membres en
  hauteur, le verrou est dans la flèche entre deux événements (`Terminal/CanonicalTransition.lean`).

Bornes : l'existence d'un prédicteur exact et nul dans l'état engagé équivaut à la loi « seule la
hauteur évolue » (`predictor_pair_iff_heightOnly`) ; « le résidu est nul partout » équivaut à la
borne en `√x` du reste arithmétique. Contrôles : le détecteur se déclenche sur les jumeaux de
`engagedBreakWorld` et de `regimeWitness` (`engagedBreakWorld_change_detected`,
`regimeWitness_change_detected`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune `def` de prémisse.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. E141 : le résidu de changement, détecteur unique -/

/-- **Le résidu de changement d'un candidat `(β, T)`** : phase de la Tour de ligne à la hauteur
`T`, moins phase de la Tour du candidat. -/
noncomputable def changeResidueAt (β T : ℝ) : ℝ := linePhase T - Real.arctan (T / β)

/-- **Le résidu de changement d'un membre.** -/
noncomputable def changeResidue (w : TNonTrivialZetaZero) : ℝ :=
  changeResidueAt (rZeroRadialPosition w) (rZeroHeight w)

/-- Le résidu d'un candidat est nul si et seulement si le candidat est en ligne. -/
theorem changeResidueAt_eq_zero_iff {β T : ℝ} (hβ : 0 < β) (hT : T ≠ 0) :
    changeResidueAt β T = 0 ↔ β = 1 / 2 := by
  unfold changeResidueAt linePhase
  constructor
  · intro h
    have h1 : T / (1 / 2) = T / β := Real.arctan_injective (sub_eq_zero.mp h)
    rw [div_eq_div_iff (by norm_num) hβ.ne'] at h1
    exact mul_left_cancel₀ hT h1
  · rintro rfl
    exact sub_self _

/-- Le résidu d'un candidat est strictement négatif si et seulement si le candidat est sous la
ligne. -/
theorem changeResidueAt_neg_iff {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) :
    changeResidueAt β T < 0 ↔ β < 1 / 2 := by
  unfold changeResidueAt linePhase
  rw [sub_neg, Real.arctan_strictMono.lt_iff_lt]
  exact div_lt_div_iff_of_pos_left hT (by norm_num) hβ

/-- Le résidu d'un candidat est strictement positif si et seulement si le candidat est au-dessus
de la ligne. -/
theorem changeResidueAt_pos_iff {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) :
    0 < changeResidueAt β T ↔ 1 / 2 < β := by
  unfold changeResidueAt linePhase
  rw [sub_pos, Real.arctan_strictMono.lt_iff_lt]
  exact div_lt_div_iff_of_pos_left hT hβ (by norm_num)

theorem arctan_lt_self_of_pos {x : ℝ} (hx : 0 < x) : Real.arctan x < x := by
  have h := Real.lt_tan (Real.arctan_pos.mpr hx) (Real.arctan_lt_pi_div_two x)
  rwa [Real.tan_arctan] at h

/-- **Fenêtre du résidu.** Dans la bande, à la hauteur `T > 0`, le résidu est compris strictement
entre `−1/(2T)` et `1/T` : une prédiction ne sélectionne que si elle est plus fine que cela. -/
theorem changeResidueAt_window {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) :
    -(1 / (2 * T)) < changeResidueAt β T ∧ changeResidueAt β T < 1 / T := by
  unfold changeResidueAt linePhase
  have h2 : Real.arctan (2 * T)⁻¹ = Real.pi / 2 - Real.arctan (2 * T) :=
    Real.arctan_inv_of_pos (by positivity)
  have h1 : Real.arctan T⁻¹ = Real.pi / 2 - Real.arctan T := Real.arctan_inv_of_pos hT
  have ha := arctan_lt_self_of_pos (x := (2 * T)⁻¹) (by positivity)
  have hb := arctan_lt_self_of_pos (x := T⁻¹) (by positivity)
  have hup := Real.arctan_lt_pi_div_two (T / β)
  have hup2 := Real.arctan_lt_pi_div_two (2 * T)
  have hlow : Real.arctan T < Real.arctan (T / β) :=
    Real.arctan_strictMono (by rw [lt_div_iff₀ hβ]; nlinarith [mul_pos hT (sub_pos.2 hβ1)])
  have e : T / (1 / 2) = 2 * T := by ring
  rw [e, one_div, one_div]
  constructor <;> linarith

/-- Le résidu d'un membre est nul si et seulement si le membre est en ligne. -/
theorem changeResidue_eq_zero_iff (w : TNonTrivialZetaZero) :
    changeResidue w = 0 ↔ rZeroRadialPosition w = 1 / 2 :=
  changeResidueAt_eq_zero_iff (thm_zeroRadialPosition_positive w) (thm_zeroHeight_ne_zero w)

/-- Le résidu d'un membre : phase de ligne à sa hauteur moins sa phase. -/
theorem changeResidue_eq_phase (z : TrueZero) :
    changeResidue z.1 = linePhase (rZeroHeight z.1) - (towerMotionOf z).phase := by
  rw [towerMotion_phase]
  rfl

/-- **Le terme premier disparaît.** Pour tout `q`, la position de `q` dans la Tour du membre moins
sa position dans la Tour de ligne à la même hauteur est le résidu : il ne dépend pas de `q`. -/
theorem changeResidue_eq_position_sub (z : TrueZero) (q : ℝ) :
    Real.pi * towerPosition z q -
        (rZeroHeight z.1 * Real.log q - linePhase (rZeroHeight z.1)) = changeResidue z.1 := by
  rw [pi_mul_towerPosition, changeResidue_eq_phase]
  ring

/-- **`D = −T·log r`.** -/
theorem changeResidue_eq_radial (z : TrueZero) :
    changeResidue z.1 = -(rZeroHeight z.1 * Real.log (radialFactor z)) := by
  rw [changeResidue_eq_phase, phase_eq_line_add_radial z]
  ring

/-- **Le détecteur unique.** Sur un membre, toutes les représentations du changement radial sont
équivalentes à `D = 0` : position radiale, phase, facteur radial, contacts, position de
l'occurrence ; le signe de `D` donne le côté. -/
theorem change_detector (z : TrueZero) :
    (changeResidue z.1 = 0 ↔ rZeroRadialPosition z.1 = 1 / 2) ∧
    (changeResidue z.1 = 0 ↔ (towerMotionOf z).phase = linePhase (rZeroHeight z.1)) ∧
    (changeResidue z.1 = 0 ↔ radialFactor z = 1) ∧
    (changeResidue z.1 = 0 ↔
      ∀ k : ℤ, contactMinusAt z k = lineContact (rZeroHeight z.1) k) ∧
    (changeResidue z.1 = 0 ↔
      occurrencePosition z =
        rZeroHeight z.1 * Real.log (occurrence z : ℝ) - linePhase (rZeroHeight z.1)) ∧
    (changeResidue z.1 < 0 ↔ rZeroRadialPosition z.1 < 1 / 2) ∧
    (0 < changeResidue z.1 ↔ 1 / 2 < rZeroRadialPosition z.1) := by
  have hT : (0 : ℝ) < rZeroHeight z.1 := z.2
  have h0 := changeResidue_eq_zero_iff z.1
  refine ⟨h0, ?_, h0.trans (radialFactor_eq_one_iff z).symm,
    h0.trans (contacts_height_determined_iff_onLine z).symm, ?_,
    changeResidueAt_neg_iff (thm_zeroRadialPosition_positive z.1) hT,
    changeResidueAt_pos_iff (thm_zeroRadialPosition_positive z.1) hT⟩
  · rw [changeResidue_eq_phase]
    constructor <;> intro h <;> linarith
  · rw [← changeResidue_eq_position_sub z (occurrence z : ℝ)]
    unfold occurrencePosition
    constructor <;> intro h <;> linarith

/-- **Équation du registre, écrite sur le résidu.** Sur tout passage, la variation du résidu est
le déplacement de la position de l'occurrence, moins la part que la hauteur détermine, moins la
progression grammaticale. -/
theorem changeResidue_ledger (e l : TrueZero) (h : occurrence l = expectedMinimumPrime e) :
    changeResidue l.1 - changeResidue e.1 =
      (occurrencePosition l - occurrencePosition e) - heightShift e l -
        rZeroHeight e.1 * rPrimeGapLogRatio (nZeroSourceIndex e.1) := by
  rw [passage_ledger_radial e l h, changeResidue_eq_radial, changeResidue_eq_radial]
  ring

/-- **Depuis l'état engagé**, le résidu de l'arrivée est le déplacement de la position de
l'occurrence moins ce que hauteur et grammaire déterminent. -/
theorem engaged_changeResidue_from_ledger (e l : TrueZero)
    (h : occurrence l = expectedMinimumPrime e) (hOn : rZeroRadialPosition e.1 = 1 / 2) :
    changeResidue l.1 =
      (occurrencePosition l - occurrencePosition e) - heightShift e l -
        rZeroHeight e.1 * rPrimeGapLogRatio (nZeroSourceIndex e.1) := by
  have h1 := changeResidue_ledger e l h
  rw [(changeResidue_eq_zero_iff e.1).mpr hOn, sub_zero] at h1
  exact h1

/-- **Le détecteur lu sur un passage parti de la ligne.** `D = 0` à l'arrivée ⟺ la position
radiale n'a pas évolué ; sur un passage vertical, `D ≤ 0`, et `D = 0` ⟺ aucun passage horizontal ne
part de l'arrivée. -/
theorem passage_change_detector (p : TZeroPassage)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    (changeResidue p.zLaterMember = 0 ↔
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember) ∧
    (VerticalPassage p → changeResidue p.zLaterMember ≤ 0) ∧
    (VerticalPassage p → (changeResidue p.zLaterMember = 0 ↔
      ∀ q : TZeroPassage, p.zLaterMember = q.zEarlierMember → ¬ HorizontalPassage q)) := by
  have hd := change_detector ⟨p.zLaterMember, hL⟩
  refine ⟨by rw [hOn]; exact changeResidue_eq_zero_iff _, fun hV => ?_, fun hV => ?_⟩
  · have hle := passage_entry_radial_le_half p hV
    by_contra hpos
    exact absurd (hd.2.2.2.2.2.2.mp (not_le.mp hpos)) (not_lt.mpr hle)
  · rw [← arrival_radial_le_one_iff_regime_kept p hL hV]
    have hge := arrival_radial_ge_one p hL hV
    constructor
    · intro h0
      exact (hd.2.2.1.mp h0).le
    · intro hle
      exact hd.2.2.1.mpr (le_antisymm hle hge)

/-! ## 2. E142 à E145 : le prédicteur -/

/-- **E142, borne de signature.** Il existe une fonction de la hauteur de départ et du rang, sans
aucune lecture de l'arrivée dans ses arguments, égale au résidu de l'arrivée sur tout passage parti
de la ligne : le générateur existe. La signature ne fait donc pas une prédiction ; il faut une
formule. -/
theorem predictor_exists :
    ∃ F : ℝ → ℕ → ℝ, ∀ p : TZeroPassage, rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      F (rZeroHeight p.zEarlierMember) (nZeroSourceIndex p.zEarlierMember) =
        changeResidue p.zLaterMember := by
  obtain ⟨G, hG⟩ := engaged_successor_function
  refine ⟨fun T _ => changeResidueAt (G T).2 (G T).1, fun p hOn => ?_⟩
  change changeResidueAt (G (rZeroHeight p.zEarlierMember)).2
    (G (rZeroHeight p.zEarlierMember)).1 = _
  rw [hG p hOn]
  rfl

/-- **E145, propagation : un pas.** Si un prédicteur est exact sur les passages verticaux partis
de la ligne (E143) et vaut zéro dans l'état engagé (E144), alors sur ces passages seule la hauteur
évolue. Les deux propriétés sont des hypothèses du théorème. -/
theorem predictor_closes (F : ℝ → ℕ → ℝ)
    (hCorrect : ∀ p : TZeroPassage, VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      F (rZeroHeight p.zEarlierMember) (nZeroSourceIndex p.zEarlierMember) =
        changeResidue p.zLaterMember)
    (hZero : ∀ p : TZeroPassage, VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      F (rZeroHeight p.zEarlierMember) (nZeroSourceIndex p.zEarlierMember) = 0) :
    ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember :=
  fun p hV hOn =>
    ((changeResidue_eq_zero_iff _).mp ((hCorrect p hV hOn).symm.trans (hZero p hV hOn))).trans
      hOn.symm

/-- **E145, propagation : jusqu'à l'infini.** Sous les mêmes deux hypothèses, tout membre
au-dessus d'un membre engagé est en ligne, atteint et quitté verticalement. -/
theorem engaged_persists_of_predictor (F : ℝ → ℕ → ℝ)
    (hCorrect : ∀ p : TZeroPassage, VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      F (rZeroHeight p.zEarlierMember) (nZeroSourceIndex p.zEarlierMember) =
        changeResidue p.zLaterMember)
    (hZero : ∀ p : TZeroPassage, VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      F (rZeroHeight p.zEarlierMember) (nZeroSourceIndex p.zEarlierMember) = 0)
    {o : TZeroPassage} (hE : 0 < rZeroHeight o.zLaterMember) (ho : VerticalPassage o)
    (hOn : rZeroRadialPosition o.zLaterMember = 1 / 2) :
    ∀ w : TNonTrivialZetaZero, PZeroMemberPrecedes o.zLaterMember w →
      rZeroRadialPosition w = 1 / 2 ∧
      (∃ q : TZeroPassage, q.zLaterMember = w ∧ VerticalPassage q) ∧
      (∀ q : TZeroPassage, q.zEarlierMember = w → VerticalPassage q ∧ ¬ HorizontalPassage q) :=
  engaged_persists_to_infinity (predictor_closes F hCorrect hZero) hE ho hOn

/-- **Borne.** « Il existe un prédicteur exact et nul dans l'état engagé » équivaut à la loi
« seule la hauteur évolue sur un passage vertical parti de la ligne ». Poser les deux propriétés
ensemble réinjecte la cible : l'une des deux doit être calculée sur une formule. -/
theorem predictor_pair_iff_heightOnly :
    (∃ F : ℝ → ℕ → ℝ,
      (∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
        F (rZeroHeight p.zEarlierMember) (nZeroSourceIndex p.zEarlierMember) =
          changeResidue p.zLaterMember) ∧
      (∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
        F (rZeroHeight p.zEarlierMember) (nZeroSourceIndex p.zEarlierMember) = 0)) ↔
    (∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember) := by
  constructor
  · rintro ⟨F, hC, hZ⟩
    exact predictor_closes F hC hZ
  · intro h
    refine ⟨fun _ _ => 0, fun p hV hOn => ?_, fun _ _ _ => rfl⟩
    exact ((changeResidue_eq_zero_iff _).mpr ((h p hV hOn).trans hOn)).symm

/-- **Un prédicteur qui ne lit aucun zéro : l'exposant de croissance du reste arithmétique.** Si le
reste, écrit avec les seuls premiers, est borné par `C·x^θ` avec `θ < 1`, le résidu de tout membre
est encadré par deux fonctions de sa hauteur et de `θ`. Exactitude compilée (E143). -/
theorem changeResidue_enclosed_by_remainder_growth {θ C : ℝ} (hθ : θ < 1)
    (h : ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ θ) (z : TrueZero) :
    linePhase (rZeroHeight z.1) - Real.arctan (rZeroHeight z.1 / (1 - θ)) ≤ changeResidue z.1 ∧
    changeResidue z.1 ≤ linePhase (rZeroHeight z.1) - Real.arctan (rZeroHeight z.1 / θ) := by
  have hβ := thm_zeroRadialPosition_positive z.1
  have hT : (0 : ℝ) < rZeroHeight z.1 := z.2
  have hup := radial_le_of_remainder_growth h z
  have hm := radial_le_of_remainder_growth h (mirrorMember z)
  rw [mirrorMember_radial] at hm
  have h1 : 0 < 1 - θ := by linarith
  have hlow : 1 - θ ≤ rZeroRadialPosition z.1 := by linarith
  unfold changeResidue changeResidueAt
  constructor
  · have hd : rZeroHeight z.1 / rZeroRadialPosition z.1 ≤ rZeroHeight z.1 / (1 - θ) :=
      div_le_div_of_nonneg_left hT.le h1 hlow
    have := Real.arctan_strictMono.monotone hd
    linarith
  · have hd : rZeroHeight z.1 / θ ≤ rZeroHeight z.1 / rZeroRadialPosition z.1 :=
      div_le_div_of_nonneg_left hT.le hβ hup
    have := Real.arctan_strictMono.monotone hd
    linarith

/-- **E144 pour ce prédicteur.** Sous la borne en `√x` du reste arithmétique, le résidu de tout
membre est nul. -/
theorem changeResidue_zero_of_remainder_sqrt_growth
    (h : ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 : ℝ))
    (w : TNonTrivialZetaZero) : changeResidue w = 0 :=
  (changeResidue_eq_zero_iff w).mpr
    (thm_zeroRadialPosition_half_of_riemannHypothesis
      (riemannHypothesis_of_remainder_sqrt_growth h) w)

/-- **Borne.** « Le résidu de changement est nul sur tout membre » équivaut à la borne en `√x` du
reste arithmétique : l'évaluation à zéro du prédicteur est cette borne, non dérivée. -/
theorem changeResidue_vanishes_iff_remainder_sqrt_growth :
    (∀ w : TNonTrivialZetaZero, changeResidue w = 0) ↔
      ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 : ℝ) := by
  constructor
  · intro h
    rw [← riemannHypothesis_iff_remainder_sqrt_growth]
    refine riemannHypothesis_of_noLowerSide fun z hβ => ?_
    have := (changeResidue_eq_zero_iff z.1).mp (h z.1)
    linarith
  · intro h w
    exact changeResidue_zero_of_remainder_sqrt_growth h w

/-! ## 3. Contrôles : le détecteur se déclenche dans les mondes dont le régime change -/

/-- Dans `engagedBreakWorld`, le résidu est nul sur le membre en ligne et non nul sur chacun des
deux jumeaux situés plus haut. -/
theorem engagedBreakWorld_change_detected (d τ : ℝ) (hd : d ≠ 0) (hd' : |d| < 1 / 2)
    (hτ : 0 < τ) (z : TrueZero) (hOn : rZeroRadialPosition z.1 = 1 / 2) :
    changeResidueAt (zeroPoint z).re (zeroPoint z).im = 0 ∧
    changeResidueAt (zeroPoint z - d + τ * Complex.I).re (zeroPoint z - d + τ * Complex.I).im ≠ 0 ∧
    changeResidueAt (zeroPoint z + d + τ * Complex.I).re
      (zeroPoint z + d + τ * Complex.I).im ≠ 0 := by
  have hT : (0 : ℝ) < rZeroHeight z.1 := z.2
  obtain ⟨⟨_, hre, him⟩, _, ⟨him1, him2, _⟩, hm, hp, hne1, hne2⟩ :=
    engagedBreakWorld_line_then_twins d τ hd hτ z hOn
  obtain ⟨hdl, hdu⟩ := abs_lt.mp hd'
  refine ⟨?_, fun h => hne1 ?_, fun h => hne2 ?_⟩
  · rw [changeResidueAt_eq_zero_iff (by rw [hre]; norm_num) (by rw [him]; exact hT.ne'), hre]
  · exact (changeResidueAt_eq_zero_iff (by rw [hm]; linarith)
      (by rw [him1]; linarith)).mp h
  · exact (changeResidueAt_eq_zero_iff (by rw [hp]; linarith)
      (by rw [him2]; linarith)).mp h

/-- Dans `regimeWitness`, le résidu est nul sur le membre en ligne de hauteur `1` et non nul sur
les deux jumeaux de hauteur `2`. -/
theorem regimeWitness_change_detected :
    changeResidueAt (1 / 2) 1 = 0 ∧ changeResidueAt (1 / 4) 2 ≠ 0 ∧
      changeResidueAt (3 / 4) 2 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [changeResidueAt_eq_zero_iff (by norm_num) (by norm_num)]
  · rw [Ne, changeResidueAt_eq_zero_iff (by norm_num) (by norm_num)]
    norm_num
  · rw [Ne, changeResidueAt_eq_zero_iff (by norm_num) (by norm_num)]
    norm_num

/-! ## 4. Le bit de changement : ce qui est disponible avant l'arrivée (auteur, 2026-10-01)

Énoncé de l'auteur : « inutile de reconstruire `β`. Il faut seulement prédire un bit de changement.
Quelle donnée disponible avant l'arrivée détermine si `D = 0` ou `D ≠ 0` ? » La fonction réelle sur
la ligne, au-dessus de la hauteur de départ, ne lit aucun membre d'arrivée. -/

/-- Un membre en ligne annule la fonction réelle à sa hauteur. -/
theorem lineValue_zero_of_onLine (w : TNonTrivialZetaZero)
    (h : rZeroRadialPosition w = 1 / 2) : lineValue (rZeroHeight w) = 0 := by
  have he : linePoint (rZeroHeight w) = w.1 := Complex.ext h.symm rfl
  exact (onLine_zero_iff_lineValue _).mp (he ▸ w.2)

/-- **Le bit de changement est une course.** Sur un passage vertical, `D = 0` à l'arrivée si et
seulement si aucun membre hors ligne n'a une hauteur au-dessus du départ atteinte avant que la
fonction réelle sur la ligne ne s'annule. -/
theorem change_bit_iff_race (p : TZeroPassage) (hV : VerticalPassage p) :
    changeResidue p.zLaterMember = 0 ↔
      ¬ ∃ w : TNonTrivialZetaZero, rZeroRadialPosition w ≠ 1 / 2 ∧
        rZeroHeight p.zEarlierMember < rZeroHeight w ∧
        ∀ t : ℝ, rZeroHeight p.zEarlierMember < t → t < rZeroHeight w → lineValue t ≠ 0 := by
  constructor
  · rintro h0 ⟨w, hoff, hTw, hfree⟩
    have hOnL := (changeResidue_eq_zero_iff _).mp h0
    have hz := lineValue_zero_of_onLine _ hOnL
    have hle : rZeroHeight w ≤ rZeroHeight p.zLaterMember := by
      by_contra hlt
      exact hfree _ hV (not_le.mp hlt) hz
    obtain ⟨w', hT', hβ'⟩ : ∃ w' : TNonTrivialZetaZero,
        rZeroHeight w' = rZeroHeight w ∧ rZeroRadialPosition w' < 1 / 2 := by
      rcases lt_or_gt_of_ne hoff with hlt | hgt
      · exact ⟨w, rfl, hlt⟩
      · exact ⟨zMirrorZero w, thm_mirror_sameHeight w, by
          rw [thm_mirror_radialPosition]; linarith⟩
    apply p.hConsecutive.2
    refine ⟨w', ?_, ?_⟩
    · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
      left
      rw [hT']
      exact hTw
    · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
      rcases lt_or_eq_of_le hle with hlt | heq
      · left
        rw [hT']
        exact hlt
      · right
        exact ⟨by rw [hT']; exact heq, by rw [hOnL]; exact hβ'⟩
  · intro h
    by_contra h0
    exact h ⟨p.zLaterMember, fun hOn => h0 ((changeResidue_eq_zero_iff _).mpr hOn), hV,
      fun t h1 h2 => lineValue_ne_zero_between p h1 h2⟩

/-- **L'échéance.** Si la fonction réelle change de signe entre `t₁` et `t₂` au-dessus du départ,
l'arrivée a lieu avant `t₂` : le changement, s'il a lieu, a lieu dans une fenêtre que la fonction
réelle fixe sans lire l'arrivée. -/
theorem arrival_before_sign_change (p : TZeroPassage) {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁)
    (hE : rZeroHeight p.zEarlierMember ≤ t₁) (h12 : t₁ < t₂)
    (h : lineValue t₁ * lineValue t₂ < 0) : rZeroHeight p.zLaterMember < t₂ := by
  obtain ⟨z, _, hz1, hz2⟩ := onLine_member_of_sign_change h0 h12 h
  by_contra hge
  apply p.hConsecutive.2
  exact ⟨z.1,
    (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mpr (Or.inl (lt_of_le_of_lt hE hz1)),
    (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mpr
      (Or.inl (lt_of_lt_of_le hz2 (not_lt.mp hge)))⟩

#print axioms change_bit_iff_race
#print axioms arrival_before_sign_change
#print axioms changeResidueAt_eq_zero_iff
#print axioms changeResidueAt_window
#print axioms changeResidue_eq_position_sub
#print axioms changeResidue_eq_radial
#print axioms change_detector
#print axioms changeResidue_ledger
#print axioms engaged_changeResidue_from_ledger
#print axioms passage_change_detector
#print axioms predictor_exists
#print axioms predictor_closes
#print axioms engaged_persists_of_predictor
#print axioms predictor_pair_iff_heightOnly
#print axioms changeResidue_enclosed_by_remainder_growth
#print axioms changeResidue_zero_of_remainder_sqrt_growth
#print axioms changeResidue_vanishes_iff_remainder_sqrt_growth
#print axioms engagedBreakWorld_change_detected
#print axioms regimeWitness_change_detected

end RHV6Fresh
