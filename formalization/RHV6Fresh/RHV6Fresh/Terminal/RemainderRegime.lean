/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TotalityPays

/-!
# Le régime du reste : ce que des zéros sur la ligne peuvent payer (module isolé, non importé par la chaîne)

Suite de `TotalityPays.lean`. Là, le prix d'un couple hors ligne était écrit : sous demande de niveau
relatif borné aux rencontres, le reste doit fournir une annulation relative sans borne. Ici, on écrit
ce qu'un zéro de la ligne peut payer : son amplitude relative est son poids `m / (|ρ| |ρ+1|)`, et la
série de ces poids converge (déduite de la sommabilité compilée de la série des parts, `x = 2`).

Faits compilés, sans prémisse :

* la part de tout indice a pour module `poids · x^β` et pour amplitude relative `poids · x^(β − 1/2)` ;
* la somme de tous les poids est finie (`indexWeight_summable`, `totalLineWeight`) ;
* le reste, en amplitude relative, est majoré par la somme sur ses membres des poids multipliés par la
  dérive radiale `x^(β − 1/2)` de chacun (`restRelativeAmplitude_le`) ;
* si aucun zéro du reste n'est strictement à droite de un demi (hypothèse NOMMÉE, `RestNotRight`,
  jamais posée comme un fait), le reste est borné par la somme totale des poids ;
* composition avec `TotalityPays.lean` : sous demande bornée aux rencontres (hypothèse nommée) et
  reste non à droite (hypothèse nommée), le membre n'est pas une arrivée basse ;
* **propagation**, inconditionnelle sur le reste : sous demande bornée aux rencontres, une arrivée
  basse n'est jamais seule ; un zéro hors du couple est strictement à droite de un demi
  (`exists_right_of_low_of_bounded_demand`) ;
* **l'historique ne paie pas** : pour toute famille finie d'indices non à droite de la ligne (en
  particulier toute famille finie de zéros ON, de toute hauteur), le manque, demande moins couple
  moins famille, n'est borné à aucune rencontre dès que la demande l'est
  (`shortfall_unbounded_of_bounded_demand`). C'est le jumeau compilé de E396.

Ce que ce module n'établit pas : rien sur la position radiale d'aucun zéro sans les hypothèses
nommées ; le bornage de la demande n'est pas dérivé ; supposer le reste sur la ligne serait supposer la
question. La chaîne et sa prémisse unique sont intactes.

Aucun axiome, aucun `sorry`.
-/

namespace RHV6Fresh

open Complex RHV3Lean

/-! ## 1. Le poids d'un indice : son amplitude relative sur la ligne -/

/-- Poids d'un indice de la formule explicite : `m / (|ρ| · |ρ+1|)`. -/
noncomputable def indexWeight (σ : ExplicitIndex) : ℝ :=
  (zetaZeroMultiplicity (σ : ℂ) : ℝ) / (‖(σ : ℂ)‖ * ‖(σ : ℂ) + 1‖)

theorem indexDenominator_pos (σ : ExplicitIndex) : 0 < ‖(σ : ℂ)‖ * ‖(σ : ℂ) + 1‖ :=
  mul_pos (norm_pos_iff.mpr (explicitIndex_ne_zero σ).1) (norm_pos_iff.mpr (explicitIndex_ne_zero σ).2)

theorem indexWeight_nonneg (σ : ExplicitIndex) : 0 ≤ indexWeight σ :=
  div_nonneg (Nat.cast_nonneg _) (indexDenominator_pos σ).le

/-- Module de la part d'un indice : `poids · x^β`. -/
theorem norm_residueTerm_eq (σ : ExplicitIndex) {x : ℝ} (hx : 0 < x) :
    ‖nontrivialZeroResidueTerm x σ‖ = indexWeight σ * x ^ (σ : ℂ).re := by
  rw [residueTerm_eq_memberJoint σ hx]
  unfold memberJoint
  rw [jointTerm_norm_eq]
  have hm : (0 : ℝ) ≤ zetaZeroMultiplicity (σ : ℂ) := Nat.cast_nonneg _
  have hq : 0 < x ^ (σ : ℂ).re / (‖(σ : ℂ)‖ * ‖(σ : ℂ) + 1‖) :=
    div_pos (Real.rpow_pos_of_pos hx _) (indexDenominator_pos σ)
  rw [abs_of_nonneg hm, abs_of_pos hq]
  unfold indexWeight
  ring

/-- Amplitude relative de la part d'un indice : `poids · x^(β − 1/2)`. -/
theorem residueTerm_relative_eq (σ : ExplicitIndex) {x : ℝ} (hx : 0 < x) :
    ‖nontrivialZeroResidueTerm x σ‖ / x ^ (1 / 2 : ℝ) = indexWeight σ * x ^ ((σ : ℂ).re - 1 / 2) := by
  rw [norm_residueTerm_eq σ hx, Real.rpow_sub hx]
  have h1 : x ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  field_simp

/-! ## 2. La somme des poids est finie -/

/-- **Sommabilité des poids** : comparaison avec la série des parts au point `2`, dont la sommabilité
est compilée. -/
theorem indexWeight_summable : Summable indexWeight := by
  have hs : Summable (fun σ : ExplicitIndex => ‖nontrivialZeroResidueTerm 2 σ‖) :=
    summable_norm_iff.mpr (nontrivial_zero_residue_series_summable (by norm_num))
  refine Summable.of_nonneg_of_le indexWeight_nonneg (fun σ => ?_) hs
  rw [norm_residueTerm_eq σ (by norm_num)]
  have h1 : (1 : ℝ) ≤ 2 ^ (σ : ℂ).re :=
    Real.one_le_rpow (by norm_num) (isNontrivialZetaZero_re_mem_Ioo σ.property).1.le
  calc indexWeight σ = indexWeight σ * 1 := (mul_one _).symm
    _ ≤ indexWeight σ * 2 ^ (σ : ℂ).re := mul_le_mul_of_nonneg_left h1 (indexWeight_nonneg σ)

/-- La somme totale des poids : l'amplitude relative d'une famille entièrement sur la ligne (borne de norme). -/
noncomputable def totalLineWeight : ℝ := ∑' σ : ExplicitIndex, indexWeight σ

theorem totalLineWeight_nonneg : 0 ≤ totalLineWeight := tsum_nonneg indexWeight_nonneg

/-- Sur tout sous-ensemble d'indices, la somme des poids ne dépasse pas la somme totale. -/
theorem tsum_indexWeight_subset_le (S : Set ExplicitIndex) :
    ∑' σ : S, indexWeight σ ≤ totalLineWeight := by
  unfold totalLineWeight
  exact Summable.tsum_le_tsum_of_inj (fun σ : S => (σ : ExplicitIndex)) Subtype.coe_injective
    (fun c _ => indexWeight_nonneg c) (fun _ => le_rfl) (indexWeight_summable.subtype _)
    indexWeight_summable

/-- Poids multiplié par la dérive radiale : au plus le poids quand la position n'est pas à droite. -/
theorem weighted_le_weight (σ : ExplicitIndex) (hσ : (σ : ℂ).re ≤ 1 / 2) {x : ℝ} (hx : 1 ≤ x) :
    indexWeight σ * x ^ ((σ : ℂ).re - 1 / 2) ≤ indexWeight σ := by
  have h : x ^ ((σ : ℂ).re - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  calc indexWeight σ * x ^ ((σ : ℂ).re - 1 / 2) ≤ indexWeight σ * 1 :=
        mul_le_mul_of_nonneg_left h (indexWeight_nonneg σ)
    _ = indexWeight σ := mul_one _

/-! ## 3. Le reste est majoré par les poids de ses membres, chacun avec sa dérive -/

/-- Le reste en norme : au plus la somme, sur ses membres, de `poids · x^β`. -/
theorem norm_restOfPair_le (l : TrueZero) {x : ℝ} (hx : 1 < x) :
    ‖restOfPair l x‖ ≤
      ∑' ρ : ((pairIndices l : Set ExplicitIndex)ᶜ : Set ExplicitIndex),
        indexWeight ρ * x ^ (ρ : ℂ).re := by
  unfold restOfPair
  have hs := (summable_norm_iff.mpr (nontrivial_zero_residue_series_summable hx)).subtype
    (· ∈ ((pairIndices l : Set ExplicitIndex)ᶜ : Set ExplicitIndex))
  refine (norm_tsum_le_tsum_norm hs).trans_eq ?_
  exact tsum_congr (fun ρ => norm_residueTerm_eq ρ (by linarith))

/-- **Le reste en amplitude relative** : au plus la somme, sur ses membres, des poids multipliés par la
dérive radiale `x^(β − 1/2)` de chacun. -/
theorem restRelativeAmplitude_le (l : TrueZero) {x : ℝ} (hx : 1 < x) :
    restRelativeAmplitude l x ≤
      ∑' ρ : ((pairIndices l : Set ExplicitIndex)ᶜ : Set ExplicitIndex),
        indexWeight ρ * x ^ ((ρ : ℂ).re - 1 / 2) := by
  have hx0 : (0 : ℝ) < x := by linarith
  unfold restRelativeAmplitude
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)]
  refine (norm_restOfPair_le l hx).trans_eq ?_
  rw [← tsum_mul_right]
  exact tsum_congr (fun ρ => by rw [mul_assoc, ← Real.rpow_add hx0, sub_add_cancel])

/-! ## 4. Hypothèse nommée : aucun zéro du reste strictement à droite de un demi -/

/-- Hypothèse NOMMÉE (jamais posée comme un fait) : aucun zéro hors du couple n'est strictement à
droite de un demi. -/
def RestNotRight (l : TrueZero) : Prop :=
  ∀ ρ : ExplicitIndex, ρ ∉ pairIndices l → (ρ : ℂ).re ≤ 1 / 2

/-- Sous `RestNotRight`, le reste est borné par la somme totale des poids, en tout point. -/
theorem restRelativeAmplitude_le_total (l : TrueZero) (h : RestNotRight l) {x : ℝ} (hx : 1 < x) :
    restRelativeAmplitude l x ≤ totalLineWeight := by
  refine (restRelativeAmplitude_le l hx).trans ?_
  refine le_trans ?_ (tsum_indexWeight_subset_le ((pairIndices l : Set ExplicitIndex)ᶜ))
  have hmem : ∀ ρ : ((pairIndices l : Set ExplicitIndex)ᶜ : Set ExplicitIndex),
      (ρ : ℂ).re ≤ 1 / 2 := fun ρ => h ρ (fun hρ => ρ.2 (Finset.mem_coe.mpr hρ))
  have hle : ∀ ρ : ((pairIndices l : Set ExplicitIndex)ᶜ : Set ExplicitIndex),
      indexWeight ρ * x ^ ((ρ : ℂ).re - 1 / 2) ≤ indexWeight ρ :=
    fun ρ => weighted_le_weight ρ (hmem ρ) hx.le
  refine Summable.tsum_le_tsum hle ?_ (indexWeight_summable.subtype _)
  exact Summable.of_nonneg_of_le
    (fun ρ => mul_nonneg (indexWeight_nonneg ρ) (Real.rpow_nonneg (by linarith) _)) hle
    (indexWeight_summable.subtype _)

/-- Composition avec `TotalityPays.lean` : demande bornée aux rencontres (hypothèse nommée) et reste
non à droite (hypothèse nommée) entraînent que le membre n'est pas une arrivée basse. Ce n'est pas une
exclusion : les deux hypothèses restent des hypothèses. -/
theorem not_low_of_bounded_demand_and_restNotRight (l : TrueZero)
    (hdem : ∃ C : ℝ, ∀ I : PrimeGapInterval, demandRelativeLevel (meetingPoint I) ≤ C)
    (h : RestNotRight l) : ¬ rZeroRadialPosition l.1 < 1 / 2 :=
  not_low_of_bounded_demand_and_rest l hdem
    ⟨totalLineWeight, fun I => restRelativeAmplitude_le_total l h (one_lt_meetingPoint I)⟩

/-- **Propagation** (inconditionnelle sur le reste) : sous demande bornée aux rencontres, une arrivée
basse n'est jamais seule : un zéro hors de son couple est strictement à droite de un demi. -/
theorem exists_right_of_low_of_bounded_demand (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2)
    (hdem : ∃ C : ℝ, ∀ I : PrimeGapInterval, demandRelativeLevel (meetingPoint I) ≤ C) :
    ∃ ρ : ExplicitIndex, ρ ∉ pairIndices l ∧ 1 / 2 < (ρ : ℂ).re := by
  by_contra hcon
  push Not at hcon
  exact not_low_of_bounded_demand_and_restNotRight l hdem (fun ρ hρ => hcon ρ hρ) hlow

/-! ## 5. L'historique ne paie pas : aucune famille finie non à droite ne couvre le prix -/

/-- Part d'une famille finie d'indices au point `x`. -/
noncomputable def familySum (F : Finset ExplicitIndex) (x : ℝ) : ℂ :=
  ∑ ρ ∈ F, nontrivialZeroResidueTerm x ρ

/-- Une famille finie dont aucun membre n'est à droite de un demi a une amplitude relative bornée par
la somme totale des poids, en tout point. -/
theorem familySum_relative_le (F : Finset ExplicitIndex) (hF : ∀ ρ ∈ F, (ρ : ℂ).re ≤ 1 / 2)
    {x : ℝ} (hx : 1 < x) :
    ‖familySum F x‖ / x ^ (1 / 2 : ℝ) ≤ totalLineWeight := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)]
  calc ‖familySum F x‖ ≤ ∑ ρ ∈ F, ‖nontrivialZeroResidueTerm x ρ‖ := norm_sum_le _ _
    _ = ∑ ρ ∈ F, indexWeight ρ * x ^ (ρ : ℂ).re :=
        Finset.sum_congr rfl (fun ρ _ => norm_residueTerm_eq ρ hx0)
    _ ≤ ∑ ρ ∈ F, indexWeight ρ * x ^ (1 / 2 : ℝ) :=
        Finset.sum_le_sum (fun ρ hρ => mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hx.le (hF ρ hρ)) (indexWeight_nonneg ρ))
    _ = (∑ ρ ∈ F, indexWeight ρ) * x ^ (1 / 2 : ℝ) := (Finset.sum_mul _ _ _).symm
    _ ≤ totalLineWeight * x ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (Summable.sum_le_tsum F (fun ρ _ => indexWeight_nonneg ρ) indexWeight_summable)
          (Real.rpow_nonneg hx0.le _)

/-- Le manque : la demande moins le couple moins la part d'une famille finie. -/
noncomputable def shortfall (l : TrueZero) (F : Finset ExplicitIndex) (x : ℝ) : ℂ :=
  smoothedRemainder x - pairJoint l x - familySum F x

/-- Le manque, en amplitude relative, vaut au moins le couple moins la demande moins la somme totale
des poids, pour toute famille finie non à droite. -/
theorem shortfall_relative_ge (l : TrueZero) (F : Finset ExplicitIndex)
    (hF : ∀ ρ ∈ F, (ρ : ℂ).re ≤ 1 / 2) {x : ℝ} (hx : 1 < x) :
    pairRelativeAmplitude l x - demandRelativeLevel x - totalLineWeight ≤
      ‖shortfall l F x‖ / x ^ (1 / 2 : ℝ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have h1 : ‖pairJoint l x‖ - ‖smoothedRemainder x‖ - ‖familySum F x‖ ≤ ‖shortfall l F x‖ := by
    unfold shortfall
    have h2 := norm_sub_norm_le (pairJoint l x) (smoothedRemainder x)
    have h3 : ‖pairJoint l x - smoothedRemainder x‖ = ‖smoothedRemainder x - pairJoint l x‖ :=
      norm_sub_rev _ _
    have h4 := norm_sub_norm_le (smoothedRemainder x - pairJoint l x) (familySum F x)
    linarith
  have hS := familySum_relative_le F hF hx
  have hdiv := div_le_div_of_nonneg_right h1 (Real.rpow_pos_of_pos hx0 (1 / 2 : ℝ)).le
  rw [sub_div, sub_div] at hdiv
  unfold pairRelativeAmplitude demandRelativeLevel
  linarith

/-- **L'historique ne paie pas** : pour un couple hors ligne, sous demande bornée aux rencontres, le
manque après toute famille finie non à droite (en particulier toute famille finie de zéros ON, de
toute hauteur) n'est borné à aucune rencontre. Jumeau compilé de E396. -/
theorem shortfall_unbounded_of_bounded_demand (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2)
    (F : Finset ExplicitIndex) (hF : ∀ ρ ∈ F, (ρ : ℂ).re ≤ 1 / 2) {C : ℝ}
    (hC : ∀ I : PrimeGapInterval, demandRelativeLevel (meetingPoint I) ≤ C) (c : ℝ) :
    ∃ I : PrimeGapInterval, c < ‖shortfall l F (meetingPoint I)‖ / (meetingPoint I) ^ (1 / 2 : ℝ) := by
  obtain ⟨I, hI⟩ := pairRelativeAmplitude_unbounded l hlow (c + C + totalLineWeight)
  refine ⟨I, ?_⟩
  have h1 := shortfall_relative_ge l F hF (one_lt_meetingPoint I)
  have h2 := hC I
  linarith

end RHV6Fresh
