/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ArrivalFiberHypotheses
import RHV6Fresh.Terminal.EngagedNoTranslation
import RHV6Fresh.Terminal.TowerTwoSidedRoom

/-!
# Comparaison directe de l'arrivée au premier zéro par les contacts (auteur, 2026-10-12)

Identité de l'auteur, instanciée aux contacts authentiques :
`log(C_{l,k}/C_{1,k}) = log λ_l + (arctan(2T_l) + kπ)/T_l − (arctan(2T_1) + kπ)/T_1`.
Elle sépare exactement le DÉPLACEMENT RADIAL de l'arrivée (`log λ_l ≥ 0`, nul ⟺ en ligne), le changement des contacts
produit par la hauteur d'arrivée (`lineHeightShift`, indépendant de `β_l`), et les contacts fixes du premier zéro. Aucune
« place disponible » n'intervient : seules des égalités et des comparaisons de contacts.

Ce que ce module établit, dans sa portée exacte :
- l'identité (`contact_log_ratio`, `contact_log_ratio_onLine`) ;
- le terme de hauteur décroît strictement avec l'indice (`lineHeightShift_strictAnti_index`) et est strictement négatif à tout
  indice `k ≥ 0` dès que la hauteur dépasse celle du premier zéro (`lineHeightShift_neg`) ;
- lecture du signe : `C_{l,k} < C_{1,k} ⟺ log λ_l < −lineHeightShift` (`contact_lt_iff_factor`) ;
- une comparaison de contacts `C_{l,k} ≤ C_{1,k}` ne donne `λ_l ≤ 1` qu'aux indices où `lineHeightShift ≥ 0`
  (`factor_le_one_of_contact_le`), indices tous NÉGATIFS (contacts strictement sous `1`, aucun premier), et à ces indices
  l'arrivée EN LIGNE elle-même ne satisfait pas la comparaison stricte (`onLine_fails_strict_comparison`) ;
- l'ordre des contacts par rapport au premier zéro, à TOUS les indices `k ≥ 0`, est satisfait par une grille strictement
  translatée (`exists_shifted_grid_nested_in_first`) : il ne fournit pas la borne supérieure `λ ≤ 1` ;
- la fenêtre `λ < e^{1/(2T²)}` entraîne à elle seule l'ordre à tout indice où `1/(2T_l²) ≤ −lineHeightShift`
  (`contact_order_of_window`) : l'emboîtement n'y ajoute rien.
Aucune hypothèse ajoutée ; aucun énoncé ne ferme le but.
-/

namespace RHV6Fresh

open RHV3Lean

/-- Changement des contacts produit par la hauteur seule, entre la hauteur `T₁` et la hauteur `T`, à l'indice `k` :
`(arctan(2T) + kπ)/T − (arctan(2T₁) + kπ)/T₁` (écrit avec `linePhase T = arctan(T/(1/2))`). -/
noncomputable def lineHeightShift (T₁ T : ℝ) (k : ℤ) : ℝ :=
  (linePhase T + (k : ℝ) * Real.pi) / T - (linePhase T₁ + (k : ℝ) * Real.pi) / T₁

theorem linePhase_eq_arctan (T : ℝ) : linePhase T = Real.arctan (2 * T) := by
  unfold linePhase; congr 1; ring

theorem lineHeightShift_eq_arctan (T₁ T : ℝ) (k : ℤ) :
    lineHeightShift T₁ T k =
      (Real.arctan (2 * T) + (k : ℝ) * Real.pi) / T - (Real.arctan (2 * T₁) + (k : ℝ) * Real.pi) / T₁ := by
  unfold lineHeightShift; rw [linePhase_eq_arctan, linePhase_eq_arctan]

/-- Découpage du terme de hauteur : part d'indice `kπ(1/T − 1/T₁)` et part de phase de ligne. -/
theorem lineHeightShift_split (T₁ T : ℝ) (k : ℤ) :
    lineHeightShift T₁ T k =
      (k : ℝ) * Real.pi * (1 / T - 1 / T₁) + (linePhase T / T - linePhase T₁ / T₁) := by
  unfold lineHeightShift; ring

/-- Logarithme d'un contact authentique. -/
theorem log_contactMinusAt (z : TrueZero) (k : ℤ) :
    Real.log (contactMinusAt z k) =
      (Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) + (k : ℝ) * Real.pi) / rZeroHeight z.1 := by
  rw [contactMinusAt_eq_exp, Real.log_exp]

/-- Logarithme du facteur radial = déplacement radial, `(arctan(T/β) − arctan(2T))/T`. -/
theorem log_radialFactor (z : TrueZero) :
    Real.log (radialFactor z) =
      (Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) - linePhase (rZeroHeight z.1)) / rZeroHeight z.1 := by
  unfold radialFactor; rw [Real.log_exp, towerMotion_phase]

/-- Le déplacement radial est positif ou nul pour tout membre au plus en ligne, nul ⟺ en ligne. -/
theorem log_radialFactor_nonneg (z : TrueZero) (hβ : rZeroRadialPosition z.1 ≤ 1 / 2) :
    0 ≤ Real.log (radialFactor z) := by
  rw [radialFactor_eq_arctan]
  have h := (parameter_grid_admissible z.2 (thm_zeroRadialPosition_positive z.1) hβ).1
  exact Real.log_nonneg h

/-- **Identité de l'auteur, forme générale** (deux membres quelconques) :
`log(C_{z,k}/C_{w,k}) = log λ_z − log λ_w + lineHeightShift T_w T_z k`. -/
theorem contact_log_ratio (z w : TrueZero) (k : ℤ) :
    Real.log (contactMinusAt z k / contactMinusAt w k) =
      Real.log (radialFactor z) - Real.log (radialFactor w) +
        lineHeightShift (rZeroHeight w.1) (rZeroHeight z.1) k := by
  rw [Real.log_div (contactMinusAt_positive z k).ne' (contactMinusAt_positive w k).ne', log_contactMinusAt,
    log_contactMinusAt, log_radialFactor, log_radialFactor]
  unfold lineHeightShift
  ring

/-- **Identité de l'auteur, instanciée au premier zéro (ou à tout membre en ligne `w`)** :
`log(C_{z,k}/C_{w,k}) = log λ_z + (arctan(2T_z) + kπ)/T_z − (arctan(2T_w) + kπ)/T_w`. Le facteur de l'arrivée n'entre que
dans le premier terme ; les contacts de `w` ne dépendent pas de `z`. -/
theorem contact_log_ratio_onLine (z w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2) (k : ℤ) :
    Real.log (contactMinusAt z k / contactMinusAt w k) =
      Real.log (radialFactor z) +
        ((Real.arctan (2 * rZeroHeight z.1) + (k : ℝ) * Real.pi) / rZeroHeight z.1 -
          (Real.arctan (2 * rZeroHeight w.1) + (k : ℝ) * Real.pi) / rZeroHeight w.1) := by
  rw [contact_log_ratio, (radialFactor_eq_one_iff w).mpr hw, Real.log_one, sub_zero, lineHeightShift_eq_arctan]

/-- **Le terme de hauteur décroît strictement avec l'indice** dès que la hauteur dépasse celle du premier zéro : à chaque
étage le rapport des contacts est divisé par `exp(π(1/T₁ − 1/T))`. -/
theorem lineHeightShift_strictAnti_index {T₁ T : ℝ} (hT₁ : 0 < T₁) (hT : T₁ < T) {k k' : ℤ} (hk : k < k') :
    lineHeightShift T₁ T k' < lineHeightShift T₁ T k := by
  rw [lineHeightShift_split, lineHeightShift_split]
  have h1 : 1 / T - 1 / T₁ < 0 := by
    rw [sub_neg]; exact one_div_lt_one_div_of_lt hT₁ hT
  have hkk : (k : ℝ) < k' := by exact_mod_cast hk
  nlinarith [Real.pi_pos, mul_lt_mul_of_pos_right hkk Real.pi_pos]

/-- Le terme de hauteur est strictement négatif à tout indice où la phase de ligne du premier zéro plus `kπ` dépasse `1/2`
(donc à tout `k ≥ 1`, et à `k = 0` dès que `T₁ ≥ 1/2`). -/
theorem lineHeightShift_neg {T₁ T : ℝ} (hT₁ : 0 < T₁) (hT : T₁ < T) {k : ℤ}
    (hk : 1 / 2 ≤ linePhase T₁ + (k : ℝ) * Real.pi) : lineHeightShift T₁ T k < 0 := by
  have hTpos : 0 < T := hT₁.trans hT
  have hinc := phase_increment_lt (β := 1 / 2) (T := T₁) (T' := T) (by norm_num) hT₁ hT
  unfold lineHeightShift linePhase
  rw [sub_neg, div_lt_div_iff₀ hTpos hT₁]
  have hd : 0 < T - T₁ := sub_pos.mpr hT
  unfold linePhase at hk
  nlinarith [mul_le_mul_of_nonneg_left hk hd.le]

/-- Indice `k ≥ 1` : terme de hauteur strictement négatif. -/
theorem lineHeightShift_neg_of_one_le {T₁ T : ℝ} (hT₁ : 0 < T₁) (hT : T₁ < T) {k : ℤ} (hk : 1 ≤ k) :
    lineHeightShift T₁ T k < 0 := by
  apply lineHeightShift_neg hT₁ hT
  have hφ : 0 < linePhase T₁ := Real.arctan_pos.mpr (div_pos hT₁ (by norm_num))
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith [Real.pi_gt_three]

/-- Indice `k ≥ 0` et `T₁ ≥ 1/2` : terme de hauteur strictement négatif (le premier zéro est bien au-delà). -/
theorem lineHeightShift_neg_of_nonneg {T₁ T : ℝ} (hT₁ : 1 / 2 ≤ T₁) (hT : T₁ < T) {k : ℤ} (hk : 0 ≤ k) :
    lineHeightShift T₁ T k < 0 := by
  apply lineHeightShift_neg (by linarith) hT
  have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (1 : ℝ) ≤ T₁ / (1 / 2) := by rw [le_div_iff₀ (by norm_num)]; linarith
  have h2 : Real.arctan 1 ≤ linePhase T₁ := Real.arctan_strictMono.monotone h1
  rw [Real.arctan_one] at h2
  nlinarith [Real.pi_gt_three, Real.pi_pos]

/-- **Lecture du signe** : à l'indice `k`, le contact de `z` est en deçà de celui d'un membre en ligne `w` ⟺ le déplacement
radial de `z` est strictement sous `−lineHeightShift`. -/
theorem contact_lt_iff_factor (z w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2) (k : ℤ) :
    contactMinusAt z k < contactMinusAt w k ↔
      Real.log (radialFactor z) < -lineHeightShift (rZeroHeight w.1) (rZeroHeight z.1) k := by
  have hz := contactMinusAt_positive z k
  have hw' := contactMinusAt_positive w k
  rw [← Real.log_lt_log_iff hz hw', ← sub_neg, ← Real.log_div hz.ne' hw'.ne', contact_log_ratio,
    (radialFactor_eq_one_iff w).mpr hw, Real.log_one, sub_zero]
  constructor <;> intro h <;> linarith

theorem contact_le_iff_factor (z w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2) (k : ℤ) :
    contactMinusAt z k ≤ contactMinusAt w k ↔
      Real.log (radialFactor z) ≤ -lineHeightShift (rZeroHeight w.1) (rZeroHeight z.1) k := by
  have hz := contactMinusAt_positive z k
  have hw' := contactMinusAt_positive w k
  rw [← Real.log_le_log_iff hz hw', ← sub_nonpos, ← Real.log_div hz.ne' hw'.ne', contact_log_ratio,
    (radialFactor_eq_one_iff w).mpr hw, Real.log_one, sub_zero]
  constructor <;> intro h <;> linarith

/-- **Où une comparaison de contacts donnerait la borne supérieure un.** Si `C_{z,k} ≤ C_{w,k}` (`w` en ligne) à un indice
où le terme de hauteur est `≥ 0`, alors `λ_z ≤ 1`. -/
theorem factor_le_one_of_contact_le (z w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2) (k : ℤ)
    (hShift : 0 ≤ lineHeightShift (rZeroHeight w.1) (rZeroHeight z.1) k)
    (h : contactMinusAt z k ≤ contactMinusAt w k) : radialFactor z ≤ 1 := by
  have := (contact_le_iff_factor z w hw k).mp h
  rw [← Real.log_le_log_iff (radialFactor_pos z) one_pos, Real.log_one]
  linarith

/-- Avec la borne inférieure acquise (`β_z ≤ 1/2`), une telle comparaison donnerait exactement `λ_z = 1`, donc `z` en ligne. -/
theorem onLine_of_contact_le (z w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2)
    (hβ : rZeroRadialPosition z.1 ≤ 1 / 2) (k : ℤ)
    (hShift : 0 ≤ lineHeightShift (rZeroHeight w.1) (rZeroHeight z.1) k)
    (h : contactMinusAt z k ≤ contactMinusAt w k) : rZeroRadialPosition z.1 = 1 / 2 := by
  have hle := factor_le_one_of_contact_le z w hw k hShift h
  have hge : 1 ≤ radialFactor z := by
    rw [radialFactor_eq_arctan]
    exact (parameter_grid_admissible z.2 (thm_zeroRadialPosition_positive z.1) hβ).1
  exact (radialFactor_eq_one_iff z).mp (le_antisymm hle hge)

/-- **À ces indices, l'arrivée en ligne elle-même ne satisfait pas la comparaison stricte** : avec `λ_z = 1` et
`lineHeightShift ≥ 0`, `C_{z,k} ≥ C_{w,k}`. La comparaison n'est donc pas une obligation du régime conservé. -/
theorem onLine_fails_strict_comparison (z w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2)
    (hz : rZeroRadialPosition z.1 = 1 / 2) (k : ℤ)
    (hShift : 0 ≤ lineHeightShift (rZeroHeight w.1) (rZeroHeight z.1) k) :
    ¬ contactMinusAt z k < contactMinusAt w k := by
  rw [contact_lt_iff_factor z w hw k, (radialFactor_eq_one_iff z).mpr hz, Real.log_one]
  linarith

/-- **Les indices où le terme de hauteur est `≥ 0` sont tous négatifs** dès que `T_w ≥ 1/2 ` et `T_w < T_z`. -/
theorem index_neg_of_heightShift_nonneg {T₁ T : ℝ} (hT₁ : 1 / 2 ≤ T₁) (hT : T₁ < T) {k : ℤ}
    (hShift : 0 ≤ lineHeightShift T₁ T k) : k < 0 := by
  by_contra hk
  exact absurd hShift (not_le.mpr (lineHeightShift_neg_of_nonneg hT₁ hT (not_lt.mp hk)))

/-- À tout indice négatif, le contact est strictement sous `1` : aucun nombre premier n'y est lu. -/
theorem contact_lt_one_of_neg (z : TrueZero) {k : ℤ} (hk : k < 0) : contactMinusAt z k < 1 := by
  rw [contactMinusAt_eq_exp, Real.exp_lt_one_iff]
  have hφ := Real.arctan_lt_pi_div_two (rZeroHeight z.1 / rZeroRadialPosition z.1)
  have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk
  have : (k : ℝ) * Real.pi ≤ -Real.pi := by nlinarith [Real.pi_pos]
  exact div_neg_of_neg_of_pos (by linarith [Real.pi_pos]) z.2

/-- **Composition** : toute comparaison de contacts avec un membre en ligne `w` (`1/2 ≤ T_w < T_z`) qui force `λ_z ≤ 1`
se place à un indice négatif, à un contact strictement sous `1`, et l'arrivée en ligne y viole la comparaison stricte.
Aux indices `k ≥ 0` (tous les contacts `> 1`, où vivent les premiers), `lineHeightShift < 0` et la comparaison ne borne
`log λ_z` que par la quantité strictement positive `−lineHeightShift`. -/
theorem upper_bound_one_only_below_one (z w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2)
    (hT₁ : 1 / 2 ≤ rZeroHeight w.1) (hT : rZeroHeight w.1 < rZeroHeight z.1) :
    (∀ k : ℤ, 0 ≤ lineHeightShift (rZeroHeight w.1) (rZeroHeight z.1) k →
        k < 0 ∧ contactMinusAt z k < 1 ∧
          (rZeroRadialPosition z.1 = 1 / 2 → ¬ contactMinusAt z k < contactMinusAt w k)) ∧
      ∀ k : ℤ, 0 ≤ k → 0 < -lineHeightShift (rZeroHeight w.1) (rZeroHeight z.1) k := by
  refine ⟨fun k hS => ?_, fun k hk => ?_⟩
  · have hkneg := index_neg_of_heightShift_nonneg hT₁ hT hS
    exact ⟨hkneg, contact_lt_one_of_neg z hkneg, fun hz => onLine_fails_strict_comparison z w hw hz k hS⟩
  · have := lineHeightShift_neg_of_nonneg hT₁ hT hk
    linarith

/-- Grille paramétrique en deçà de la grille de ligne du premier zéro, à l'indice `k`, en logarithmes :
`log λ(β,T) < −lineHeightShift T₁ T k`. -/
theorem param_grid_lt_line_iff {β T T₁ : ℝ} (_hT : 0 < T) (_hT₁ : 0 < T₁) (k : ℤ) :
    windingContact β T k < lineContact T₁ k ↔ Real.log (paramFactor β T) < -lineHeightShift T₁ T k := by
  unfold windingContact lineContact paramFactor lineHeightShift linePhase
  rw [Real.exp_lt_exp, Real.log_exp]
  have : T / (1 / 2) = 2 * T := by ring
  rw [this]
  constructor
  · intro h
    have h' : (Real.arctan (T / β) + (k : ℝ) * Real.pi) / T - (Real.arctan (2 * T) + (k : ℝ) * Real.pi) / T <
        (Real.arctan (T₁ / (1 / 2)) + (k : ℝ) * Real.pi) / T₁ -
          (Real.arctan (2 * T) + (k : ℝ) * Real.pi) / T := by linarith
    rw [← sub_div] at h'
    convert h' using 1 <;> ring
  · intro h
    have h' : (Real.arctan (T / β) - Real.arctan (2 * T)) / T <
        (Real.arctan (T₁ / (1 / 2)) + (k : ℝ) * Real.pi) / T₁ -
          (Real.arctan (2 * T) + (k : ℝ) * Real.pi) / T := by linarith
    rw [sub_div] at h'
    have := add_lt_add_right h' ((Real.arctan (2 * T) + (k : ℝ) * Real.pi) / T)
    convert this using 1 <;> ring

/-- **La fenêtre seule entraîne l'ordre des contacts** à tout indice où `1/(2T)/T ≤ −lineHeightShift T₁ T k` : l'emboîtement
n'y ajoute aucune contrainte sur `λ`. -/
theorem contact_order_of_window {β T T₁ : ℝ} (hT : 0 < T) (hT₁ : 0 < T₁) (hβ : 0 < β) (hβ2 : β ≤ 1 / 2)
    (k : ℤ) (hk : 1 / (2 * T) / T ≤ -lineHeightShift T₁ T k) :
    windingContact β T k < lineContact T₁ k := by
  rw [param_grid_lt_line_iff hT hT₁]
  have hw := (parameter_grid_admissible hT hβ hβ2).2.1
  have hpos := (parameter_grid_admissible hT hβ hβ2).1
  have := (Real.log_lt_log_iff (lt_of_lt_of_le one_pos hpos) (Real.exp_pos _)).mpr hw
  rw [Real.log_exp] at this
  linarith

/-- **Grille strictement translatée emboîtée à partir d'un indice** : si l'écart de hauteur à l'indice `k₀` est strictement
positif, il existe `β ∈ ]0, 1/2[` (donc `λ(β,T) > 1`) dont tous les contacts d'indice `k ≥ k₀` sont en deçà des contacts de
ligne à la hauteur `T₁`. -/
theorem exists_shifted_grid_of_gap {T₁ T : ℝ} (hT₁ : 0 < T₁) (hT : T₁ < T) (k₀ : ℤ)
    (hgpos : 0 < -lineHeightShift T₁ T k₀) :
    ∃ β : ℝ, 0 < β ∧ β < 1 / 2 ∧ 1 < paramFactor β T ∧
      ∀ k : ℤ, k₀ ≤ k → windingContact β T k < lineContact T₁ k := by
  have hTpos : 0 < T := by linarith
  set g := -lineHeightShift T₁ T k₀ with hg
  have hgk : ∀ k : ℤ, k₀ ≤ k → g ≤ -lineHeightShift T₁ T k := by
    intro k hk
    rcases eq_or_lt_of_le hk with h | h
    · subst h; exact le_rfl
    · have := lineHeightShift_strictAnti_index hT₁ hT h; linarith
  -- angle `θ = arctan(2T) + η`, strictement entre `arctan(2T)` et `π/2`
  set a := Real.arctan (2 * T) with ha
  have ha_lt : a < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have ha_pos : 0 < a := Real.arctan_pos.mpr (by linarith)
  set η := min (T * g) (Real.pi / 2 - a) / 2 with hη
  have hηpos : 0 < η := by
    have : 0 < min (T * g) (Real.pi / 2 - a) := lt_min (mul_pos hTpos hgpos) (by linarith)
    positivity
  have hη1 : η < T * g := by
    have : 0 < T * g := mul_pos hTpos hgpos
    linarith [min_le_left (T * g) (Real.pi / 2 - a)]
  have hη2 : a + η < Real.pi / 2 := by
    have := min_le_right (T * g) (Real.pi / 2 - a)
    linarith
  set θ := a + η with hθ
  have hθpos : 0 < θ := by linarith
  have hθlt : θ < Real.pi / 2 := hη2
  have hθgt : -(Real.pi / 2) < θ := by linarith [Real.pi_pos]
  have htan_pos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθpos hθlt
  have htan_gt : 2 * T < Real.tan θ := by
    have h := Real.tan_lt_tan_of_lt_of_lt_pi_div_two (x := a) (y := θ)
      (by linarith [Real.pi_pos]) hθlt (by linarith)
    rwa [ha, Real.tan_arctan] at h
  refine ⟨T / Real.tan θ, div_pos hTpos htan_pos, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ htan_pos]; linarith
  · unfold paramFactor
    rw [Real.one_lt_exp_iff]
    have : T / (T / Real.tan θ) = Real.tan θ := by field_simp
    rw [this, Real.arctan_tan hθgt hθlt]
    exact div_pos (by linarith) hTpos
  · intro k hk
    rw [param_grid_lt_line_iff hTpos hT₁]
    unfold paramFactor
    rw [Real.log_exp]
    have : T / (T / Real.tan θ) = Real.tan θ := by field_simp
    rw [this, Real.arctan_tan hθgt hθlt]
    have hlog : (θ - Real.arctan (2 * T)) / T = η / T := by rw [hθ, ha]; ring
    rw [hlog]
    have h1 : η / T < g := by rw [div_lt_iff₀ hTpos]; linarith
    exact lt_of_lt_of_le h1 (hgk k hk)

/-- **Une grille strictement translatée est emboîtée dans la grille du premier zéro à TOUS les indices `k ≥ 0`** : pour
toute hauteur `T > T₁ ≥ 1/2`, il existe `β ∈ ]0, 1/2[` (donc `λ(β,T) > 1`) dont tous les contacts d'indice `k ≥ 0` sont en
deçà des contacts de ligne à la hauteur `T₁`. L'ordre des contacts par rapport au premier zéro ne fournit donc pas la
borne supérieure `λ ≤ 1`. -/
theorem exists_shifted_grid_nested_in_first {T₁ T : ℝ} (hT₁ : 1 / 2 ≤ T₁) (hT : T₁ < T) :
    ∃ β : ℝ, 0 < β ∧ β < 1 / 2 ∧ 1 < paramFactor β T ∧
      ∀ k : ℤ, 0 ≤ k → windingContact β T k < lineContact T₁ k :=
  exists_shifted_grid_of_gap (by linarith) hT 0
    (by have := lineHeightShift_neg_of_nonneg hT₁ hT (k := 0) le_rfl; linarith)

/-- Même énoncé aux indices `k ≥ 1` (convention de `WindingNested`), pour toute hauteur `0 < T₁ < T`. -/
theorem exists_shifted_grid_windingNested {T₁ T : ℝ} (hT₁ : 0 < T₁) (hT : T₁ < T) :
    ∃ β : ℝ, 0 < β ∧ β < 1 / 2 ∧ 1 < paramFactor β T ∧
      ∀ k : ℤ, 1 ≤ k → windingContact β T k < lineContact T₁ k :=
  exists_shifted_grid_of_gap hT₁ hT 1
    (by have := lineHeightShift_neg_of_one_le hT₁ hT (k := 1) le_rfl; linarith)

/-- **Forme sur les vrais zéros** : depuis tout membre en ligne `w` de hauteur strictement inférieure à `T`, l'emboîtement à
tout indice `k ≥ 1` (`WindingNested`) est réalisé par une grille de facteur `λ > 1` à la hauteur `T`. -/
theorem windingNested_realized_by_shifted_grid (w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2) {T : ℝ}
    (hT : rZeroHeight w.1 < T) :
    ∃ β : ℝ, 0 < β ∧ β < 1 / 2 ∧ 1 < paramFactor β T ∧
      ∀ k : ℤ, 1 ≤ k → windingContact β T k < contactMinusAt w k := by
  obtain ⟨β, h1, h2, h3, h4⟩ := exists_shifted_grid_windingNested w.2 hT
  refine ⟨β, h1, h2, h3, fun k hk => ?_⟩
  rw [contactMinusAt_eq_windingContact w, hw, windingContact_half]
  exact h4 k hk

/-- Aux indices `k ≥ 1`, forme sans borne sur `T_w` : tout indice où une comparaison de contacts forcerait `λ_z ≤ 1` est
`≤ 0`, et l'arrivée en ligne y viole la comparaison stricte. -/
theorem upper_bound_one_only_nonpos_index (z w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2)
    (hT : rZeroHeight w.1 < rZeroHeight z.1) :
    (∀ k : ℤ, 0 ≤ lineHeightShift (rZeroHeight w.1) (rZeroHeight z.1) k →
        k ≤ 0 ∧ (rZeroRadialPosition z.1 = 1 / 2 → ¬ contactMinusAt z k < contactMinusAt w k)) ∧
      ∀ k : ℤ, 1 ≤ k → 0 < -lineHeightShift (rZeroHeight w.1) (rZeroHeight z.1) k := by
  refine ⟨fun k hS => ⟨?_, fun hz => onLine_fails_strict_comparison z w hw hz k hS⟩, fun k hk => ?_⟩
  · by_contra hk
    exact absurd hS (not_le.mpr (lineHeightShift_neg_of_one_le (T₁ := rZeroHeight w.1) w.2 hT (not_le.mp hk)))
  · have := lineHeightShift_neg_of_one_le (T₁ := rZeroHeight w.1) w.2 hT hk
    linarith

/-- **Instanciation à un passage** : départ `e` en ligne, premier zéro `w` en ligne, arrivée `l` au plus en ligne. Les trois
termes de l'identité, le déplacement radial `≥ 0`, la lecture du signe à tout indice, et l'ordre acquis vers le premier zéro
à tout indice dès la fenêtre (sans emboîtement supposé), et l'emboîtement `k ≥ 1` dans `w` réalisé par une grille
translatée à la hauteur d'arrivée. -/
theorem passage_first_zero_comparison (l e w : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2)
    (hw : rZeroRadialPosition w.1 = 1 / 2) (hβ : rZeroRadialPosition l.1 ≤ 1 / 2)
    (hTw : rZeroHeight w.1 < rZeroHeight l.1) :
    (∀ k : ℤ, Real.log (contactMinusAt l k / contactMinusAt w k) =
        Real.log (radialFactor l) + lineHeightShift (rZeroHeight w.1) (rZeroHeight l.1) k) ∧
      (∀ k : ℤ, Real.log (contactMinusAt l k / contactMinusAt e k) =
        Real.log (radialFactor l) + lineHeightShift (rZeroHeight e.1) (rZeroHeight l.1) k) ∧
      0 ≤ Real.log (radialFactor l) ∧
      (∀ k : ℤ, contactMinusAt l k < contactMinusAt w k ↔
        Real.log (radialFactor l) < -lineHeightShift (rZeroHeight w.1) (rZeroHeight l.1) k) ∧
      (∀ k : ℤ, 1 ≤ k → lineHeightShift (rZeroHeight w.1) (rZeroHeight l.1) k < 0) ∧
      (∀ k : ℤ, 1 / (2 * rZeroHeight l.1) / rZeroHeight l.1 ≤
          -lineHeightShift (rZeroHeight w.1) (rZeroHeight l.1) k → contactMinusAt l k < contactMinusAt w k) ∧
      (∃ β : ℝ, 0 < β ∧ β < 1 / 2 ∧ 1 < paramFactor β (rZeroHeight l.1) ∧
        ∀ k : ℤ, 1 ≤ k → windingContact β (rZeroHeight l.1) k < contactMinusAt w k) := by
  refine ⟨fun k => ?_, fun k => ?_, log_radialFactor_nonneg l hβ, fun k => contact_lt_iff_factor l w hw k,
    fun k hk => lineHeightShift_neg_of_one_le w.2 hTw hk, fun k hk => ?_,
    windingNested_realized_by_shifted_grid w hw hTw⟩
  · rw [contact_log_ratio, (radialFactor_eq_one_iff w).mpr hw, Real.log_one, sub_zero]
  · rw [contact_log_ratio, (radialFactor_eq_one_iff e).mpr he, Real.log_one, sub_zero]
  · rw [contactMinusAt_eq_windingContact l, contactMinusAt_eq_windingContact w, hw, windingContact_half]
    exact contact_order_of_window l.2 w.2 (thm_zeroRadialPosition_positive l.1) hβ k hk

#print axioms contact_log_ratio_onLine
#print axioms upper_bound_one_only_below_one
#print axioms exists_shifted_grid_nested_in_first
#print axioms windingNested_realized_by_shifted_grid
#print axioms upper_bound_one_only_nonpos_index
#print axioms passage_first_zero_comparison

end RHV6Fresh
