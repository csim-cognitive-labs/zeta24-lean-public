/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CountingFieldContacts

/-!
# Sensibilité des contacts du champ de comptage à la position radiale, identifiabilité, contre-modèle (E207, 2026-10-13)

Le décalage extremum–contact d'un zéro, `δ(β, T) = arctan(β/T)/T` (`extremum_contact_offset`), restitue `β`
(`radial_of_extremum_offset`) et lit le facteur radial `log λ = δ(1/2, T) − δ(β, T)` (`log_radialFactor_eq_offset`).
Ce module en donne la TAILLE (tout est DÉMONTRÉ, axiomes standard) :

* §1 encadrement de l'accroissement de `arctan` par les accroissements finis :
  `(b − a)/(1 + B²) ≤ arctan b − arctan a ≤ b − a` pour `0 ≤ a ≤ b ≤ B` ;
* §2 sensibilité du décalage : `(β' − β)/(T² + B²) ≤ δ(β') − δ(β) ≤ (β' − β)/T²` ; `δ` strictement croissant en `β`,
  donc `β` identifiable à `T` donné ;
* §3 taille du facteur radial d'un zéro : sous la ligne `(1/2 − β)/(T² + 1/4) ≤ log λ ≤ (1/2 − β)/T²`, au-dessus
  `(β − 1/2)/(T² + 1) ≤ −log λ ≤ (β − 1/2)/T²` ; `|log λ| ≤ |β − 1/2|/T²` : un déplacement radial `d` ne déplace
  tous les contacts que d'au plus `d/T²` en logarithme ;
* §4 identifiabilité à précision finie : une lecture du décalage à `ε` près sépare `β` de la ligne dès
  `2ε < (1/2 − β)/(T² + 1/4)` (condition suffisante) ; dès `(1/2 − β)/T² ≤ 2ε` une même lecture est compatible avec
  `β` et avec `1/2` (condition d'aveuglement) ;
* §5 contre-modèle du système réduit : fenêtre de phase, `λ ≥ 1` et `λ < e^{1/(2T²)}`, décalage au plus celui de la
  ligne, enveloppe au plus celle de la ligne sur `x ≥ 1` ; ce système est satisfait par TOUTE `β ∈ ]0, 1/2]`, il ne
  fixe donc pas `λ = 1` (`reducedContactSystem_not_identifying`).

Portée : énoncés sur les paramètres d'une Tour isolée ou d'un zéro donné ; aucun ne lit la somme de toutes les
contributions (aucune formule explicite du canal `J` dans le dépôt ; `Ei` absente de Mathlib ; les intersections `X_k`
avec l'axe `li` ne sont lues que numériquement, E204, E207). Aucun énoncé ne fixe la position radiale.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Accroissements de `arctan` -/

/-- **Encadrement de l'accroissement de `arctan`** : pour `0 ≤ a ≤ b ≤ B`,
`(b − a)/(1 + B²) ≤ arctan b − arctan a ≤ b − a`. -/
theorem arctan_sub_bounds {a b B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbB : b ≤ B) :
    (b - a) / (1 + B ^ 2) ≤ Real.arctan b - Real.arctan a ∧ Real.arctan b - Real.arctan a ≤ b - a := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.arctan (fun x => 1 / (1 + x ^ 2)) h
    Real.continuous_arctan.continuousOn (fun x _ => Real.hasDerivAt_arctan x)
  have hba : 0 < b - a := sub_pos.mpr h
  have heq : Real.arctan b - Real.arctan a = (b - a) * (1 / (1 + c ^ 2)) := by
    rw [hcd]; field_simp
  have hc0 : 0 < c := lt_of_le_of_lt ha hc.1
  have hcB : c ≤ B := (le_of_lt hc.2).trans hbB
  have hc2 : c ^ 2 ≤ B ^ 2 := by nlinarith
  have hpos : 0 < 1 + c ^ 2 := by positivity
  constructor
  · rw [heq, div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_left _ hba.le
    apply one_div_le_one_div_of_le hpos; linarith
  · rw [heq]
    have : 1 / (1 + c ^ 2) ≤ 1 := by rw [div_le_one hpos]; nlinarith
    nlinarith

/-- `arctan y ≤ y` pour `y ≥ 0`. -/
theorem arctan_le_self_of_nonneg {y : ℝ} (hy : 0 ≤ y) : Real.arctan y ≤ y := by
  have := (arctan_sub_bounds le_rfl hy le_rfl).2
  simpa using this

/-! ## 2. Sensibilité du décalage extremum–contact -/

/-- Décalage extremum–contact d'une Tour de paramètres `(β, T)` : `δ(β, T) = arctan(β/T)/T`. -/
noncomputable def contactOffset (β T : ℝ) : ℝ := Real.arctan (β / T) / T

/-- Le décalage d'un zéro est `δ(β, T)` à tout étage (`extremum_contact_offset`). -/
theorem contactOffset_eq_reading (z : TrueZero) (k : ℤ) :
    Real.log (modulationExtremum z k) - Real.log (contactMinusAt z k) =
      contactOffset (rZeroRadialPosition z.1) (rZeroHeight z.1) :=
  extremum_contact_offset z k

/-- Le décalage de la ligne est `δ(1/2, T)`. -/
theorem lineExtremumOffset_eq (T : ℝ) : lineExtremumOffset T = contactOffset (1 / 2) T := by
  unfold lineExtremumOffset contactOffset
  congr 2
  ring

/-- **Sensibilité du décalage** : pour `0 ≤ β ≤ β' ≤ B` et `T > 0`,
`(β' − β)/(T² + B²) ≤ δ(β') − δ(β) ≤ (β' − β)/T²`. -/
theorem contactOffset_sub_bounds {β β' B T : ℝ} (hT : 0 < T) (hβ : 0 ≤ β) (hββ' : β ≤ β') (hβ'B : β' ≤ B) :
    (β' - β) / (T ^ 2 + B ^ 2) ≤ contactOffset β' T - contactOffset β T ∧
      contactOffset β' T - contactOffset β T ≤ (β' - β) / T ^ 2 := by
  have h := arctan_sub_bounds (a := β / T) (b := β' / T) (B := B / T) (div_nonneg hβ hT.le)
    (div_le_div_of_nonneg_right hββ' hT.le) (div_le_div_of_nonneg_right hβ'B hT.le)
  have hsplit : contactOffset β' T - contactOffset β T = (Real.arctan (β' / T) - Real.arctan (β / T)) / T := by
    unfold contactOffset; ring
  rw [hsplit]
  constructor
  · have hl : (β' - β) / (T ^ 2 + B ^ 2) = ((β' / T - β / T) / (1 + (B / T) ^ 2)) / T := by
      field_simp
    rw [hl]
    exact div_le_div_of_nonneg_right h.1 hT.le
  · have hr : (β' - β) / T ^ 2 = (β' / T - β / T) / T := by field_simp
    rw [hr]
    exact div_le_div_of_nonneg_right h.2 hT.le

/-- `δ(·, T)` est strictement croissant sur `[0, ∞[`. -/
theorem contactOffset_strictMonoOn {T : ℝ} (hT : 0 < T) : StrictMonoOn (fun β => contactOffset β T) (Set.Ici 0) := by
  intro β hβ β' _ hlt
  have h := (contactOffset_sub_bounds (B := β') hT hβ hlt.le le_rfl).1
  have : 0 < (β' - β) / (T ^ 2 + β' ^ 2) := div_pos (sub_pos.mpr hlt) (by positivity)
  simp only
  linarith

/-- **Identifiabilité exacte à hauteur donnée** : deux positions radiales positives de même décalage sont égales. -/
theorem contactOffset_injOn {T : ℝ} (hT : 0 < T) {β β' : ℝ} (hβ : 0 ≤ β) (hβ' : 0 ≤ β')
    (h : contactOffset β T = contactOffset β' T) : β = β' :=
  (contactOffset_strictMonoOn hT).injOn hβ hβ' h

/-! ## 3. Taille du facteur radial d'un zéro -/

/-- `log λ = δ(1/2, T) − δ(β, T)` (`log_radialFactor_eq_offset`). -/
theorem log_radialFactor_eq_contactOffset (z : TrueZero) :
    Real.log (radialFactor z) =
      contactOffset (1 / 2) (rZeroHeight z.1) - contactOffset (rZeroRadialPosition z.1) (rZeroHeight z.1) := by
  rw [log_radialFactor_eq_offset z 0, contactOffset_eq_reading, lineExtremumOffset_eq]

/-- **Sous la ligne** : `(1/2 − β)/(T² + 1/4) ≤ log λ ≤ (1/2 − β)/T²`. -/
theorem log_radialFactor_bounds_of_low (z : TrueZero) (hlow : rZeroRadialPosition z.1 ≤ 1 / 2) :
    (1 / 2 - rZeroRadialPosition z.1) / (rZeroHeight z.1 ^ 2 + 1 / 4) ≤ Real.log (radialFactor z) ∧
      Real.log (radialFactor z) ≤ (1 / 2 - rZeroRadialPosition z.1) / rZeroHeight z.1 ^ 2 := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hβ : 0 ≤ rZeroRadialPosition z.1 := (thm_zeroRadialPosition_positive z.1).le
  have h := contactOffset_sub_bounds (B := 1 / 2) hT hβ hlow le_rfl
  rw [log_radialFactor_eq_contactOffset]
  have hq : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
  rw [hq] at h
  exact h

/-- **Au-dessus de la ligne** : `(β − 1/2)/(T² + 1) ≤ −log λ ≤ (β − 1/2)/T²`. -/
theorem log_radialFactor_bounds_of_high (z : TrueZero) (hhigh : 1 / 2 ≤ rZeroRadialPosition z.1) :
    (rZeroRadialPosition z.1 - 1 / 2) / (rZeroHeight z.1 ^ 2 + 1) ≤ -Real.log (radialFactor z) ∧
      -Real.log (radialFactor z) ≤ (rZeroRadialPosition z.1 - 1 / 2) / rZeroHeight z.1 ^ 2 := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hlt1 : rZeroRadialPosition z.1 ≤ 1 := (thm_zeroRadialPosition_lt_one z.1).le
  have h := contactOffset_sub_bounds (B := 1) hT (by norm_num) hhigh hlt1
  rw [log_radialFactor_eq_contactOffset, neg_sub]
  have hq : (1 : ℝ) ^ 2 = 1 := by norm_num
  rw [hq] at h
  exact h

/-- **Un déplacement radial `d` déplace les contacts d'au plus `d/T²`** : `|log λ| ≤ |β − 1/2|/T²`. -/
theorem abs_log_radialFactor_le (z : TrueZero) :
    |Real.log (radialFactor z)| ≤ |rZeroRadialPosition z.1 - 1 / 2| / rZeroHeight z.1 ^ 2 := by
  rcases le_total (rZeroRadialPosition z.1) (1 / 2) with h | h
  · have hb := log_radialFactor_bounds_of_low z h
    have hT2 : 0 < rZeroHeight z.1 ^ 2 + 1 / 4 := by positivity
    have h0 : 0 ≤ Real.log (radialFactor z) := le_trans (div_nonneg (by linarith) hT2.le) hb.1
    rw [abs_of_nonneg h0, abs_of_nonpos (by linarith), neg_sub]
    exact hb.2
  · have hb := log_radialFactor_bounds_of_high z h
    have hT2 : 0 < rZeroHeight z.1 ^ 2 + 1 := by positivity
    have h0 : 0 ≤ -Real.log (radialFactor z) := le_trans (div_nonneg (by linarith) hT2.le) hb.1
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    exact hb.2

/-! ## 4. Identifiabilité à précision finie -/

/-- **Condition suffisante de séparation** : une lecture `δ̂` du décalage d'un zéro bas à `ε` près, avec
`2ε < (1/2 − β)/(T² + 1/4)`, est à plus de `ε` du décalage de la ligne. -/
theorem offset_reading_separates (z : TrueZero) (hlow : rZeroRadialPosition z.1 < 1 / 2) {δ ε : ℝ}
    (hread : |δ - contactOffset (rZeroRadialPosition z.1) (rZeroHeight z.1)| ≤ ε)
    (hprec : 2 * ε < (1 / 2 - rZeroRadialPosition z.1) / (rZeroHeight z.1 ^ 2 + 1 / 4)) :
    ε < |δ - lineExtremumOffset (rZeroHeight z.1)| := by
  have hb := (log_radialFactor_bounds_of_low z hlow.le).1
  rw [log_radialFactor_eq_contactOffset] at hb
  rw [lineExtremumOffset_eq]
  have h1 := (abs_le.mp hread)
  rw [lt_abs]
  right
  linarith [h1.1, h1.2]

/-- **Condition d'aveuglement** : si `(1/2 − β)/T² ≤ 2ε`, une même lecture (le milieu) est à `ε` près du décalage
de `β` ET de celui de la ligne. -/
theorem offset_reading_blind {β T ε : ℝ} (hT : 0 < T) (hβ : 0 ≤ β) (hle : β ≤ 1 / 2)
    (hprec : (1 / 2 - β) / T ^ 2 ≤ 2 * ε) :
    ∃ δ, |δ - contactOffset β T| ≤ ε ∧ |δ - contactOffset (1 / 2) T| ≤ ε := by
  have h := contactOffset_sub_bounds (B := 1 / 2) hT hβ hle le_rfl
  have h0 : 0 ≤ (1 / 2 - β) / (T ^ 2 + (1 / 2) ^ 2) := div_nonneg (by linarith) (by positivity)
  refine ⟨(contactOffset β T + contactOffset (1 / 2) T) / 2, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith [h.1, h.2]
  · rw [abs_le]; constructor <;> linarith [h.1, h.2]

/-! ## 5. Contre-modèle du système réduit -/

/-- Système réduit des obligations de contact acquises à l'arrivée, écrit sur les paramètres `(β, T)` :
position positive au plus `1/2`, fenêtre de phase `arctan 2T ≤ φ < arctan 2T + 1/(2T)`, facteur `1 ≤ λ < e^{1/(2T²)}`
(`log λ = δ(1/2) − δ(β)`), décalage au plus celui de la ligne, enveloppe au plus celle de la ligne sur `x ≥ 1`. -/
def ReducedContactSystem (β T : ℝ) : Prop :=
  0 < β ∧ β ≤ 1 / 2 ∧
    Real.arctan (T / (1 / 2)) ≤ Real.arctan (T / β) ∧
    Real.arctan (T / β) < Real.arctan (T / (1 / 2)) + 1 / (2 * T) ∧
    0 ≤ contactOffset (1 / 2) T - contactOffset β T ∧
    contactOffset (1 / 2) T - contactOffset β T < 1 / (2 * T ^ 2) ∧
    contactOffset β T ≤ contactOffset (1 / 2) T ∧
    ∀ x : ℝ, 1 ≤ x → x ^ (β - 1 / 2) ≤ 1

/-- **Toute position radiale `β ∈ ]0, 1/2]` satisfait le système réduit.** -/
theorem reducedContactSystem_of_low {β T : ℝ} (hT : 0 < T) (hβ : 0 < β) (hle : β ≤ 1 / 2) :
    ReducedContactSystem β T := by
  have hoff := contactOffset_sub_bounds (B := 1 / 2) hT hβ.le hle le_rfl
  have hden : 0 < (1 / 2 : ℝ) := by norm_num
  have hphase : Real.arctan (T / (1 / 2)) ≤ Real.arctan (T / β) :=
    Real.arctan_le_arctan_iff.mpr (div_le_div_of_nonneg_left hT.le hβ hle)
  have h2T : 0 < 2 * T := by positivity
  have hinv : Real.arctan (T / (1 / 2)) = Real.pi / 2 - Real.arctan (1 / (2 * T)) := by
    have := Real.arctan_inv_of_pos h2T
    rw [show (2 * T)⁻¹ = 1 / (2 * T) by ring] at this
    rw [show T / (1 / 2) = 2 * T by ring]
    linarith
  have hsmall : Real.arctan (1 / (2 * T)) ≤ 1 / (2 * T) := arctan_le_self_of_nonneg (by positivity)
  have hlt : Real.arctan (T / β) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hstrict : (1 / 2 - β) / T ^ 2 < 1 / (2 * T ^ 2) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg T, pow_pos hT 2]
  have h0 : 0 ≤ (1 / 2 - β) / (T ^ 2 + (1 / 2) ^ 2) := div_nonneg (by linarith) (by positivity)
  refine ⟨hβ, hle, hphase, by linarith, by linarith [hoff.1], lt_of_le_of_lt hoff.2 hstrict,
    by linarith [hoff.1], ?_⟩
  intro x hx
  exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)

/-- **Contre-modèle** : le système réduit ne fixe pas la position radiale ; il est satisfait par `β = 1/4 ≠ 1/2`. -/
theorem reducedContactSystem_not_identifying {T : ℝ} (hT : 0 < T) :
    ∃ β, β ≠ 1 / 2 ∧ ReducedContactSystem β T :=
  ⟨1 / 4, by norm_num, reducedContactSystem_of_low hT (by norm_num) (by norm_num)⟩

/-- La ligne satisfait aussi le système réduit, avec `log λ = 0`. -/
theorem reducedContactSystem_onLine {T : ℝ} (hT : 0 < T) : ReducedContactSystem (1 / 2) T :=
  reducedContactSystem_of_low hT (by norm_num) le_rfl

/-- **Lecture de l'arrivée d'un passage** : un zéro de position radiale au plus `1/2` satisfait le système réduit, et
son facteur radial est encadré par `(1/2 − β)/(T² + 1/4) ≤ log λ ≤ (1/2 − β)/T²`. Toute position radiale `≤ 1/2`. -/
theorem arrival_contact_geometry (z : TrueZero) (hle : rZeroRadialPosition z.1 ≤ 1 / 2) :
    ReducedContactSystem (rZeroRadialPosition z.1) (rZeroHeight z.1) ∧
      (1 / 2 - rZeroRadialPosition z.1) / (rZeroHeight z.1 ^ 2 + 1 / 4) ≤ Real.log (radialFactor z) ∧
      Real.log (radialFactor z) ≤ (1 / 2 - rZeroRadialPosition z.1) / rZeroHeight z.1 ^ 2 :=
  ⟨reducedContactSystem_of_low z.2 (thm_zeroRadialPosition_positive z.1) hle,
    log_radialFactor_bounds_of_low z hle⟩

#print axioms arctan_sub_bounds
#print axioms contactOffset_sub_bounds
#print axioms abs_log_radialFactor_le
#print axioms offset_reading_separates
#print axioms offset_reading_blind
#print axioms reducedContactSystem_not_identifying
#print axioms arrival_contact_geometry

end RHV6Fresh
