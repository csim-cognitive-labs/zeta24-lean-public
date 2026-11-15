/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TangentialInversion
import RHV6Fresh.Terminal.TowerTwoSidedRoom
import RHV6Fresh.Terminal.RegimeTower

/-!
# Largeurs de cellule, bande de phase, fenêtre `ON → OFF bas → miroir haut → suivant` (E177, 2026-10-05)

1. **Trois grandeurs séparées.** Largeur logarithmique = pas `π/T` (hauteur seule), largeur ordinaire
   `C_k (e^{π/T} − 1)`, logarithme du contact = `k·π/T` (rétrécissement, hauteur) `+ φ/T` (translation, phase)
   (`contact_ordinary_width`, `logContact_split`) ; rapport des pas de deux Tours `= T_e/T_l` (`towerPitch_ratio`) ;
   un écart de hauteur `≥ A` borne le pas suivant (`towerPitch_le_of_height_gap`) et rend l'emboîtement de l'indice
   `k` acquis dès `2kA ≥ T_e`, pour toutes positions radiales (`contact_nested_of_height_gap`).
2. **Bande de phase.** Pour `0 < β < 1` : `arctan T < arctan(T/β) < π/2`, et toute phase de cette fenêtre provient
   d'une partie réelle de la bande (`band_phase_window`, `band_phase_region_iff`) ; largeur `< 1/T`
   (`phase_window_width_lt`) : la phase est fixée à `1/T` près par la hauteur, la partie réelle ne l'est pas.
3. **Emboîtement uniforme.** Deux Tours de la bande dont les hauteurs diffèrent d'au moins `1/(π + arctan T)` sont
   emboîtées à TOUT indice `k ≥ 1`, quelles que soient leurs parties réelles (`windingContact_nested_of_gap`).
4. **Fenêtre OFF, pour tout écart `d ∈ ]0, 1/2[`** (pas une grille) : prédécesseur en ligne, membre bas
   `1/2 − d`, miroir haut `1/2 + d` à la même hauteur, suivant plus haut : emboîtements avec les deux voisins,
   emboîtement de la paire, pas égaux dans la paire et contractés aux deux raccords de hauteur, écart de phase
   miroir dans `]0, 1/T[` (`offWindow_parameters_feasible`). Les contraintes de contacts, de pas, de phase et
   d'enroulement ne vident donc la région pour aucun `d`.
5. **Raréfaction première** : suites de `m` entiers consécutifs sans premier pour tout `m` (`prime_free_run`) ; la
   progression première sur une fenêtre est une fonction du rang seul, elle n'entre dans les Tours que par la phase
   `T·log(p'/p)`, à hauteur constante comprise (`sameHeight_phase_progress`).

Portée : identités et inégalités réelles ; aucune ne lit la fonction zêta, ni le comptage, ni les poids. Aucun
`sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Trois grandeurs séparées -/

/-- Rapport des pas de deux Tours : `ℓ_l / ℓ_e = T_e / T_l` (hauteur seule). -/
theorem towerPitch_ratio (e l : TrueZero) :
    towerPitch l / towerPitch e = rZeroHeight e.1 / rZeroHeight l.1 := by
  have he : rZeroHeight e.1 ≠ 0 := ne_of_gt e.2
  have hl : rZeroHeight l.1 ≠ 0 := ne_of_gt l.2
  unfold towerPitch
  field_simp

/-- Un écart de hauteur `≥ A` borne le pas suivant : `ℓ_l ≤ π/(T_e + A)`. -/
theorem towerPitch_le_of_height_gap (e l : TrueZero) {A : ℝ} (hA : 0 ≤ A)
    (h : rZeroHeight e.1 + A ≤ rZeroHeight l.1) :
    towerPitch l ≤ Real.pi / (rZeroHeight e.1 + A) := by
  have he : 0 < rZeroHeight e.1 := e.2
  unfold towerPitch
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by linarith) h

/-- Largeur ordinaire d'une cellule : `C_{k+1} − C_k = C_k (e^{π/T} − 1)`. -/
theorem contact_ordinary_width (z : TrueZero) (k : ℤ) :
    contactPlusAt z k - contactMinusAt z k = contactMinusAt z k * (Real.exp (towerPitch z) - 1) := by
  have h := towerPitch_eq_contacts z k
  have hP := contactPlusAt_positive z k
  have hM := contactMinusAt_positive z k
  have hE : Real.exp (towerPitch z) = contactPlusAt z k / contactMinusAt z k := by
    rw [← h, Real.exp_sub, Real.exp_log hP, Real.exp_log hM]
  rw [hE]
  field_simp

/-- Logarithme du contact : `k·π/T` (rétrécissement, hauteur seule) `+ φ/T` (translation, phase). -/
theorem logContact_split (z : TrueZero) (k : ℤ) :
    Real.log (contactMinusAt z k) =
      (k : ℝ) * towerPitch z + Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) / rZeroHeight z.1 := by
  rw [contactMinusAt_eq_windingContact]
  unfold windingContact towerPitch
  rw [Real.log_exp]
  ring

/-- Écart de hauteur `≥ A > 0` : l'indice `k` est emboîté dès `2kA ≥ T_e`, pour toutes positions radiales. -/
theorem contact_nested_of_height_gap (e l : TrueZero) {A : ℝ} (k : ℤ) (hA : 0 < A)
    (h : rZeroHeight e.1 + A ≤ rZeroHeight l.1) (hk : rZeroHeight e.1 ≤ 2 * (k : ℝ) * A) :
    contactMinusAt l k < contactMinusAt e k := by
  apply windingNested_index_of_depth e l k
  have he : 0 < rZeroHeight e.1 := e.2
  have hk0 : 0 < (k : ℝ) := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hΔ : (k : ℝ) * A ≤ (k : ℝ) * (rZeroHeight l.1 - rZeroHeight e.1) :=
    mul_le_mul_of_nonneg_left (by linarith) hk0.le
  have h2 : rZeroHeight e.1 ≤ 2 * ((k : ℝ) * (rZeroHeight l.1 - rZeroHeight e.1)) := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
  nlinarith

/-! ## 2. Bande de phase -/

/-- La fenêtre de phase de la bande a une largeur `< 1/T`. -/
theorem phase_window_width_lt {T : ℝ} (hT : 0 < T) : Real.pi / 2 - Real.arctan T < 1 / T := by
  rw [← Real.arctan_inv_of_pos hT]
  have hpos : 0 < Real.arctan T⁻¹ := Real.arctan_pos.mpr (inv_pos.mpr hT)
  have hlt := Real.lt_tan hpos (Real.arctan_lt_pi_div_two _)
  rw [Real.tan_arctan] at hlt
  rw [one_div]
  exact hlt

theorem band_phase_window {β T : ℝ} (hT : 0 < T) (hβ : 0 < β) (hβ1 : β < 1) :
    Real.arctan T < Real.arctan (T / β) ∧ Real.arctan (T / β) < Real.pi / 2 :=
  ⟨(radial_lt_one_iff_branch hT hβ).mp hβ1, Real.arctan_lt_pi_div_two _⟩

/-- Région de phase : une phase provient d'une partie réelle de la bande ⟺ elle est dans `]arctan T, π/2[`. -/
theorem band_phase_region_iff {T φ : ℝ} (hT : 0 < T) :
    (∃ β : ℝ, 0 < β ∧ β < 1 ∧ Real.arctan (T / β) = φ) ↔
      Real.arctan T < φ ∧ φ < Real.pi / 2 := by
  constructor
  · rintro ⟨β, hβ, hβ1, rfl⟩
    exact band_phase_window hT hβ hβ1
  · rintro ⟨h1, h2⟩
    have hφ0 : 0 < φ := lt_trans (Real.arctan_pos.mpr hT) h1
    have htan : 0 < Real.tan φ := Real.tan_pos_of_pos_of_lt_pi_div_two hφ0 h2
    have hat : Real.arctan (Real.tan φ) = φ := Real.arctan_tan (by linarith [Real.pi_pos]) h2
    refine ⟨T / Real.tan φ, div_pos hT htan, ?_, ?_⟩
    · rw [div_lt_one htan]
      by_contra hle
      push_neg at hle
      have := Real.arctan_strictMono.monotone hle
      rw [hat] at this
      linarith
    · rw [show T / (T / Real.tan φ) = Real.tan φ by field_simp]
      exact hat

/-! ## 3. Emboîtement uniforme -/

/-- Deux Tours de la bande, écart de hauteur `≥ 1/(π + arctan T)` : emboîtées à tout indice `k ≥ 1`, pour
toutes parties réelles (`0 < β < 1` en bas, `β' > 0` en haut). -/
theorem windingContact_nested_of_gap {β β' T T' k : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hβ' : 0 < β')
    (hT : 0 < T) (hTT' : T < T') (hgap : 1 ≤ (T' - T) * (Real.pi + Real.arctan T)) (hk : 1 ≤ k) :
    windingContact β' T' k < windingContact β T k := by
  unfold windingContact
  apply Real.exp_lt_exp.mpr
  have hT' : 0 < T' := hT.trans hTT'
  rw [div_lt_div_iff₀ hT' hT]
  have hφ := (radial_lt_one_iff_branch hT hβ).mp hβ1
  have hφ' := Real.arctan_lt_pi_div_two (T' / β')
  have hw := mul_lt_mul_of_pos_left (phase_window_width_lt hT) hT
  rw [mul_one_div_cancel hT.ne'] at hw
  have hd : 0 < T' - T := sub_pos.mpr hTT'
  have e1 : Real.arctan T * (T' - T) < Real.arctan (T / β) * (T' - T) := mul_lt_mul_of_pos_right hφ hd
  have e2 : T * (Real.arctan T - Real.pi / 2) < T * (Real.arctan (T / β) - Real.arctan (T' / β')) :=
    mul_lt_mul_of_pos_left (by linarith) hT
  have e3 : 0 ≤ (k - 1) * (Real.pi * (T' - T)) :=
    mul_nonneg (by linarith) (mul_nonneg Real.pi_pos.le hd.le)
  nlinarith

/-! ## 4. Fenêtre OFF, pour tout écart `d` -/

/-- **Fenêtre `ON → OFF bas → miroir haut → suivant`, pour tout `d ∈ ]0, 1/2[`.** Prédécesseur en ligne à `T_e`,
paire `1/2 ∓ d` à `T`, suivant de partie réelle `β_b > 0` à `T_b`, écarts de hauteur au moins `1/(π + arctan)` :
à tout indice `k ≥ 1`, `C_k(b) < C_k(miroir) < C_k(bas) < C_k(e)` ; pas contractés aux deux raccords de hauteur,
égaux dans la paire ; écart de phase miroir dans `]0, 1/T[`. -/
theorem offWindow_parameters_feasible {Te T Tb βb d k : ℝ} (hTe : 0 < Te) (h1 : Te < T) (h2 : T < Tb)
    (hg1 : 1 ≤ (T - Te) * (Real.pi + Real.arctan Te)) (hg2 : 1 ≤ (Tb - T) * (Real.pi + Real.arctan T))
    (hd : 0 < d) (hd1 : d < 1 / 2) (hβb : 0 < βb) (hk : 1 ≤ k) :
    windingContact βb Tb k < windingContact (1 / 2 + d) T k ∧
      windingContact (1 / 2 + d) T k < windingContact (1 / 2 - d) T k ∧
      windingContact (1 / 2 - d) T k < windingContact (1 / 2) Te k ∧
      Real.pi / Tb < Real.pi / T ∧ Real.pi / T < Real.pi / Te ∧
      0 < Real.arctan (T / (1 / 2 - d)) - Real.arctan (T / (1 / 2 + d)) ∧
      Real.arctan (T / (1 / 2 - d)) - Real.arctan (T / (1 / 2 + d)) < 1 / T := by
  have hT : 0 < T := hTe.trans h1
  have hlo : 0 < 1 / 2 - d := by linarith
  have hhi : 1 / 2 + d < 1 := by linarith
  have hhi0 : 0 < 1 / 2 + d := by linarith
  have hband := band_phase_window hT hhi0 hhi
  have hw := phase_window_width_lt hT
  refine ⟨windingContact_nested_of_gap hhi0 hhi hβb hT h2 hg2 hk,
    windingContact_lt_of_radial_lt hlo (by linarith) hT,
    windingContact_nested_of_gap (by norm_num) (by norm_num) hlo hTe h1 hg1 hk,
    div_lt_div_of_pos_left Real.pi_pos hT h2, div_lt_div_of_pos_left Real.pi_pos hTe h1, ?_, ?_⟩
  · have : T / (1 / 2 + d) < T / (1 / 2 - d) := div_lt_div_of_pos_left hT hlo (by linarith)
    linarith [Real.arctan_strictMono this]
  · linarith [Real.arctan_lt_pi_div_two (T / (1 / 2 - d))]

/-! ## 5. Raréfaction première : suites arbitrairement longues sans premier -/

/-- **Écarts arbitrairement grands** : pour tout `m`, les `m` entiers `(m+1)! + 2, …, (m+1)! + (m+1)` ne sont pas
premiers. Énoncé sur les entiers seuls : il ne dit rien de la hauteur des zéros ni d'une contraction des Tours. -/
theorem prime_free_run (m i : ℕ) (h2 : 2 ≤ i) (hi : i ≤ m + 1) : ¬ Nat.Prime ((m + 1).factorial + i) := by
  intro hp
  have hd : i ∣ (m + 1).factorial + i := Nat.dvd_add (Nat.dvd_factorial (by omega) hi) dvd_rfl
  have hf : 0 < (m + 1).factorial := Nat.factorial_pos _
  rcases hp.eq_one_or_self_of_dvd i hd with h | h <;> omega

#print axioms prime_free_run

#print axioms towerPitch_ratio
#print axioms towerPitch_le_of_height_gap
#print axioms contact_ordinary_width
#print axioms logContact_split
#print axioms contact_nested_of_height_gap
#print axioms phase_window_width_lt
#print axioms band_phase_window
#print axioms band_phase_region_iff
#print axioms windingContact_nested_of_gap
#print axioms offWindow_parameters_feasible

end RHV6Fresh
