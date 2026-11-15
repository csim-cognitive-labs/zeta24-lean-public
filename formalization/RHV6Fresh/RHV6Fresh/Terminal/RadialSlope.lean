/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TowerWinding
import RHV6Fresh.Terminal.CanonicalTransition

/-!
# RHV6Fresh — hauteur → fréquence, position radiale → pente d'amplitude (E150, auteur, 2026-10-02)

Architecture de l'auteur : le fond Li donne l'échelle macroscopique, la hauteur `T` d'un membre donne la fréquence
(enroulement, résolution `π/T`, `Terminal/TowerWinding.lean`), la position radiale `β` donne la pente d'amplitude
du raffinement. Ce fichier écrit cette séparation exactement, pour chaque membre.

* **Deux coordonnées séparées** (§1) : entre deux points `x, y > 0`, la position de Tour avance de
  `T·log(y/x)/π` (la hauteur seule) et le logarithme de l'amplitude de `x^ρ/ρ` avance de `β·log(y/x)`
  (la position radiale seule) (`member_coordinates_separate`, `amplitude_ratio_eq_rpow`, `amplitude_log_eq`).
* **Pente 1/2** (§2) : l'amplitude ramenée à l'échelle `√x` vaut `x^{β − 1/2}/‖ρ‖`
  (`rescaled_amplitude_eq`) ; elle est constante en `x` ⟺ le membre est en ligne (`rescaled_amplitude_flat_iff`).
* **Même horloge, autre pente** (§3) : un membre déplacé de `d` (monde témoin `ζ(s−δ)ζ(s+δ)`) garde sa hauteur
  et multiplie son amplitude par exactement `x^d` (`shifted_member_same_height`, `shifted_member_amplitude`).
* **Horizon de lecture** (§4) : l'excès `x^{1/2+d}/T` dépasse `c·√x` ⟺ `x ≥ (c·T)^{1/d}`
  (`visibility_horizon`) : un membre de hauteur `T` et de décalage `d` n'émerge d'un reste de taille `c·√x`
  qu'au-delà de `(c·T)^{1/d}`.

Borne : la pente est lue sur le membre ; aucun énoncé ici ne la fixe. La lecture de la pente sur les premiers seuls
pour tout membre est la borne en `√x` du reste (`riemannHypothesis_iff_remainder_sqrt_growth`, caractérisation).
Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Real RHV3Lean

/-! ## 1. Deux coordonnées séparées -/


/-- **Pente d'amplitude** : le rapport des amplitudes en `y` et `x` est `(y/x)^β`, sans la hauteur. -/
theorem amplitude_ratio_eq_rpow (z : TrueZero) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ‖zeroTerm z y‖ / ‖zeroTerm z x‖ = (y / x) ^ rZeroRadialPosition z.1 := by
  rw [zeroTerm_norm hx, zeroTerm_norm hy, Real.div_rpow hy.le hx.le]
  have hn := (zeroPoint_norm_pos z).ne'
  have hxb : 0 < x ^ rZeroRadialPosition z.1 := Real.rpow_pos_of_pos hx _
  field_simp

/-- **Logarithme de l'amplitude** : `log‖x^ρ/ρ‖ = β·log x − log‖ρ‖`. -/
theorem amplitude_log_eq (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    Real.log ‖zeroTerm z x‖ = rZeroRadialPosition z.1 * Real.log x - Real.log ‖zeroPoint z‖ := by
  rw [zeroTerm_norm hx, Real.log_div (Real.rpow_pos_of_pos hx _).ne' (zeroPoint_norm_pos z).ne',
    Real.log_rpow hx]

/-- **Séparation** : la position de Tour avance par la hauteur seule, le logarithme de l'amplitude par la position
radiale seule. -/
theorem member_coordinates_separate (z : TrueZero) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    towerPosition z y - towerPosition z x = rZeroHeight z.1 * (Real.log y - Real.log x) / Real.pi ∧
      Real.log ‖zeroTerm z y‖ - Real.log ‖zeroTerm z x‖ =
        rZeroRadialPosition z.1 * (Real.log y - Real.log x) := by
  refine ⟨tower_relative_position z y x, ?_⟩
  rw [amplitude_log_eq z hx, amplitude_log_eq z hy]
  ring

/-! ## 2. Pente 1/2 -/

/-- **Amplitude ramenée à l'échelle `√x`** : `x^{−1/2}·‖x^ρ/ρ‖ = x^{β − 1/2}/‖ρ‖`. -/
theorem rescaled_amplitude_eq (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 / 2 : ℝ)) * ‖zeroTerm z x‖ = x ^ (rZeroRadialPosition z.1 - 1 / 2) / ‖zeroPoint z‖ := by
  rw [zeroTerm_norm hx, ← mul_div_assoc, ← Real.rpow_add hx]
  congr 2
  ring

/-- **Pente 1/2 ⟺ en ligne** : l'amplitude ramenée à `√x` est constante en `x` exactement pour un membre en ligne. -/
theorem rescaled_amplitude_flat_iff (z : TrueZero) :
    (∀ x : ℝ, 0 < x → x ^ (-(1 / 2 : ℝ)) * ‖zeroTerm z x‖ = 1 / ‖zeroPoint z‖) ↔
      rZeroRadialPosition z.1 = 1 / 2 := by
  have hn := (zeroPoint_norm_pos z).ne'
  constructor
  · intro h
    have he := h (Real.exp 1) (Real.exp_pos 1)
    rw [rescaled_amplitude_eq z (Real.exp_pos 1), Real.exp_one_rpow, div_left_inj' hn] at he
    have := Real.exp_eq_one_iff _ |>.mp he
    linarith
  · intro hβ x hx
    rw [rescaled_amplitude_eq z hx, hβ, sub_self, Real.rpow_zero]

/-! ## 3. Même horloge, autre pente -/

/-- Un membre déplacé de `d` réel garde sa hauteur. -/
theorem shifted_member_same_height (z : TrueZero) (d : ℝ) : (zeroPoint z + d).im = rZeroHeight z.1 := by
  simp [zeroPoint_im]

/-- **Amplitude du membre déplacé** : `‖x^{ρ+d}‖ = x^d·‖x^ρ‖`, le facteur exact du monde témoin. -/
theorem shifted_member_amplitude (z : TrueZero) (d : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (zeroPoint z + d)‖ = x ^ d * ‖(x : ℂ) ^ zeroPoint z‖ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re,
    Complex.ofReal_re, Real.rpow_add hx, mul_comm]

/-! ## 4. Horizon de lecture -/

/-- **Horizon** : l'amplitude `x^{1/2+d}/T` d'un membre décalé de `d` dépasse `c·√x` exactement au-delà de
`(c·T)^{1/d}`. -/
theorem visibility_horizon {d T c x : ℝ} (hd : 0 < d) (hT : 0 < T) (hc : 0 < c) (hx : 0 < x) :
    c * x ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 + d) / T ↔ (c * T) ^ (1 / d) ≤ x := by
  have hs : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  rw [Real.rpow_add hx, le_div_iff₀ hT, one_div d, Real.rpow_inv_le_iff_of_pos (by positivity) hx.le hd]
  constructor
  · intro h
    have : x ^ (1 / 2 : ℝ) * (c * T) ≤ x ^ (1 / 2 : ℝ) * x ^ d := by nlinarith
    exact le_of_mul_le_mul_left this hs
  · intro h
    nlinarith

#print axioms amplitude_ratio_eq_rpow
#print axioms amplitude_log_eq
#print axioms member_coordinates_separate
#print axioms rescaled_amplitude_eq
#print axioms rescaled_amplitude_flat_iff
#print axioms shifted_member_same_height
#print axioms shifted_member_amplitude
#print axioms visibility_horizon

end RHV6Fresh
