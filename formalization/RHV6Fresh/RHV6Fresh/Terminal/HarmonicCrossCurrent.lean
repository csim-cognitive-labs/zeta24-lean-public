/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.HarmonicCurrentTransport
import RHV6Fresh.Terminal.LocalRaccordCaptivity
import RHV6Fresh.Terminal.RegimeTransportAudit

/-!
# RHV6Fresh — courant croisé, battements et courant collectif (mission E239–E241, parties C et D, 2026-10-13)

Courant croisé `W₁₂ = Im(ū₁ u₂')` (`crossCurrent`, `crossCurrent_eq` dans `HarmonicCurrentTransport`) :
`W₁₂ = e^{(d₁ + d₂)t}[T₂ cos((T₂ − T₁)t) + d₂ sin((T₂ − T₁)t)]`. Résultats (axiomes standard) :

1. **Partie symétrique** `W₁₂ + W₂₁ = e^{(d₁ + d₂)t}[(T₁ + T₂) cos((T₂ − T₁)t) + (d₂ − d₁) sin((T₂ − T₁)t)]`
   (`crossCurrent_symm_eq`) : elle lit la SOMME `d₁ + d₂` dans l'enveloppe et la DIFFÉRENCE `d₂ − d₁` seulement à travers le
   battement de différence `sin((T₂ − T₁)t)`.
2. **Courant collectif** d'une famille finie : `Im(conj(Σu) (Σu)') = Σ_n Σ_m W_{nm}` (`collectiveCurrent_eq_sum`), diagonale =
   courants individuels.
3. **Configurations** : deux Tours ON, battement pur d'enveloppe `1` (`crossCurrent_symm_onLine`) ; ON suivie d'OFF, enveloppe
   `e^{dt}` (`crossCurrent_symm_on_off`) ; paire miroir de même hauteur : partie croisée `2T` POUR TOUTE `d`
   (`mirror_cross_current_blind`), courant total `4T cosh²(dt)` (`mirror_pair_current_eq`), égal au courant d'un double ON
   `4T` en un `t ≠ 0` ⟺ `d = 0` (`mirror_pair_current_eq_double_iff`). Portée (audit radial, 2026-10-13) : ces énoncés
   portent sur les modes UNITAIRES `e^{(d+iT)t}` ; pour le signal exact `x^ρ/ρ` la partie croisée miroir vaut
   `T e^{t}(1/‖ρ₊‖² + 1/‖ρ₋‖²)` et lit `d` à l'ordre `d²` (`exact_mirror_cross_lt_double`, `Terminal/ExactSignalArchitecture.lean`).
4. **Verrou de phase du courant croisé** : à même hauteur, `W₁₂ + W₂₁ = (T₁ + T₂)·e^{(d₁ + d₂)t}` ; la paire miroir
   `(d, −d)` et le double ON `(0, 0)` ont la même partie croisée (`cross_current_same_height_reads_sum`) : contre-modèle, la
   partie croisée est la réécriture du battement miroir d'exposant `1` (`mirror_beat_modulus`), elle ne sépare pas.

5. **Le rapport des courants EST le carré du rapport des normes de Tours** : `Q(log x) = (‖Z_l(x)‖/‖Z_e(x)‖ · ‖ρ_l‖/‖ρ_e‖)²`
   (`currentRatio_eq_tower_ratio_sq`, par `successive_tower_ratio`) ; le transport du courant à deux abscisses ⟺ l'égalité des
   rapports de normes en deux points d'E216 (`two_point_current_iff_norm_ratio`, par `transport_ratio_eq_at_two_points_iff`) :
   le test C d'E240 est la réécriture d'une égalité déjà classée (caractérisation, même `β`).

Aucune identité de ce module n'impose `d = 0` : ce sont des identités vraies pour tout `(d, T)` ou des caractérisations.
Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Partie symétrique -/

theorem crossCurrent_symm_eq (d₁ T₁ d₂ T₂ t : ℝ) :
    crossCurrent d₁ T₁ d₂ T₂ t + crossCurrent d₂ T₂ d₁ T₁ t =
      Real.exp ((d₁ + d₂) * t) *
        ((T₁ + T₂) * Real.cos ((T₂ - T₁) * t) + (d₂ - d₁) * Real.sin ((T₂ - T₁) * t)) := by
  rw [crossCurrent_eq, crossCurrent_eq, add_comm d₂ d₁]
  have h1 : (T₁ - T₂) * t = -((T₂ - T₁) * t) := by ring
  rw [h1, Real.cos_neg, Real.sin_neg]; ring

/-! ## 2. Courant collectif d'une famille finie -/

/-- Courant du signal collectif `Σ u_n` : `Im(conj(Σu)·Σ(d_n + iT_n)u_n)`. -/
noncomputable def collectiveCurrent {ι : Type*} (s : Finset ι) (d T : ι → ℝ) (t : ℝ) : ℝ :=
  (starRingEnd ℂ (∑ n ∈ s, complexMode (d n) (T n) t) *
    ∑ m ∈ s, (((d m : ℂ) + (T m : ℂ) * Complex.I) * complexMode (d m) (T m) t)).im

/-- **Développement complet** : le courant collectif est la somme de tous les courants croisés, diagonale comprise. -/
theorem collectiveCurrent_eq_sum {ι : Type*} (s : Finset ι) (d T : ι → ℝ) (t : ℝ) :
    collectiveCurrent s d T t = ∑ n ∈ s, ∑ m ∈ s, crossCurrent (d n) (T n) (d m) (T m) t := by
  unfold collectiveCurrent crossCurrent
  rw [map_sum, Finset.sum_mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.im_sum]

/-- La diagonale est faite des courants individuels `T_n e^{2d_n t}`. -/
theorem collectiveCurrent_diag {ι : Type*} (n : ι) (d T : ι → ℝ) (t : ℝ) :
    crossCurrent (d n) (T n) (d n) (T n) t = T n * Real.exp (2 * d n * t) :=
  harmonicCurrent_eq (d n) (T n) t

/-- Le courant collectif d'une seule Tour est son courant individuel. -/
theorem collectiveCurrent_singleton {ι : Type*} (n : ι) (d T : ι → ℝ) (t : ℝ) :
    collectiveCurrent {n} d T t = T n * Real.exp (2 * d n * t) := by
  rw [collectiveCurrent_eq_sum]; simp only [Finset.sum_singleton]; exact collectiveCurrent_diag n d T t

/-- Deux Tours : `J₁ + J₂ + (W₁₂ + W₂₁)`. -/
theorem collectiveCurrent_pair (d₁ T₁ d₂ T₂ t : ℝ) :
    collectiveCurrent (Finset.univ : Finset (Fin 2)) ![d₁, d₂] ![T₁, T₂] t =
      T₁ * Real.exp (2 * d₁ * t) + T₂ * Real.exp (2 * d₂ * t) +
        Real.exp ((d₁ + d₂) * t) *
          ((T₁ + T₂) * Real.cos ((T₂ - T₁) * t) + (d₂ - d₁) * Real.sin ((T₂ - T₁) * t)) := by
  rw [collectiveCurrent_eq_sum, ← crossCurrent_symm_eq]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← harmonicCurrent_eq_cross, ← harmonicCurrent_eq_cross, harmonicCurrent_eq, harmonicCurrent_eq]; ring

/-! ## 3. Configurations -/

/-- Deux Tours ON : battement pur, enveloppe `1`. -/
theorem crossCurrent_symm_onLine (T₁ T₂ t : ℝ) :
    crossCurrent 0 T₁ 0 T₂ t + crossCurrent 0 T₂ 0 T₁ t = (T₁ + T₂) * Real.cos ((T₂ - T₁) * t) := by
  rw [crossCurrent_symm_eq]; simp

/-- ON suivie d'une Tour de profondeur `d` : enveloppe `e^{dt}`, battement de différence pondéré par `d`. -/
theorem crossCurrent_symm_on_off (T₁ d T₂ t : ℝ) :
    crossCurrent 0 T₁ d T₂ t + crossCurrent d T₂ 0 T₁ t =
      Real.exp (d * t) * ((T₁ + T₂) * Real.cos ((T₂ - T₁) * t) + d * Real.sin ((T₂ - T₁) * t)) := by
  rw [crossCurrent_symm_eq, zero_add, sub_zero]

/-- **Paire miroir de même hauteur** : la partie croisée vaut `2T` pour TOUTE profondeur `d`. -/
theorem mirror_cross_current_blind (d T t : ℝ) :
    crossCurrent d T (-d) T t + crossCurrent (-d) T d T t = 2 * T := by
  rw [crossCurrent_symm_eq]; simp; ring

/-- À même hauteur, la partie croisée ne lit que la somme `d₁ + d₂`. -/
theorem cross_current_same_height_reads_sum (d₁ d₂ T t : ℝ) :
    crossCurrent d₁ T d₂ T t + crossCurrent d₂ T d₁ T t = 2 * T * Real.exp ((d₁ + d₂) * t) := by
  rw [crossCurrent_symm_eq]; simp; ring

/-- **Courant total d'une paire miroir** : `J(d) + J(−d) + W + W' = 4T cosh²(dt)`. -/
theorem mirror_pair_current_eq (d T t : ℝ) :
    harmonicCurrent d T t + harmonicCurrent (-d) T t + (crossCurrent d T (-d) T t + crossCurrent (-d) T d T t) =
      4 * T * Real.cosh (d * t) ^ 2 := by
  rw [mirror_cross_current_blind, harmonicCurrent_eq, harmonicCurrent_eq, Real.cosh_eq]
  have h1 : Real.exp (2 * d * t) = Real.exp (d * t) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : Real.exp (2 * -d * t) = Real.exp (-(d * t)) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Real.exp (d * t) * Real.exp (-(d * t)) = 1 := by rw [← Real.exp_add]; simp
  rw [h1, h2]; linear_combination (-2 * T) * h3

/-- Le courant de la paire égale celui d'un double ON (`4T`) en un `t ≠ 0` ⟺ `d = 0` (`T ≠ 0`). Caractérisation. -/
theorem mirror_pair_current_eq_double_iff {d T t : ℝ} (hT : T ≠ 0) (ht : t ≠ 0) :
    4 * T * Real.cosh (d * t) ^ 2 = 4 * T ↔ d = 0 := by
  constructor
  · intro h
    have hc : Real.cosh (d * t) ^ 2 = 1 := by
      have h4 : (4 * T) * (Real.cosh (d * t) ^ 2 - 1) = 0 := by linarith
      rcases mul_eq_zero.mp h4 with h' | h'
      · exact absurd (by linarith : T = 0) hT
      · linarith
    have hc1 : Real.cosh (d * t) = 1 := by
      have := Real.cosh_pos (d * t); nlinarith
    by_contra hd
    have := Real.one_lt_cosh.mpr (mul_ne_zero hd ht); linarith
  · intro h; simp [h]

/-- **Contre-modèle du verrou croisé** : la paire miroir `(d, −d)` et le double ON `(0, 0)` ont, à même hauteur, la même
partie croisée en tout point. -/
theorem cross_current_mirror_eq_double (d T t : ℝ) :
    crossCurrent d T (-d) T t + crossCurrent (-d) T d T t = crossCurrent 0 T 0 T t + crossCurrent 0 T 0 T t := by
  rw [cross_current_same_height_reads_sum, cross_current_same_height_reads_sum]; simp

/-- Zéros du courant croisé : `W₁₂ = 0 ⟺ T₂ cos((T₂ − T₁)t) + d₂ sin((T₂ − T₁)t) = 0`. La condition lit `d₂` par la même phase
`arctan(T₂/d₂)` que les contacts : aucune lecture nouvelle. -/
theorem crossCurrent_eq_zero_iff (d₁ T₁ d₂ T₂ t : ℝ) :
    crossCurrent d₁ T₁ d₂ T₂ t = 0 ↔ T₂ * Real.cos ((T₂ - T₁) * t) + d₂ * Real.sin ((T₂ - T₁) * t) = 0 := by
  rw [crossCurrent_eq, mul_eq_zero]; simp [(Real.exp_pos _).ne']

/-! ## 4. Le courant est une réécriture des rapports de normes -/

theorem currentRatio_eq_tower_ratio_sq (e l : TrueZero) {x : ℝ} (hx : 0 < x) :
    currentRatio (zeroDepth e) (zeroDepth l) (Real.log x) =
      ((‖zeroTerm l x‖ / ‖zeroTerm e x‖) * (‖zeroPoint l‖ / ‖zeroPoint e‖)) ^ 2 := by
  have hA := norm_zeroPoint_pos l
  have hB := norm_zeroPoint_pos e
  rw [successive_tower_ratio e l hx, currentRatio_eq]
  have h1 : x ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * (‖zeroPoint e‖ / ‖zeroPoint l‖) *
      (‖zeroPoint l‖ / ‖zeroPoint e‖) = x ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) := by
    field_simp
  rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hx.le, Real.rpow_def_of_pos hx, zeroDepth, zeroDepth]
  congr 1; push_cast; ring

/-- Le transport du courant réduit entre deux abscisses `0 < M₁ < M₂` équivaut à l'égalité des rapports de normes de Tours en
ces deux abscisses (E216), elle-même équivalente à « même partie réelle ». -/
theorem two_point_current_iff_norm_ratio (e l : TrueZero) {M₁ M₂ : ℝ} (h₁ : 0 < M₁) (h₁₂ : M₁ < M₂) :
    currentRatio (zeroDepth e) (zeroDepth l) (Real.log M₁) = currentRatio (zeroDepth e) (zeroDepth l) (Real.log M₂) ↔
      ‖zeroTerm l M₁‖ / ‖zeroTerm e M₁‖ = ‖zeroTerm l M₂‖ / ‖zeroTerm e M₂‖ := by
  have hlog : Real.log M₁ ≠ Real.log M₂ :=
    (Real.log_lt_log h₁ h₁₂).ne
  rw [currentRatio_two_points_iff hlog, transport_ratio_eq_at_two_points_iff e l h₁ h₁₂, zeroDepth, zeroDepth]
  constructor
  · intro h; linarith
  · intro h; linarith

end RHV6Fresh
