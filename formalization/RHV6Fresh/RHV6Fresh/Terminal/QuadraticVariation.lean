/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PairInteraction

/-!
# RHV6Fresh — variation quadratique locale : paire séparée contre référence fusionnée (auteur, 2026-10-03)

Lemme demandé par l'auteur : comparer, dans une même fenêtre, l'énergie d'une configuration où une paire miroir est
séparée radialement à celle de sa référence fusionnée sur la ligne (le double en ligne de même hauteur), décomposer
la variation en excès propre de la paire et terme croisé avec le complément, puis établir si ce terme croisé
s'annule ou a un signe forcé. Calcul symbolique exact, sans borne ni horizon.

Fenêtre : un ensemble fini de réels `q > 0` muni de poids `μ ≥ 0`, énergie `Σ μ(q) ‖f(q)‖²`.

* **Décomposition** (§1) : variation = (énergie de la paire − énergie du double) + 2 × interaction de l'atome
  `paire − double` avec le complément (`windowVariation_split`).
* **Excès propre** (§2) : pointwise `‖paire‖² − ‖double‖² = q (4κ + κ²)`, `κ` = courbure radiale ; `≥ 0`, nul ⟺
  `κ = 0` (`pair_self_excess_eq`, `window_self_excess_nonneg`) : l'excès propre est strict et positif.
* **Le complément s'élimine exactement** (§3) : si le reste total `R` est fixé (côté arithmétique), le complément vaut
  `R − paire` et la variation s'écrit `2 × interaction(atome, R) − énergie(atome)` (`windowVariation_via_remainder`) :
  aucun terme du complément n'y figure ; le terme croisé devient la lecture du reste lui-même par l'atome
  (`complement_cross_eq_remainder_cross`), c'est-à-dire, à chaque `q`, la courbure × l'interaction du terme en ligne de
  hauteur `T` avec le reste (`remainder_cross_curvature`) : une lecture du reste à la fréquence `T`, pondérée par la
  courbure.
* **Ni le miroir ni la courbure ne fixent ce terme** (§4) : il est pair en la profondeur (canal symétrique, celui que
  porte le côté arithmétique de zêta) (`remainder_cross_even`) ; pour tout atome non nul, toute valeur réelle est
  atteinte par un complément (`cross_term_unconstrained`) : aucune identité algébrique ne l'annule ni ne le signe.

Borne : identités exactes. Le terme croisé ne s'annule pas et n'a pas de signe algébriquement forcé ; il est la
lecture du reste arithmétique exact, à la fréquence de la paire, pondérée par la courbure. Le déterminer, c'est savoir si
le reste contient la paire (lecture du pôle, déjà compilée) ; le borner uniformément sur toutes les hauteurs et toutes
les profondeurs est la croissance critique du reste. Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Real

/-! ## 1. Énergie de fenêtre et décomposition de la variation -/

/-- **Énergie de fenêtre** : `Σ_{q ∈ S} μ(q) ‖f(q)‖²`. -/
noncomputable def windowEnergy (S : Finset ℝ) (μ : ℝ → ℝ) (f : ℝ → ℂ) : ℝ :=
  ∑ q ∈ S, μ q * Complex.normSq (f q)

/-- **Interaction de fenêtre** : `Σ_{q ∈ S} μ(q) Re(f(q) · conj g(q))`. -/
noncomputable def windowCross (S : Finset ℝ) (μ : ℝ → ℝ) (f g : ℝ → ℂ) : ℝ :=
  ∑ q ∈ S, μ q * towerInteraction (f q) (g q)

theorem windowEnergy_add (S : Finset ℝ) (μ : ℝ → ℝ) (f g : ℝ → ℂ) :
    windowEnergy S μ (f + g) = windowEnergy S μ f + windowEnergy S μ g + 2 * windowCross S μ f g := by
  unfold windowEnergy windowCross towerInteraction
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.add_apply, Complex.normSq_add]
  ring

theorem windowCross_sub_left (S : Finset ℝ) (μ : ℝ → ℝ) (f f' g : ℝ → ℂ) :
    windowCross S μ (f - f') g = windowCross S μ f g - windowCross S μ f' g := by
  unfold windowCross towerInteraction
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.sub_apply, sub_mul, Complex.sub_re]
  ring

theorem windowCross_sub_right (S : Finset ℝ) (μ : ℝ → ℝ) (f g g' : ℝ → ℂ) :
    windowCross S μ f (g - g') = windowCross S μ f g - windowCross S μ f g' := by
  unfold windowCross towerInteraction
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.sub_apply, map_sub, mul_sub, Complex.sub_re]

/-- **Décomposition de la variation** : configuration séparée `P + C` contre référence fusionnée `P₀ + C`, même
complément `C` : excès propre + 2 × interaction de l'atome `P − P₀` avec le complément. -/
theorem windowVariation_split (S : Finset ℝ) (μ : ℝ → ℝ) (P P₀ C : ℝ → ℂ) :
    windowEnergy S μ (P + C) - windowEnergy S μ (P₀ + C) =
      (windowEnergy S μ P - windowEnergy S μ P₀) + 2 * windowCross S μ (P - P₀) C := by
  rw [windowEnergy_add, windowEnergy_add, windowCross_sub_left]
  ring

/-! ## 2. Excès propre de la paire contre le double : strict et positif -/

/-- La paire de profondeur `d` à hauteur `T`, lue en `q` (sans dénominateur). -/
noncomputable def pairTerm (T d : ℝ) (q : ℝ) : ℂ :=
  (q : ℂ) ^ mirrorPoint T d + (q : ℂ) ^ mirrorPoint T (-d)

/-- Le double en ligne de même hauteur, lu en `q`. -/
noncomputable def doubleTerm (T : ℝ) (q : ℝ) : ℂ := 2 * (q : ℂ) ^ mirrorPoint T 0

theorem pairTerm_sub_doubleTerm (T d q : ℝ) : pairTerm T d q - doubleTerm T q = pairOverDouble q T d := by
  unfold pairTerm doubleTerm pairOverDouble; ring

theorem normSq_lineTerm {q : ℝ} (hq : 0 < q) (T : ℝ) : Complex.normSq ((q : ℂ) ^ mirrorPoint T 0) = q := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_cpow_eq_rpow_re_of_pos hq]
  simp only [mirrorPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]; norm_num

/-- **Excès propre ponctuel** : `‖paire‖² − ‖double‖² = q (4κ + κ²)`. -/
theorem pair_self_excess_eq {q : ℝ} (hq : 0 < q) (T d : ℝ) :
    Complex.normSq (pairTerm T d q) - Complex.normSq (doubleTerm T q) =
      q * (4 * radialCurvature q d + radialCurvature q d ^ 2) := by
  have hp : pairTerm T d q = (q : ℂ) ^ mirrorPoint T 0 * ((2 + radialCurvature q d : ℝ) : ℂ) := by
    have h := pairTerm_sub_doubleTerm T d q
    rw [pairOverDouble_eq hq] at h
    rw [show pairTerm T d q = doubleTerm T q + (q : ℂ) ^ mirrorPoint T 0 * (radialCurvature q d : ℂ) by
      rw [← h]; ring]
    unfold doubleTerm; push_cast; ring
  have hd : doubleTerm T q = (q : ℂ) ^ mirrorPoint T 0 * ((2 : ℝ) : ℂ) := by
    unfold doubleTerm; push_cast; ring
  rw [hp, hd, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_ofReal,
    normSq_lineTerm hq]
  ring

theorem pair_self_excess_nonneg {q : ℝ} (hq : 0 < q) (T d : ℝ) :
    0 ≤ Complex.normSq (pairTerm T d q) - Complex.normSq (doubleTerm T q) := by
  rw [pair_self_excess_eq hq]
  have := radialCurvature_nonneg q d
  positivity

/-- Ponctuellement, l'excès propre est nul ⟺ la courbure est nulle (⟺ `d log q = 0`). -/
theorem pair_self_excess_eq_zero_iff {q : ℝ} (hq : 0 < q) (T d : ℝ) :
    Complex.normSq (pairTerm T d q) - Complex.normSq (doubleTerm T q) = 0 ↔ d * Real.log q = 0 := by
  rw [pair_self_excess_eq hq, ← radialCurvature_eq_zero_iff]
  have hk := radialCurvature_nonneg q d
  constructor
  · intro h
    have h' : radialCurvature q d * (4 + radialCurvature q d) = 0 := by
      have := mul_eq_zero.1 h
      rcases this with h0 | h0
      · exact absurd h0 hq.ne'
      · linarith [h0]
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact h0
    · linarith
  · intro h; rw [h]; ring

/-- **Excès propre de fenêtre** `≥ 0`, sur toute fenêtre de réels positifs à poids positifs. -/
theorem window_self_excess_nonneg (S : Finset ℝ) (μ : ℝ → ℝ) (hS : ∀ q ∈ S, 0 < q) (hμ : ∀ q ∈ S, 0 ≤ μ q)
    (T d : ℝ) : 0 ≤ windowEnergy S μ (pairTerm T d) - windowEnergy S μ (doubleTerm T) := by
  unfold windowEnergy
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun q hq => ?_
  rw [← mul_sub]
  exact mul_nonneg (hμ q hq) (pair_self_excess_nonneg (hS q hq) T d)

/-! ## 3. Le complément s'élimine exactement ; le terme croisé est une lecture du reste -/

/-- **Variation lue sur le reste** : si le reste total `R` est fixé et que la référence remplace la paire par le double
(atome `K = paire − double`), alors `E(R) − E(R − K) = 2 ⟨K, R⟩ − E(K)` : le complément n'apparaît plus. -/
theorem windowVariation_via_remainder (S : Finset ℝ) (μ : ℝ → ℝ) (R K : ℝ → ℂ) :
    windowEnergy S μ R - windowEnergy S μ (R - K) = 2 * windowCross S μ K R - windowEnergy S μ K := by
  have h := windowEnergy_add S μ (R - K) K
  rw [sub_add_cancel] at h
  have hc : windowCross S μ (R - K) K = windowCross S μ K R - windowEnergy S μ K := by
    rw [windowCross_sub_left]
    unfold windowCross windowEnergy towerInteraction
    congr 1
    · refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [Complex.mul_conj, Complex.ofReal_re]
  rw [h, hc]; ring

/-- **Terme croisé avec le complément = lecture du reste moins lecture de la paire** (`C = R − P`). -/
theorem complement_cross_eq_remainder_cross (S : Finset ℝ) (μ : ℝ → ℝ) (K R P : ℝ → ℂ) :
    windowCross S μ K (R - P) = windowCross S μ K R - windowCross S μ K P :=
  windowCross_sub_right S μ K R P

/-- **Le terme croisé décisif est une lecture du reste à la fréquence de la paire, pondérée par la courbure** :
`⟨paire − double, R⟩ = Σ μ(q) κ_q(d) Re(q^{1/2 + iT} · conj R(q))`. -/
theorem remainder_cross_curvature (S : Finset ℝ) (μ : ℝ → ℝ) (hS : ∀ q ∈ S, 0 < q) (T d : ℝ) (R : ℝ → ℂ) :
    windowCross S μ (fun q => pairOverDouble q T d) R =
      ∑ q ∈ S, μ q * (radialCurvature q d * towerInteraction ((q : ℂ) ^ mirrorPoint T 0) (R q)) := by
  unfold windowCross
  exact Finset.sum_congr rfl fun q hq => by rw [interaction_change_radial (hS q hq)]

/-! ## 4. Ni le miroir ni la courbure ne fixent le terme croisé -/

/-- **Canal symétrique** : le terme croisé est pair en la profondeur. -/
theorem remainder_cross_even (S : Finset ℝ) (μ : ℝ → ℝ) (T d : ℝ) (R : ℝ → ℂ) :
    windowCross S μ (fun q => pairOverDouble q T (-d)) R = windowCross S μ (fun q => pairOverDouble q T d) R := by
  unfold windowCross
  exact Finset.sum_congr rfl fun q _ => by simp only [pairOverDouble_even]

/-- **Aucune identité algébrique ne fixe le terme croisé** : pour tout atome non nul et toute valeur réelle `c`, un
complément réalise exactement `c`. Seule la donnée du reste lui-même le fixe. -/
theorem cross_term_unconstrained {K : ℂ} (hK : K ≠ 0) (c : ℝ) : ∃ w : ℂ, towerInteraction K w = c := by
  refine ⟨(c / Complex.normSq K : ℝ) * K, ?_⟩
  unfold towerInteraction
  have hn : Complex.normSq K ≠ 0 := (Complex.normSq_pos.2 hK).ne'
  rw [map_mul, Complex.conj_ofReal, mul_left_comm, Complex.mul_conj, ← Complex.ofReal_mul,
    Complex.ofReal_re, div_mul_cancel₀ _ hn]

end RHV6Fresh
