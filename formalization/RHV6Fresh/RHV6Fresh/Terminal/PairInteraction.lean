/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PairCurvature

/-!
# RHV6Fresh — les deux continuations de la configuration dégénérée et leur interaction avec les Tours engagées (E160, auteur, 2026-10-03)

Suite de E159. La configuration dégénérée de référence (le double en ligne de hauteur `T`) n'est pas un événement de
l'histoire des zéros : c'est un point de comparaison. Ses deux continuations, radiale (paire `1/2 ± d + iT`) et verticale
(paire `1/2 + i(T ± h)`), portent des courbures de signes opposés (E159). Question de l'auteur : le changement
d'**interaction** de la continuation avec les Tours déjà engagées, de hauteurs différentes, porte-t-il une orientation que
la contribution propre de la paire perd ?

* **Interaction** (§1) : terme croisé `Re(u · v̄)` de l'énergie `‖u + v‖²` (`towerInteraction`). Le changement
  d'interaction d'une continuation avec **toute** Tour `w` vaut la courbure réelle de la continuation multipliée par
  l'interaction du double avec `w` (`interaction_change_radial`, `interaction_change_vertical`) ; pour une famille finie
  quelconque de Tours, même facteur (`interaction_change_family`). La continuation radiale est une paire d'ensemble
  symétrique : toute lecture, propre ou croisée, est paire en la profondeur (`pairOverDouble_even`,
  `interaction_change_even`) ; aucune orientation `d ↦ −d` n'existe à lire.
* **Signes** (§2) : les deux changements d'interaction avec une même Tour sont de signes opposés ou nuls
  (`interaction_changes_opposite`) ; le facteur commun est l'interaction du double avec la Tour, indépendante de la
  continuation. Avec une Tour engagée de hauteur `T' ≠ T`, ce facteur vaut `q^{1+d'}·cos((T − T') log q)`
  (`referenceCross_eq`) et change de signe arbitrairement loin (`referenceCross_sign_changes`) : le signe de
  l'interaction est fixé par une phase relative, pas par la continuation.
* **Seul terme de signe fixe : le terme propre** (§3) : `‖continuation radiale‖ = √q·(2 + κ) ≥ 2√q = ‖double‖ ≥
  ‖continuation verticale‖ = √q·|2 + c|` (`self_energy_order`) — c'est le paquet de hauteur déjà compilé.
* **Raffinement** (§4) : la courbure verticale reste dans `[−4, 0]` à tout horizon (`lineSplitCurvature_ge_neg_four`),
  la courbure radiale n'est bornée par aucun horizon (`radialCurvature_unbounded`). L'asymétrie sous raffinement est
  celle de la croissance : en faire une loi revient à borner le reste (anti-circularité, voir le maître).

Borne : identités algébriques valables pour toute famille de Tours, sans aucune donnée arithmétique ; elles sont donc
vraies dans tout monde témoin. L'interaction ne contient aucune information de continuation au-delà de la courbure propre
et n'en sélectionne aucune. Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Real

/-! ## 1. Le changement d'interaction se factorise par la courbure de la continuation -/

/-- **Interaction** de deux termes : le terme croisé `Re(u · v̄)` de `‖u + v‖² = ‖u‖² + ‖v‖² + 2 Re(u · v̄)`. -/
noncomputable def towerInteraction (u v : ℂ) : ℝ := (u * (starRingEnd ℂ) v).re

theorem towerInteraction_add_left (u u' v : ℂ) :
    towerInteraction (u + u') v = towerInteraction u v + towerInteraction u' v := by
  unfold towerInteraction; rw [add_mul, Complex.add_re]

private theorem towerInteraction_mul_real (z : ℂ) (c : ℝ) (v : ℂ) :
    towerInteraction (z * (c : ℂ)) v = c * towerInteraction z v := by
  unfold towerInteraction
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Continuation radiale** : changement d'interaction avec toute Tour `w` = courbure radiale × interaction du double. -/
theorem interaction_change_radial {q : ℝ} (hq : 0 < q) (T d : ℝ) (w : ℂ) :
    towerInteraction (pairOverDouble q T d) w =
      radialCurvature q d * towerInteraction ((q : ℂ) ^ mirrorPoint T 0) w := by
  rw [pairOverDouble_eq hq, towerInteraction_mul_real]

/-- **Continuation verticale** : même facteur, courbure le long de la ligne. -/
theorem interaction_change_vertical {q : ℝ} (hq : 0 < q) (T h : ℝ) (w : ℂ) :
    towerInteraction (lineSplitOverDouble q T h) w =
      lineSplitCurvature q h * towerInteraction ((q : ℂ) ^ mirrorPoint T 0) w := by
  rw [lineSplitOverDouble_eq hq, towerInteraction_mul_real]

/-- **Toute famille finie de Tours engagées** : le changement d'interaction total est la courbure × l'interaction du
double avec la famille. -/
theorem interaction_change_family {ι : Type*} (S : Finset ι) (w : ι → ℂ) {q : ℝ} (hq : 0 < q) (T d : ℝ) :
    ∑ i ∈ S, towerInteraction (pairOverDouble q T d) (w i) =
      radialCurvature q d * ∑ i ∈ S, towerInteraction ((q : ℂ) ^ mirrorPoint T 0) (w i) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => interaction_change_radial hq T d (w i)

/-- **La paire est un ensemble symétrique** : la continuation radiale ne dépend pas du signe de la profondeur. -/
theorem pairOverDouble_even (q T d : ℝ) : pairOverDouble q T (-d) = pairOverDouble q T d := by
  unfold pairOverDouble; rw [neg_neg]; ring

/-- **Aucune orientation de profondeur dans l'interaction** : paire en `d`, avec toute Tour. -/
theorem interaction_change_even (q T d : ℝ) (w : ℂ) :
    towerInteraction (pairOverDouble q T (-d)) w = towerInteraction (pairOverDouble q T d) w := by
  rw [pairOverDouble_even]

#print axioms interaction_change_radial
#print axioms interaction_change_vertical
#print axioms interaction_change_family
#print axioms interaction_change_even

/-! ## 2. Signes : opposés entre continuations, fixés par une phase relative -/

/-- **Les deux continuations changent l'interaction avec une même Tour en sens opposés** (ou pas du tout). -/
theorem interaction_changes_opposite {q : ℝ} (hq : 0 < q) (T d h : ℝ) (w : ℂ) :
    towerInteraction (pairOverDouble q T d) w * towerInteraction (lineSplitOverDouble q T h) w ≤ 0 := by
  rw [interaction_change_radial hq, interaction_change_vertical hq]
  have hk := radialCurvature_nonneg q d
  have hc := (lineSplitCurvature_bounds q h).2
  have : radialCurvature q d * lineSplitCurvature q h ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk hc
  nlinarith [sq_nonneg (towerInteraction ((q : ℂ) ^ mirrorPoint T 0) w)]

/-- **Interaction du double de hauteur `T` avec une Tour engagée** `1/2 + d' + iT'`, lue au réel `q`. -/
noncomputable def referenceCross (q T T' d' : ℝ) : ℝ :=
  towerInteraction ((q : ℂ) ^ mirrorPoint T 0) ((q : ℂ) ^ mirrorPoint T' d')

/-- **Forme exacte** : `q^{1+d'}·cos((T − T') log q)`. -/
theorem referenceCross_eq {q : ℝ} (hq : 0 < q) (T T' d' : ℝ) :
    referenceCross q T T' d' = Real.exp (Real.log q * (1 + d')) * Real.cos (Real.log q * (T - T')) := by
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq.ne'
  have ex : ∀ z : ℂ, (q : ℂ) ^ z = Complex.exp (Real.log q * z) := fun z => by
    rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.ofReal_log hq.le]
  unfold referenceCross towerInteraction
  rw [ex, ex, ← Complex.exp_conj, ← Complex.exp_add, Complex.exp_re]
  congr 1
  · congr 1
    simp [mirrorPoint]; ring
  · congr 1
    simp [mirrorPoint]; ring

/-- **Le signe de l'interaction avec une Tour de hauteur différente change arbitrairement loin** : au-delà de tout
horizon, il existe des lectures où elle est positive et des lectures où elle est négative. -/
theorem referenceCross_sign_changes {T T' : ℝ} (hT : T ≠ T') (d' U : ℝ) :
    (∃ u, U ≤ u ∧ 0 < referenceCross (Real.exp u) T T' d') ∧
      (∃ u, U ≤ u ∧ referenceCross (Real.exp u) T T' d' < 0) := by
  have hD : 0 < |T - T'| := abs_pos.2 (sub_ne_zero.2 hT)
  obtain ⟨k, hk⟩ := exists_nat_gt (|U| * |T - T'| / (2 * π))
  have hk' : |U| ≤ 2 * π * k / |T - T'| := by
    rw [div_lt_iff₀ (by positivity)] at hk
    rw [le_div_iff₀ hD]; nlinarith [Real.pi_pos]
  have key : ∀ m : ℝ, Real.cos (m / |T - T'| * (T - T')) = Real.cos m := fun m => by
    rcases le_or_gt 0 (T - T') with h | h
    · rw [abs_of_nonneg h, div_mul_cancel₀ _ (sub_ne_zero.2 hT)]
    · rw [abs_of_neg h, div_neg, neg_mul, div_mul_cancel₀ _ (sub_ne_zero.2 hT), Real.cos_neg]
  refine ⟨⟨2 * π * k / |T - T'|, by linarith [le_abs_self U], ?_⟩,
    ⟨(2 * π * k + π) / |T - T'|, ?_, ?_⟩⟩
  · rw [referenceCross_eq (Real.exp_pos _), Real.log_exp, key]
    rw [show 2 * π * (k : ℝ) = (k : ℕ) * (2 * π) by ring, Real.cos_nat_mul_two_pi, mul_one]
    exact Real.exp_pos _
  · have : 2 * π * k / |T - T'| ≤ (2 * π * k + π) / |T - T'| :=
      div_le_div_of_nonneg_right (by linarith [Real.pi_pos]) hD.le
    linarith [le_abs_self U]
  · rw [referenceCross_eq (Real.exp_pos _), Real.log_exp, key]
    rw [show 2 * π * (k : ℝ) + π = π + (k : ℕ) * (2 * π) by ring, Real.cos_add_nat_mul_two_pi, Real.cos_pi]
    rw [mul_neg_one]; exact neg_neg_of_pos (Real.exp_pos _)

#print axioms interaction_changes_opposite
#print axioms referenceCross_eq
#print axioms referenceCross_sign_changes

/-! ## 3. Le seul terme de signe fixe est le terme propre -/

/-- **Ordre des énergies propres** : continuation radiale `≥` double `≥` continuation verticale, en module. -/
theorem self_energy_order {q : ℝ} (hq : 0 < q) (T d h : ℝ) :
    ‖2 * (q : ℂ) ^ mirrorPoint T 0‖ ≤ ‖2 * (q : ℂ) ^ mirrorPoint T 0 + pairOverDouble q T d‖ ∧
      ‖2 * (q : ℂ) ^ mirrorPoint T 0 + lineSplitOverDouble q T h‖ ≤ ‖2 * (q : ℂ) ^ mirrorPoint T 0‖ := by
  have hn : ‖(q : ℂ) ^ mirrorPoint T 0‖ = q ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq]; simp [mirrorPoint]
  have hr : 0 ≤ q ^ (1 / 2 : ℝ) := Real.rpow_nonneg hq.le _
  have e1 : 2 * (q : ℂ) ^ mirrorPoint T 0 + pairOverDouble q T d =
      (q : ℂ) ^ mirrorPoint T 0 * ((2 + radialCurvature q d : ℝ) : ℂ) := by
    rw [pairOverDouble_eq hq]; push_cast; ring
  have e2 : 2 * (q : ℂ) ^ mirrorPoint T 0 + lineSplitOverDouble q T h =
      (q : ℂ) ^ mirrorPoint T 0 * ((2 + lineSplitCurvature q h : ℝ) : ℂ) := by
    rw [lineSplitOverDouble_eq hq]; push_cast; ring
  have e0 : ‖2 * (q : ℂ) ^ mirrorPoint T 0‖ = 2 * q ^ (1 / 2 : ℝ) := by
    rw [norm_mul, hn]; norm_num
  have hk := radialCurvature_nonneg q d
  have hc := (lineSplitCurvature_bounds q h).2
  have hc4 : -4 ≤ lineSplitCurvature q h := by
    unfold lineSplitCurvature; linarith [Real.neg_one_le_cos (h * Real.log q)]
  rw [e1, e2, e0, norm_mul, norm_mul, hn, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 + radialCurvature q d)]
  refine ⟨by nlinarith, ?_⟩
  have : |2 + lineSplitCurvature q h| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
  nlinarith

#print axioms self_energy_order

/-! ## 4. Raffinement : la courbure verticale est bornée, la radiale ne l'est pas -/

theorem lineSplitCurvature_ge_neg_four (q h : ℝ) : -4 ≤ lineSplitCurvature q h := by
  unfold lineSplitCurvature; linarith [Real.neg_one_le_cos (h * Real.log q)]

/-- **La courbure radiale n'est bornée par aucun horizon** dès que la profondeur est non nulle. -/
theorem radialCurvature_unbounded {d : ℝ} (hd : d ≠ 0) (C : ℝ) : ∃ q : ℝ, 1 < q ∧ C < radialCurvature q d := by
  have hd' : 0 < |d| := abs_pos.2 hd
  refine ⟨Real.exp ((|C| + 1) / |d|), Real.one_lt_exp_iff.2 (by positivity), ?_⟩
  have h := radialCurvature_ge_sq (Real.exp ((|C| + 1) / |d|)) d
  rw [Real.log_exp] at h
  have : (d * ((|C| + 1) / |d|)) ^ 2 = (|C| + 1) ^ 2 := by
    rw [mul_pow, div_pow, sq_abs, mul_div_assoc', mul_comm, mul_div_assoc, div_self (pow_ne_zero 2 hd), mul_one]
  rw [this] at h
  nlinarith [le_abs_self C, abs_nonneg C]

#print axioms lineSplitCurvature_ge_neg_four
#print axioms radialCurvature_unbounded

end RHV6Fresh
