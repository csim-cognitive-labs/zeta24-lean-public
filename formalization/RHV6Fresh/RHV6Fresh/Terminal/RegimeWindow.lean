/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RegimeCell
import RHV6Fresh.Terminal.GrammarWordLoad
import RHV6Fresh.Terminal.RadialSlope

/-!
# RHV6Fresh — la fenêtre minimale de changement de régime, lue d'un seul tenant (E158, auteur, 2026-10-03)

Correction d'échelle de l'auteur : un changement de régime n'est ni un passage ni toute l'histoire ; son unité minimale
est la cellule complète `a → e → l → b` (quatre membres, trois passages, un premier partagé par passage, ces trois
premiers étant consécutifs, deux écarts entre eux). On réunit ici, sur ce même objet, le mot premier de la cellule, la
lecture de ce mot par les Tours de la cellule, la charge et la lecture côté premier (somme sur les membres).

* **Comptage** (§1) : la cellule occupe trois rangs successifs au-delà de `a` (`rank_span`) et seulement trois hauteurs
  pour quatre membres (`heights_three_for_four`) : elle consomme un rang sans hauteur nouvelle.
* **Lecture du mot par les deux membres centraux** (§2) : sur toute marche `p → q`, même avance de phase
  (`central_phase_advance_eq`), amplitudes `(q/p)^{1/2 ∓ d}` (`central_amplitude_readings`) ; l'écart des deux lectures
  est linéaire en `d` et ne voit que les extrémités.
* **La charge, lecture orientée par la structure interne du mot** (§3) : son logarithme vaut `d` fois la différence
  seconde `log(M₂/M₁) − log(M₃/M₂)` des trois premiers (`log_charge_eq`), impair en la profondeur
  (`log_rpow_neg_eq`) ; il est borné par la profondeur fois la somme des écarts relatifs
  (`abs_log_charge_le`) : la charge est d'ordre profondeur × écart relatif.
* **La lecture côté premier est paire en la profondeur** (§4) : la somme des deux termes de la paire miroir dans la
  formule explicite est une fonction paire de `d` (`mirrorPairTerm_even`, `central_pair_term`) ; toute dérivée en
  `d = 0` est nulle (`mirrorPairTerm_first_order_blind`). Le côté premier, qui ne voit que la somme sur tous les
  membres, ne lit la profondeur d'une paire qu'à l'ordre deux ; le terme linéaire de la charge n'existe que dans les
  lectures individuelles des Tours.

Borne : ce sont des identités sur la cellule ; aucune n'exclut la cellule. Elles disent où vit chaque ordre en la
profondeur : linéaire dans les lectures individuelles (charge, dette du mot), quadratique dans tout ce que le côté
premier mesure. Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Real RHV3Lean

/-! ## 1. Comptage : quatre membres, trois passages, trois hauteurs -/

namespace RegimeCell

variable (C : RegimeCell)

/-- **La cellule occupe trois rangs au-delà de `a`.** -/
theorem rank_span :
    nZeroSourceIndex C.e.1 = nZeroSourceIndex C.a.1 + 1 ∧
      nZeroSourceIndex C.l.1 = nZeroSourceIndex C.a.1 + 2 ∧
      nZeroSourceIndex C.b.1 = nZeroSourceIndex C.a.1 + 3 := by
  have n1 := thm_zeroSourceIndex_succ_of_consecutive C.a.2 C.cons_ae
  have n2 := thm_zeroSourceIndex_succ_of_consecutive C.e.2 C.cons_el
  have n3 := thm_zeroSourceIndex_succ_of_consecutive C.l.2 C.cons_lb
  refine ⟨n1, ?_, ?_⟩
  · rw [n2, n1]
  · rw [n3, n2, n1]

/-- **Trois hauteurs pour quatre membres** : les deux membres centraux sont distincts et de même hauteur. -/
theorem heights_three_for_four :
    rZeroHeight C.a.1 < rZeroHeight C.e.1 ∧ rZeroHeight C.e.1 = rZeroHeight C.l.1 ∧
      rZeroHeight C.l.1 < rZeroHeight C.b.1 ∧ C.e ≠ C.l := by
  refine ⟨C.enter, C.level, C.leave, fun h => ?_⟩
  have := C.radial_lt
  rw [h] at this
  exact lt_irrefl _ this

/-! ## 2. Lecture d'une marche du mot par les deux membres centraux -/

/-- **Même avance de phase** sur toute marche : la hauteur est commune. -/
theorem central_phase_advance_eq (p q : ℝ) :
    rZeroHeight C.e.1 * (Real.log q - Real.log p) = rZeroHeight C.l.1 * (Real.log q - Real.log p) := by
  rw [C.level]

private theorem norm_zeroTerm_ratio (z : TrueZero) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ‖zeroTerm z q‖ / ‖zeroTerm z p‖ = (q / p) ^ rZeroRadialPosition z.1 := by
  unfold zeroTerm
  rw [norm_div, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hq,
    Complex.norm_cpow_eq_rpow_re_of_pos hp, zeroPoint_re, Real.div_rpow hq.le hp.le]
  have hN := (zeroPoint_norm_pos z).ne'
  have hp' := (Real.rpow_pos_of_pos hp (rZeroRadialPosition z.1)).ne'
  field_simp

/-- **Amplitudes lues sur une marche** : `(q/p)^{1/2 − d}` pour `e`, `(q/p)^{1/2 + d}` pour `l`. -/
theorem central_amplitude_readings {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ‖zeroTerm C.e q‖ / ‖zeroTerm C.e p‖ = (q / p) ^ (1 / 2 - C.offset) ∧
      ‖zeroTerm C.l q‖ / ‖zeroTerm C.l p‖ = (q / p) ^ (1 / 2 + C.offset) := by
  rw [norm_zeroTerm_ratio C.e hp hq, norm_zeroTerm_ratio C.l hp hq, C.radial_e_eq, C.radial_l_eq]
  exact ⟨rfl, rfl⟩

/-- **L'écart des deux lectures d'amplitude** sur une marche est `2d · log(q/p)` : linéaire en `d`, et, sommé sur
le mot, fixé par ses extrémités. -/
theorem central_amplitude_gap {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Real.log ((q / p) ^ (1 / 2 + C.offset)) - Real.log ((q / p) ^ (1 / 2 - C.offset)) =
      2 * C.offset * Real.log (q / p) := by
  have h := div_pos hq hp
  rw [Real.log_rpow h, Real.log_rpow h]
  ring

end RegimeCell

/-! ## 3. La charge : lecture orientée par la structure interne du mot -/

/-- La base de la charge est la différence seconde des logarithmes des trois premiers. -/
theorem log_charge_base_eq {M₁ M₂ M₃ : ℝ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃) :
    Real.log (M₂ ^ 2 / (M₁ * M₃)) = Real.log (M₂ / M₁) - Real.log (M₃ / M₂) := by
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul h₁.ne' h₃.ne', Real.log_pow,
    Real.log_div h₂.ne' h₁.ne', Real.log_div h₃.ne' h₂.ne']
  push_cast
  ring

/-- **Une charge est impaire en la profondeur.** -/
theorem log_rpow_neg_eq {b : ℝ} (hb : 0 < b) (d : ℝ) :
    Real.log (b ^ (-d)) = -Real.log (b ^ d) := by
  rw [Real.log_rpow hb, Real.log_rpow hb]
  ring

/-- Un pas de logarithme est borné par l'écart relatif. -/
theorem log_ratio_bounds {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    0 ≤ Real.log (q / p) ∧ Real.log (q / p) ≤ (q - p) / p := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  refine ⟨Real.log_nonneg ((one_le_div hp).2 hpq), ?_⟩
  have h := Real.log_le_sub_one_of_pos (div_pos hq hp)
  have e : q / p - 1 = (q - p) / p := by field_simp
  linarith

namespace RegimeCell

variable (C : RegimeCell)

private theorem M_pos : (0 : ℝ) < C.M₁ ∧ (0 : ℝ) < C.M₂ ∧ (0 : ℝ) < C.M₃ := by
  obtain ⟨p1, p2, p3, _⟩ := C.primes
  exact ⟨by exact_mod_cast p1.pos, by exact_mod_cast p2.pos, by exact_mod_cast p3.pos⟩

/-- **Le logarithme de la charge** est la profondeur fois la différence seconde des logarithmes des trois premiers :
il lit la comparaison des deux écarts, pas seulement les extrémités. -/
theorem log_charge_eq :
    Real.log C.charge =
      C.offset * (Real.log ((C.M₂ : ℝ) / C.M₁) - Real.log ((C.M₃ : ℝ) / C.M₂)) := by
  obtain ⟨h1, h2, h3⟩ := C.M_pos
  unfold charge
  rw [Real.log_rpow (by positivity), log_charge_base_eq h1 h2 h3]

/-- **Taille de la charge** : profondeur × somme des deux écarts relatifs. -/
theorem abs_log_charge_le :
    |Real.log C.charge| ≤
      C.offset * (((C.M₂ : ℝ) - C.M₁) / C.M₁ + ((C.M₃ : ℝ) - C.M₂) / C.M₂) := by
  obtain ⟨h1, h2, h3⟩ := C.M_pos
  obtain ⟨_, _, _, h12, h23, _⟩ := C.primes
  have l12 : (C.M₁ : ℝ) ≤ C.M₂ := by exact_mod_cast h12.le
  have l23 : (C.M₂ : ℝ) ≤ C.M₃ := by exact_mod_cast h23.le
  obtain ⟨a0, a1⟩ := log_ratio_bounds h1 l12
  obtain ⟨b0, b1⟩ := log_ratio_bounds h2 l23
  rw [C.log_charge_eq, abs_mul, abs_of_pos C.offset_pos]
  apply mul_le_mul_of_nonneg_left _ C.offset_pos.le
  rw [abs_le]
  constructor <;> linarith

end RegimeCell

/-! ## 4. La lecture côté premier d'une paire miroir est paire en la profondeur -/

/-- Le point `1/2 + d + iT`. -/
noncomputable def mirrorPoint (T d : ℝ) : ℂ := ((1 / 2 + d : ℝ) : ℂ) + (T : ℂ) * Complex.I

/-- **La contribution d'une paire miroir** `1/2 ± d + iT` au terme `q^ρ/ρ` de la formule explicite. -/
noncomputable def mirrorPairTerm (q T d : ℝ) : ℂ :=
  (q : ℂ) ^ mirrorPoint T d / mirrorPoint T d + (q : ℂ) ^ mirrorPoint T (-d) / mirrorPoint T (-d)

/-- **Parité** : la contribution d'une paire miroir ne change pas quand la profondeur change de signe. -/
theorem mirrorPairTerm_even (q T d : ℝ) : mirrorPairTerm q T (-d) = mirrorPairTerm q T d := by
  unfold mirrorPairTerm
  rw [neg_neg, add_comm]

/-- Une fonction paire a une dérivée nulle en `0`, si elle en a une. -/
theorem even_hasDerivAt_zero {f : ℝ → ℂ} {f' : ℂ} (he : ∀ d, f (-d) = f d) (h : HasDerivAt f f' 0) :
    f' = 0 := by
  have h2 : HasDerivAt (fun d => f (-d)) (-f') 0 := by
    have hg : HasDerivAt f f' (-(0 : ℝ)) := by simpa using h
    have := hg.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    simpa [Function.comp_def] using this
  have hfun : (fun d => f (-d)) = f := funext he
  rw [hfun] at h2
  have := h.unique h2
  linear_combination (1 / 2 : ℂ) * this

/-- **Le côté premier ne lit pas la profondeur au premier ordre** : quelle que soit sa dérivée en `d = 0`, la
contribution de la paire y a une dérivée nulle. -/
theorem mirrorPairTerm_first_order_blind (q T : ℝ) {f' : ℂ}
    (h : HasDerivAt (fun d => mirrorPairTerm q T d) f' 0) : f' = 0 :=
  even_hasDerivAt_zero (fun d => mirrorPairTerm_even q T d) h

/-- **Les deux membres centraux de la cellule** contribuent ensemble la paire miroir de leur hauteur et de leur
profondeur. -/
theorem RegimeCell.central_pair_term (C : RegimeCell) (q : ℝ) :
    zeroTerm C.e q + zeroTerm C.l q = mirrorPairTerm q (rZeroHeight C.e.1) C.offset := by
  have he : zeroPoint C.e = mirrorPoint (rZeroHeight C.e.1) (-C.offset) := by
    apply Complex.ext
    · simp [mirrorPoint, zeroPoint_re, C.radial_e_eq, sub_eq_add_neg]
    · simp [mirrorPoint, zeroPoint_im]
  have hl : zeroPoint C.l = mirrorPoint (rZeroHeight C.e.1) C.offset := by
    apply Complex.ext
    · simp [mirrorPoint, zeroPoint_re, C.radial_l_eq]
    · simp [mirrorPoint, zeroPoint_im, C.level]
  unfold zeroTerm mirrorPairTerm
  rw [he, hl, add_comm]

#print axioms RegimeCell.rank_span
#print axioms RegimeCell.heights_three_for_four
#print axioms RegimeCell.central_phase_advance_eq
#print axioms RegimeCell.central_amplitude_readings
#print axioms RegimeCell.central_amplitude_gap
#print axioms log_charge_base_eq
#print axioms log_rpow_neg_eq
#print axioms RegimeCell.log_charge_eq
#print axioms RegimeCell.abs_log_charge_le
#print axioms mirrorPairTerm_even
#print axioms even_hasDerivAt_zero
#print axioms mirrorPairTerm_first_order_blind
#print axioms RegimeCell.central_pair_term

end RHV6Fresh
