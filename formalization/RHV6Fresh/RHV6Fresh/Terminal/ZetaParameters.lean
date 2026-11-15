/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ArithmeticReading
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# RHV6Fresh — zêta et ses paramètres (auteur, 2026-09-30)

Énoncé de l'auteur : « la seule chose qui génère des zéros est zêta. Si zêta n'a pas de paramètre
qui change quelque chose, alors le régime ne change pas malgré sa progression vers le haut. Il te
suffit d'utiliser zêta et ses paramètres. »

Ce fichier prend l'énoncé au mot : il écrit ce que sont les paramètres de zêta, et il teste si
« aucun paramètre ne change » suffit à transmettre le régime.

* **§1 Les paramètres de zêta sont les premiers, et eux seuls** (`zeta_generated_by_primes`) :
  zêta est le produit, sur les premiers, du même facteur. Aucun autre paramètre n'entre dans sa
  définition, et aucun ne dépend de la hauteur.
* **§2 Monde témoin du changement de régime** (`regimeWitness`) : une fonction fixe, sans aucun
  paramètre, qui a le même miroir que zêta, la même conjugaison, qui est réelle sur la ligne, et
  dont le régime change en montant : un zéro sur la ligne à la hauteur `1`, seul à sa hauteur,
  puis deux jumeaux à la hauteur `2`, aucun zéro entre les deux
  (`regimeWitness_regime_changes`). Donc « aucun paramètre ne change », joint au miroir, à la
  conjugaison et à la réalité sur la ligne, ne suffit pas à transmettre le régime. Ce que zêta
  possède et que le témoin n'a pas : ses paramètres, les premiers.
* **§3 Le maillon manquant, dérivé des paramètres de zêta**
  (`heightOnly_of_remainder_sqrt_growth`, `engaged_persists_of_remainder_sqrt_growth`) : si le
  reste arithmétique, écrit avec les seuls premiers, est borné par `C · √x`, alors sur un passage
  vertical parti de la ligne seule la hauteur évolue, et le régime engagé perdure jusqu'à
  l'infini.

Borne : la borne en `√x` n'est pas dérivée.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Les paramètres de zêta -/

/-- **Zêta est engendrée par les premiers seuls** : pour `Re s > 1`, elle est le produit, sur les
premiers, du facteur `(1 − p^{−s})⁻¹`. Aucun autre paramètre, et aucun qui dépende de la
hauteur. -/
theorem zeta_generated_by_primes {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  riemannZeta_eulerProduct_tprod hs

/-! ## 2. Monde témoin du changement de régime -/

/-- **Le témoin** : une fonction fixe, sans paramètre. Avec `w = s − 1/2`,
`(w² + 1) · ((w − 1/4)² + 4) · ((w + 1/4)² + 4)`. -/
noncomputable def regimeWitness (s : ℂ) : ℂ :=
  ((s - 1 / 2) ^ 2 + 1) * (((s - 1 / 2) - 1 / 4) ^ 2 + 4) * (((s - 1 / 2) + 1 / 4) ^ 2 + 4)

/-- Le témoin a le miroir de zêta : `f(1 − s) = f(s)`. -/
theorem regimeWitness_mirror (s : ℂ) : regimeWitness (1 - s) = regimeWitness s := by
  unfold regimeWitness
  ring

/-- Le témoin commute à la conjugaison. -/
theorem regimeWitness_conj (s : ℂ) :
    regimeWitness ((starRingEnd ℂ) s) = (starRingEnd ℂ) (regimeWitness s) := by
  unfold regimeWitness
  simp only [map_mul, map_add, map_sub, map_pow, map_one, map_div₀, map_ofNat]

/-- Le témoin est réel sur la ligne. -/
theorem regimeWitness_real_onLine (t : ℝ) :
    (regimeWitness ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).im = 0 := by
  have h : regimeWitness ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
      (((1 - t ^ 2) * ((t ^ 2 - 1 / 16 - 4) ^ 2 + t ^ 2 / 4) : ℝ) : ℂ) := by
    unfold regimeWitness
    push_cast
    ring_nf
    rw [show Complex.I ^ 6 = -1 by
        rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Complex.I_sq]; norm_num,
      show Complex.I ^ 4 = 1 by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Complex.I_sq]; norm_num,
      Complex.I_sq]
    ring
  rw [h, Complex.ofReal_im]

/-- **Les zéros du témoin** : `1/2 ± i` sur la ligne, et les quatre points `1/2 ± 1/4 ± 2i`. -/
theorem regimeWitness_zero_iff (s : ℂ) :
    regimeWitness s = 0 ↔
      (s = 1 / 2 + Complex.I ∨ s = 1 / 2 - Complex.I) ∨
      (s = 3 / 4 + 2 * Complex.I ∨ s = 3 / 4 - 2 * Complex.I) ∨
      (s = 1 / 4 + 2 * Complex.I ∨ s = 1 / 4 - 2 * Complex.I) := by
  have h1 : (s - 1 / 2) ^ 2 + 1 = (s - (1 / 2 + Complex.I)) * (s - (1 / 2 - Complex.I)) := by
    have := Complex.I_sq
    linear_combination this
  have h2 : ((s - 1 / 2) - 1 / 4) ^ 2 + 4 =
      (s - (3 / 4 + 2 * Complex.I)) * (s - (3 / 4 - 2 * Complex.I)) := by
    have := Complex.I_sq
    linear_combination 4 * this
  have h3 : ((s - 1 / 2) + 1 / 4) ^ 2 + 4 =
      (s - (1 / 4 + 2 * Complex.I)) * (s - (1 / 4 - 2 * Complex.I)) := by
    have := Complex.I_sq
    linear_combination 4 * this
  unfold regimeWitness
  rw [h1, h2, h3, mul_eq_zero, mul_eq_zero, mul_eq_zero, mul_eq_zero, mul_eq_zero,
    sub_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero, or_assoc]

/-- **Le régime du témoin change en montant, sans aucun paramètre.** Un zéro sur la ligne à la
hauteur `1`, seul à sa hauteur ; aucun zéro de hauteur strictement comprise entre `1` et `2` ; à
la hauteur `2`, deux jumeaux de part et d'autre de la ligne. -/
theorem regimeWitness_regime_changes :
    regimeWitness (1 / 2 + Complex.I) = 0 ∧
    (∀ s : ℂ, regimeWitness s = 0 → s.im = 1 → s = 1 / 2 + Complex.I) ∧
    (∀ s : ℂ, regimeWitness s = 0 → ¬ (1 < s.im ∧ s.im < 2)) ∧
    regimeWitness (1 / 4 + 2 * Complex.I) = 0 ∧
    regimeWitness (3 / 4 + 2 * Complex.I) = 0 := by
  have him : ∀ s : ℂ, regimeWitness s = 0 →
      s.im = 1 ∧ s = 1 / 2 + Complex.I ∨ s.im = -1 ∨ s.im = 2 ∨ s.im = -2 := by
    intro s hs
    rcases (regimeWitness_zero_iff s).mp hs with (h | h) | (h | h) | (h | h)
    · exact Or.inl ⟨by rw [h]; simp, h⟩
    · exact Or.inr (Or.inl (by rw [h]; simp))
    · exact Or.inr (Or.inr (Or.inl (by rw [h]; simp)))
    · exact Or.inr (Or.inr (Or.inr (by rw [h]; simp)))
    · exact Or.inr (Or.inr (Or.inl (by rw [h]; simp)))
    · exact Or.inr (Or.inr (Or.inr (by rw [h]; simp)))
  refine ⟨(regimeWitness_zero_iff _).mpr (Or.inl (Or.inl rfl)), fun s hs h1 => ?_,
    fun s hs ⟨h1, h2⟩ => ?_, (regimeWitness_zero_iff _).mpr (Or.inr (Or.inr (Or.inl rfl))),
    (regimeWitness_zero_iff _).mpr (Or.inr (Or.inl (Or.inl rfl)))⟩
  · rcases him s hs with ⟨_, h⟩ | h | h | h
    · exact h
    · linarith
    · linarith
    · linarith
  · rcases him s hs with ⟨h, _⟩ | h | h | h <;> linarith

/-! ## 3. Le maillon manquant, dérivé des paramètres de zêta -/

/-- **La loi « seule la hauteur évolue », depuis les premiers seuls** : si le reste arithmétique
est borné par `C · √x`, alors sur tout passage vertical parti de la ligne la position radiale
n'évolue pas. -/
theorem heightOnly_of_remainder_sqrt_growth
    (h : ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 : ℝ)) :
    ∀ p : TZeroPassage, VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember :=
  heightOnly_of_riemannHypothesis (riemannHypothesis_of_remainder_sqrt_growth h)

/-- **Le régime engagé perdure jusqu'à l'infini, depuis les premiers seuls** : sous la borne en
`√x` du reste arithmétique, tout membre au-dessus d'un membre engagé est en ligne, atteint par un
passage vertical, et quitté verticalement. -/
theorem engaged_persists_of_remainder_sqrt_growth
    (h : ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 : ℝ))
    {o : TZeroPassage} (hE : 0 < rZeroHeight o.zLaterMember) (ho : VerticalPassage o)
    (hOn : rZeroRadialPosition o.zLaterMember = 1 / 2) :
    ∀ w : TNonTrivialZetaZero, PZeroMemberPrecedes o.zLaterMember w →
      rZeroRadialPosition w = 1 / 2 ∧
      (∃ q : TZeroPassage, q.zLaterMember = w ∧ VerticalPassage q) ∧
      (∀ q : TZeroPassage, q.zEarlierMember = w → VerticalPassage q ∧ ¬ HorizontalPassage q) :=
  engaged_persists_to_infinity (heightOnly_of_remainder_sqrt_growth h) hE ho hOn

#print axioms zeta_generated_by_primes
#print axioms regimeWitness_mirror
#print axioms regimeWitness_conj
#print axioms regimeWitness_real_onLine
#print axioms regimeWitness_zero_iff
#print axioms regimeWitness_regime_changes
#print axioms heightOnly_of_remainder_sqrt_growth
#print axioms engaged_persists_of_remainder_sqrt_growth

end RHV6Fresh
