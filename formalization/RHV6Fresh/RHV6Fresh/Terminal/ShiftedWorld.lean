/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ExplicitFormulaLink

/-!
# RHV6Fresh — le monde témoin où tous les zéros sont hors ligne (auteur, 2026-09-30)

Expérience par l'absurde demandée par l'auteur : « ignore les zéros connus sauf leurs hauteurs et fais
un monde où TOUS les zéros sont OFF ». Ce monde existe : c'est celui de
`F_δ(s) = ζ(s − δ) · ζ(s + δ)`.

* **Zéros** (`shiftedWorld_pair_off`) : chaque hauteur d'un zéro de `ζ` sur la ligne porte deux zéros
  de `F_δ`, de parties réelles `1/2 − δ` et `1/2 + δ`, à la MÊME hauteur — tous hors ligne.
* **Premiers** (`shiftedWorld_negLogDeriv`) : pour `Re s > 1 + |δ|`,
  `−ζ'/ζ(s − δ) − ζ'/ζ(s + δ) = Σ Λ(n)·n^δ·n^{−s} + Σ Λ(n)·n^{−δ}·n^{−s}`.
  Le support arithmétique est celui de `Λ` : les MÊMES puissances de premiers, donc la même
  grammaire ; seul le POIDS de chaque premier change (`n^δ + n^{−δ}` au lieu de `1`).

Conséquence (contrôle, pas une clôture) : aucune loi qui ne lit que les positions des premiers, la
grammaire et les hauteurs ne peut exclure le hors-ligne ; la loi cherchée doit lire le poids exact
`Λ(n)` ou la densité des membres. Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

open Complex ArithmeticFunction LSeries.notation

namespace RHV6Fresh

open RHV3Lean

/-- La fonction du monde témoin : `F_δ(s) = ζ(s − δ) · ζ(s + δ)`. -/
noncomputable def shiftedZeta (d : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (s - d) * riemannZeta (s + d)

/-- **Tous les zéros du monde témoin issus de la ligne sont hors ligne** : à la hauteur de tout zéro
`z` de `ζ` sur la ligne, `F_δ` s'annule en deux points de parties réelles `1/2 − δ` et `1/2 + δ`,
à la même hauteur que `z`, aucun sur la ligne dès que `δ ≠ 0`. -/
theorem shiftedWorld_pair_off (d : ℝ) (hd : d ≠ 0) (z : TrueZero)
    (hOn : rZeroRadialPosition z.1 = 1 / 2) :
    shiftedZeta d (zeroPoint z - d) = 0 ∧ shiftedZeta d (zeroPoint z + d) = 0 ∧
      (zeroPoint z - d).im = rZeroHeight z.1 ∧ (zeroPoint z + d).im = rZeroHeight z.1 ∧
      (zeroPoint z - d).re = 1 / 2 - d ∧ (zeroPoint z + d).re = 1 / 2 + d ∧
      (zeroPoint z - d).re ≠ 1 / 2 ∧ (zeroPoint z + d).re ≠ 1 / 2 := by
  have hz : riemannZeta (zeroPoint z) = 0 := z.1.2.1
  have hre : (zeroPoint z).re = 1 / 2 := hOn
  have hm : (zeroPoint z - d).re = 1 / 2 - d := by simp [hre]
  have hp : (zeroPoint z + d).re = 1 / 2 + d := by simp [hre]
  refine ⟨?_, ?_, ?_, ?_, hm, hp, ?_, ?_⟩
  · unfold shiftedZeta
    rw [sub_add_cancel, hz, mul_zero]
  · unfold shiftedZeta
    rw [add_sub_cancel_right, hz, zero_mul]
  · simp [zeroPoint_im]
  · simp [zeroPoint_im]
  · rw [hm]; intro h; apply hd; linarith
  · rw [hp]; intro h; apply hd; linarith

/-- Terme à terme : décaler l'argument de `δ` revient à multiplier le poids de `n` par `n^δ`. -/
theorem vonMangoldt_term_shift (d s : ℂ) (n : ℕ) :
    LSeries.term (fun n => (Λ n : ℂ) * (n : ℂ) ^ d) s n = LSeries.term ↗Λ (s - d) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_sub _ _ (Nat.cast_ne_zero.mpr hn), div_div_eq_mul_div]

/-- **La série décalée** : `L(Λ, s − δ) = L(Λ·n^δ, s)` — mêmes premiers, poids `n^δ`. -/
theorem LSeries_vonMangoldt_shift (d s : ℂ) :
    LSeries ↗Λ (s - d) = LSeries (fun n => (Λ n : ℂ) * (n : ℂ) ^ d) s := by
  unfold LSeries
  exact tsum_congr fun n => (vonMangoldt_term_shift d s n).symm

/-- **Les premiers du monde témoin sont les mêmes premiers** : pour `Re s > 1 + |δ|`, la dérivée
logarithmique de `F_δ` est la série de Dirichlet de `Λ(n)·n^δ` plus celle de `Λ(n)·n^{−δ}`. -/
theorem shiftedWorld_negLogDeriv (d : ℝ) {s : ℂ} (hs : 1 + |d| < s.re) :
    -logDeriv riemannZeta (s - d) - logDeriv riemannZeta (s + d) =
      LSeries (fun n => (Λ n : ℂ) * (n : ℂ) ^ (d : ℂ)) s +
        LSeries (fun n => (Λ n : ℂ) * (n : ℂ) ^ (-(d : ℂ))) s := by
  have h1 : 1 < (s - d).re := by
    simp only [sub_re, ofReal_re]
    linarith [le_abs_self d]
  have h2 : 1 < (s + d).re := by
    simp only [add_re, ofReal_re]
    linarith [neg_abs_le d]
  rw [← LSeries_vonMangoldt_shift, ← LSeries_vonMangoldt_shift, sub_neg_eq_add,
    ← negLogDeriv_riemannZeta_eq_LSeries_vonMangoldt h1,
    ← negLogDeriv_riemannZeta_eq_LSeries_vonMangoldt h2]
  ring

/-- **Même support arithmétique** : le poids du monde témoin en `n` est non nul exactement quand
`Λ(n)` l'est — mêmes puissances de premiers, même grammaire. -/
theorem shiftedWorld_weight_ne_zero_iff (d : ℝ) (n : ℕ) :
    (Λ n : ℂ) * (n : ℂ) ^ (d : ℂ) ≠ 0 ↔ Λ n ≠ 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hpow : (n : ℂ) ^ (d : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h => (Nat.cast_ne_zero.mpr hn) h.1
    simp [hpow]

#print axioms shiftedWorld_pair_off
#print axioms LSeries_vonMangoldt_shift
#print axioms shiftedWorld_negLogDeriv
#print axioms shiftedWorld_weight_ne_zero_iff

end RHV6Fresh
