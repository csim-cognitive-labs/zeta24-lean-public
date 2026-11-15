/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RemainderEnergy
import RHV6Fresh.Terminal.RadialSlope

/-!
# RHV6Fresh — lecture exacte de l'axe algébrique et aveuglement de la diagonale (E155, auteur, 2026-10-02)

Réorientation de l'auteur : `Li` est un fond macroscopique de comptage, une moyenne ; il ne définit le contenu
d'aucune cellule. Les objets locaux sont exacts : contacts, cellules, rayons, premiers, poids `Λ`, écarts
`log(p'/p) = Λ(p') − Λ(p)`. Ce fichier écrit ce que ces objets exacts donnent, et ce que la diagonale `Λ²` ne voit pas.

* **Un écart exact, trois lectures** (§1) : entre deux premiers, l'écart logarithmique est la différence des poids
  (`prime_gap_eq_weight_difference`) ; la Tour d'un membre le lit en demi-tours par la hauteur, en logarithme
  d'amplitude par la position radiale, en logarithme d'énergie par le double de la position radiale
  (`exact_gap_three_readings`).
* **Télescopage** (§2) : le long d'une chaîne d'événements, la lecture cumulée ne dépend que des extrémités
  (`chain_reading_telescopes`, `chain_reading_endpoint_only`) et pas de l'ordre des écarts
  (`chain_reading_gap_order_blind`) ; l'écart radial miroir cumulé vaut `2d·log(q_m/q_0)`, logarithme du facteur
  d'amplitude des extrémités (`mirror_chain_accumulation`). L'accumulation radiale sur les écarts exacts est la
  translation rigide déjà compilée ; elle n'apporte aucune contrainte nouvelle.
* **Exposition au contact** (§3) : au contact, la projection réelle du terme propre a pour carré le carré de son
  rayon (`contact_energy_exposed`) : l'oscillation n'y cache pas l'amplitude.
* **La diagonale est aveugle aux signes** (§4) : pour tout choix de signes, le monde de poids `±Λ(n)` a le même
  support, la même valeur absolue et la même diagonale terme à terme (`signedWorld_abs_weight`,
  `diagonal_sign_blind`) ; la borne critique de la diagonale vaut donc mot pour mot dans chacun de ces mondes
  (`signedWorld_diagonal_linear`). E155 en construit un, de signes cohérents, qui porte des membres hors ligne.

Borne : la diagonale, le support et l'ordre des écarts lus par les Tours ne séparent pas zêta d'un monde à membres
hors ligne ; le transfert « énergie de cellule / diagonale » doit lire les signes et l'ordre exacts des poids
(structure multiplicative), à toutes les résolutions. Aucun `sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction

/-! ## 1. Un écart exact, trois lectures -/

/-- **L'écart entre deux premiers est la différence de leurs poids exacts.** -/
theorem prime_gap_eq_weight_difference {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    Λ q - Λ p = Real.log q - Real.log p := by
  rw [vonMangoldt_apply_prime hp, vonMangoldt_apply_prime hq]

/-- **Trois lectures du même écart** : demi-tours par la hauteur, amplitude par la position radiale, énergie par
le double de la position radiale. -/
theorem exact_gap_three_readings (z : TrueZero) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    towerPosition z q - towerPosition z p = rZeroHeight z.1 * (Real.log q - Real.log p) / Real.pi ∧
      Real.log ‖zeroTerm z q‖ - Real.log ‖zeroTerm z p‖ =
        rZeroRadialPosition z.1 * (Real.log q - Real.log p) ∧
      Real.log (‖zeroTerm z q‖ ^ 2) - Real.log (‖zeroTerm z p‖ ^ 2) =
        2 * rZeroRadialPosition z.1 * (Real.log q - Real.log p) := by
  obtain ⟨h1, h2⟩ := member_coordinates_separate z hp hq
  refine ⟨h1, h2, ?_⟩
  rw [Real.log_pow, Real.log_pow]
  push_cast
  linear_combination 2 * h2

/-! ## 2. Télescopage -/

/-- **La lecture cumulée ne dépend que des extrémités** : `Σ c·(log q_{i+1} − log q_i) = c·(log q_m − log q_0)`. -/
theorem chain_reading_telescopes (c : ℝ) (q : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, c * (Real.log (q (i + 1)) - Real.log (q i)) =
      c * (Real.log (q m) - Real.log (q 0)) := by
  rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => Real.log (q i))]

/-- **Deux chaînes de mêmes extrémités ont la même lecture cumulée**, quels que soient les événements
intermédiaires. -/
theorem chain_reading_endpoint_only (c : ℝ) (q q' : ℕ → ℝ) (m m' : ℕ) (h0 : q 0 = q' 0) (hm : q m = q' m') :
    ∑ i ∈ Finset.range m, c * (Real.log (q (i + 1)) - Real.log (q i)) =
      ∑ i ∈ Finset.range m', c * (Real.log (q' (i + 1)) - Real.log (q' i)) := by
  rw [chain_reading_telescopes, chain_reading_telescopes, h0, hm]

/-- **L'ordre des écarts n'est pas lu** : la lecture cumulée d'une famille d'écarts est invariante par permutation. -/
theorem chain_reading_gap_order_blind (c : ℝ) {m : ℕ} (g : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) :
    ∑ i, c * g (σ i) = ∑ i, c * g i :=
  Equiv.sum_comp σ (fun i => c * g i)

/-- **Accumulation radiale miroir** : l'écart entre les lectures radiales `1/2 + d` et `1/2 − d`, cumulé sur une
chaîne, vaut `2d·log(q_m/q_0)`, logarithme du facteur d'amplitude `(q_m/q_0)^{2d}` des extrémités. -/
theorem mirror_chain_accumulation (d : ℝ) (q : ℕ → ℝ) (m : ℕ) (h0 : 0 < q 0) (hm : 0 < q m) :
    ∑ i ∈ Finset.range m, ((1 / 2 + d) - (1 / 2 - d)) * (Real.log (q (i + 1)) - Real.log (q i)) =
      Real.log ((q m / q 0) ^ (2 * d)) := by
  rw [chain_reading_telescopes, Real.log_rpow (div_pos hm h0), Real.log_div hm.ne' h0.ne']
  ring

/-! ## 3. Exposition au contact -/

/-- **Au contact, l'oscillation ne cache pas l'amplitude** : le carré de la projection réelle du terme propre est le
carré de son rayon. -/
theorem contact_energy_exposed (z : TrueZero) (k : ℤ) :
    (zeroTerm z (contactMinusAt z k)).re ^ 2 = ‖zeroTerm z (contactMinusAt z k)‖ ^ 2 := by
  rw [ray_energy, zeroTerm_norm (contactMinusAt_positive z k), div_pow, div_pow, mul_pow,
    ← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul]
  norm_num

/-! ## 4. La diagonale est aveugle aux signes -/

/-- Dans un monde de poids `±Λ(n)`, la valeur absolue du poids est le poids exact. -/
theorem signedWorld_abs_weight (s : ℕ → ℝ) (hs : ∀ n, |s n| = 1) (n : ℕ) : |Λ n * s n| = Λ n := by
  rw [abs_mul, hs, mul_one, abs_of_nonneg vonMangoldt_nonneg]

/-- **Même diagonale terme à terme** : `(Λ(n)·s(n))² = Λ(n)²` pour tout choix de signes. -/
theorem diagonal_sign_blind (s : ℕ → ℝ) (hs : ∀ n, |s n| = 1) :
    (fun n => (Λ n * s n) ^ 2) = fun n => Λ n ^ 2 := by
  funext n
  rw [← sq_abs, signedWorld_abs_weight s hs]

/-- **La borne critique de la diagonale vaut dans tout monde signé** : elle ne peut donc séparer zêta d'aucun d'eux. -/
theorem signedWorld_diagonal_linear (s : ℕ → ℝ) (hs : ∀ n, |s n| = 1) {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Λ n * s n) ^ 2 ≤ (Real.log 4 + 4) * x * Real.log x := by
  have h := congrFun (diagonal_sign_blind s hs)
  simp only [h]
  exact vonMangoldt_sq_sum_linear hx

end RHV6Fresh
