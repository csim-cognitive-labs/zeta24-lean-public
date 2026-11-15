/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TransmissionIncrements

/-!
# Exposant du retrait de l'historique (auteur, 2026-10-11 : « démontre le retrait d'exposant »)

Le but de la transmission demande une estimation du retrait de l'historique `R − P_H` sur toute fenêtre finie
d'événements premiers, d'exposant `θ < 1 − β_l`. Ce module DÉMONTRE ce que vaut exactement cet exposant (canal lissé,
seule représentation démontrée), sans prémisse :

* `historyRemoved_eq_tail` : sur la fenêtre, le retrait signé est la queue `Σ_r λ_r Q_H(x_r)` (identité exacte) ;
* `followingSum_le_of_zero_free_above` : si tout zéro au-dessus de `H` a une partie réelle `≤ θ`, `‖Q_H(x)‖ ≤ budget(H)·x^θ` ;
* `removal_estimate_of_zero_free_above` : alors le retrait vérifie l'estimation d'exposant `θ` sur TOUTE fenêtre, constante
  `budget(H)` explicite ;
* `zero_free_above_of_removal_estimate` : réciproquement, une estimation d'exposant `θ` (même aux seules fenêtres à un
  point) force tout zéro au-dessus de `H` sous `θ` (lecture du pôle) ;
* `removal_estimate_iff_zero_free_above` : les exposants admissibles du retrait sont EXACTEMENT les majorants des parties
  réelles des zéros au-dessus de `H` ;
* `removal_estimate_reads_arrival` : au-dessus de `H < T_l`, toute estimation d'exposant `θ` lit l'arrivée et son miroir :
  `max(β_l, 1 − β_l) ≤ θ`.

Portée : caractérisation exacte de l'exposant du retrait ; aucune borne d'exposant `< 1` n'est démontrée (seul `θ = 1`,
`removal_increment_le`). Aucune régularité observée n'est posée en hypothèse.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **Retrait = queue** : sur une fenêtre de points `> 1`, `Σ_r λ_r (R − P_H)(x_r) = Σ_r λ_r Q_H(x_r)`. -/
theorem historyRemoved_eq_tail (H : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    historyRemoved H x lam = ∑ r, lam r * followingSum H (x r) := by
  unfold historyRemoved
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [remainder_eq_preceding_add_following H (hx r)]
  ring

/-- **Queue sous la bande** : tout zéro au-dessus de `H` sous `θ` ⟹ `‖Q_H(x)‖ ≤ budget(H)·x^θ` pour `x > 1`. -/
theorem followingSum_le_of_zero_free_above {H θ : ℝ}
    (h : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → (σ : ℂ).re ≤ θ) {x : ℝ} (hx : 1 < x) :
    ‖followingSum H x‖ ≤ followingBudget H * x ^ θ := by
  have hx0 : 0 < x := lt_trans one_pos hx
  have hterm : ∀ σ : ExplicitIndex, ‖followingWeight H σ * (x : ℂ) ^ (σ : ℂ)‖ ≤
      ‖followingWeight H σ‖ * x ^ θ := by
    intro σ
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    by_cases hσ : H < |(σ : ℂ).im|
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx.le (h σ hσ)) (norm_nonneg _)
    · have h0 : followingWeight H σ = 0 := by unfold followingWeight; rw [if_neg hσ]
      rw [h0, norm_zero, zero_mul, zero_mul]
  have hdom : Summable fun σ : ExplicitIndex => ‖followingWeight H σ‖ * x ^ θ :=
    (followingWeight_norm_summable H).mul_right _
  have hs : Summable fun σ : ExplicitIndex => ‖followingWeight H σ * (x : ℂ) ^ (σ : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hdom
  unfold followingSum followingBudget
  calc ‖∑' σ : ExplicitIndex, followingWeight H σ * (x : ℂ) ^ (σ : ℂ)‖
      ≤ ∑' σ : ExplicitIndex, ‖followingWeight H σ * (x : ℂ) ^ (σ : ℂ)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' σ : ExplicitIndex, ‖followingWeight H σ‖ * x ^ θ := Summable.tsum_le_tsum hterm hs hdom
    _ = (∑' σ : ExplicitIndex, ‖followingWeight H σ‖) * x ^ θ := tsum_mul_right

/-- **Estimation du retrait depuis la bande au-dessus de `H`** : sur toute fenêtre finie de points `> 1`,
`‖Σ_r λ_r (R − P_H)(x_r)‖ ≤ budget(H)·Σ_r |λ_r| x_r^θ`. -/
theorem removal_estimate_of_zero_free_above {H θ : ℝ}
    (h : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → (σ : ℂ).re ≤ θ)
    (m : ℕ) (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    ‖historyRemoved H x lam‖ ≤ followingBudget H * ∑ r, ‖lam r‖ * x r ^ θ := by
  rw [historyRemoved_eq_tail H x lam hx, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul]
  calc ‖lam r‖ * ‖followingSum H (x r)‖ ≤ ‖lam r‖ * (followingBudget H * x r ^ θ) :=
        mul_le_mul_of_nonneg_left (followingSum_le_of_zero_free_above h (hx r)) (norm_nonneg _)
    _ = followingBudget H * (‖lam r‖ * x r ^ θ) := by ring

/-- **Lecture du pôle par le retrait** : une estimation d'exposant `θ` (fenêtres à un point suffisent) force tout zéro
au-dessus de `H` sous `θ`. -/
theorem zero_free_above_of_removal_estimate {H θ C : ℝ}
    (hEst : ∀ (m : ℕ) (x : Fin m → ℝ) (lam : Fin m → ℂ), (∀ r, 1 < x r) →
      ‖historyRemoved H x lam‖ ≤ C * ∑ r, ‖lam r‖ * x r ^ θ) :
    ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → (σ : ℂ).re ≤ θ := by
  refine fun σ hσ => followingSum_growth_bounds_each (C := C) (fun x hx => ?_) σ hσ
  have h1 := hEst 1 (fun _ => x) (fun _ => 1) (fun _ => hx)
  rw [historyRemoved_eq_tail H _ _ (fun _ => hx)] at h1
  simpa only [Fin.sum_univ_one, one_mul, norm_one] using h1

/-- **Exposant exact du retrait** : l'estimation du retrait de l'historique `]−∞, H]` d'exposant `θ`, sur toute fenêtre
finie d'événements premiers, existe ⟺ tout zéro au-dessus de `H` a une partie réelle `≤ θ`. Caractérisation : aucun des
deux côtés n'est dérivé ici. -/
theorem removal_estimate_iff_zero_free_above (H θ : ℝ) :
    (∃ C : ℝ, ∀ (m : ℕ) (x : Fin m → ℝ) (lam : Fin m → ℂ), (∀ r, 1 < x r) →
      ‖historyRemoved H x lam‖ ≤ C * ∑ r, ‖lam r‖ * x r ^ θ) ↔
      ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → (σ : ℂ).re ≤ θ :=
  ⟨fun ⟨_, hC⟩ => zero_free_above_of_removal_estimate hC,
    fun h => ⟨followingBudget H, removal_estimate_of_zero_free_above h⟩⟩

/-- **Le retrait lit l'arrivée et son miroir** : si `H < T_z`, toute estimation du retrait d'exposant `θ` donne
`β_z ≤ θ` et `1 − β_z ≤ θ` (le miroir est à la même hauteur). -/
theorem removal_estimate_reads_arrival {H θ C : ℝ} (z : TrueZero) (hz : H < rZeroHeight z.1)
    (hEst : ∀ (m : ℕ) (x : Fin m → ℝ) (lam : Fin m → ℂ), (∀ r, 1 < x r) →
      ‖historyRemoved H x lam‖ ≤ C * ∑ r, ‖lam r‖ * x r ^ θ) :
    rZeroRadialPosition z.1 ≤ θ ∧ 1 - rZeroRadialPosition z.1 ≤ θ := by
  have hS := zero_free_above_of_removal_estimate hEst
  have hread : ∀ w : TrueZero, H < rZeroHeight w.1 → rZeroRadialPosition w.1 ≤ θ := fun w hw => by
    have hpos : 0 < rZeroHeight w.1 := w.2
    have := hS (memberIndex w) (by
      rw [show ((memberIndex w : ExplicitIndex) : ℂ) = zeroPoint w from rfl, zeroPoint_im, abs_of_pos hpos]
      exact hw)
    rwa [show ((memberIndex w : ExplicitIndex) : ℂ) = zeroPoint w from rfl, zeroPoint_re] at this
  refine ⟨hread z hz, ?_⟩
  have := hread (mirrorMember z) (by rw [mirrorMember_ordinate]; exact hz)
  rwa [mirrorMember_radial] at this

#print axioms historyRemoved_eq_tail
#print axioms followingSum_le_of_zero_free_above
#print axioms removal_estimate_of_zero_free_above
#print axioms zero_free_above_of_removal_estimate
#print axioms removal_estimate_iff_zero_free_above
#print axioms removal_estimate_reads_arrival

end RHV6Fresh
