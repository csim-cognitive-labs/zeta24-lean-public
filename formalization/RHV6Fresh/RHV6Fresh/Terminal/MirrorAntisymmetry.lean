/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MirrorLoop

/-!
# RHV6Fresh — canal antisymétrique d'une paire miroir et côté arithmétique (E163, auteur, 2026-10-03)

Question de l'auteur : la symétrie fonctionnelle fournit-elle deux expressions arithmétiques du même objet dont la
différence isole le canal antisymétrique d'une paire miroir (Tour croissante moins Tour décroissante) ?

* **Le canal existe au niveau des Tours** (§1) : `A_ρ(u) = Γ_ρ(u) − Γ_{ρ*}(u)` est nul en ligne
  (`pairAntisym_onLine`), change de signe quand on échange les deux membres (`pairAntisym_swap`), et n'est pas nul
  hors ligne (`pairAntisym_ne_zero_of_offLine`) : il est impair en la profondeur et orienté.
* **Le côté arithmétique ne le porte pas** (§2) : toute expression du côté arithmétique est une somme, sur toute la
  famille des membres, d'un même poids évalué en chaque membre. Sur toute famille stable par la réflexion, l'expression
  originale et l'expression miroir sont égales, pour tout poids (`mirror_sum_reindex`) : leur différence est nulle
  identiquement (`mirror_antisym_collective_zero`). Un poids impair par la réflexion s'annule sur la ligne
  (`mirror_odd_weight_zero_on_line`) ; s'il est holomorphe sur tout le plan il est nul (`mirror_odd_entire_weight_zero`).
  La différence de deux expressions arithmétiques distinctes (originale et boucle de E162) est un nouveau poids, qui
  lit aussi les membres en ligne (`loop_difference_onLine_ne_zero`) : ce n'est pas le canal antisymétrique.
* **Absence n'est pas annulation** (§3) : toute paire hors ligne forme une famille stable dont le canal collectif est
  nul pour tout poids, alors que son canal de Tour n'est pas nul (`antisym_channel_not_forced`). Vrai mot pour mot
  dans le monde décalé, dont tous les membres sont hors ligne.

Borne : l'hypothèse « le côté arithmétique n'a qu'un canal symétrique » est démontrée ; la conclusion « donc une
paire miroir véritable est fusionnée » ne l'est pas, et elle est fausse dans tout monde qui a le miroir. Aucun
`sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Complex RHV3Lean Filter Topology

/-! ## 1. Le canal antisymétrique d'une paire, au niveau des Tours -/

/-- **Canal antisymétrique** d'une paire miroir : Tour du membre moins Tour de son miroir. -/
noncomputable def pairAntisym (ρ : ℂ) (u : ℝ) : ℂ := pointCurve ρ u - pointCurve (zetaReflect ρ) u

theorem pairAntisym_onLine (ρ : ℂ) (h : ρ.re = 1 / 2) (u : ℝ) : pairAntisym ρ u = 0 := by
  unfold pairAntisym; rw [(zetaReflect_eq_self_iff ρ).2 h, sub_self]

theorem pairAntisym_swap (ρ : ℂ) (u : ℝ) : pairAntisym (zetaReflect ρ) u = -pairAntisym ρ u := by
  unfold pairAntisym; rw [zetaReflect_involutive]; ring

theorem pairAntisym_zero (ρ : ℂ) : pairAntisym ρ 0 = 1 / ρ - 1 / zetaReflect ρ := by
  unfold pairAntisym; rw [pointCurve_eq, pointCurve_eq]; simp

theorem pairAntisym_ne_zero_of_offLine (ρ : ℂ) (h : ρ.re ≠ 1 / 2) : pairAntisym ρ 0 ≠ 0 := by
  rw [pairAntisym_zero, sub_ne_zero]
  intro he
  have : ρ = zetaReflect ρ := by
    simpa [one_div, inv_inj] using he
  exact h ((zetaReflect_eq_self_iff ρ).1 this.symm)

/-! ## 2. Le côté arithmétique n'a qu'un canal symétrique -/

/-- Sur une famille stable par la réflexion, l'expression miroir d'un poids est l'expression originale. -/
theorem mirror_sum_reindex (S : Finset ℂ) (hS : ∀ ρ ∈ S, zetaReflect ρ ∈ S) (H : ℂ → ℂ) :
    ∑ σ ∈ S, H (zetaReflect σ) = ∑ σ ∈ S, H σ :=
  Finset.sum_nbij' zetaReflect zetaReflect hS hS
    (fun ρ _ => zetaReflect_involutive ρ) (fun ρ _ => zetaReflect_involutive ρ) (fun _ _ => rfl)

/-- La différence « originale − miroir » est nulle identiquement, pour tout poids. -/
theorem mirror_antisym_collective_zero (S : Finset ℂ) (hS : ∀ ρ ∈ S, zetaReflect ρ ∈ S) (H : ℂ → ℂ) :
    ∑ σ ∈ S, (H σ - H (zetaReflect σ)) = 0 := by
  rw [Finset.sum_sub_distrib, mirror_sum_reindex S hS H, sub_self]

theorem zetaReflect_onLine (t : ℝ) : zetaReflect ((1 / 2 : ℂ) + t * I) = (1 / 2 : ℂ) + t * I :=
  (zetaReflect_eq_self_iff _).2 (by simp)

/-- Un poids impair par la réflexion s'annule sur la ligne. -/
theorem mirror_odd_weight_zero_on_line (H : ℂ → ℂ) (hodd : ∀ s, H (zetaReflect s) = -H s) (t : ℝ) :
    H ((1 / 2 : ℂ) + t * I) = 0 := by
  have h := hodd ((1 / 2 : ℂ) + t * I)
  rw [zetaReflect_onLine] at h
  linear_combination h / 2

/-- **Aucun poids holomorphe n'est impair par la réflexion**, sauf le poids nul. -/
theorem mirror_odd_entire_weight_zero (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (hodd : ∀ s, H (zetaReflect s) = -H s) : H = 0 := by
  have han : AnalyticOnNhd ℂ H Set.univ := analyticOnNhd_univ_iff_differentiable.2 hH
  have hfreq : ∃ᶠ z in 𝓝[≠] ((1 / 2 : ℂ)), H z = 0 := by
    let f : ℝ → ℂ := fun t => (1 / 2 : ℂ) + t * I
    have hcont : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 ((1 / 2 : ℂ))) := by
      have : Continuous f := by fun_prop
      have h0 : f 0 = 1 / 2 := by simp [f]
      simpa [h0] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    have hne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), f t ∈ ({(1 / 2 : ℂ)}ᶜ : Set ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, f]
      intro h
      have := congrArg Complex.im h
      simp at this
      exact ht this
    have ht : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝[≠] ((1 / 2 : ℂ))) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f hcont hne
    exact ht.frequently (Frequently.of_forall (fun t => mirror_odd_weight_zero_on_line H hodd t))
  funext s
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ _) hfreq
    (Set.mem_univ s)

/-- La différence des expressions originale et boucle (E162) est un poids qui lit les membres en ligne. -/
theorem loop_difference_onLine_ne_zero (σ : ℂ) (hT : σ.im ≠ 0) : (1 : ℂ) / σ - 1 / (1 - σ) ≠ 0 :=
  sub_ne_zero.2 (loop_coefficient_ne σ hT).symm

/-! ## 3. Absence d'observable n'est pas annulation -/

/-- Toute paire hors ligne : famille stable, canal collectif nul pour tout poids, canal de Tour non nul. -/
theorem antisym_channel_not_forced (ρ : ℂ) (h : ρ.re ≠ 1 / 2) :
    (∀ σ ∈ ({ρ, zetaReflect ρ} : Finset ℂ), zetaReflect σ ∈ ({ρ, zetaReflect ρ} : Finset ℂ)) ∧
    (∀ H : ℂ → ℂ, ∑ σ ∈ ({ρ, zetaReflect ρ} : Finset ℂ), (H σ - H (zetaReflect σ)) = 0) ∧
    pairAntisym ρ 0 ≠ 0 := by
  have hS : ∀ σ ∈ ({ρ, zetaReflect ρ} : Finset ℂ), zetaReflect σ ∈ ({ρ, zetaReflect ρ} : Finset ℂ) := by
    intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ ⊢
    rcases hσ with rfl | rfl
    · right; rfl
    · left; exact zetaReflect_involutive _
  exact ⟨hS, fun H => mirror_antisym_collective_zero _ hS H, pairAntisym_ne_zero_of_offLine ρ h⟩

end RHV6Fresh

#print axioms RHV6Fresh.pairAntisym_onLine
#print axioms RHV6Fresh.pairAntisym_swap
#print axioms RHV6Fresh.pairAntisym_zero
#print axioms RHV6Fresh.pairAntisym_ne_zero_of_offLine
#print axioms RHV6Fresh.mirror_sum_reindex
#print axioms RHV6Fresh.mirror_antisym_collective_zero
#print axioms RHV6Fresh.zetaReflect_onLine
#print axioms RHV6Fresh.mirror_odd_weight_zero_on_line
#print axioms RHV6Fresh.mirror_odd_entire_weight_zero
#print axioms RHV6Fresh.loop_difference_onLine_ne_zero
#print axioms RHV6Fresh.antisym_channel_not_forced
