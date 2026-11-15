/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.JointComparison
import RHV6Fresh.Terminal.EngagedNoTranslation
import RHV6Fresh.Terminal.RaccordDetector

/-!
# Transmission locale sur une fenêtre finie de contacts acquis (auteur, 2026-10-11)

Directive de l'auteur : revenir à une fenêtre FINIE définie par les contacts acquis ; utiliser ses événements premiers
exacts et le retrait signé de l'historique ON ; conserver le complément collectif et démontrer sa marge admissible sur
cette fenêtre ; chercher une contradiction locale avec le signal du groupe d'arrivée ; commencer par le premier zéro
certifié, puis établir le lemme de transmission réutilisable à chaque passage ; ne plus imposer une borne globale de
croissance comme unique voie de fermeture.

Canal lissé (seule représentation démontrée). Fenêtre : `x_r = C_{k₀+r}(e)`, `r < m`, contacts acquis de la Tour de
départ (`contactMinusAt`, tous `> 1`), poids `λ_r ∈ ℂ` quelconques.

* §1 fenêtre de contacts acquis (`contactWindow`, `contactWindow_gt_one`) ;
* §2 retrait signé exact : `historyRemoved = Σλ_r (R − P_H)(x_r)`, écrit avec les seuls événements premiers
  (`Σ_{n<x} Λ(n)(1 − n/x)`) et l'historique fini (`historyRemoved_prime_events`) ; majoration LOCALE sous l'historique ON par
  les valeurs du reste aux seuls points de la fenêtre (`historyRemoved_le_local`), aucune borne globale ;
* §3 complément collectif conservé entier : `historyRemoved = groupSignal + Σλ_r Q_{H'}(x_r)` (`window_exact_split`) ;
  marge admissible DÉMONTRÉE `‖Σλ_r Q_{H'}(x_r)‖ ≤ budget(H')·Σ|λ_r| x_r` (`window_complement_margin`) ;
* §4 lemme de transmission réutilisable : une minoration `S` du signal du groupe d'arrivée et une majoration `A` du retrait
  signé, avec `A + marge < S`, donnent une contradiction (`local_transmission_closes`) ; sur tout passage qui monte depuis un
  membre ON, l'obligation de séparation sous l'hypothèse « arrivée basse » donne la conservation radiale
  (`window_transmission`) ;
* §5 portée : avec les valeurs EXACTES, la séparation n'a jamais lieu (`window_separation_not_exact`) ; une fermeture ne peut
  venir que d'une minoration du signal tirée de l'arrivée basse elle-même. Les identités posent la comparaison ; elles ne
  la prouvent pas.

Tout est démontré (axiomes standard). La séparation (minoration du signal de rupture au-delà de la compensation admissible)
n'est PAS démontrée.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Fenêtre de contacts acquis -/

/-- Fenêtre finie des contacts acquis `C_{k₀}, …, C_{k₀+m−1}` de la Tour de `z`. -/
noncomputable def contactWindow (z : TrueZero) (k₀ m : ℕ) : Fin m → ℝ :=
  fun r => contactMinusAt z ((k₀ : ℤ) + ((r : ℕ) : ℤ))

theorem contactWindow_gt_one (z : TrueZero) (k₀ m : ℕ) : ∀ r, 1 < contactWindow z k₀ m r :=
  fun _ => contact_gt_one z (by positivity)

/-! ## 2. Retrait signé de l'historique -/

/-- Retrait signé de l'historique `]−∞, H]` sur la fenêtre : `Σ_r λ_r (R(x_r) − P_H(x_r))`. -/
noncomputable def historyRemoved (H : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) : ℂ :=
  ∑ r, lam r * (smoothedRemainder (x r) - precedingSum H (x r))

/-- Signal du groupe d'arrivée `]H, H']` (membre atteint, son miroir, points de même hauteur, multiplicités). -/
noncomputable def groupSignal (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) : ℂ :=
  ∑ r, lam r * nextFiberSum H H' (x r)

/-- Majoration de la norme du complément collectif au-dessus de `H'` sur la fenêtre : `budget(H')·Σ_r |λ_r| x_r`.
(Nom `windowMargin` conservé ; ce n'est pas une marge admise à la rencontre : la rencontre est exacte, le
complément est une identité, §19.21.) -/
noncomputable def windowMargin (H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) : ℝ :=
  followingBudget H' * ∑ r, ‖lam r‖ * x r

/-- **Événements premiers exacts** : le retrait signé n'utilise que `Σ_{n<x_r} Λ(n)(1 − n/x_r)`, le fond et
l'historique fini. -/
theorem historyRemoved_prime_events (H : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) :
    historyRemoved H x lam =
      ∑ r, lam r * (smoothedVonMangoldtSum (x r) - smoothedZeroBackground (x r) - precedingSum H (x r)) := rfl

/-- **Majoration LOCALE du retrait** sous l'historique ON : seules les valeurs du reste aux points de la fenêtre entrent. -/
theorem historyRemoved_le_local {H : ℝ}
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ H → rZeroRadialPosition w.1 = 1 / 2)
    {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    ‖historyRemoved H x lam‖ ≤
      ∑ r, ‖lam r‖ * (‖smoothedRemainder (x r)‖ + precedingBudget H * x r ^ (1 / 2 : ℝ)) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((norm_sub_le _ _).trans (add_le_add le_rfl (precedingSum_le_budget_of_onLine hOn (hx r)))) (norm_nonneg _)

/-! ## 3. Complément collectif et marge admissible -/

/-- Chaque profil `x^σ` d'un zéro vérifie `‖Σ_r λ_r x_r^σ‖ ≤ Σ_r |λ_r| x_r` sur la fenêtre (`Re σ ≤ 1`). -/
theorem window_profile_le {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) (σ : ExplicitIndex) :
    ‖∑ r, lam r * (x r : ℂ) ^ (σ : ℂ)‖ ≤ ∑ r, ‖lam r‖ * x r := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans one_pos (hx r))]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc x r ^ (σ : ℂ).re ≤ x r ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (hx r).le (explicitIndex_re_le_one σ)
    _ = x r := Real.rpow_one _

/-- **Identité exacte sur la fenêtre, complément entier conservé** : retrait signé = signal du groupe + complément. -/
theorem window_exact_split (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    historyRemoved H x lam = groupSignal H H' x lam + ∑ r, lam r * followingSum H' (x r) := by
  unfold historyRemoved groupSignal
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [expected_next_fiber H H' (hx r)]; ring

/-- **Marge admissible démontrée** du complément collectif sur la fenêtre. -/
theorem window_complement_margin (H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    ‖∑ r, lam r * followingSum H' (x r)‖ ≤ windowMargin H' x lam :=
  tail_joint_functional_bound H' Finset.univ x lam (fun r _ => hx r)
    (fun σ _ => window_profile_le x lam hx σ)

/-- La majoration est `≥ 0`. -/
theorem windowMargin_nonneg (H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    0 ≤ windowMargin H' x lam :=
  mul_nonneg (tsum_nonneg fun _ => norm_nonneg _)
    (Finset.sum_nonneg fun r _ => mul_nonneg (norm_nonneg _) (by linarith [hx r]))

/-- **Majoration de l'écart** (borne de norme, pas une tolérance) : `‖historyRemoved − groupSignal‖ ≤ windowMargin`. -/
theorem window_group_within_margin (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    ‖historyRemoved H x lam - groupSignal H H' x lam‖ ≤ windowMargin H' x lam := by
  rw [window_exact_split H H' x lam hx, add_sub_cancel_left]
  exact window_complement_margin H' x lam hx

/-! ## 4. Lemme de transmission réutilisable -/

/-- **Fermeture locale** : une minoration `S` du signal du groupe d'arrivée et une majoration `A` du retrait signé, séparées
par plus que la marge admissible, sont contradictoires. Aucune borne globale de croissance. -/
theorem local_transmission_closes (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r)
    {S A : ℝ} (hS : S ≤ ‖groupSignal H H' x lam‖) (hA : ‖historyRemoved H x lam‖ ≤ A)
    (hsep : A + windowMargin H' x lam < S) : False := by
  have h := window_group_within_margin H H' x lam hx
  have htri : ‖groupSignal H H' x lam‖ ≤ ‖historyRemoved H x lam‖ +
      ‖historyRemoved H x lam - groupSignal H H' x lam‖ := by
    have := norm_sub_le (historyRemoved H x lam) (historyRemoved H x lam - groupSignal H H' x lam)
    simpa using this
  linarith

/-- **Lemme de transmission, réutilisable à chaque passage** : sur un passage qui monte, si une arrivée basse impose sur une
fenêtre de contacts acquis du départ une séparation entre le signal du groupe d'arrivée et le retrait signé plus la marge
admissible, alors la partie réelle est conservée depuis un départ ON. -/
theorem window_transmission (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hV : VerticalPassage p) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hSep : rZeroRadialPosition p.zLaterMember < 1 / 2 → ∃ (k₀ m : ℕ) (lam : Fin m → ℂ) (S A : ℝ),
      S ≤ ‖groupSignal (rZeroHeight p.zEarlierMember) (rZeroHeight p.zLaterMember)
        (contactWindow ⟨p.zEarlierMember, hE⟩ k₀ m) lam‖ ∧
      ‖historyRemoved (rZeroHeight p.zEarlierMember) (contactWindow ⟨p.zEarlierMember, hE⟩ k₀ m) lam‖ ≤ A ∧
      A + windowMargin (rZeroHeight p.zLaterMember) (contactWindow ⟨p.zEarlierMember, hE⟩ k₀ m) lam < S) :
    rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember := by
  rw [hOn]
  refine le_antisymm (passage_entry_radial_le_half p hV) (le_of_not_gt fun hBelow => ?_)
  obtain ⟨k₀, m, lam, S, A, hS, hA, hsep⟩ := hSep hBelow
  exact local_transmission_closes _ _ _ lam (contactWindow_gt_one _ k₀ m) hS hA hsep

/-! ## 5. Portée -/

/-- **Avec les valeurs exactes, aucune séparation** : `‖groupSignal‖ ≤ ‖historyRemoved‖ + marge` toujours. Une fermeture
locale ne peut donc venir que d'une minoration du signal tirée de l'arrivée basse elle-même (et d'une majoration du retrait
indépendante), jamais des identités seules. -/
theorem window_separation_not_exact (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    ‖groupSignal H H' x lam‖ ≤ ‖historyRemoved H x lam‖ + windowMargin H' x lam := by
  by_contra h
  exact local_transmission_closes H H' x lam hx le_rfl le_rfl (lt_of_not_ge h)

#print axioms contactWindow_gt_one
#print axioms historyRemoved_prime_events
#print axioms historyRemoved_le_local
#print axioms window_profile_le
#print axioms window_exact_split
#print axioms window_complement_margin
#print axioms windowMargin_nonneg
#print axioms window_group_within_margin
#print axioms local_transmission_closes
#print axioms window_transmission
#print axioms window_separation_not_exact

end RHV6Fresh
