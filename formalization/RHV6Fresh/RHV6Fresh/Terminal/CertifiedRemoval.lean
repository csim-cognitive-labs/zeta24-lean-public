/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.LocalWindowTransmission
import RHV6Fresh.Terminal.MirrorGroupNonCompensation

/-!
# Retrait des trois contributions certifiées et estimation arithmétique du retrait (auteur, 2026-10-11)

Directive de l'auteur : conserver la conclusion de transmission ; retirer uniquement la recherche de séparation entre le
signal et le retrait exact augmenté de sa marge ; retirer ENSEMBLE les trois contributions certifiées (membres de hauteur
`≤ 28`, démontrés ON dans la bibliothèque), avec leurs signes et leurs phases, lorsque l'historique les contient ; composer
les cas fermés jusqu'à vingt-huit ; construire une estimation arithmétique supplémentaire du retrait, depuis les
événements premiers de la fenêtre, en conservant interactions et complément ; démontrer qu'elle est incompatible avec le
signal nécessaire de rupture, sans supposer ni la domination universelle ni la séparation.

Canal lissé (seule représentation démontrée).

* §1 part certifiée `P_28(x)` : somme EXACTE des termes lissés `−m x^ρ/(ρ(ρ+1))` des zéros de hauteur absolue `≤ 28`
  (membres et conjugués, signes et phases conservés, aucun module pris) ; bornée par `budget(28)·√x` dès que ces membres
  sont ON (`certifiedPart_le`) ;
* §2 retrait certifié sur une fenêtre : `Σλ_r (R − P_28 − fibre]28, H])(x_r)`, égal au retrait de l'historique
  (`certifiedRemoved_eq_historyRemoved`), écrit avec les seuls événements premiers (`certifiedRemoved_prime_events`) ;
  identité avec le groupe d'arrivée et le complément entier conservés (`certifiedRemoved_split`), majoration de l'écart
  (`certifiedRemoved_within_margin`, borne de norme, aucune tolérance à la rencontre) ;
* §3 estimation arithmétique du retrait des trois contributions certifiées sur toute fenêtre d'événements premiers :
  `‖Σλ_r (R − P_28)(x_r)‖ ≤ C·Σ|λ_r| x_r^θ` ; INCOMPATIBILITÉ démontrée avec le signal de rupture : sous `β_z < 1/2`, toute
  telle estimation d'exposant `θ < 1 − β_z` est contradictoire (`certified_estimate_incompatible`) : le miroir de la
  rupture (`1 − β_z > 1/2`) est lu par le reste, les trois contributions certifiées n'y portent que `√x`.

Tout est démontré (axiomes standard). L'estimation elle-même n'est PAS démontrée : elle contient les fenêtres à un point,
donc une croissance du reste privé de la part certifiée d'exposant `θ` sur tout `x > 1` (`certified_estimate_pointwise`).
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Part certifiée -/

/-- **Part certifiée** : contributions exactes (termes lissés, signes, phases, multiplicités, conjugués) des zéros de hauteur
absolue `≤ 28` ; sous les comptages démontrés `N(15) = 1`, `N(22) = 2`, `N(28) = 3`, ce sont les trois premiers membres
canoniques et leurs conjugués. -/
noncomputable def certifiedPart (x : ℝ) : ℂ := precedingSum 28 x

/-- La part certifiée est bornée par `budget(28)·√x` dès que les membres de hauteur `≤ 28` sont ON. -/
theorem certifiedPart_le (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ 28 → rZeroRadialPosition w.1 = 1 / 2)
    {x : ℝ} (hx : 1 < x) : ‖certifiedPart x‖ ≤ precedingBudget 28 * x ^ (1 / 2 : ℝ) :=
  precedingSum_le_budget_of_onLine hOn hx

theorem precedingBudget_nonneg (H : ℝ) : 0 ≤ precedingBudget H :=
  tsum_nonneg fun _ => norm_nonneg _

/-! ## 2. Retrait certifié sur une fenêtre -/

/-- Retrait sur la fenêtre des trois contributions certifiées ENSEMBLE puis de la fibre `]28, H]` de l'historique. -/
noncomputable def certifiedRemoved (H : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) : ℂ :=
  ∑ r, lam r * (smoothedRemainder (x r) - certifiedPart (x r) - nextFiberSum 28 H (x r))

/-- Le retrait certifié est le retrait signé de l'historique (identité exacte, aucun module). -/
theorem certifiedRemoved_eq_historyRemoved (H : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) :
    certifiedRemoved H x lam = historyRemoved H x lam := by
  unfold certifiedRemoved historyRemoved certifiedPart nextFiberSum
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- **Événements premiers exacts** : le retrait certifié n'utilise que `Σ_{n<x_r} Λ(n)(1 − n/x_r)`, le fond, la part
certifiée et la fibre intermédiaire de l'historique. -/
theorem certifiedRemoved_prime_events (H : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) :
    certifiedRemoved H x lam = ∑ r, lam r * (smoothedVonMangoldtSum (x r) - smoothedZeroBackground (x r) -
      certifiedPart (x r) - nextFiberSum 28 H (x r)) := rfl

/-- **Interactions et complément conservés** : retrait certifié = signal du groupe d'arrivée + complément entier. -/
theorem certifiedRemoved_split (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    certifiedRemoved H x lam = groupSignal H H' x lam + ∑ r, lam r * followingSum H' (x r) := by
  rw [certifiedRemoved_eq_historyRemoved]; exact window_exact_split H H' x lam hx

/-- Majoration de l'écart du retrait certifié au signal du groupe par la borne du complément (borne de norme ;
aucune tolérance : le complément est une identité, §19.21). -/
theorem certifiedRemoved_within_margin (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    ‖certifiedRemoved H x lam - groupSignal H H' x lam‖ ≤ windowMargin H' x lam := by
  rw [certifiedRemoved_eq_historyRemoved]; exact window_group_within_margin H H' x lam hx

/-- Retrait des trois contributions certifiées seules = fibre intermédiaire + groupe d'arrivée + complément, en tout point. -/
theorem certified_only_split (H H' : ℝ) {x : ℝ} (hx : 1 < x) :
    smoothedRemainder x - certifiedPart x =
      nextFiberSum 28 H x + nextFiberSum H H' x + followingSum H' x := by
  rw [remainder_eq_preceding_add_following H' hx]; unfold certifiedPart nextFiberSum; ring

/-! ## 3. Estimation arithmétique du retrait et incompatibilité avec la rupture -/

/-- L'estimation sur toutes les fenêtres d'événements premiers contient les fenêtres à un point. -/
theorem certified_estimate_pointwise {θ C : ℝ}
    (hEst : ∀ (m : ℕ) (x : Fin m → ℝ) (lam : Fin m → ℂ), (∀ r, 1 < x r) →
      ‖∑ r, lam r * (smoothedRemainder (x r) - certifiedPart (x r))‖ ≤ C * ∑ r, ‖lam r‖ * x r ^ θ)
    {x : ℝ} (hx : 1 < x) : ‖smoothedRemainder x - certifiedPart x‖ ≤ C * x ^ θ := by
  have h := hEst 1 (fun _ => x) (fun _ => 1) (fun _ => hx)
  simpa only [Fin.sum_univ_one, one_mul, norm_one] using h

/-- **Incompatibilité avec le signal nécessaire de rupture** : si un membre `z` est bas (`β_z < 1/2`) et que les membres de
hauteur `≤ 28` sont ON (démontré), aucune estimation du retrait des trois contributions certifiées d'exposant
`θ < 1 − β_z` n'existe : le miroir de `z` (même hauteur, partie réelle `1 − β_z > 1/2`) est lu par le reste, la part
certifiée n'y porte que `√x`. Ni domination universelle ni séparation supposées. -/
theorem certified_estimate_incompatible (z : TrueZero) (hBelow : rZeroRadialPosition z.1 < 1 / 2)
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ 28 → rZeroRadialPosition w.1 = 1 / 2)
    {θ C : ℝ} (hθ : θ < 1 - rZeroRadialPosition z.1)
    (hEst : ∀ (m : ℕ) (x : Fin m → ℝ) (lam : Fin m → ℂ), (∀ r, 1 < x r) →
      ‖∑ r, lam r * (smoothedRemainder (x r) - certifiedPart (x r))‖ ≤ C * ∑ r, ‖lam r‖ * x r ^ θ) :
    False := by
  set θ' := max θ (1 / 2) with hθ'
  have hθ'lt : θ' < 1 - rZeroRadialPosition z.1 := max_lt hθ (by linarith)
  refine mirror_closes_of_remainder_growth z ⟨θ', |C| + precedingBudget 28, hθ'lt, fun x hx => ?_⟩
  have h1 := certified_estimate_pointwise hEst hx
  have h2 := certifiedPart_le hOn hx
  have hxθ : x ^ θ ≤ x ^ θ' := Real.rpow_le_rpow_of_exponent_le hx.le (le_max_left _ _)
  have hxh : x ^ (1 / 2 : ℝ) ≤ x ^ θ' := Real.rpow_le_rpow_of_exponent_le hx.le (le_max_right _ _)
  have hpos : 0 ≤ x ^ θ := Real.rpow_nonneg (by linarith) _
  have hB := precedingBudget_nonneg 28
  have hR : smoothedRemainder x = (smoothedRemainder x - certifiedPart x) + certifiedPart x := by ring
  calc ‖smoothedRemainder x‖ ≤ ‖smoothedRemainder x - certifiedPart x‖ + ‖certifiedPart x‖ := by
        conv_lhs => rw [hR]
        exact norm_add_le _ _
    _ ≤ C * x ^ θ + precedingBudget 28 * x ^ (1 / 2 : ℝ) := add_le_add h1 h2
    _ ≤ |C| * x ^ θ' + precedingBudget 28 * x ^ θ' := by
        exact add_le_add ((mul_le_mul_of_nonneg_right (le_abs_self C) hpos).trans
          (mul_le_mul_of_nonneg_left hxθ (abs_nonneg C))) (mul_le_mul_of_nonneg_left hxh hB)
    _ = (|C| + precedingBudget 28) * x ^ θ' := by ring

#print axioms certifiedPart_le
#print axioms certifiedRemoved_eq_historyRemoved
#print axioms certifiedRemoved_prime_events
#print axioms certifiedRemoved_split
#print axioms certifiedRemoved_within_margin
#print axioms certified_only_split
#print axioms certified_estimate_pointwise
#print axioms certified_estimate_incompatible

end RHV6Fresh
