/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GapPartialRemainders
import RHV6Fresh.Terminal.RawSpectralChannel

/-!
# RHV6Fresh — Terminal/CollectiveGapRecomposition : recomposition collective d'un écart par les restes
partiels d'une famille finie de Tours, canal brut, reste explicite
(E437, §19.53–19.54, 2026-11-07 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse,
aucun axiome, aucun `sorry`, aucune position radiale, aucune somme infinie)

Ordre de l'auteur (§19.53) : connaissance et maîtrise des écarts et des contacts avant toute chasse
radiale. Question : comment une famille FINIE de Tours recompose-t-elle un écart par les restes partiels
de chacune, que porte le reste explicite, et comment le bilan passe-t-il à l'écart suivant ?

Canal brut sur l'axe réel : demande brute `rawDemand x = ψ(x) − x` (Tchebychev de Mathlib ; aux entiers
c'est `psiRemainder`, E405).

## R4. La demande brute entre deux rencontres et au passage d'un entier
* `rawDemand_on_cell` : sur `[N, N+1[`, `ψ(x) − x = massA N − x` (descente linéaire) ;
* `rawDemand_jump` : de tout point de `[N, N+1[` à l'entier `N+1`, la demande varie de `Λ(N+1) − (N+1−x)`.

## R1–R2. Famille finie : parts, recomposition par les restes partiels, bilan avec reste explicite
* `familyRe s x` : somme des Tours de la famille ; `rawResidual s x = breakResidual s (rawDemand x) x`
  (reste explicite = demande − famille) ; `rawResidual_erase` : retirer un membre ajoute sa valeur au reste.
* `familyGapShare_eq_remainders` (**R1**) : si chaque membre a un contact dans l'écart, la part de la famille
  sur l'écart est la somme, membre par membre, de (reste partiel initial + cellules entières + reste partiel
  final) — la recomposition collective par les restes partiels d'E436.
* `gap_balance` (**R2**) : demande de l'écart = part de la famille + variation du reste explicite sur l'écart.

## R3. Passage à l'écart suivant
* `rawResidual_series`, `rawGapDemand_series`, `series_balance` : sur `J` écarts consécutifs, les variations
  du reste et les demandes télescopent ; le bilan de la série est la somme des parts plus la variation du
  reste entre les deux bouts.

## R5–R7. Ce que porte le reste explicite à la rencontre
* `towerRe_continuousAt`, `familyRe_continuousAt` (**R5**) : toute famille finie de Tours est continue en
  toute abscisse positive.
* `rawResidual_jump_tendsto`, `meeting_jump_carried_by_residual` (**R6**) : pour TOUTE famille finie, la
  variation du reste explicite au passage d'une rencontre tend vers le poids du premier `log p_{n+1}` :
  **le saut de la rencontre est porté entièrement par le reste**, jamais par les contacts de la famille.
* `no_finite_family_recomposes_meeting`, `meeting_not_recomposed_by_finite_family` (**R7**) : le reste
  explicite d'aucune famille finie n'est constant à gauche d'une rencontre : aucune famille finie ne
  recompose la rencontre seule.

Rien ici ne parle de la position radiale ; rien n'exclut un zéro OFF ; aucune somme infinie n'est invoquée.
-/

namespace RHV6Fresh

open Real RHV3Lean Filter Topology ArithmeticFunction

/-! ## R4. La demande brute sur l'axe réel -/

/-- Demande brute à l'abscisse `x` : `ψ(x) − x` (Tchebychev de Mathlib). -/
noncomputable def rawDemand (x : ℝ) : ℝ := Chebyshev.psi x - x

/-- Aux entiers, la demande brute est le reste brut d'E405. -/
theorem rawDemand_nat (N : ℕ) : rawDemand (N : ℝ) = psiRemainder N := by
  unfold rawDemand psiRemainder; rw [massA_eq_psi]

/-- **Entre deux entiers** : sur `[N, N+1[`, la demande brute descend linéairement depuis la masse en `N`. -/
theorem rawDemand_on_cell {N : ℕ} {x : ℝ} (hx : (N : ℝ) ≤ x) (hx' : x < N + 1) :
    rawDemand x = massA N - x := by
  have hfl : ⌊x⌋₊ = N := (Nat.floor_eq_iff ((Nat.cast_nonneg N).trans hx)).mpr ⟨hx, hx'⟩
  unfold rawDemand
  rw [Chebyshev.psi_eq_psi_coe_floor x, hfl, massA_eq_psi]

/-- **Au passage de l'entier `N+1`** : depuis tout point de `[N, N+1[`, la demande varie du poids `Λ(N+1)`
moins la descente restante `N+1−x`. -/
theorem rawDemand_jump {N : ℕ} {x : ℝ} (hx : (N : ℝ) ≤ x) (hx' : x < N + 1) :
    rawDemand ((N + 1 : ℕ) : ℝ) - rawDemand x = Λ (N + 1) - (((N + 1 : ℕ) : ℝ) - x) := by
  rw [rawDemand_nat, rawDemand_on_cell hx hx']
  unfold psiRemainder
  rw [massA_succ]
  push_cast
  ring

/-! ## R1–R2. Famille finie de Tours : parts, reste explicite -/

/-- Somme réelle d'une famille finie de Tours `(β, T)` à l'abscisse `x`. -/
noncomputable def familyRe (s : Finset (ℝ × ℝ)) (x : ℝ) : ℝ := ∑ ρ ∈ s, towerRe ρ.1 ρ.2 x

/-- Reste explicite de la famille à `x` : demande brute moins la famille (instance de `breakResidual`). -/
noncomputable def rawResidual (s : Finset (ℝ × ℝ)) (x : ℝ) : ℝ := breakResidual s (rawDemand x) x

theorem rawResidual_eq (s : Finset (ℝ × ℝ)) (x : ℝ) :
    rawResidual s x = rawDemand x - familyRe s x := rfl

/-- Retirer un membre de la famille ajoute exactement sa valeur au reste explicite. -/
theorem rawResidual_erase {s : Finset (ℝ × ℝ)} {ρ : ℝ × ℝ} (hρ : ρ ∈ s) (x : ℝ) :
    rawResidual (s.erase ρ) x = rawResidual s x + towerRe ρ.1 ρ.2 x :=
  breakResidual_erase hρ _ _

/-- Part (réelle) d'une Tour sur l'écart : sa variation entre les deux premiers. -/
noncomputable def towerGapShare (β T : ℝ) (I : PrimeGapInterval) : ℝ :=
  towerRe β T I.upper - towerRe β T I.lower

/-- Part de la famille sur l'écart. -/
noncomputable def familyGapShare (s : Finset (ℝ × ℝ)) (I : PrimeGapInterval) : ℝ :=
  ∑ ρ ∈ s, towerGapShare ρ.1 ρ.2 I

theorem familyGapShare_eq (s : Finset (ℝ × ℝ)) (I : PrimeGapInterval) :
    familyGapShare s I = familyRe s I.upper - familyRe s I.lower := by
  unfold familyGapShare familyRe towerGapShare; rw [Finset.sum_sub_distrib]

/-- La trajectoire réelle d'une Tour vue comme contribution complexe (pour le découpage d'E436). -/
noncomputable def towerReC (β T : ℝ) : ℝ → ℂ := fun x => ((towerRe β T x : ℝ) : ℂ)

/-- **R1 — Recomposition collective par les restes partiels.** Si chaque membre de la famille a un contact
dans l'écart, la part de la famille sur l'écart est la somme, membre par membre, de son reste partiel
initial, de ses cellules entières et de son reste partiel final (découpage d'E436, chaque Tour sur ses
propres contacts). -/
theorem familyGapShare_eq_remainders (s : Finset (ℝ × ℝ)) (I : PrimeGapInterval)
    (h : ∀ ρ ∈ s, GapHasContact ρ.1 ρ.2 I) :
    ((familyGapShare s I : ℝ) : ℂ) = ∑ ρ ∈ s,
      (initialEdgeRemainder (towerReC ρ.1 ρ.2) ρ.1 ρ.2 I + wholeCellSum (towerReC ρ.1 ρ.2) ρ.1 ρ.2 I +
        finalEdgeRemainder (towerReC ρ.1 ρ.2) ρ.1 ρ.2 I) := by
  unfold familyGapShare towerGapShare
  push_cast
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [← gap_variation_eq_remainders (towerReC ρ.1 ρ.2) (h ρ hρ)]
  rfl

/-- Demande brute de l'écart : variation de `ψ(x) − x` entre les deux premiers. -/
noncomputable def rawGapDemand (I : PrimeGapInterval) : ℝ := rawDemand I.upper - rawDemand I.lower

/-- **R2 — Bilan d'un écart avec reste explicite** : demande de l'écart = part de la famille + variation du
reste explicite sur l'écart (identité, toute famille finie). -/
theorem gap_balance (s : Finset (ℝ × ℝ)) (I : PrimeGapInterval) :
    rawGapDemand I = familyGapShare s I + (rawResidual s I.upper - rawResidual s I.lower) := by
  rw [familyGapShare_eq, rawResidual_eq, rawResidual_eq]; unfold rawGapDemand; ring

/-! ## R3. Passage à l'écart suivant -/

/-- Les variations du reste explicite sur `J` écarts consécutifs télescopent. -/
theorem rawResidual_series (s : Finset (ℝ × ℝ)) (n J : ℕ) :
    ∑ j ∈ Finset.range J,
        (rawResidual s (fnPrimeAtRank (n + j + 1)) - rawResidual s (fnPrimeAtRank (n + j))) =
      rawResidual s (fnPrimeAtRank (n + J)) - rawResidual s (fnPrimeAtRank n) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, show n + (J + 1) = n + J + 1 by ring]; ring

/-- Les demandes de `J` écarts consécutifs télescopent. -/
theorem rawGapDemand_series (n J : ℕ) :
    ∑ j ∈ Finset.range J, rawGapDemand ⟨n + j⟩ =
      rawDemand (fnPrimeAtRank (n + J)) - rawDemand (fnPrimeAtRank n) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    unfold rawGapDemand PrimeGapInterval.upper PrimeGapInterval.lower
    simp only
    rw [show n + (J + 1) = n + J + 1 by ring]
    ring

/-- **R3 — Bilan d'une série d'écarts** : la demande de la série = somme des parts de la famille sur chaque
écart + variation du reste explicite entre les deux bouts de la série. -/
theorem series_balance (s : Finset (ℝ × ℝ)) (n J : ℕ) :
    rawDemand (fnPrimeAtRank (n + J)) - rawDemand (fnPrimeAtRank n) =
      ∑ j ∈ Finset.range J, familyGapShare s ⟨n + j⟩ +
        (rawResidual s (fnPrimeAtRank (n + J)) - rawResidual s (fnPrimeAtRank n)) := by
  rw [← rawGapDemand_series, ← rawResidual_series, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact gap_balance s ⟨n + j⟩

/-! ## R5. Continuité d'une famille finie -/

theorem towerRe_continuousAt (β T : ℝ) {x : ℝ} (hx : 0 < x) : ContinuousAt (towerRe β T) x := by
  show ContinuousAt
    (fun y : ℝ => y ^ β / ‖(⟨β, T⟩ : ℂ)‖ * Real.cos (T * Real.log y - towerPhase β T)) x
  have h1 : ContinuousAt (fun y : ℝ => y ^ β / ‖(⟨β, T⟩ : ℂ)‖) x :=
    (continuousAt_id.rpow_const (Or.inl hx.ne')).div_const _
  have h2 : ContinuousAt (fun y : ℝ => Real.cos (T * Real.log y - towerPhase β T)) x :=
    Real.continuous_cos.continuousAt.comp
      ((continuousAt_const.mul (Real.continuousAt_log hx.ne')).sub continuousAt_const)
  exact h1.mul h2

/-- Toute famille finie de Tours est continue en toute abscisse positive. -/
theorem familyRe_continuousAt (s : Finset (ℝ × ℝ)) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (familyRe s) x := by
  show Tendsto (fun y => ∑ ρ ∈ s, towerRe ρ.1 ρ.2 y) (𝓝 x) (𝓝 (∑ ρ ∈ s, towerRe ρ.1 ρ.2 x))
  exact tendsto_finsetSum s fun ρ _ => towerRe_continuousAt ρ.1 ρ.2 hx

/-! ## R6–R7. Le reste explicite porte le saut de la rencontre -/

/-- **R6 — Le reste porte tout le saut.** Pour toute famille finie, la variation du reste explicite entre
un point à gauche de l'entier `N+1` et cet entier tend vers le poids `Λ(N+1)` quand le point tend vers
l'entier par la gauche. -/
theorem rawResidual_jump_tendsto (s : Finset (ℝ × ℝ)) (N : ℕ) :
    Tendsto (fun x => rawResidual s ((N + 1 : ℕ) : ℝ) - rawResidual s x)
      (𝓝[<] ((N + 1 : ℕ) : ℝ)) (𝓝 (Λ (N + 1))) := by
  have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hfam : ContinuousAt (familyRe s) ((N + 1 : ℕ) : ℝ) := familyRe_continuousAt s hpos
  have hg : Tendsto
      (fun x : ℝ => Λ (N + 1) - (((N + 1 : ℕ) : ℝ) - x) -
        (familyRe s ((N + 1 : ℕ) : ℝ) - familyRe s x))
      (𝓝 ((N + 1 : ℕ) : ℝ)) (𝓝 (Λ (N + 1))) := by
    have h : ContinuousAt
        (fun x : ℝ => Λ (N + 1) - (((N + 1 : ℕ) : ℝ) - x) -
          (familyRe s ((N + 1 : ℕ) : ℝ) - familyRe s x)) ((N + 1 : ℕ) : ℝ) :=
      (continuousAt_const.sub (continuousAt_const.sub continuousAt_id)).sub
        (continuousAt_const.sub hfam)
    have := h.tendsto
    simp only [sub_self, sub_zero] at this
    exact this
  refine (tendsto_nhdsWithin_of_tendsto_nhds hg).congr' ?_
  filter_upwards [Ico_mem_nhdsLT
    (show ((N : ℕ) : ℝ) < ((N + 1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_succ_self N)] with x hx
  have hj := rawDemand_jump hx.1 (by exact_mod_cast hx.2)
  rw [rawResidual_eq, rawResidual_eq]
  linarith

/-- **R7 — Aucune famille finie ne recompose la rencontre seule** : si le poids de `N+1` n'est pas nul, le
reste explicite d'aucune famille finie n'est constant sur `[N, N+1[` jusqu'à `N+1`. -/
theorem no_finite_family_recomposes_meeting (s : Finset (ℝ × ℝ)) (N : ℕ) (hΛ : Λ (N + 1) ≠ 0) :
    ¬ ∀ x ∈ Set.Ico ((N : ℕ) : ℝ) ((N + 1 : ℕ) : ℝ),
        rawResidual s ((N + 1 : ℕ) : ℝ) = rawResidual s x := by
  intro h
  have h0 : Tendsto (fun x => rawResidual s ((N + 1 : ℕ) : ℝ) - rawResidual s x)
      (𝓝[<] ((N + 1 : ℕ) : ℝ)) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ico_mem_nhdsLT
      (show ((N : ℕ) : ℝ) < ((N + 1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_succ_self N)] with x hx
    rw [h x hx, sub_self]
  exact hΛ (tendsto_nhds_unique (rawResidual_jump_tendsto s N) h0)

/-- **Au point de rencontre d'un écart** : pour toute famille finie, la variation du reste explicite au
passage de `p_{n+1}` tend vers `log p_{n+1}` (tout le saut du premier). -/
theorem meeting_jump_carried_by_residual (s : Finset (ℝ × ℝ)) (I : PrimeGapInterval) :
    Tendsto (fun x => rawResidual s (meetingPoint I) - rawResidual s x) (𝓝[<] (meetingPoint I))
      (𝓝 (Real.log (fnPrimeAtRank (I.rank + 1)))) := by
  have hp := thm_primeAtRank_isPrime (I.rank + 1)
  obtain ⟨N, hN⟩ : ∃ N, fnPrimeAtRank (I.rank + 1) = N + 1 :=
    ⟨fnPrimeAtRank (I.rank + 1) - 1, by have := hp.two_le; omega⟩
  have := rawResidual_jump_tendsto s N
  rw [← hN, vonMangoldt_apply_prime hp] at this
  exact this

/-- **Aucune famille finie ne recompose un point de rencontre** : le reste explicite n'est constant à gauche
d'aucun premier `p_{n+1}`. -/
theorem meeting_not_recomposed_by_finite_family (s : Finset (ℝ × ℝ)) (I : PrimeGapInterval) :
    ¬ ∀ x ∈ Set.Ico (meetingPoint I - 1) (meetingPoint I),
        rawResidual s (meetingPoint I) = rawResidual s x := by
  have hp := thm_primeAtRank_isPrime (I.rank + 1)
  obtain ⟨N, hN⟩ : ∃ N, fnPrimeAtRank (I.rank + 1) = N + 1 :=
    ⟨fnPrimeAtRank (I.rank + 1) - 1, by have := hp.two_le; omega⟩
  have hΛ : Λ (N + 1) ≠ 0 := by
    rw [← hN, vonMangoldt_apply_prime hp]
    exact (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hM : meetingPoint I = ((N + 1 : ℕ) : ℝ) := by
    show ((fnPrimeAtRank (I.rank + 1) : ℕ) : ℝ) = _
    rw [hN]
  rw [hM]
  intro h
  refine no_finite_family_recomposes_meeting s N hΛ fun x hx => h x ⟨?_, hx.2⟩
  have := hx.1
  push_cast at this ⊢
  linarith

#print axioms rawDemand_jump
#print axioms familyGapShare_eq_remainders
#print axioms gap_balance
#print axioms series_balance
#print axioms familyRe_continuousAt
#print axioms rawResidual_jump_tendsto
#print axioms meeting_jump_carried_by_residual
#print axioms meeting_not_recomposed_by_finite_family

end RHV6Fresh
