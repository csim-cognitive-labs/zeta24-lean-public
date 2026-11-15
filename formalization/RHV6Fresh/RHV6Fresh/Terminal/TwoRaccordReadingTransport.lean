/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.AuthenticRaccordLock
import RHV6Fresh.Terminal.OffCarrier
import RHV6Fresh.Terminal.FrequencyCap
import RHV6Fresh.Terminal.ThreeZeroWindow
import RHV6Fresh.Terminal.OccurrenceHeightComposition

/-!
# Composition de deux raccords consécutifs : transport de la lecture du précédent (module isolé, 2026-11-01)

Décision de l'auteur (2026-11-01, après 7eda05dd) : composer deux raccords consécutifs sur trois membres
`z_n, z_{n+1}, z_{n+2}`, leurs deux écarts d'occurrence et leurs contributions complexes exactes, phases conservées,
et tenter d'obtenir une **obligation de lecture transmise** au second raccord qui interdise le gel
(`low_arrival_freezes_cascade`). Critère de succès fixé par l'auteur : une contradiction avec le gel obtenue d'une
contrainte *indépendante* sur le second raccord. Si la composition ne produit que des identités ou reformule
`arrival_onLine_iff_next_hierarchy`, elle ne ferme rien et doit être déclarée insuffisante.
`RadialConservationAtAuthenticDeparture` n'est **pas** introduite comme hypothèse.

**Correction de l'auteur en cours d'exécution (2026-11-01)** : réintégrer simultanément CAP inférieur + CAP supérieur +
contacts + deux raccords successifs + contributions exactes (`FrequencyCap`, `ThreeZeroWindow`,
`OccurrenceHeightComposition` importés explicitement). Critère révisé : une incompatibilité démontrée entre les deux
lectures successives et une hauteur commune, **sans supposer que deux rangs exigent déjà deux hauteurs**. Objectif :
déterminer si les contraintes des deux rencontres consécutives imposent deux progressions de fréquence distinctes, là où
la paire n'en possède qu'une (différence entre compter deux places et exiger deux fréquences). Voir §5.

## 1. Transport exact d'une lecture de Tour à travers un écart (phase conservée)
* `zeroTerm_transport` : `𝒯_z(y) = (y/x)^{ρ_z}·𝒯_z(x)` (identité complexe).
* `transport_factor_polar` : `(u)^{ρ_z} = u^{β_z}·e^{i·T_z·log u}` — module radial, phase de fréquence.
* `relative_reading_transport` : `R_{e,l}(y) = R_{e,l}(x)·(y/x)^{β_l−β_e}` — la lecture relative du suivant sur le
  précédent se transporte d'un bout à l'autre d'un écart par un facteur purement radial.

## 2. Trois membres, deux raccords `R₁ : e→l`, `R₂ : l→m`, deux écarts d'occurrence
* `second_gap_bounds` : le second écart `⟨idx l⟩` a pour bornes `R₁.M = Occ(l)` et `R₂.M = p_min(l)` ; `sharedPrime_lt`.
* `contribution_second_gap` : `Δ_{z,idx l} = 𝒯_z(R₂.M) − 𝒯_z(R₁.M)` pour toute Tour `z`.
* `two_gap_telescoping` : `Δ_{z,idx e} + Δ_{z,idx l} = 𝒯_z(R₂.M) − 𝒯_z(Occ e)`.
* `frozen_reading_ratio` : à fréquence égale (`T_l = T_m`), `𝒯_m(q) = q^{β_m−β_l}·(ρ_l/ρ_m)·𝒯_l(q)` : la phase relative
  des deux Tours gelées est constante (`arg(ρ_l/ρ_m)`), seul le module dépend de `q`.
* `composite_transport` : `R_{e,m}(R₂.M) = R_{l,m}(R₂.M)·R_{e,l}(R₁.M)·(R₂.M/R₁.M)^{β_l−β_e}` — le transport composé
  sur deux raccords est le produit des deux transports et du facteur radial transmis le long du second écart.

## 3. Instanciation sur le porteur (`OffCarrier` : `e` ON, `l` OFF, `m` sortant gelé), dès `T ≥ 2`
* `off_two_raccord_profile` : `R_{e,l}(R₁.M) ≤ 1` (hiérarchie d'arrivée), facteur transmis `< 1`, et
  `1 < R_{l,m}(R₂.M)` (renversement au raccord sortant). Trois faits compilés, simultanément vrais sur le porteur.
* `previous_dominates_at_second_prime` : le précédent ON domine encore strictement le zéro OFF en `R₂.M`.
* `composite_ratio_eq` : `R_{e,m}(R₂.M) = (R₂.M)^{β_m − 1/2}·‖ρ_e‖/‖ρ_m‖` — seul objet radialement sensible reliant
  `z_n` et `z_{n+2}` ; **aucun théorème du corpus ne fixe son signe par rapport à 1**.

## 4. Verdict compilé : toute contrainte au second raccord exprimable sur les acquis EST le verrou
* `outgoing_oriented_iff_continuationForced`, `outgoing_transport_le_one_iff_continuationForced`,
  `outgoing_hierarchy_iff_continuationForced` : orientation, transport `≤ 1`, hiérarchie au second raccord sont
  chacun équivalents à `ContinuationForced` (⟺ RH). `outgoing_not_oriented` : sur le porteur, aucun ne tient.

## 5. Les CAP réintégrés : deux lectures successives à hauteur commune
* `pair_second_gap_same_phase` : sur le second écart, le zéro OFF et le membre sortant lisent le même nombre de cellules
  (même phase `T·log(R₂.M/R₁.M)`, instance de `pair_reads_gaps_identically`).
* `pair_second_gap_frozen_contribution` : la contribution exacte du membre sortant sur le second écart est celle du zéro
  OFF, point par point, multipliée par le facteur radial `q^{β_m−β_l}` et la phase constante `ρ_l/ρ_m`.
* `pair_lower_cap_common_height` : le CAP inférieur au rang `n+1` (le plus strict des deux) s'applique à la hauteur
  commune ; `pair_counts_two_places` : la paire occupe deux places (`pair_two_places`, `caps_count_off_pairs_twice`).
* `pair_contacts_same_pitch` : les contacts des deux membres ont le même pas `π/T` (`pair_contacts_equal`).
* `next_frequency_bracketed_by_common_height` : le membre porté par `p_{n+2}` est strictement au-dessus de la paire et au
  plus à son double (instance de `three_events_bracketed`, cas miroir, hauteur `≥ T₁`).
* **Verdict** `common_height_excluded_iff_riemannHypothesis` : « sur tout porteur, les rangs `n` et `n+1` ont des
  hauteurs distinctes » ⟺ RH. Les CAP, les contacts et les contributions exactes sont tous des instances satisfaites par
  la paire à hauteur commune (théorèmes ci-dessus) ; aucun d'eux ne transforme le second événement premier en obligation
  d'une fréquence **nouvelle**. Cette obligation est exactement `ContinuationForced` (⟺ RH).

**Lecture honnête (critère de l'auteur appliqué)** : la composition produit des identités (§1–2), un profil de signes
(§3) et des équivalences (§4). Aucune contrainte indépendante sur le second raccord n'a été obtenue : les identités
valent pour toute Tour, donc ne peuvent contredire le gel ; les seules quantités radialement sensibles sont les
transports, et la seule inégalité qui interdirait le gel est le verrou lui-même. **Insuffisant.**
Aucun `sorry`, aucun `admit`, aucun axiome, aucune hypothèse nouvelle. Non ajouté à `RHV6Fresh.lean`.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Transport exact d'une lecture de Tour à travers un écart -/

/-- `𝒯_z(y) = (y/x)^{ρ_z}·𝒯_z(x)` : la lecture d'une Tour en `y` est sa lecture en `x` transportée par `(y/x)^{ρ_z}`. -/
theorem zeroTerm_transport (z : TrueZero) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    zeroTerm z y = ((y / x : ℝ) : ℂ) ^ zeroPoint z * zeroTerm z x := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hxy : (y : ℂ) = ((y / x : ℝ) : ℂ) * (x : ℂ) := by
    rw [Complex.ofReal_div]; field_simp
  unfold zeroTerm
  rw [hxy, Complex.mul_cpow_ofReal_nonneg (div_pos hy hx).le hx.le, mul_div_assoc]

/-- **Décomposition polaire du facteur de transport** : `u^{ρ_z} = u^{β_z}·exp(i·T_z·log u)`. Le module est radial,
la phase est une lecture de fréquence. -/
theorem transport_factor_polar (z : TrueZero) {u : ℝ} (hu : 0 < u) :
    ((u : ℝ) : ℂ) ^ zeroPoint z =
      ((u ^ rZeroRadialPosition z.1 : ℝ) : ℂ) *
        Complex.exp (((rZeroHeight z.1 * Real.log u : ℝ) : ℂ) * Complex.I) := by
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  rw [Complex.cpow_def_of_ne_zero hu', ← Complex.ofReal_log hu.le]
  have hsplit : (Real.log u : ℂ) * zeroPoint z =
      ((rZeroRadialPosition z.1 * Real.log u : ℝ) : ℂ) +
        ((rZeroHeight z.1 * Real.log u : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im, zeroPoint_re, zeroPoint_im, mul_comm]
    · simp [Complex.mul_re, Complex.mul_im, zeroPoint_re, zeroPoint_im, mul_comm]
  rw [hsplit, Complex.exp_add, Real.rpow_def_of_pos hu, Complex.ofReal_exp, mul_comm (Real.log u)]

/-- **Transport de la lecture relative** : `R_{e,l}(y) = R_{e,l}(x)·(y/x)^{β_l−β_e}`. Le rapport des amplitudes du
suivant sur le précédent se transporte le long d'un écart par un facteur purement radial. -/
theorem relative_reading_transport (e l : TrueZero) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    energyRatio e l y =
      energyRatio e l x * (y / x) ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) := by
  rw [energyRatio_eq e l hy, energyRatio_eq e l hx, Real.div_rpow hy.le hx.le]
  have hpx : 0 < x ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) := Real.rpow_pos_of_pos hx _
  field_simp

/-! ## 2. Trois membres, deux raccords, deux écarts d'occurrence -/

/-- `0 < ‖𝒯_z(q)‖` pour `q > 0`. -/
theorem zeroTerm_norm_pos' (z : TrueZero) {q : ℝ} (hq : 0 < q) : 0 < ‖zeroTerm z q‖ := by
  rw [zeroTerm_norm hq]
  exact div_pos (Real.rpow_pos_of_pos hq _) (zeroPoint_norm_pos z)

section ThreeMembers

variable {e l m : TrueZero}

/-- Le second écart d'occurrence `⟨idx l⟩` a pour bornes les deux premiers partagés `R₁.M = Occ(l)` et
`R₂.M = p_min(l)` : sa rencontre est le premier partagé du second raccord. -/
theorem second_gap_bounds (R₁ : TowerRaccord e l) (R₂ : TowerRaccord l m) :
    ((R₁.M : ℝ) = (occurrenceGap l).lower) ∧ ((R₂.M : ℝ) = meetingPoint (occurrenceGap l)) :=
  ⟨by rw [occurrenceGap_lower, R₁.entry_eq], sharedPrime_eq_meeting R₂⟩

/-- Les deux premiers partagés sont ordonnés. -/
theorem sharedPrime_lt (R₁ : TowerRaccord e l) (R₂ : TowerRaccord l m) : (R₁.M : ℝ) < R₂.M := by
  rw [(second_gap_bounds R₁ R₂).1, (second_gap_bounds R₁ R₂).2]
  exact meetingPoint_gt_lower _

theorem sharedPrime_pos₁ (R₁ : TowerRaccord e l) : (0 : ℝ) < R₁.M := by
  rw [R₁.exit_eq]; exact_mod_cast expectedMinimumPrime_pos e

theorem sharedPrime_pos₂ (R₂ : TowerRaccord l m) : (0 : ℝ) < R₂.M := by
  rw [R₂.exit_eq]; exact_mod_cast expectedMinimumPrime_pos l

/-- **Contribution exacte de toute Tour sur le second écart** : `Δ_{z,idx l} = 𝒯_z(R₂.M) − 𝒯_z(R₁.M)`. -/
theorem contribution_second_gap (R₁ : TowerRaccord e l) (R₂ : TowerRaccord l m) (z : TrueZero) :
    primeGapContribution (zeroPoint z) (nZeroSourceIndex l.1) = zeroTerm z R₂.M - zeroTerm z R₁.M := by
  rw [contribution_on_occurrenceGap, R₂.exit_eq, R₁.entry_eq]

/-- **Télescopage sur les deux écarts** : `Δ_{z,idx e} + Δ_{z,idx l} = 𝒯_z(R₂.M) − 𝒯_z(Occ e)`. -/
theorem two_gap_telescoping (R₁ : TowerRaccord e l) (R₂ : TowerRaccord l m) (z : TrueZero) :
    primeGapContribution (zeroPoint z) (nZeroSourceIndex e.1) +
        primeGapContribution (zeroPoint z) (nZeroSourceIndex l.1) =
      zeroTerm z R₂.M - zeroTerm z (occurrence e) := by
  rw [contribution_on_occurrenceGap z e, contribution_second_gap R₁ R₂ z, R₁.exit_eq]
  ring

/-- **Lecture gelée** : à fréquence égale (`T_l = T_m`), `𝒯_m(q) = q^{β_m−β_l}·(ρ_l/ρ_m)·𝒯_l(q)`. La phase relative des
deux Tours gelées est constante (celle de `ρ_l/ρ_m`) ; seul le module `q^{β_m−β_l}` dépend du point. -/
theorem frozen_reading_ratio {l m : TrueZero} (hT : rZeroHeight l.1 = rZeroHeight m.1) {q : ℝ} (hq : 0 < q) :
    zeroTerm m q =
      ((q ^ (rZeroRadialPosition m.1 - rZeroRadialPosition l.1) : ℝ) : ℂ) * (zeroPoint l / zeroPoint m) *
        zeroTerm l q := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hρ : zeroPoint m = zeroPoint l + ((rZeroRadialPosition m.1 - rZeroRadialPosition l.1 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [zeroPoint_re]
    · simp [zeroPoint_im, hT]
  have hpow : (q : ℂ) ^ zeroPoint m =
      (q : ℂ) ^ zeroPoint l * (q : ℂ) ^ ((rZeroRadialPosition m.1 - rZeroRadialPosition l.1 : ℝ) : ℂ) := by
    rw [← Complex.cpow_add _ _ hq', ← hρ]
  have hl := zeroPoint_ne_zero l
  have hm := zeroPoint_ne_zero m
  unfold zeroTerm
  rw [hpow, Complex.ofReal_cpow hq.le]
  field_simp

/-- **Transport composé sur deux raccords** : `R_{e,m}(R₂.M) = R_{l,m}(R₂.M)·R_{e,l}(R₁.M)·(R₂.M/R₁.M)^{β_l−β_e}`.
Le rapport du troisième membre sur le premier au second premier partagé est le produit des deux transports de raccord
et du facteur radial transmis le long du second écart. -/
theorem composite_transport (R₁ : TowerRaccord e l) (R₂ : TowerRaccord l m) :
    energyRatio e m R₂.M =
      energyRatio l m R₂.M *
        (energyRatio e l R₁.M * ((R₂.M : ℝ) / R₁.M) ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1)) := by
  rw [← relative_reading_transport e l (sharedPrime_pos₁ R₁) (sharedPrime_pos₂ R₂)]
  unfold energyRatio
  have hl : 0 < ‖zeroTerm l R₂.M‖ := zeroTerm_norm_pos' l (sharedPrime_pos₂ R₂)
  have he : 0 < ‖zeroTerm e R₂.M‖ := zeroTerm_norm_pos' e (sharedPrime_pos₂ R₂)
  field_simp

end ThreeMembers

/-! ## 3. Instanciation sur le porteur : `e` ON, `l` OFF, `m` sortant gelé -/

namespace OffCarrier

variable (C : OffCarrier)

/-- Le facteur radial transmis le long du second écart. -/
noncomputable def transmittedFactor : ℝ :=
  ((C.outgoingRaccord.M : ℝ) / C.arrivalRaccord.M) ^
    (rZeroRadialPosition C.zero.1 - rZeroRadialPosition C.arrival.zEarlierMember)

theorem arrivalRaccord_M_lt_outgoingRaccord_M : (C.arrivalRaccord.M : ℝ) < C.outgoingRaccord.M := by
  rw [C.arrivalRaccord_M, C.outgoingRaccord_M]
  exact_mod_cast thm_primeAtRank_strictMono (Nat.lt_succ_self C.n)

/-- Le facteur transmis est strictement inférieur à un : le zéro OFF perd encore, relativement au précédent ON, le long
de son propre écart d'occurrence. -/
theorem transmittedFactor_lt_one : C.transmittedFactor < 1 := by
  unfold transmittedFactor
  have hM : (0 : ℝ) < C.arrivalRaccord.M := by
    rw [C.arrivalRaccord_M]; exact_mod_cast (thm_primeAtRank_isPrime C.n).pos
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · rw [one_lt_div hM]; exact C.arrivalRaccord_M_lt_outgoingRaccord_M
  · rw [C.arrival_earlier_onLine]; linarith [C.zero_low]

/-- **Profil à deux raccords d'une arrivée OFF** (dès `T ≥ 2`) : transport d'arrivée `≤ 1`, facteur transmis `< 1`,
transport sortant `> 1`. Trois faits compilés, simultanément vrais sur le porteur : la composition ne les oppose pas. -/
theorem off_two_raccord_profile (hT2 : 2 ≤ rZeroHeight C.zero.1) :
    energyRatio ⟨C.arrival.zEarlierMember, C.arrival_earlier_pos⟩ ⟨C.arrival.zLaterMember, C.arrival_later_pos⟩
        C.arrivalRaccord.M ≤ 1 ∧
      C.transmittedFactor < 1 ∧
      1 < energyRatio ⟨C.outgoing.zEarlierMember, C.outgoing_earlier_pos⟩
        ⟨C.outgoing.zLaterMember, C.outgoing_later_pos⟩ C.outgoingRaccord.M := by
  refine ⟨?_, C.transmittedFactor_lt_one, ?_⟩
  · have hO := (C.arrival_hierarchy hT2).1
    have := C.arrivalRaccord.oriented_iff_transport_le_one.mp hO
    rwa [← C.arrivalRaccord.transport] at this
  · have hrev := towerRaccord_reverses_of_sameHeight C.outgoingRaccord C.outgoing_horizontal hT2
      (horizontalPassage_radial_lt C.outgoing_horizontal)
    unfold energyRatio
    have hpos : 0 < ‖zeroTerm (⟨C.outgoing.zEarlierMember, C.outgoing_earlier_pos⟩ : TrueZero)
        C.outgoingRaccord.M‖ := zeroTerm_norm_pos' _ (sharedPrime_pos₂ C.outgoingRaccord)
    rw [one_lt_div hpos]
    exact hrev

/-- **Le précédent ON domine encore strictement le zéro OFF au second premier partagé** (dès `T ≥ 2`). -/
theorem previous_dominates_at_second_prime (hT2 : 2 ≤ rZeroHeight C.zero.1) :
    ‖zeroTerm ⟨C.arrival.zLaterMember, C.arrival_later_pos⟩ C.outgoingRaccord.M‖ <
      ‖zeroTerm ⟨C.arrival.zEarlierMember, C.arrival_earlier_pos⟩ C.outgoingRaccord.M‖ := by
  have hM1 : (0 : ℝ) < C.arrivalRaccord.M := sharedPrime_pos₁ C.arrivalRaccord
  have hM2 : (0 : ℝ) < C.outgoingRaccord.M := sharedPrime_pos₂ C.outgoingRaccord
  have h := relative_reading_transport ⟨C.arrival.zEarlierMember, C.arrival_earlier_pos⟩
    ⟨C.arrival.zLaterMember, C.arrival_later_pos⟩ hM1 hM2
  have hle := (C.off_two_raccord_profile hT2).1
  have hfac : ((C.outgoingRaccord.M : ℝ) / C.arrivalRaccord.M) ^
      (rZeroRadialPosition C.arrival.zLaterMember - rZeroRadialPosition C.arrival.zEarlierMember) < 1 := by
    have := C.transmittedFactor_lt_one
    unfold transmittedFactor at this
    rwa [← C.arrival_later] at this
  have hfacpos : 0 < ((C.outgoingRaccord.M : ℝ) / C.arrivalRaccord.M) ^
      (rZeroRadialPosition C.arrival.zLaterMember - rZeroRadialPosition C.arrival.zEarlierMember) :=
    Real.rpow_pos_of_pos (div_pos hM2 hM1) _
  have hpos : 0 < ‖zeroTerm (⟨C.arrival.zEarlierMember, C.arrival_earlier_pos⟩ : TrueZero)
      C.outgoingRaccord.M‖ := zeroTerm_norm_pos' _ hM2
  have hlt : energyRatio ⟨C.arrival.zEarlierMember, C.arrival_earlier_pos⟩
      ⟨C.arrival.zLaterMember, C.arrival_later_pos⟩ C.outgoingRaccord.M < 1 := by
    rw [h]
    calc _ ≤ 1 * ((C.outgoingRaccord.M : ℝ) / C.arrivalRaccord.M) ^
          (rZeroRadialPosition C.arrival.zLaterMember - rZeroRadialPosition C.arrival.zEarlierMember) :=
          mul_le_mul_of_nonneg_right hle hfacpos.le
      _ < 1 := by rw [one_mul]; exact hfac
  unfold energyRatio at hlt
  rwa [div_lt_one hpos] at hlt

/-- **Rapport composé `z_n → z_{n+2}` au second premier partagé** : `R_{e,m}(R₂.M) = (R₂.M)^{β_m − 1/2}·‖ρ_e‖/‖ρ_m‖`.
C'est le seul objet radialement sensible qui relie le précédent ON au membre sortant ; aucun théorème du corpus ne
fixe son signe par rapport à `1`. -/
theorem composite_ratio_eq :
    energyRatio ⟨C.arrival.zEarlierMember, C.arrival_earlier_pos⟩ C.outgoingMember C.outgoingRaccord.M =
      (C.outgoingRaccord.M : ℝ) ^ (rZeroRadialPosition C.outgoing.zLaterMember - 1 / 2) *
        (‖zeroPoint ⟨C.arrival.zEarlierMember, C.arrival_earlier_pos⟩‖ / ‖zeroPoint C.outgoingMember‖) := by
  refine (energyRatio_eq _ _ (sharedPrime_pos₂ C.outgoingRaccord)).trans ?_
  show (C.outgoingRaccord.M : ℝ) ^
      (rZeroRadialPosition C.outgoing.zLaterMember - rZeroRadialPosition C.arrival.zEarlierMember) * _ = _
  rw [C.arrival_earlier_onLine]

/-! ## 4. Verdict compilé : toute contrainte au second raccord exprimable sur les acquis est le verrou -/

/-- L'orientation du raccord sortant est exactement la continuation forcée (dès `T ≥ 2`). -/
theorem outgoing_oriented_iff_continuationForced (hT2 : 2 ≤ rZeroHeight C.zero.1) :
    C.outgoingRaccord.Oriented ↔ C.ContinuationForced :=
  towerRaccord_oriented_iff_height_lt C.outgoing C.outgoing_earlier_pos C.outgoing_later_pos hT2

/-- Le transport sortant `≤ 1` est exactement la continuation forcée (dès `T ≥ 2`). -/
theorem outgoing_transport_le_one_iff_continuationForced (hT2 : 2 ≤ rZeroHeight C.zero.1) :
    (C.outgoingRaccord.M : ℝ) ^ (rZeroRadialPosition C.outgoing.zLaterMember - rZeroRadialPosition C.zero.1) *
        (‖zeroPoint C.zero‖ / ‖zeroPoint C.outgoingMember‖) ≤ 1 ↔
      C.ContinuationForced :=
  (lock_relation_le_one_iff_oriented C.outgoingRaccord).trans (C.outgoing_oriented_iff_continuationForced hT2)

/-- La hiérarchie au raccord sortant est exactement la continuation forcée (dès `T ≥ 2`) — déjà
`continuationForced_iff_hierarchy`, rappelée ici pour le verdict. -/
theorem outgoing_hierarchy_iff_continuationForced (hT2 : 2 ≤ rZeroHeight C.zero.1) :
    RaccordHierarchy C.outgoing C.outgoing_earlier_pos C.outgoing_later_pos ↔ C.ContinuationForced :=
  (C.continuationForced_iff_hierarchy hT2).symm

/-- Sur le porteur, le raccord sortant n'est pas orienté (dès `T ≥ 2`) : la composition ne produit aucune contrainte
indépendante qui l'oriente ; l'orienter serait la continuation forcée elle-même. -/
theorem outgoing_not_oriented (hT2 : 2 ≤ rZeroHeight C.zero.1) : ¬ C.outgoingRaccord.Oriented :=
  fun h => C.continuation_contradiction ((C.outgoing_oriented_iff_continuationForced hT2).mp h)

/-! ## 5. Les CAP réintégrés : deux lectures successives à hauteur commune -/

/-- **Même phase sur le second écart** : le zéro OFF et le membre sortant lisent le second écart `[R₁.M, R₂.M]` par le
même nombre de cellules. -/
theorem pair_second_gap_same_phase :
    towerPosition C.outgoingMember C.outgoingRaccord.M - towerPosition C.outgoingMember C.arrivalRaccord.M =
      towerPosition C.zero C.outgoingRaccord.M - towerPosition C.zero C.arrivalRaccord.M :=
  C.pair_reads_gaps_identically _ _

/-- **Contribution gelée du membre sortant sur le second écart** `[p_n, p_{n+1}]` : point par point celle du zéro OFF,
multipliée par le facteur radial `q^{β_m−β_l}` et la phase constante `ρ_l/ρ_m`. -/
theorem pair_second_gap_frozen_contribution :
    primeGapContribution (zeroPoint C.outgoingMember) C.n =
      ((fnPrimeAtRank (C.n + 1) : ℝ) ^ (rZeroRadialPosition C.outgoingMember.1 - rZeroRadialPosition C.zero.1) : ℝ) *
          (zeroPoint C.zero / zeroPoint C.outgoingMember) * zeroTerm C.zero (fnPrimeAtRank (C.n + 1)) -
        ((fnPrimeAtRank C.n : ℝ) ^ (rZeroRadialPosition C.outgoingMember.1 - rZeroRadialPosition C.zero.1) : ℝ) *
          (zeroPoint C.zero / zeroPoint C.outgoingMember) * zeroTerm C.zero (fnPrimeAtRank C.n) := by
  have hT : rZeroHeight C.zero.1 = rZeroHeight C.outgoingMember.1 := C.outgoingMember_height.symm
  have hp1 : (0 : ℝ) < fnPrimeAtRank (C.n + 1) := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  have hp0 : (0 : ℝ) < fnPrimeAtRank C.n := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  have h := contribution_on_occurrenceGap C.outgoingMember C.zero
  rw [C.zero_index, C.zero_expectedMinimumPrime, C.zero_occurrence] at h
  rw [h, frozen_reading_ratio hT hp1, frozen_reading_ratio hT hp0]

/-- **CAP inférieur à hauteur commune** : le plancher du rang `n+1` (le plus strict des deux) s'applique à la hauteur
commune de la paire. -/
theorem pair_lower_cap_common_height : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ n' : ℕ,
    (n' : ℝ) * (A₀ * Real.log (n' + 3)) < ((C.n + 1 : ℕ) : ℝ) + 1 → (n' : ℝ) < rZeroHeight C.zero.1 := by
  obtain ⟨A₀, hA1, hA⟩ := lower_cap
  refine ⟨A₀, hA1, fun n' hn => ?_⟩
  have := hA (C.n + 1) n' hn
  rwa [C.mirror_height] at this

/-- **La paire occupe deux places du comptage** : sous sa hauteur, le comptage vaut `ON + 2·bas`, et la fenêtre unité
sous `T` contient au moins deux points. -/
theorem pair_counts_two_places :
    Zeta23.Ncount 0 (rZeroHeight C.zero.1) = onCount (rZeroHeight C.zero.1) + 2 * lowCount (rZeroHeight C.zero.1) ∧
    2 ≤ Zeta23.Ncount (rZeroHeight C.zero.1 - 1) (rZeroHeight C.zero.1) :=
  ⟨caps_count_off_pairs_twice _, C.pair_two_places⟩

/-- **Même pas de contacts** `π/T` pour les deux membres de la paire (cas miroir). -/
theorem pair_contacts_same_pitch (k : ℤ) :
    Real.log (contactMinusAt (mirrorMember C.zero) (k + 1) / contactMinusAt (mirrorMember C.zero) k) =
    Real.log (contactMinusAt C.zero (k + 1) / contactMinusAt C.zero k) :=
  C.pair_contacts_equal k

/-- **Le membre porté par `p_{n+2}` est encadré par la hauteur commune** (cas miroir, hauteur `≥ T₁`) :
strictement au-dessus, au plus au double. -/
theorem next_frequency_bracketed_by_common_height : ∃ T₁ : ℝ, ∀ C : OffCarrier,
    C.outgoing.zLaterMember = (mirrorMember C.zero).1 → T₁ ≤ rZeroHeight C.zero.1 →
    rZeroHeight C.zero.1 < rZeroHeight C.nextMember.1 ∧ rZeroHeight C.nextMember.1 ≤ 2 * rZeroHeight C.zero.1 :=
  three_events_bracketed

end OffCarrier

/-- **Verdict (critère révisé de l'auteur)** : « sur tout porteur, les rangs consécutifs `n` et `n+1` ont des hauteurs
distinctes » est exactement RH. L'incompatibilité cherchée entre les deux lectures successives et une hauteur commune
n'est donc pas un lemme intermédiaire : c'est la conclusion elle-même. -/
theorem common_height_excluded_iff_riemannHypothesis :
    (∀ C : OffCarrier, rZeroHeight (canonicalMember C.n).1 ≠ rZeroHeight (canonicalMember (C.n + 1)).1) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    by_contra hNot
    obtain ⟨C⟩ := exists_offCarrier_of_not_riemannHypothesis hNot
    exact h C C.mirror_height.symm
  · exact fun hRH C => (no_offCarrier_of_riemannHypothesis hRH C).elim


#print axioms zeroTerm_transport
#print axioms transport_factor_polar
#print axioms relative_reading_transport
#print axioms second_gap_bounds
#print axioms contribution_second_gap
#print axioms two_gap_telescoping
#print axioms frozen_reading_ratio
#print axioms composite_transport
#print axioms OffCarrier.off_two_raccord_profile
#print axioms OffCarrier.previous_dominates_at_second_prime
#print axioms OffCarrier.composite_ratio_eq
#print axioms OffCarrier.outgoing_transport_le_one_iff_continuationForced
#print axioms OffCarrier.outgoing_not_oriented
#print axioms OffCarrier.pair_second_gap_same_phase
#print axioms OffCarrier.pair_second_gap_frozen_contribution
#print axioms OffCarrier.pair_lower_cap_common_height
#print axioms OffCarrier.pair_counts_two_places
#print axioms OffCarrier.next_frequency_bracketed_by_common_height
#print axioms common_height_excluded_iff_riemannHypothesis

end RHV6Fresh
