/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.SameGapsAudit
import RHV6Fresh.Terminal.AuthenticPassageProfile
import RHV6Fresh.Terminal.PairInteraction

/-!
# Le verrou au raccord sortant du zéro authentique (module isolé, non importé par la chaîne, 2026-11-01)

Étape K′ du plan §19.26, exécutée sur la direction corrigée de l'auteur (2026-11-01, dix points) :
point de départ = un zéro authentique `ρ_n = (1/2, T_n)`, sa Tour, ses contacts, sa contribution exacte aux
écarts premiers ; verrou unique = la lecture obligatoire du précédent au premier partagé `M` impose-t-elle la
hiérarchie au raccord sortant ? Aucune étude OFF–miroir, aucune compensation, aucune hypothèse énergétique.

Tout énoncé est une instance, une composition ou une réécriture de théorèmes compilés. **Aucune hypothèse
nouvelle** ; une définition `Prop` nommée (`RadialConservationAtAuthenticDeparture`), jamais prouvée, qui nomme le
premier but non résolu.

## 1. La relation à exploiter (point 5 de l'auteur) — déjà compilée
* `lock_relation_at_sharedPrime` : `A_l(M)/A_e(M) = M^{β_l − β_e}·‖ρ_e‖/‖ρ_l‖` (c'est le champ `transport` du raccord).
* `lock_relation_le_one_iff_oriented` : la relation `≤ 1` est exactement l'orientation du raccord.

## 2. Les mêmes bornes premières (point 3) — le premier partagé est la rencontre de l'écart d'occurrence
* `occurrenceGap`, `occurrenceGap_lower`, `occurrenceGap_meeting`, `sharedPrime_eq_meeting` : l'écart `⟨idx e⟩` a pour
  bornes `Occ(e) = p_idx` et `p_min(e) = p_{idx+1} = M`, le premier partagé de tout raccord sortant de `e`.

## 3. Première obligation (point 6) — contribution exacte de chaque Tour sur l'écart, phases conservées
* `contribution_on_occurrenceGap` : `Δ_{z,idx e} = 𝒯_z(M) − 𝒯_z(Occ e)` pour TOUTE Tour `z`.
* `towerInteraction_same_tower` : `Re(𝒯_z(q)·conj 𝒯_z(p)) = A_z(q)·A_z(p)·cos(T_z·log(q/p))`.
* `contribution_energy_on_occurrenceGap` : `‖Δ‖² = A(M)² + A(Occ)² − 2·A(M)·A(Occ)·cos(T·log(M/Occ))`.
  La comparaison ponctuelle en `M` ne porte que sur `A(M)` ; la contribution dépend aussi de `A(Occ)` et de la phase
  `T·log(M/Occ)`, qui est une lecture de fréquence.

## 4. Deuxième obligation (point 7) — la succession authentique impose l'orientation au raccord sortant
* `authentic_departure_hierarchy` : zéro authentique atteint verticalement ⟹ le passage sortant monte, la hiérarchie
  tient au raccord sortant et la relation d'amplitudes est `≤ 1`, **quelle que soit la position radiale de
  l'arrivée** (composition de `engaged_regime_kept`, `raccordHierarchy_of_height_advance`,
  `oriented_iff_transport_le_one`).
* `first_departure_hierarchy` : même chose au premier zéro (fait de l'auteur : premier zéro ON ; `bottom_exit_vertical`).

## 5. Ce que la relation ne lit pas (point 9 : « la relation d'amplitudes seule ne suffit pas encore »)
* `lock_relation_reads_frequency_only` : dès `T_e ≥ 2`, la relation `≤ 1` ⟺ `T_e < T_l`. Elle ne contraint pas `β_l`.
* `off_arrival_keeps_hierarchy_breaks_next` : une arrivée OFF (`β_l < 1/2`) sur un passage vertical laisse la hiérarchie
  tenir au raccord sortant du zéro authentique ; c'est au raccord SUIVANT que le pas gèle et que la hiérarchie casse.

## 6. Le premier but non résolu (point 8)
* `arrival_onLine_iff_next_hierarchy` : depuis un zéro authentique atteint verticalement, l'arrivée est en ligne SI ET
  SEULEMENT SI la hiérarchie tient au raccord qui la quitte. Le verrou de l'auteur, lu sur les acquis, est donc la
  hiérarchie au raccord *suivant*, équivalente à `β_{n+1} = 1/2` : c'est le problème terminal lui-même, déplacé d'un
  raccord, jamais résolu ici.
* `RadialConservationAtAuthenticDeparture` (Prop nommée, jamais prouvée) : `β` conservée sur tout passage vertical qui
  quitte un membre ON. `canonical_onLine_of_lock`, `riemannHypothesis_of_lock` : sous ce but et le premier zéro ON,
  tous les membres canoniques sont en ligne et RH suit (compositions de théorèmes existants).

Aucun énoncé ne conclut sur `β`. Aucun `sorry`, aucun `admit`, aucun axiome. Non ajouté à `RHV6Fresh.lean`.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. La relation d'amplitudes au premier partagé -/

/-- **Point 5 de l'auteur, compilé** : `A_l(M)/A_e(M) = M^{β_l − β_e}·‖ρ_e‖/‖ρ_l‖` au premier partagé de tout raccord. -/
theorem lock_relation_at_sharedPrime {e l : TrueZero} (R : TowerRaccord e l) :
    ‖zeroTerm l R.M‖ / ‖zeroTerm e R.M‖ =
      (R.M : ℝ) ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * (‖zeroPoint e‖ / ‖zeroPoint l‖) := by
  have h := R.transport
  unfold energyRatio at h
  exact h

/-- La relation `≤ 1` est exactement l'orientation du raccord (`‖𝒯_l(M)‖ ≤ ‖𝒯_e(M)‖`). -/
theorem lock_relation_le_one_iff_oriented {e l : TrueZero} (R : TowerRaccord e l) :
    (R.M : ℝ) ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * (‖zeroPoint e‖ / ‖zeroPoint l‖) ≤ 1 ↔
      R.Oriented :=
  R.oriented_iff_transport_le_one.symm

/-! ## 2. Le premier partagé est la rencontre de l'écart d'occurrence -/

/-- L'écart d'occurrence du zéro `e` : `⟨idx e⟩ = [p_idx, p_{idx+1}]`. -/
noncomputable def occurrenceGap (e : TrueZero) : PrimeGapInterval := ⟨nZeroSourceIndex e.1⟩

/-- Sa borne inférieure est l'occurrence du zéro. -/
theorem occurrenceGap_lower (e : TrueZero) : (occurrenceGap e).lower = (occurrence e : ℝ) := by
  rw [occurrence_eq_canonicalAnchor]; rfl

/-- Sa rencontre est le premier attendu `p_min(e)`. -/
theorem occurrenceGap_meeting (e : TrueZero) :
    meetingPoint (occurrenceGap e) = (expectedMinimumPrime e : ℝ) := rfl

/-- **Point 3** : le premier partagé de tout raccord sortant de `e` est la rencontre de l'écart d'occurrence de `e`. -/
theorem sharedPrime_eq_meeting {e l : TrueZero} (R : TowerRaccord e l) :
    (R.M : ℝ) = meetingPoint (occurrenceGap e) := by
  rw [occurrenceGap_meeting, R.exit_eq]

/-! ## 3. Contribution exacte de chaque Tour sur l'écart d'occurrence, phases conservées -/

/-- **Point 6, identité** : `Δ_{z, idx e} = 𝒯_z(p_min e) − 𝒯_z(Occ e)` pour toute Tour `z` (instance de F3 bis). -/
theorem contribution_on_occurrenceGap (z e : TrueZero) :
    primeGapContribution (zeroPoint z) (nZeroSourceIndex e.1) =
      zeroTerm z (expectedMinimumPrime e) - zeroTerm z (occurrence e) := by
  rw [occurrence_eq_canonicalAnchor]
  exact primeGapContribution_eq_zeroTerm_sub z _

/-- **Interaction de deux lectures de la même Tour** : `Re(𝒯_z(q)·conj 𝒯_z(p)) = A_z(q)·A_z(p)·cos(T_z·(log q − log p))`.
La phase est conservée : c'est une lecture de fréquence. -/
theorem towerInteraction_same_tower (z : TrueZero) {q p : ℝ} (hq : 0 < q) (hp : 0 < p) :
    towerInteraction (zeroTerm z q) (zeroTerm z p) =
      ‖zeroTerm z q‖ * ‖zeroTerm z p‖ * Real.cos (rZeroHeight z.1 * (Real.log q - Real.log p)) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hρ := zeroPoint_ne_zero z
  have hρc : (starRingEnd ℂ) (zeroPoint z) ≠ 0 := (map_ne_zero _).mpr hρ
  have key : zeroTerm z q * (starRingEnd ℂ) (zeroTerm z p) =
      Complex.exp (zeroPoint z * (Real.log q : ℂ) + (starRingEnd ℂ) (zeroPoint z) * (Real.log p : ℂ)) /
        (Complex.normSq (zeroPoint z) : ℂ) := by
    unfold zeroTerm
    rw [Complex.cpow_def_of_ne_zero hq', Complex.cpow_def_of_ne_zero hp', ← Complex.ofReal_log hq.le,
      ← Complex.ofReal_log hp.le, map_div₀, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.exp_add,
      ← Complex.mul_conj]
    field_simp
  unfold towerInteraction
  rw [key, Complex.div_ofReal_re, Complex.exp_re]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, zeroPoint_re, zeroPoint_im, mul_zero, sub_zero, zero_add, add_zero]
  rw [zeroTerm_norm hq, zeroTerm_norm hp, Real.rpow_def_of_pos hq, Real.rpow_def_of_pos hp,
    Complex.normSq_eq_norm_sq, Real.exp_add, mul_sub]
  have hN := zeroPoint_norm_pos z
  field_simp
  ring

/-- **Point 6, énergie exacte de la contribution** : `‖Δ‖² = A(M)² + A(Occ)² − 2·A(M)·A(Occ)·cos(T·(log M − log Occ))`.
La comparaison ponctuelle en `M` ne porte que sur le premier terme. -/
theorem contribution_energy_on_occurrenceGap (z e : TrueZero) :
    ‖primeGapContribution (zeroPoint z) (nZeroSourceIndex e.1)‖ ^ 2 =
      ‖zeroTerm z (expectedMinimumPrime e)‖ ^ 2 + ‖zeroTerm z (occurrence e)‖ ^ 2 -
        2 * (‖zeroTerm z (expectedMinimumPrime e)‖ * ‖zeroTerm z (occurrence e)‖ *
          Real.cos (rZeroHeight z.1 * (Real.log (expectedMinimumPrime e) - Real.log (occurrence e)))) := by
  have hM : (0 : ℝ) < expectedMinimumPrime e := by exact_mod_cast (expectedMinimumPrime_prime e).pos
  have hO : (0 : ℝ) < occurrence e := by
    rw [occurrence_eq_canonicalAnchor]; exact_mod_cast (thm_memberCanonicalAnchor_isPrime e).pos
  rw [← towerInteraction_same_tower z hM hO, contribution_on_occurrenceGap, Complex.sq_norm, Complex.sq_norm,
    Complex.sq_norm, Complex.normSq_sub]
  rfl

/-! ## 4. La succession authentique impose l'orientation au raccord sortant -/

/-- **Point 7, compilé** : un zéro authentique (`β_e = 1/2`) atteint par un passage vertical est quitté par un passage
qui monte ; la hiérarchie tient à son raccord sortant et la relation d'amplitudes y est `≤ 1`, **quelle que soit la
position radiale de l'arrivée**. -/
theorem authentic_departure_hierarchy {o p : TZeroPassage} (hJ : o.zLaterMember = p.zEarlierMember)
    (ho : VerticalPassage o) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hT2 : 2 ≤ rZeroHeight p.zLaterMember) :
    VerticalPassage p ∧ RaccordHierarchy p hE hL ∧
      ((towerRaccordOf p hE hL).M : ℝ) ^ (rZeroRadialPosition p.zLaterMember - rZeroRadialPosition p.zEarlierMember) *
        (‖zeroPoint ⟨p.zEarlierMember, hE⟩‖ / ‖zeroPoint ⟨p.zLaterMember, hL⟩‖) ≤ 1 := by
  obtain ⟨hV, hH⟩ := raccordHierarchy_of_engaged_departure hJ ho hOn hE hL hT2
  exact ⟨hV, hH, (lock_relation_le_one_iff_oriented _).mpr hH.1⟩

/-- **Au premier zéro** (fait de l'auteur : premier zéro ON, posé comme hypothèse nommée `hAnchor` comme dans
`canonical_onLine_of_conservation`) : le passage canonique `0` monte et la hiérarchie tient à son raccord. -/
theorem first_departure_hierarchy (hAnchor : rZeroRadialPosition (canonicalMember 0).1 = 1 / 2)
    (hT2 : 2 ≤ rZeroHeight (canonicalMember 1).1) :
    VerticalPassage (canonicalPassage 0) ∧
      RaccordHierarchy (canonicalPassage 0) (canonicalMember 0).2 (canonicalMember 1).2 := by
  have hV : VerticalPassage (canonicalPassage 0) :=
    bottom_exit_vertical _ (canonicalMember 0).2 canonicalMember_zero_bottom hAnchor
  exact ⟨hV, raccordHierarchy_of_height_advance _ _ _ hV hT2⟩

/-! ## 5. Ce que la relation d'amplitudes ne lit pas -/

/-- **Point 9** : dès `T_e ≥ 2`, la relation d'amplitudes `≤ 1` au raccord sortant équivaut à `T_e < T_l` seule
(`towerRaccord_oriented_iff_height_lt`). Elle ne contraint pas la position radiale de l'arrivée. -/
theorem lock_relation_reads_frequency_only (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hT2 : 2 ≤ rZeroHeight p.zEarlierMember) :
    ((towerRaccordOf p hE hL).M : ℝ) ^
        (rZeroRadialPosition p.zLaterMember - rZeroRadialPosition p.zEarlierMember) *
        (‖zeroPoint ⟨p.zEarlierMember, hE⟩‖ / ‖zeroPoint ⟨p.zLaterMember, hL⟩‖) ≤ 1 ↔
      rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember :=
  (lock_relation_le_one_iff_oriented (towerRaccordOf p hE hL)).trans
    (towerRaccord_oriented_iff_height_lt p hE hL hT2)

/-- **Une arrivée OFF ne casse pas le raccord sortant du zéro authentique** : sur un passage vertical dont l'arrivée
est sous un demi, la hiérarchie tient au raccord sortant ; c'est le passage SUIVANT qui gèle (même hauteur) et dont le
raccord viole la hiérarchie. -/
theorem off_arrival_keeps_hierarchy_breaks_next {p q : TZeroPassage}
    (hJ : p.zLaterMember = q.zEarlierMember)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hV : VerticalPassage p) (hT2 : 2 ≤ rZeroHeight p.zLaterMember)
    (hOff : rZeroRadialPosition p.zLaterMember < 1 / 2)
    (hqE : 0 < rZeroHeight q.zEarlierMember) (hqL : 0 < rZeroHeight q.zLaterMember) :
    RaccordHierarchy p hE hL ∧ HorizontalPassage q ∧ ¬ RaccordHierarchy q hqE hqL := by
  have hH : HorizontalPassage q := (low_arrival_freezes_cascade hJ hV hOff hqE hqL).1
  exact ⟨raccordHierarchy_of_height_advance p hE hL hV hT2, hH,
    (sameHeight_breaks_hierarchy q hqE hqL hH).2.2⟩

/-! ## 6. Le premier but non résolu -/

/-- **Point 8 — équivalence exacte au pas suivant** : depuis un zéro authentique atteint verticalement, l'arrivée est
en ligne si et seulement si la hiérarchie tient au raccord qui la quitte. Le verrou lu sur les acquis est donc la
hiérarchie au raccord *suivant*, c'est-à-dire `β_{n+1} = 1/2` : le problème terminal déplacé d'un raccord. -/
theorem arrival_onLine_iff_next_hierarchy {o p q : TZeroPassage} (hJ : o.zLaterMember = p.zEarlierMember)
    (ho : VerticalPassage o) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hJ' : p.zLaterMember = q.zEarlierMember)
    (hqE : 0 < rZeroHeight q.zEarlierMember) (hqL : 0 < rZeroHeight q.zLaterMember)
    (hT2 : 2 ≤ rZeroHeight q.zLaterMember) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ↔ RaccordHierarchy q hqE hqL := by
  constructor
  · intro hOn'
    have hp : VerticalPassage p := (engaged_regime_kept hJ ho (by rw [hJ]; exact hOn)).1
    exact (raccordHierarchy_of_engaged_departure hJ' hp (by rw [← hJ']; exact hOn') hqE hqL hT2).2
  · intro hq
    exact (engaged_step_of_next_hierarchy hJ ho hOn hE hL hJ' hq).1

/-- **PREMIER BUT NON RÉSOLU (Prop nommée, jamais prouvée)** : la position radiale est conservée sur tout passage
vertical qui quitte un membre en ligne. C'est exactement l'hypothèse `hLaw` de `canonical_onLine_of_conservation`. -/
def RadialConservationAtAuthenticDeparture : Prop :=
  ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
    rZeroRadialPosition p.zEarlierMember = 1 / 2 →
    rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember

/-- Sous ce but et le premier zéro ON, tous les membres canoniques sont en ligne et tous les passages montent. -/
theorem canonical_onLine_of_lock (hAnchor : rZeroRadialPosition (canonicalMember 0).1 = 1 / 2)
    (h : RadialConservationAtAuthenticDeparture) :
    ∀ n : ℕ, rZeroRadialPosition (canonicalMember n).1 = 1 / 2 ∧ VerticalPassage (canonicalPassage n) :=
  canonical_onLine_of_conservation hAnchor h

/-- Sous ce but et le premier zéro ON, l'hypothèse de Riemann. -/
theorem riemannHypothesis_of_lock (hAnchor : rZeroRadialPosition (canonicalMember 0).1 = 1 / 2)
    (h : RadialConservationAtAuthenticDeparture) : RiemannHypothesis :=
  riemannHypothesis_of_all_canonical_onLine fun n _ => (canonical_onLine_of_lock hAnchor h (n - 1)).1

#print axioms lock_relation_at_sharedPrime
#print axioms sharedPrime_eq_meeting
#print axioms contribution_on_occurrenceGap
#print axioms towerInteraction_same_tower
#print axioms contribution_energy_on_occurrenceGap
#print axioms authentic_departure_hierarchy
#print axioms first_departure_hierarchy
#print axioms lock_relation_reads_frequency_only
#print axioms off_arrival_keeps_hierarchy_breaks_next
#print axioms arrival_onLine_iff_next_hierarchy
#print axioms canonical_onLine_of_lock
#print axioms riemannHypothesis_of_lock

end RHV6Fresh
