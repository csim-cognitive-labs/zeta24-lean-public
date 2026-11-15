/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ArgumentPrinciple
import RHV6Fresh.Terminal.EulerMaclaurinFine
import RHV6Fresh.Terminal.EulerMaclaurinTenCertificate
import RHV6Fresh.Terminal.BoxAnchor
import RHV6Fresh.Terminal.CountingDeficit
import RHV6Fresh.Terminal.AuthenticPassageProfile
import RHV6Fresh.Terminal.FirstGainPremise
import RHV6Fresh.Terminal.NoRegimeChange
import RHV6Fresh.Terminal.ZetaBox.Final
import RHV6Fresh.Terminal.BoxCountHeight
import RHV6Fresh.Terminal.RiemannHypothesisDefinition
import RHV6Fresh.Terminal.LocalWindowTransmission
import RHV6Fresh.Terminal.StageCell
import RHV6Fresh.Terminal.EngagedAllConstraints
import RHV6Fresh.Terminal.AmplitudeStableSynchronization
import RHV6Fresh.Terminal.ConstantAmplitudeNeed
import RHV6Fresh.Terminal.CoupleLock
import RHV6Fresh.Terminal.OccupiedFrequency
import RHV6Fresh.Terminal.GeneratedFrequency
import RHV6Fresh.Terminal.GapTranslationInvariance
import RHV6Fresh.Terminal.CollectiveCurvature
import RHV6Fresh.Terminal.GrammarOperator
import RHV6Fresh.Terminal.GrammarTailBound
import RHV6Fresh.Terminal.AstraSeparation
import RHV6Fresh.Terminal.OffAmplificationAudit
import RHV6Fresh.Terminal.FirstExceedanceRaccord
import RHV6Fresh.Terminal.GrammarTransportLaw
import RHV6Fresh.Terminal.ZeroCascadeReading
import RHV6Fresh.Terminal.ConstraintCorrelation
import RHV6Fresh.Terminal.LowNextZeroSignatures
import RHV6Fresh.Terminal.CertifiedRemoval
import RHV6Fresh.Terminal.FirstArrivalsAnchor
import RHV6Fresh.Terminal.WindingReadingChain
import RHV6Fresh.Terminal.InterlacingLink
import RHV6Fresh.Terminal.CascadeContinuation
import RHV6Fresh.Terminal.FrequencyCascadeStability
import RHV6Fresh.Terminal.HorizontalExclusion
import RHV6Fresh.Terminal.ZeroFreeRegionBand
import RHV6Fresh.Terminal.FirstArrivalsAnchor

/-!
# Trois premiers zéros certifiés (bandes 22 et 28) — cible optionnelle `RHV6FreshCertificates`

Déplacé de `Terminal/DemonstrationChain.lean` le 2026-10-27 (direction Fable) : les certificats `ZetaBox22` et `ZetaBox28`
(100 fichiers, 125 000 lignes, plusieurs heures de CPU et jusqu'à 6,5 Go de mémoire par fichier) ne servent qu'à ces
contrôles, qui ne sont consommés par aucun théorème de la chaîne (`goal_dependencies.py` : 0). Ils sont compilés par
`lake build RHV6FreshCertificates`, jamais par `lake build RHV6Fresh`. Énoncés et preuves inchangés ; seule la référence
`three_arrivals_certified` est remplacée par son équivalent `three_arrivals_certified` (`FirstArrivalsAnchor`), de même
contenu, et `ZB.Cert.zeta_box_certificate` par `ZB.Cert.zeta_box_certificate`.
-/

namespace RHV6Fresh

open RHV3Lean
open scoped InnerProductSpace ArithmeticFunction

/-! ## Contrôle : les deux premières bandes (comptage en pas, module fermé `CountingDeficit` §6) -/

/-- **Comptage de la seconde bande dans la bibliothèque** : `N(22) = 2`, par les rectangles `[1/4, 2] × [−1, 22]` et
`[3/4, 2] × [−1, 22]` (certificat généré `ZB.Cert.H22.zeta_box_certificate`, `experiments/e196_zeta_box_height_generator.py`,
même méthode que la première bande) et les rectangles de la première bande (`upperCount_of_zeta_boxes`). Fermé. -/
theorem upperCountWithMultiplicity_twentytwo : upperCountWithMultiplicity 22 = 2 := by
  obtain ⟨hZ₁₀, hZ₂₀, hW₁₀, hW₂₀⟩ := ZB.Cert.zeta_box_certificate
  obtain ⟨hZ₁, hZ₂, hW₁, hW₂⟩ := ZB.Cert.H22.zeta_box_certificate
  exact upperCount_of_zeta_boxes (σ₀ := 1 / 4) (t₁ := 1) (T₀ := 15) (T := 22) (K := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hZ₁₀ hZ₂₀ hW₁₀ hW₂₀ hZ₁ hZ₂
    (by rw [hW₁]; norm_num) hW₂

#print axioms upperCountWithMultiplicity_twentytwo

/-- **Comptage de la troisième bande dans la bibliothèque** : `N(28) = 3`, par les rectangles `[1/4, 2] × [−1, 28]` et
`[3/4, 2] × [−1, 28]` (certificat généré `ZB.Cert.H28.zeta_box_certificate`, même générateur, troncatures `N ≤ 120`) et
les rectangles de la première bande. Fermé. -/
theorem upperCountWithMultiplicity_twentyeight : upperCountWithMultiplicity 28 = 3 := by
  obtain ⟨hZ₁₀, hZ₂₀, hW₁₀, hW₂₀⟩ := ZB.Cert.zeta_box_certificate
  obtain ⟨hZ₁, hZ₂, hW₁, hW₂⟩ := ZB.Cert.H28.zeta_box_certificate
  exact upperCount_of_zeta_boxes (σ₀ := 1 / 4) (t₁ := 1) (T₀ := 15) (T := 28) (K := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hZ₁₀ hZ₂₀ hW₁₀ hW₂₀ hZ₁ hZ₂
    (by rw [hW₁]; norm_num) hW₂

#print axioms upperCountWithMultiplicity_twentyeight

/-- **Contrôle, deux premiers zéros** : par le comptage de la seconde bande `N(22) = 2` (`upperCountWithMultiplicity_twentytwo`,
fermé), les deux premiers membres canoniques sont ON et annulent leur
miroir, le second est strictement au-dessus de quinze et au plus à vingt-deux, et tout membre de hauteur `≤ 22` est ON
(`lowCount_eq_zero_of_count_step` : une rupture coûte deux unités de comptage). Fermé (consolidation du 2026-10-11) ;
il n'entre pas dans la chaîne vers RH (la récurrence n'utilise que l'ancre). -/
theorem first_two_zeros_control :
    (rZeroRadialPosition (canonicalZero 1).1 = 1 / 2 ∧ mirrorMember (canonicalZero 1) = canonicalZero 1) ∧
    (rZeroRadialPosition (canonicalZero 2).1 = 1 / 2 ∧ mirrorMember (canonicalZero 2) = canonicalZero 2) ∧
    15 < rZeroHeight (canonicalZero 2).1 ∧ rZeroHeight (canonicalZero 2).1 ≤ 22 ∧
    (∀ w : TrueZero, rZeroHeight w.1 ≤ 22 → rZeroRadialPosition w.1 = 1 / 2) :=
  let h15 := arrivals_count_fifteen
  let h22 := upperCountWithMultiplicity_twentytwo
  ⟨(first_two_canonical_onLine h15 h22).1, (first_two_canonical_onLine h15 h22).2,
   canonicalZero_two_height_gt h15, canonicalZero_two_height_le h15 h22,
   fun w hw => (all_onLine_le_twentytwo h15 h22 w hw).1⟩


/-- **Contrôle, trois premiers zéros, coupures démontrées** : `N(0) = 0`, `N(15) = 1`, `N(22) = 2`, `N(28) = 3`, tous
démontrés dans la bibliothèque (rectangles de `ζ`, `upperCount_of_zeta_boxes`), placent les trois premiers membres
canoniques dans `]0, 15]`, `]15, 22]`, `]22, 28]`, ON, miroir annulé, et tout membre de hauteur `≤ 28` ON
(`first_three_canonical_onLine`). Fermé (consolidation du 2026-10-11 ; la coupure 23 d'E176 est remplacée par 22, qui
sépare aussi le deuxième et le troisième zéro) ; hors de la récurrence vers RH. -/
theorem first_three_zeros_control :
    (0 < rZeroHeight (canonicalMember 0).1 ∧ rZeroHeight (canonicalMember 0).1 ≤ 15) ∧
    (15 < rZeroHeight (canonicalMember 1).1 ∧ rZeroHeight (canonicalMember 1).1 ≤ 22) ∧
    (22 < rZeroHeight (canonicalMember 2).1 ∧ rZeroHeight (canonicalMember 2).1 ≤ 28) ∧
    (∀ j < 3, rZeroRadialPosition (canonicalMember j).1 = 1 / 2 ∧
      mirrorMember (canonicalMember j) = canonicalMember j) ∧
    (∀ w : TrueZero, rZeroHeight w.1 ≤ 28 → rZeroRadialPosition w.1 = 1 / 2) :=
  first_three_canonical_onLine (by norm_num) (by norm_num) (by norm_num)
    arrivals_count_zero arrivals_count_fifteen upperCountWithMultiplicity_twentytwo
    upperCountWithMultiplicity_twentyeight

#print axioms first_three_zeros_control

/-- **Pas canonique entre deux membres ON** : composition de `engaged_step_all_constraints`, `engaged_event_restriction` et
`whole_winding_iff_onLine` sur le passage canonique `m`. Fermé (aucune hypothèse au-delà de ses arguments). -/
theorem canonical_onLine_step (m : ℕ) (hOnE : rZeroRadialPosition (canonicalMember m).1 = 1 / 2)
    (hOnL : rZeroRadialPosition (canonicalMember (m + 1)).1 = 1 / 2)
    (hV : VerticalPassage (canonicalPassage m)) (h2 : 2 ≤ rZeroHeight (canonicalMember (m + 1)).1) :
    towerPitch (canonicalMember (m + 1)) < towerPitch (canonicalMember m) ∧
    nZeroSourceIndex (canonicalMember (m + 1)).1 = nZeroSourceIndex (canonicalMember m).1 + 1 ∧
    expectedMinimumPrime (canonicalMember m) = occurrence (canonicalMember (m + 1)) ∧
    radialFactor (canonicalMember (m + 1)) = 1 ∧
    WindingNestedAtInfinity (canonicalMember m) (canonicalMember (m + 1)) ∧
    (∀ x : ℝ, 0 < x → ‖zeroTerm (canonicalMember (m + 1)) x‖ ≤ ‖zeroTerm (canonicalMember m) x‖) := by
  have hE : 0 < rZeroHeight (canonicalPassage m).zEarlierMember := (canonicalMember m).2
  have hL : 0 < rZeroHeight (canonicalPassage m).zLaterMember := (canonicalMember (m + 1)).2
  obtain ⟨-, -, -, hPitch, -, -, hNest, -, hSymIff⟩ :=
    engaged_step_all_constraints (canonicalPassage m) hE hL hV hOnE h2
  obtain ⟨hIdx, hPrime, -⟩ := engaged_event_restriction (canonicalPassage m) hE hL hV hOnL.le
  have hSymL : TowerSymmetric (canonicalMember (m + 1)) := (towerSymmetric_iff_onLine _).mpr hOnL
  exact ⟨hPitch, hIdx, hPrime, hSymIff.mp hSymL, hNest,
    (whole_winding_iff_onLine (canonicalPassage m) hE hL hOnE).mpr hOnL⟩

/-- **Les trois premiers membres, tout ensemble** : miroir annulé et Tour normalisée symétrique ; rayon normalisé constant
`r(T_j)` (frontières des anneaux), strictement décroissant d'un membre au suivant ; domination stricte des enveloppes
parmi les membres ON ; deux passages canoniques qui montent ; pas contracté, rang + 1 et premier partagé (grammaire) ;
grilles non translatées (`λ = 1`) et emboîtement des contacts à l'infini ; Tour entière de chaque suivant sous la
précédente. Fermé : comptages `N(15) = 1`, `N(22) = 2`, `N(28) = 3` démontrés (consolidation du 2026-10-11). -/
theorem first_three_members_geometry :
    (∀ j < 3, TowerSymmetric (canonicalMember j) ∧ mirrorMember (canonicalMember j) = canonicalMember j) ∧
    (∀ j < 3, ∀ x : ℝ, 0 < x →
      normalizedRadius (canonicalMember j) x = onRadius (rZeroHeight (canonicalMember j).1)) ∧
    onRadius (rZeroHeight (canonicalMember 1).1) < onRadius (rZeroHeight (canonicalMember 0).1) ∧
    onRadius (rZeroHeight (canonicalMember 2).1) < onRadius (rZeroHeight (canonicalMember 1).1) ∧
    (∀ x : ℝ, 0 < x → pairAmplitude (canonicalMember 1) x < pairAmplitude (canonicalMember 0) x ∧
      pairAmplitude (canonicalMember 2) x < pairAmplitude (canonicalMember 1) x) ∧
    VerticalPassage (canonicalPassage 0) ∧ VerticalPassage (canonicalPassage 1) ∧
    (towerPitch (canonicalMember 1) < towerPitch (canonicalMember 0) ∧
      nZeroSourceIndex (canonicalMember 1).1 = nZeroSourceIndex (canonicalMember 0).1 + 1 ∧
      expectedMinimumPrime (canonicalMember 0) = occurrence (canonicalMember 1) ∧
      radialFactor (canonicalMember 1) = 1 ∧
      WindingNestedAtInfinity (canonicalMember 0) (canonicalMember 1) ∧
      (∀ x : ℝ, 0 < x → ‖zeroTerm (canonicalMember 1) x‖ ≤ ‖zeroTerm (canonicalMember 0) x‖)) ∧
    (towerPitch (canonicalMember 2) < towerPitch (canonicalMember 1) ∧
      nZeroSourceIndex (canonicalMember 2).1 = nZeroSourceIndex (canonicalMember 1).1 + 1 ∧
      expectedMinimumPrime (canonicalMember 1) = occurrence (canonicalMember 2) ∧
      radialFactor (canonicalMember 2) = 1 ∧
      WindingNestedAtInfinity (canonicalMember 1) (canonicalMember 2) ∧
      (∀ x : ℝ, 0 < x → ‖zeroTerm (canonicalMember 2) x‖ ≤ ‖zeroTerm (canonicalMember 1) x‖)) := by
  obtain ⟨⟨b0, b0'⟩, ⟨b1, b1'⟩, ⟨b2, b2'⟩, hON, -⟩ := three_arrivals_certified
  have o0 := (hON 0 (by norm_num)).1
  have o1 := (hON 1 (by norm_num)).1
  have o2 := (hON 2 (by norm_num)).1
  have h01 : rZeroHeight (canonicalMember 0).1 < rZeroHeight (canonicalMember 1).1 := by linarith
  have h12 : rZeroHeight (canonicalMember 1).1 < rZeroHeight (canonicalMember 2).1 := by linarith
  have hV0 : VerticalPassage (canonicalPassage 0) :=
    canonical_vertical_of_history (m := 0) fun k hk => (hON k (by omega)).1
  have hV1 : VerticalPassage (canonicalPassage 1) :=
    canonical_vertical_of_history (m := 1) fun k hk => (hON k (by omega)).1
  refine ⟨fun j hj => ⟨(towerSymmetric_iff_onLine _).mpr (hON j hj).1, (hON j hj).2⟩,
    fun j hj x hx => normalizedRadius_onLine _ (hON j hj).1 hx,
    onRadius_strictAnti b0.le h01, onRadius_strictAnti (by linarith) h12,
    fun x hx => ⟨pairAmplitude_onLine_lt_of_height o0 o1 h01 hx, pairAmplitude_onLine_lt_of_height o1 o2 h12 hx⟩,
    hV0, hV1, canonical_onLine_step 0 o0 o1 hV0 (by linarith),
    canonical_onLine_step 1 o1 o2 hV1 (by linarith)⟩

#print axioms first_three_members_geometry
#print axioms first_two_zeros_control

/-! ## Contrôle : un zéro bas après les trois zéros ON certifiés (auteur, 2026-10-16 ; module fermé `LowNextZeroSignatures`) -/

/-- **Ce qu'un zéro bas imposerait après la bande certifiée** : par `N(28) = 3` et les trois zéros ON (fermé), tout zéro
sous un demi est au-dessus de `28`, et à sa hauteur le comptage vaut au moins `5` : sa fréquence serait la première où le
comptage gagne deux unités d'un coup, portées par le zéro et son miroir, sans zéro ON correspondant (déficit `≥ 2`).
Indépendant de la profondeur. Fermé ; hors de la récurrence vers RH (même preuve que `low_after_on_band`). -/
theorem low_zero_after_certified_band (w : TrueZero) (hβ : rZeroRadialPosition w.1 < 1 / 2) :
    28 < rZeroHeight w.1 ∧ 5 ≤ upperCountWithMultiplicity (rZeroHeight w.1) ∧
      2 ≤ zeroCountDeficit (rZeroHeight w.1) := by
  have hW : lowCount 28 = 0 := (lowCount_eq_zero_iff 28).mpr fun z hz hlt => by
    rw [three_arrivals_certified.2.2.2.2 z hz] at hlt; exact lt_irrefl _ hlt
  have hc : (28 : ℝ) < rZeroHeight w.1 := by
    by_contra hle
    exact (lowCount_eq_zero_iff 28).mp hW w (not_lt.mp hle) hβ
  have h1 := upperCount_eq_on_add_two_low 28
  have h2 := upperCount_eq_on_add_two_low (rZeroHeight w.1)
  have h3 := onCount_mono hc.le
  have h4 := one_le_lowCount_of_low w (le_refl (rZeroHeight w.1)) hβ
  have h28 := upperCountWithMultiplicity_twentyeight
  refine ⟨hc, by omega, ?_⟩
  rw [zeroCountDeficit_eq]; omega

#print axioms low_zero_after_certified_band

end RHV6Fresh
