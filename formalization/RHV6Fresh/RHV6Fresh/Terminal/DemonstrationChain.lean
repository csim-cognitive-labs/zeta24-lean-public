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
import RHV6Fresh.Terminal.WindingReadingChain
import RHV6Fresh.Terminal.InterlacingLink
import RHV6Fresh.Terminal.CascadeContinuation
import RHV6Fresh.Terminal.FrequencyCascadeStability
import RHV6Fresh.Terminal.HorizontalExclusion
import RHV6Fresh.Terminal.ZeroFreeRegionBand
import RHV6Fresh.Terminal.OnRegimeStabilityPackage

/-!
# Chaîne unique de la démonstration (auteur, 2026-10-09 : « intègre la démonstration entière dans une seule chaîne Lean,
importée par `RHV6Fresh.lean`, sur main ; rien à part »)

Module du build principal (`lake build RHV6Fresh`), importé par `RHV6Fresh.lean`. Il remplace l'ancienne cible séparée
`RHV6FreshTDD` (supprimée). Les preuves manquantes sont laissées sous forme de véritables buts non fermés : aucun `sorry`,
aucun `admit`, aucun axiome ajouté, aucun contournement, aucune prémisse ajoutée. Tant qu'un but reste ouvert, le build
principal est rouge et tout théorème qui en dépend est conditionnel, jamais compilé.

## Chaîne active, et elle seule

comptage initial `N(15) = 1` → premier zéro ON (ancre) → conservation du régime au passage authentique avec historique ON
→ tous les membres ON → `RiemannHypothesis`.

## Obligation 1 — comptage initial (`N(15) = 1`)

Fermé dans le build principal (axiomes standard) : `ζ(σ) ≠ 0` pour `0 < σ < 1` (`Terminal/ZetaRealSegment.lean`) ;
principe de l'argument pour la fonction entière `ξ₁` sur le rectangle `[−1, 2] × [0, T]` sans zéro au bord
(`Terminal/ArgumentPrinciple.lean`). Ouvert ici, deux lemmes NUMÉRIQUES dont E185 (Arb, intervalles) est le certificat
externe, jamais transformé en axiome ni en égalité admise : (a) la valeur `1` de `(2πi)⁻¹ ∮ ξ₁'/ξ₁` sur
`∂([−1, 2] × [0, 15])` ; (b) aucun zéro non trivial exactement à la hauteur `15`.

## Obligation 2 — la plus petite question qui reste (réorganisation, auteur, 2026-10-15)

`off_signal_amplitude_incompatible` : sous l'ancre, sur un passage `p : e → l` qui monte depuis un membre ON de hauteur
positive, tout membre qui précède l'arrivée étant ON, un zéro à la hauteur du zéro suivant dont le signal a une amplitude
strictement décroissante le long des premiers (la zone sous un demi, lue sur l'amplitude). Lock de l'auteur : « l'amplitude
d'un OFF situé à < 1/2 est incompatible avec le signal des écarts des premiers et ne peut pas être synchronisé ». But :
`False`, non fermé. En contexte, les seuls acquis du lock : reproduction exacte, aucun remplacement, miroir d'amplitude
croissante à la même hauteur, amplitude imposée par la courbe des premiers à chaque signal, échelle `x` entière démontrée,
aucun OFF jusqu'à 28. Sens unique (auteur, 2026-10-15) : les écarts immuables des premiers imposent aux zéros leur fréquence et leur
amplitude ; les zéros sont les signaux qui composent ces écarts ; aucune lecture n'intervient. `radial_conservation_anchored` en découle (fermé sous cette question) : côté haut exclu, arrivée sous un demi
⟹ amplitude décroissante. L'ancien corps (870 lignes, 309 faits en contexte, aucun consommé) est retiré ; audit §93.
VERROU DU COUPLE (auteur, 2026-10-16 : « c'est le couple amplitude, fréquence, donc (T, β), qui doit disqualifier le OFF ») :
sur la Tour normalisée projetée sur l'axe algébrique, l'espacement des rencontres lit la fréquence, la position des rencontres
et le besoin aux rencontres lisent tous deux `β` et s'accordent ; on ne change pas l'amplitude sans déplacer les points de
passage, on ne réaligne pas les rencontres en changeant la fréquence ; le couple est verrouillé (`Terminal/CoupleLock.lean`,
composé). LA FRÉQUENCE EST DÉJÀ OCCUPÉE (auteur, 2026-10-16 : « point de rencontre à une demi et hauteur attendue du zéro :
déjà pris par les zéros ON ; impossible de définir des OFF avec exactement ces fréquences ; on ne peut définir qu'en dessous,
avec β < 1/2, puisque β > 1/2 est déjà exclu » ; `Terminal/OccupiedFrequency.lean`, composé) : le signal ON d'une fréquence
occupée a ses rencontres aux positions de la ligne ; un seul signal par fréquence ⟹ tout zéro d'une fréquence occupée est sur
la ligne ; le côté haut est exclu par son miroir, seul candidat en dessous. DES ÉCARTS EXACTS VERS LES FRÉQUENCES ENGENDRÉES
ET LEURS POINTS DE RENCONTRE (auteur, 2026-10-16, E321 ; `Terminal/GeneratedFrequency.lean`, rigidités renversées dans le sens
premiers ⟶ zéro, composé) : la hauteur du zéro suivant est une fréquence engendrée par la courbe des premiers ; la position de
la rencontre du signal engendré impose sa position radiale ; rencontre à la position de la ligne ⟺ signal sur la ligne ;
rencontre au-delà ⟺ signal en dessous d'une demi ; un seul signal à une fréquence ⟺ rencontre sur la ligne ; la loi « aucune
fréquence engendrée à rencontre sous une demi » ⟺ RH. But affiché : le point de rencontre du signal que la courbe des premiers
engendre à la fréquence du zéro suivant est à la position de la ligne.

## Suite de la chaîne

Chaque flèche est un théorème fermé du build principal appliqué : récurrence forte canonique
(`canonical_onLine_of_history_conservation`), captivité universelle comme conséquence
(`universal_captivity_of_all_onLine`), fermeture (`riemannHypothesis_of_captivity_onLine`), puis conservation du régime,
progression par la hauteur, prolongement du comptage (contrôle).
-/

namespace RHV6Fresh

open RHV3Lean Complex Set Filter
open scoped Topology

/-! ## Obligation 1 — comptage initial de la première bande -/

open RHV3Lean Complex Set

-- `eulerMaclaurinMain`, l'encadrement d'ordre un et la borne FINE (`zeta_sub_eulerMaclaurinMain_le_fine` :
-- `‖ζ − main_N‖ ≤ ‖s‖‖s+1‖/12·(N^{−σ−2} + N^{−σ−1}/(σ+1))`, annulation sur chaque intervalle unité) sont dans
-- `Terminal/EulerMaclaurinFine.lean` (fermé, axiomes standard).

/-- **Réduction fermée de (b)** : aucun zéro non trivial exactement à la hauteur `15` dès que l'inégalité finie (V1) est fournie. Réduite (compilé) par la réflexion
`ρ ↦ 1 − ρ̄` (`mirrorPoint_nontrivial`, même hauteur) à la moitié droite `1/2 ≤ σ < 1`, puis, par l'encadrement
d'Euler–Maclaurin démontré (N = 10000, erreur `‖s‖·N^{−σ}/σ ≤ 0,301`), à une inégalité FINIE explicite. Non fermé :
l'évaluation certifiée de la somme finie (cosinus et sinus de `15 log n`, `n ≤ 10000`, uniformément en `σ`) n'existe pas
dans Lean (E185 : certificat externe ; marge numérique observée `|ζ| ≥ 0,669`, non certifiée). -/
theorem no_zero_at_height_fifteen_of_certificate (hFin : ∀ σ : ℝ, 1 / 2 ≤ σ → σ < 1 →
      ‖(σ : ℂ) + (15 : ℝ) * I‖ * (((10000 : ℕ) : ℝ) ^ (-σ) / σ) <
        ‖eulerMaclaurinMain 10000 ((σ : ℂ) + (15 : ℝ) * I)‖) :
    ∀ ρ : ℂ, PIsNonTrivialZetaZero ρ → ρ.im ≠ 15 := by
  suffices hRight : ∀ σ : ℝ, 1 / 2 ≤ σ → σ < 1 → riemannZeta ((σ : ℂ) + (15 : ℝ) * I) ≠ 0 by
    intro ρ hρ h15
    rcases le_or_gt (1 / 2) ρ.re with hr | hr
    · apply hRight ρ.re hr hρ.2.2
      have he : (ρ.re : ℂ) + (15 : ℝ) * I = ρ := by apply Complex.ext <;> simp [h15]
      rw [he]; exact hρ.1
    · have hm := mirrorPoint_nontrivial hρ
      apply hRight (1 - ρ.re) (by linarith) (by linarith [hρ.2.1])
      have he : ((1 - ρ.re : ℝ) : ℂ) + (15 : ℝ) * I = 1 - (starRingEnd ℂ) ρ := by
        apply Complex.ext <;> simp [h15]
      rw [he]; exact hm.1
  intro σ hσ1 hσ2
  apply zeta_ne_zero_of_eulerMaclaurinMain 10000 (by norm_num) (t := 15) (by linarith)
    (fun h => by have := congrArg Complex.im h; simp at this) (hFin σ hσ1 hσ2)
  -- `hFin` : inégalité finie explicite, certifiée hors Lean (E176, Backlund à T = 15) ; vérificateur Lean (V1) manquant

/-- **Réduction fermée de (b) par la borne fine** : aucun zéro non trivial à la hauteur `15` dès que la partie principale
d'Euler–Maclaurin à `N = 10` dépasse l'erreur fine sur `1/2 ≤ σ < 1` (moitié gauche par la réflexion). -/
theorem no_zero_at_height_fifteen_of_fine_certificate (hFin10 : ∀ σ : ℝ, 1 / 2 ≤ σ → σ < 1 →
      ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
          ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
        ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖) :
    ∀ ρ : ℂ, PIsNonTrivialZetaZero ρ → ρ.im ≠ 15 := by
  suffices hRight : ∀ σ : ℝ, 1 / 2 ≤ σ → σ < 1 → riemannZeta ((σ : ℂ) + (15 : ℝ) * I) ≠ 0 by
    intro ρ hρ h15
    rcases le_or_gt (1 / 2) ρ.re with hr | hr
    · apply hRight ρ.re hr hρ.2.2
      have he : (ρ.re : ℂ) + (15 : ℝ) * I = ρ := by apply Complex.ext <;> simp [h15]
      rw [he]; exact hρ.1
    · have hm := mirrorPoint_nontrivial hρ
      apply hRight (1 - ρ.re) (by linarith) (by linarith [hρ.2.1])
      have he : ((1 - ρ.re : ℝ) : ℂ) + (15 : ℝ) * I = 1 - (starRingEnd ℂ) ρ := by
        apply Complex.ext <;> simp [h15]
      rw [he]; exact hm.1
  intro σ hσ1 hσ2
  exact zeta_ne_zero_of_eulerMaclaurinMain_fine 10 (by norm_num) (t := 15) (by linarith)
    (fun h => by have := congrArg Complex.im h; simp at this) (hFin10 σ hσ1 hσ2)

/-- **Vérification (V1) du certificat d'E176, dans la bibliothèque : FERMÉE.** Inégalité finie à `N = 10` avec la borne fine,
uniforme sur `1/2 ≤ σ < 1` : `em10_fifteen_certificate` (`Terminal/EulerMaclaurinTenCertificate.lean`, généré par
`experiments/e191_em10_certificate_generator.py`, chaque constante revérifiée par `norm_num` ; seize sous-intervalles, marge
minimale 0,031 ; axiomes standard). -/
theorem eulerMaclaurin_ten_fifteen_certificate : ∀ σ : ℝ, 1 / 2 ≤ σ → σ < 1 →
    ‖(σ : ℂ) + (15 : ℝ) * I‖ * ‖(σ : ℂ) + (15 : ℝ) * I + 1‖ / 12 *
        ((10 : ℝ) ^ (-σ - 2) + (10 : ℝ) ^ (-σ - 1) / (σ + 1)) <
      ‖eulerMaclaurinMain 10 ((σ : ℂ) + (15 : ℝ) * I)‖ :=
  em10_fifteen_certificate

/-- **Obligation (b)**, signature historique : aucun zéro non trivial exactement à la hauteur `15`, par la réduction fermée
et la vérification (V1). -/
theorem no_zero_at_height_fifteen : ∀ ρ : ℂ, PIsNonTrivialZetaZero ρ → ρ.im ≠ 15 :=
  no_zero_at_height_fifteen_of_fine_certificate eulerMaclaurin_ten_fifteen_certificate

#print axioms no_zero_at_height_fifteen

/-- Non-annulation de `ξ₁` sur tout le contour `∂([−1, 2] × [0, 15])` : segment réel (build principal), côtés verticaux
(build principal), côté `Im = 15` (obligation (b)). Fermé dès que (b) l'est. -/
theorem rect_boundary_nonvanishing_fifteen :
    ∀ s ∈ rectBoundary (-1 : ℂ) (2 + (15 : ℝ) * I), completedEntire s ≠ 0 := by
  intro s hs
  rcases mem_rectBoundary_cases hs with h0 | h15 | ⟨hre, him0, him15⟩
  · have hσ : s = (s.re : ℂ) := by
      apply Complex.ext <;> simp [h0]
    rw [hσ]
    exact completedEntire_real_ne_zero s.re
  · intro h
    have hζ := (completedEntire_eq_zero_iff (by rw [h15]; norm_num)).mp h
    exact no_zero_at_height_fifteen s (nontrivial_of_zero_im_pos hζ (by rw [h15]; norm_num)) h15
  · rcases him0.lt_or_eq with him | him
    · exact completedEntire_ne_zero_of_re_out him.ne' (by rcases hre with h | h <;> rw [h] <;> norm_num)
    · have hσ : s = (s.re : ℂ) := by
        apply Complex.ext <;> simp [← him]
      rw [hσ]
      exact completedEntire_real_ne_zero s.re

/-- **Vérification (V2) du certificat d'E176, dans la bibliothèque, sans Γ** : deux rectangles `B₁ = [1/4, 2] × [−1, 15]`,
`B₂ = [3/4, 2] × [−1, 15]` ; `ζ` ne s'annule pas sur leurs bords ; l'enroulement de `(1 − s)ζ(s)` vaut un autour de `B₁` et
zéro autour de `B₂`. FERMÉ par le certificat généré `ZB.Cert.zeta_box_certificate` (`Terminal/ZetaBox/`, générateur
`experiments/e192_zeta_box_certificate_generator.py` : morceaux de côtés, valeurs certifiées de la partie principale
d'Euler–Maclaurin aux extrémités, interpolation, raccords d'un quart de tour) ; aucune valeur de `Γ`. -/
theorem zeta_box_certificate_fifteen :
    (∀ s ∈ rectBoundary (((1 / 4 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + ((15 : ℝ) : ℂ) * I),
        riemannZeta s ≠ 0) ∧
    (∀ s ∈ rectBoundary (((1 - 1 / 4 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + ((15 : ℝ) : ℂ) * I),
        riemannZeta s ≠ 0) ∧
    (2 * (Real.pi : ℂ) * I)⁻¹ * rectBoundaryIntegral (logDeriv (fun s => (1 - s) * riemannZeta s))
        (((1 / 4 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + ((15 : ℝ) : ℂ) * I) = 1 ∧
    rectBoundaryIntegral (logDeriv (fun s => (1 - s) * riemannZeta s))
        (((1 - 1 / 4 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + ((15 : ℝ) : ℂ) * I) = 0 := by
  exact ZB.Cert.zeta_box_certificate

/-- **Obligation (a)**, signature historique : valeur `1` de `(2πi)⁻¹ ∮ ξ₁'/ξ₁` sur `∂([−1, 2] × [0, 15])`, composée :
principe de l'argument (`hAP`), comptage de la fenêtre ouverte par deux rectangles (`upperWindowOpen_count_of_zeta_boxes`,
fermé, sans Γ) et certificat (V2). -/
theorem completedEntire_rect_integral_fifteen :
    (2 * (Real.pi : ℂ) * I)⁻¹ * rectBoundaryIntegral (logDeriv completedEntire) (-1) (2 + (15 : ℝ) * I) = 1 := by
  have hAP := completedEntire_argument_principle 15 (by norm_num) rect_boundary_nonvanishing_fifteen
  obtain ⟨hZ₁, hZ₂, hW₁, hW₂⟩ := zeta_box_certificate_fifteen
  have hcount := upperWindowOpen_count_of_zeta_boxes (σ₀ := 1 / 4) (t₁ := 1) (T := 15)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hZ₁ hZ₂ hW₁ hW₂
  rw [hAP, hcount]; norm_num

/-- **Comptage de la première bande depuis ses deux certificats** : `N(15) = 1` dès que l'inégalité finie (`hFin`, (V1))
et la valeur de l'intégrale de bord (`hInt`, (V2)) sont fournies, par le principe de l'argument démontré. Fermé ; les deux
valeurs sont certifiées hors Lean par E176 (commit 02bd2b09), aucun vérificateur Lean. -/
theorem upperCountWithMultiplicity_fifteen_of_certificates (hFin : ∀ σ : ℝ, 1 / 2 ≤ σ → σ < 1 →
      ‖(σ : ℂ) + (15 : ℝ) * I‖ * (((10000 : ℕ) : ℝ) ^ (-σ) / σ) <
        ‖eulerMaclaurinMain 10000 ((σ : ℂ) + (15 : ℝ) * I)‖)
    (hInt : (2 * (Real.pi : ℂ) * I)⁻¹ * rectBoundaryIntegral (logDeriv completedEntire) (-1) (2 + (15 : ℝ) * I) = 1) :
    upperCountWithMultiplicity 15 = 1 := by
  rw [upperCount_closed_eq_open_of_no_boundary (no_zero_at_height_fifteen_of_certificate hFin)]
  have h := completedEntire_argument_principle 15 (by norm_num) (fun s hs => by
    rcases mem_rectBoundary_cases hs with h0 | h15 | ⟨hre, him0, him15⟩
    · have hσ : s = (s.re : ℂ) := by apply Complex.ext <;> simp [h0]
      rw [hσ]; exact completedEntire_real_ne_zero s.re
    · intro h
      have hζ := (completedEntire_eq_zero_iff (by rw [h15]; norm_num)).mp h
      exact no_zero_at_height_fifteen_of_certificate hFin s (nontrivial_of_zero_im_pos hζ (by rw [h15]; norm_num)) h15
    · rcases him0.lt_or_eq with him | him
      · exact completedEntire_ne_zero_of_re_out him.ne' (by rcases hre with h | h <;> rw [h] <;> norm_num)
      · have hσ : s = (s.re : ℂ) := by apply Complex.ext <;> simp [← him]
        rw [hσ]; exact completedEntire_real_ne_zero s.re)
  rw [hInt] at h
  exact_mod_cast h.symm


/-- **Comptage de la première bande**, signature historique : `N(15) = 1`, composé depuis le principe de l'argument
(build principal), (V1) et (V2). Conditionnel aux deux vérifications ouvertes ; aucun paramètre. -/
theorem upperCountWithMultiplicity_fifteen : upperCountWithMultiplicity 15 = 1 := by
  rw [upperCount_closed_eq_open_of_no_boundary no_zero_at_height_fifteen]
  have h := completedEntire_argument_principle 15 (by norm_num) rect_boundary_nonvanishing_fifteen
  rw [completedEntire_rect_integral_fifteen] at h
  exact_mod_cast h.symm

/-! ### Ancre : dépendance stable, certificat d'E176

`N(15) = 1` (`upperCountWithMultiplicity_fifteen`) est composé dans la bibliothèque depuis le principe de l'argument
(fermé) et les deux vérifications du certificat d'E176 (commit 02bd2b09) : (V1) `eulerMaclaurin_ten_fifteen_certificate` (borne fine, N = 10),
(V2) `completedEntire_rect_integral_fifteen`. Signatures historiques rétablies (2026-10-10) : aucun théorème de la chaîne
ne prend le comptage en paramètre ; les vérifications manquantes sont des buts ouverts, jamais des hypothèses. -/

/-- **L'ancre** : le premier membre canonique est ON. Conditionnel à (a) et (b). -/
theorem anchor_canonical_one : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2 :=
  anchor_of_count_one upperCountWithMultiplicity_fifteen

/-- Le premier membre canonique coïncide avec son miroir (miroir annulé). Conditionnel à (a) et (b). -/
theorem anchor_mirror_eq_self : mirrorMember (canonicalZero 1) = canonicalZero 1 :=
  (mirror_annulled_iff_onLine _).mpr anchor_canonical_one

/-- Hauteur minimale du premier membre canonique : aucun membre supérieur en dessous (build principal, sans condition). -/
theorem anchor_bottom : sUpperZerosBelow (canonicalZero 1).1 = ∅ := canonicalZero_one_bottom

#print axioms anchor_bottom

/-- Domination de l'enveloppe du premier parmi les membres ON, par unité de multiplicité. Conditionnel à (a) et (b). -/
theorem anchor_dominates_onLine {n : ℕ} (hn : 1 ≤ n) (hOn : rZeroRadialPosition (canonicalZero n).1 = 1 / 2)
    {x : ℝ} (hx : 0 < x) : pairAmplitude (canonicalZero n) x ≤ pairAmplitude (canonicalZero 1) x :=
  canonical_onLine_amplitude_le_first anchor_canonical_one hn hOn hx


/-- Aucun membre supérieur de hauteur `≤ 0` : `N(0) = 0` (coupure basse des bandes certifiées). -/
theorem upperCount_zero : upperCountWithMultiplicity 0 = 0 := by
  unfold upperCountWithMultiplicity
  rw [Finset.sum_eq_zero]
  intro ρ hρ
  have h := mem_upperWindow.mp hρ
  linarith [h.2.1, h.2.2]


/-- **Premier passage, depuis le premier zéro certifié** (auteur, 2026-10-11) : l'historique ON jusqu'à `T₁` découle de
l'ancre démontrée (`N(15) = 1`, `T₁ ≤ 15`) ; sur toute fenêtre finie de contacts acquis du premier zéro, retrait signé
majoré localement, identité exacte avec le groupe d'arrivée et marge admissible du complément ; la conservation au deuxième
membre canonique découle de la SEULE séparation locale sous l'hypothèse « arrivée basse ». Fermé. -/
theorem first_passage_window_transmission :
    (∀ w : TrueZero, rZeroHeight w.1 ≤ rZeroHeight (canonicalMember 0).1 → rZeroRadialPosition w.1 = 1 / 2) ∧
    (∀ (k₀ m : ℕ) (lam : Fin m → ℂ),
      ‖historyRemoved (rZeroHeight (canonicalMember 0).1) (contactWindow (canonicalMember 0) k₀ m) lam -
          groupSignal (rZeroHeight (canonicalMember 0).1) (rZeroHeight (canonicalMember 1).1)
            (contactWindow (canonicalMember 0) k₀ m) lam‖ ≤
        windowMargin (rZeroHeight (canonicalMember 1).1) (contactWindow (canonicalMember 0) k₀ m) lam ∧
      ‖historyRemoved (rZeroHeight (canonicalMember 0).1) (contactWindow (canonicalMember 0) k₀ m) lam‖ ≤
        ∑ r, ‖lam r‖ * (‖smoothedRemainder (contactWindow (canonicalMember 0) k₀ m r)‖ +
          precedingBudget (rZeroHeight (canonicalMember 0).1) *
            contactWindow (canonicalMember 0) k₀ m r ^ (1 / 2 : ℝ))) ∧
    ((rZeroRadialPosition (canonicalMember 1).1 < 1 / 2 → ∃ (k₀ m : ℕ) (lam : Fin m → ℂ) (S A : ℝ),
        S ≤ ‖groupSignal (rZeroHeight (canonicalMember 0).1) (rZeroHeight (canonicalMember 1).1)
          (contactWindow (canonicalMember 0) k₀ m) lam‖ ∧
        ‖historyRemoved (rZeroHeight (canonicalMember 0).1) (contactWindow (canonicalMember 0) k₀ m) lam‖ ≤ A ∧
        A + windowMargin (rZeroHeight (canonicalMember 1).1) (contactWindow (canonicalMember 0) k₀ m) lam < S) →
      rZeroRadialPosition (canonicalMember 1).1 = 1 / 2) := by
  have h0 : lowCount 15 = 0 :=
    (saturation_iff_lowCount_zero 15).mp (saturation_of_count_one upperCountWithMultiplicity_fifteen)
  have hT₁ := canonical_in_band_of_count_step (a := 0) (b := 15) (k := 0) (by norm_num)
    (fun j hj => absurd hj (Nat.not_lt_zero _)) (by rw [upperCount_zero])
    (by rw [upperCount_zero, upperCountWithMultiplicity_fifteen]; norm_num)
  have hHistOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ rZeroHeight (canonicalMember 0).1 →
      rZeroRadialPosition w.1 = 1 / 2 := fun w hw => all_onLine_of_lowCount_zero h0 w (le_trans hw hT₁.2)
  have hOn : rZeroRadialPosition (canonicalMember 0).1 = 1 / 2 := anchor_canonical_one
  refine ⟨hHistOn, fun k₀ m lam => ⟨window_group_within_margin _ _ _ lam (contactWindow_gt_one _ k₀ m),
    historyRemoved_le_local hHistOn _ lam (contactWindow_gt_one _ k₀ m)⟩, fun hSep => ?_⟩
  have hE : 0 < rZeroHeight (canonicalPassage 0).zEarlierMember := (canonicalMember 0).2
  have hV : VerticalPassage (canonicalPassage 0) := bottom_exit_vertical (canonicalPassage 0) hE anchor_bottom hOn
  have := window_transmission (canonicalPassage 0) hE hV hOn hSep
  exact this.trans hOn

#print axioms first_passage_window_transmission




/-! ## Obligation 2 — conservation radiale au passage authentique -/

open RHV3Lean
open scoped InnerProductSpace ArithmeticFunction

/-! ## Obligation 2 — l'amplitude du signal OFF est contraire à la reproduction des premiers

Réorganisation (auteur, 2026-10-15 : « reprends tout ce qui est confirmé, audit de fidélité, modifie le Lean pour qu'il
reflète la plus petite question qui reste »). L'ancien corps (870 lignes, 309 faits en contexte, aucun consommé par le
dernier pas) est retiré ; les modules qui les portaient restent compilés et cités dans l'audit (§93). Le théorème ouvert
ne garde que les acquis du lock et la question. -/

/-- **Le but minimal** (réduction demandée par l'auteur, 2026-10-17, points A à E de l'audit E326) : sous l'ancre, sur un passage
`p : e → l` qui monte depuis un membre ON de hauteur positive, tout membre qui précède l'arrivée étant ON, une arrivée `l` sous un
demi (`hBelow`, écrite directement) mène à `False`. C'est le seul théorème ouvert de la chaîne ; `off_signal_amplitude_incompatible`
(interface conservée) s'y ramène sans perte.

Contexte RÉDUIT aux faits qui portent sur la liaison encore non démontrée, « événements premiers exacts → synchronisation
collective des fréquences, contacts et amplitudes → contrainte sur la Tour d'arrivée », groupés par rôle (l'inventaire complet de
l'ancien contexte, avec le module de chaque fait, est dans `AUDIT_SOLUTION_20261005.md` §116 ; aucun théorème compilé n'est
retiré, seuls des renvois inutilisés quittent ce contexte). Le but est affiché tel quel, `False`, sur la ligne `hObligation`. -/
theorem arrival_low_contradiction (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hV : VerticalPassage p) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hHist : ∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2)
    (hL : 0 < rZeroHeight p.zLaterMember) (hBelow : rZeroRadialPosition p.zLaterMember < 1 / 2)
    (hRaccord : NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
      (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩))) : False := by
  obtain ⟨l, hl⟩ : ∃ l : TrueZero, l.1 = p.zLaterMember := ⟨⟨p.zLaterMember, hL⟩, rfl⟩
  have hZone : rZeroRadialPosition l.1 < 1 / 2 := hl ▸ hBelow
  have hTe : rZeroHeight p.zEarlierMember < rZeroHeight l.1 := hl ▸ hV
  -- (I) DONNÉES DES PREMIERS SEULS (aucun zéro dans l'énoncé) : exposant `1` du reste lissé (Chebyshev), bande `0 ≤ β ≤ 1`
  -- lue depuis les premiers, saut de pente `Λ(N)` à chaque événement premier (porté par la somme infinie seule).
  have hGrammarAmplitude : ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 : ℝ) :=
    smoothedRemainder_linear_growth
  have hStripFromPrimes := radial_strip_from_primes l
  have hEventJump := @primeEvent_slope_jump_ne_zero
  -- (II) COMPTAGE CERTIFIÉ (Lean, rectangles de zêta, première bande seule) : tout zéro de hauteur `≤ 15` est ON ; donc
  -- l'arrivée est au-dessus de 15. (Les bandes 22 et 28 sont sorties du build par défaut le 2026-10-27 : cible
  -- `RHV6FreshCertificates`, module `FirstThreeZerosCertified`.)
  have hAbove15 : 15 < rZeroHeight l.1 := by
    have hW : lowCount 15 = 0 :=
      (saturation_iff_lowCount_zero 15).mp (saturation_of_count_one upperCountWithMultiplicity_fifteen)
    by_contra hle
    exact (lowCount_eq_zero_iff 15).mp hW l (not_lt.mp hle) hZone
  -- (III) FORMULE EXPLICITE : IDENTITÉS COLLECTIVES (vraies pour toute position radiale ; elles transportent, elles ne
  -- contraignent pas) : la courbe des premiers est la somme de tous les vrais zéros ; sur chaque écart premier, la somme des
  -- contributions conjointes (amplitude, fréquence, calage des rencontres lissées) ; entrée de matrice ; loi conjointe par écart.
  have hReproduction : ∀ x : ℝ, 1 < x →
      smoothedRemainder x = ∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm x ρ :=
    fun x hx => smoothedRemainder_eq_tsum_residueTerm hx
  have hJointSync := prime_gap_joint_synchronization
  have hGapEntry := fun (σ : ExplicitIndex) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) => gap_entry_joint σ ha hb
  have hJointStep := memberJoint_gap_step
  -- (IV) PASSAGE DE LA SOMME À LA TOUR D'ARRIVÉE (exact, aucune borne) : la contribution de `l` est imposée, courbe moins part
  -- fixe des autres vrais zéros, sur chaque écart ; aucun remplacement ne reconstruit.
  have hImposedJoint := imposed_joint_gap l
  have hImposedDrift := imposed_contribution_drift l
  have hImposedUnique := @imposed_contribution_unique l
  -- (V) HISTORIQUE ON : information arithmétique réelle sur la part PASSÉE. Tout zéro de hauteur `≤ T_e` est ON ; la part finie
  -- correspondante de la courbe est sous `budget·√x` ; la courbe = part passée + suite (identité). La SUITE (hauteurs `> T_e`,
  -- arrivée comprise) n'est contrainte par aucun fait du contexte.
  have hPastOn : ∀ z : TrueZero, rZeroHeight z.1 ≤ rZeroHeight p.zEarlierMember → rZeroRadialPosition z.1 = 1 / 2 := by
    intro z hz
    apply hHist z
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    left; rw [← hl]; linarith
  have hPastBudget := fun {x : ℝ} (hx : 1 < x) => precedingSum_le_budget_of_onLine hPastOn hx
  have hSplit := fun {x : ℝ} (hx : 1 < x) => remainder_eq_preceding_add_following (rZeroHeight p.zEarlierMember) hx
  -- (V bis) IDENTITÉ COLLECTIVE ≠ OBLIGATION PAR TERME : la contribution de `l` = courbe − part passée ON (bornée) − (suite − `l`) ;
  -- la « suite − `l` » contient le MIROIR de `l` (même hauteur `T_l > T_e`, distinct de `l`), dont la croissance `1 − β_l > 1/2`
  -- est exactement ce qu'il faudrait exclure : toute obligation par terme tirée de l'identité passe par ce miroir.
  have hArrivalThreeParts : ∀ x : ℝ, 1 < x → nontrivialZeroResidueTerm x (memberIndex l) =
      smoothedRemainder x - precedingSum (rZeroHeight p.zEarlierMember) x -
        (followingSum (rZeroHeight p.zEarlierMember) x - nontrivialZeroResidueTerm x (memberIndex l)) := by
    intro x hx; rw [remainder_eq_preceding_add_following (rZeroHeight p.zEarlierMember) hx]; ring
  have hMirrorInFollowing : rZeroHeight p.zEarlierMember < rZeroHeight (mirrorMember l).1 ∧ mirrorMember l ≠ l :=
    ⟨by rw [mirrorMember_ordinate]; exact hTe, mirrorMember_ne hZone⟩
  have hFiberLow : ∀ z : TrueZero, rZeroHeight z.1 = rZeroHeight l.1 → rZeroRadialPosition z.1 < rZeroRadialPosition l.1 →
      False := by
    intro z hz hlt
    have hz' := hHist z ((thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mpr (Or.inr ⟨hl ▸ hz, hl ▸ hlt⟩))
    linarith
  -- (VI) SIGNATURES DE L'ARRIVÉE SOUS UN DEMI (caractérisations, écart par écart) : fréquence attendue plus basse, déphasage
  -- cumulé non borné, rencontres brutes et lissées décalées, enveloppe décroissante ; le miroir, même fréquence, enveloppe
  -- croissante. Ce sont des faits ; il manque ce qui les INTERDIT dans la reconstruction collective.
  have hLowJointDeviation := fun {T' : ℝ} (hT' : 0 < T') (h : lineContact T' 0 = contactMinusAt l 0) =>
    low_joint_deviation_every_gap l hZone hT' h
  have hMirrorJointDeviation := mirror_joint_deviation_every_gap l hZone
  -- (VII) FORMES DE FERMETURE (chacune « X → False », X non démontré ; pour ce zéro chaque X équivaut à `β_l = 1/2`, sauf
  -- `hAbsurdCloses`, `hResidualCloses` et `hWeightedCloses`, écrites avec les premiers seuls, de la nature d'une bande sans zéro).
  have hAbsurdCloses : (∃ θ C : ℝ, θ < 1 - rZeroRadialPosition l.1 ∧
      ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ θ) → False := by
    rintro ⟨θ, C, hθ, hC⟩
    have hm := radial_le_of_remainder_growth hC (mirrorMember l)
    rw [mirrorMember_radial] at hm
    linarith
  have hMeetingCloses : smoothedMeeting (zeroPoint l) 0 = smoothedMeeting ⟨1 / 2, rZeroHeight l.1⟩ 0 → False :=
    fun h => by have := (smoothedMeeting_line_iff l).mp h; linarith
  have hFrequencyCloses : lineContact (rZeroHeight l.1) 0 = contactMinusAt l 0 → False :=
    fun h => lt_irrefl _ (zero_low_meeting_reads_lower_frequency l hZone (T' := rZeroHeight l.1) l.2 h).1
  have hAmplitudeCloses : ∀ n : ℕ, ImposedOnScaleAtGap l n → False :=
    fun n h => by have := (imposedOnScaleAtGap_iff l n).mp h; linarith
  have hMirrorCloses : ∀ n : ℕ, ImposedNotFasterAtGap (mirrorMember l) n → False := mirror_not_faster_closes l hZone
  -- forme fermante écrite avec les seuls premiers (`PrimeGrammarQuantitative`, A5) : borne critique du résidu cumulé des
  -- écarts `R_{0,m} = Σ_{n<m} (g_n − log p_n)` ; hypothèse de la force de RH (von Koch), non démontrée.
  have hResidualCloses : (∃ C : ℝ, ∀ m : ℕ, |windowResidual 0 m + 2 - Real.log (fnPrimeAtRank m)| ≤
      C * Real.sqrt (fnPrimeAtRank m) * Real.log (fnPrimeAtRank m) ^ 2) → False := fun h => by
    have := thm_zeroRadialPosition_half_of_riemannHypothesis (riemannHypothesis_of_cumulative_residual_bound h) l.1
    linarith
  -- forme fermante au poids intermédiaire `p^{−α}` (`PrimeGrammarQuantitative` §8, E329) : la loi bornée
  -- `|Σ_{n<m} r_n p_n^{−α}| ≤ B`, `1/2 < α < 1 − β_l`, exclut l'arrivée ; force = demi-plan sans zéro `Re s > α`, non démontré.
  have hWeightedCloses : (∃ α B : ℝ, 1 / 2 < α ∧ α < 1 - rZeroRadialPosition l.1 ∧
      ∀ m, |weightedResidual α m| ≤ B) → False := fun ⟨_, _, hα, hαl, hB⟩ =>
    weighted_law_excludes_low hα hB l hαl
  -- (VII bis) INVARIANCE RADIALE PAR TRANSLATION GRAMMATICALE (E343 → proposition mathématique, texte de l'auteur du
  -- 2026-10-19, `GapTranslationInvariance`) : le mode normalisé de `l` (partie réelle = densité de comptage normalisée), projeté
  -- à sa fréquence sur une fenêtre `[a, a+L]`, puis translaté d'un écart premier `L_r = log(p_{r+1}/p_r)`, est multiplié par
  -- `e^{(β_l−1/2)L_r}` (identité, toute position) ; invariance sous une translation `h ≠ 0` ⟺ `β_l = 1/2` (caractérisation) ;
  -- sous un demi la projection DÉCROÎT à chaque écart, celle du miroir (même fréquence) CROÎT : dérives opposées, produit des
  -- rapports = 1 ; la projection d'une somme FINIE de modes est la somme des projections (aucun échange avec la somme infinie).
  have hTranslationIff := fun (a : ℝ) {L h : ℝ} (hL : 0 < L) (hh : h ≠ 0) => zeroMode_translation_invariant_iff l a hL hh
  have hLowDrift := fun (r : ℕ) (a : ℝ) {L : ℝ} (hL : 0 < L) => low_zeroMode_gap_translate_lt l hZone r a hL
  have hMirrorDrift := fun (r : ℕ) (a : ℝ) {L : ℝ} (hL : 0 < L) => mirror_zeroMode_gap_translate_gt l hZone r a hL
  have hOppositeDrifts := mirror_pair_gap_ratios_product l
  have hProjectionLinear := @windowProjection_finset_sum
  -- forme fermante MINIMALE de cette lecture : UNE fenêtre non dégénérée, UNE translation d'UN seul écart premier, et la
  -- projection du mode de `l` à sa fréquence qui ne décroît pas ; la loi quantifiée sur tous les zéros ⟺ RH
  -- (`grammaticalRadialInvariance_all_iff`) ; aucune des deux n'est déduite des sauts et écarts exacts (ligne 28 du texte).
  have hTranslationCloses := single_gap_translation_nondecrease_closes l hZone
  have hLawCloses : GrammaticalRadialInvariance l → False :=
    fun h => absurd ((grammaticalRadialInvariance_iff l).mp h) (ne_of_lt hZone)
  -- (VII ter) COURBURE COLLECTIVE DE LA PAIRE MIROIR (texte de l'auteur du 2026-10-19 : trois niveaux séparés ; objet
  -- remplacé = observable collective des premiers et sa différence seconde ; `CollectiveCurvature`). Niveau géométrique
  -- (démontré) : paire de `l` = `2cosh(δu)e^{iTu}` ; à sa fréquence, différence seconde au pas d'un écart premier
  -- `= 2(cosh(δL_r) − 1)·(A_δ + A_{−δ}) > 0`, nulle ⟺ ligne, minorée par le plancher grammatical de la classe de
  -- transition ; non bornée le long des translations (OFF ⟹ ¬B_G, démontré). Niveau spectral (identité) : la courbure
  -- collective des premiers = courbure de la paire + courbure du complément (somme finie, aucun échange avec la somme
  -- infinie). Niveau arithmétique (NON démontré) : une borne `B_G` de la courbure collective et du complément.
  have hPairCurvatureIff := fun (a : ℝ) {L h : ℝ} (hL : 0 < L) (hh : h ≠ 0) =>
    zero_pair_curvature_eq_zero_iff l a hL hh
  have hPairCurvaturePos := fun (r : ℕ) (a : ℝ) {L : ℝ} (hL : 0 < L) => low_zero_pair_curvature_pos l hZone r a hL
  have hPairCurvatureFloor := fun (r : ℕ) (h3 : 3 < fnPrimeAtRank r) (a : ℝ) {L : ℝ} (hL : 0 < L) =>
    zero_pair_curvature_gap_floor l r h3 a hL
  have hOffNotBounded := fun (r : ℕ) {L : ℝ} (hL : 0 < L) (K : ℝ) => off_pair_curvature_unbounded l hZone r hL K
  have hCollectiveSplit := fun (a L h : ℝ) hInt => collectiveCurvature_split_pair l a L h (rZeroHeight l.1) hInt
    (mirrorMember_ne hZone)
  have hPairCurvatureCloses := pair_curvature_closes l hZone
  have hPairBoundCloses := fun (r : ℕ) {L : ℝ} (hL : 0 < L) => pair_curvature_bound_closes l hZone r hL
  have hTwoLemmaCloses := fun (r : ℕ) {L : ℝ} (hL : 0 < L) => collective_curvature_two_lemma_closes l hZone r hL
  -- (VII quater) L'OPÉRATEUR GRAMMATICAL `𝓛_G` ET LA BORNE `B_G` (E344, auteur, 2026-10-19 : « construire l'opérateur
  -- grammatical B_G » ; `GrammarOperator`). `𝓛_G = Σ_r w(classe_r) Δ²_{L_r}` sur `m` écarts consécutifs depuis le rang `r₀`,
  -- défini par trois poids, un rang et une longueur : aucune partie réelle, aucune hauteur, aucun zéro. Démontré : symbole
  -- `Σ_r w(a_r)·2(cosh(δL_r) − 1)`, nul en ligne (le signal ON est annulé), minoré par les planchers grammaticaux par classe,
  -- strictement positif hors ligne ; OFF ⟹ ¬B_G (`𝓛_G(paire)` non borné le long des translations) ; `D_G = 𝓛_G(Q)` des
  -- premiers seuls = `𝓛_G(paire) + 𝓛_G(complément)` ; toute famille FINIE de zéros en ligne a un complément borné et `𝓛_G`
  -- d'une fonction bornée est borné. NON démontré : `B_G(D_G)` et la borne de la partie infinie du complément.
  have hOperatorSymbolZero := fun (w : ℕ → ℝ) (r₀ m : ℕ) => curvatureSymbol_zero w r₀ m
  have hOperatorAnnihilatesOn := fun (w : ℕ → ℝ) (r₀ m : ℕ) (L a : ℝ) => classWeightedCurvature_onLine w r₀ m L a
  have hOperatorSymbolFloor := fun (w : ℕ → ℝ) (hw : ∀ c, 0 ≤ w c) (r₀ m : ℕ)
    (h3 : ∀ j : Fin m, 3 < fnPrimeAtRank (r₀ + j)) (d : ℝ) => curvatureSymbol_ge_classFloor w hw r₀ m h3 d
  have hOperatorOffUnbounded := fun (w : ℕ → ℝ) (hw : ∀ c, 0 ≤ w c) (r₀ m : ℕ)
    (hact : ∃ j : Fin m, 0 < w (eventClass (r₀ + j))) {L : ℝ} (hL : 0 < L) (K : ℝ) =>
    off_classWeightedCurvature_unbounded w hw r₀ m hact l hZone hL K
  have hOperatorBoundCloses := fun (w : ℕ → ℝ) (hw : ∀ c, 0 ≤ w c) (r₀ m : ℕ)
    (hact : ∃ j : Fin m, 0 < w (eventClass (r₀ + j))) {L : ℝ} (hL : 0 < L) =>
    class_operator_bound_closes w hw r₀ m hact l hZone hL
  have hOperatorSplit := fun (w : ℕ → ℝ) (r₀ m : ℕ) (L a : ℝ) hInt =>
    grammarObservable_split_pair w r₀ m l L (rZeroHeight l.1) a hInt (mirrorMember_ne hZone)
  have hOperatorTwoLemmaCloses := fun (w : ℕ → ℝ) (hw : ∀ c, 0 ≤ w c) (r₀ m : ℕ)
    (hact : ∃ j : Fin m, 0 < w (eventClass (r₀ + j))) {L : ℝ} (hL : 0 < L) =>
    grammar_operator_two_lemma_closes w hw r₀ m hact l hZone hL
  have hOnComplementBounded := fun (s : Finset TrueZero) (hs : ∀ z ∈ s, rZeroRadialPosition z.1 = 1 / 2) (a : ℝ)
    {L : ℝ} (hL : 0 ≤ L) (T : ℝ) => onLine_finset_projection_norm_le s hs a hL T
  have hOperatorOfBounded := fun (w : ℕ → ℝ) (r₀ m : ℕ) (F : ℝ → ℂ) {M : ℝ} (hF : ∀ a, ‖F a‖ ≤ M) (a : ℝ) =>
    classWeightedCurvatureC_norm_le w r₀ m F hF a
  -- (VII quinquies) LA BORNE DU COMPLÉMENT INFINI (auteur, 2026-10-19 : « chercher une borne démontrée du complément
  -- infini (zéros au-dessus de l'arrivée) » ; `GrammarTailBound`). Inventaire : aucune borne uniforme n'existe dans le
  -- dépôt. Démontré : le signal normalisé des premiers = tête (hauteurs `≤ H`, finie) + queue (hauteurs `> H`, infinie) ;
  -- la tête au-dessus de l'historique ON est bornée ; la queue est bornée à l'exposant `1` (croissance `e^{a/2}`, la même
  -- que la paire de l'arrivée peut avoir), et `𝓛_G(queue)` aussi ; la queue est bornée UNIFORMÉMENT ⟺ tout zéro au-dessus
  -- de la coupure est en ligne (lecture du pôle, aucun côté dérivé) ; sous cette hypothèse `𝓛_G(queue)` est bornée par
  -- `4 Σ|w|·budget·L` ; l'enveloppe d'exposant `1` dépasse toute constante. Le complément infini n'est donc borné par
  -- aucun théorème indépendant : sa borne uniforme est « tous les zéros au-dessus de l'arrivée en ligne ».
  have hTailSplit := fun (H : ℝ) {u : ℝ} (hu : 0 < u) => signal_eq_head_add_tail H hu
  have hHeadBounded := fun {u : ℝ} (hu : 0 < u) => headSignal_norm_le_of_onLine hPastOn hu
  have hTailLinear := fun (H : ℝ) {u : ℝ} (hu : 0 < u) => tailSignal_norm_le_linear H hu
  have hTailBoundedIff := tailSignal_bounded_iff (rZeroHeight l.1)
  have hGrammarTailLinear := fun (w : ℕ → ℝ) (r₀ m : ℕ) {L T a Lmax : ℝ} (hL : 0 ≤ L)
    (hgap : ∀ j : Fin m, rPrimeGapLogRatio (r₀ + j) ≤ Lmax) (hLmax : 0 ≤ Lmax) (ha : Lmax < a) =>
    grammarTail_norm_le_linear w r₀ m (T := T) (H := rZeroHeight l.1) hL hgap hLmax ha
  have hGrammarTailUniformOfOn := fun (w : ℕ → ℝ) (r₀ m : ℕ) {L T a : ℝ} (hL : 0 ≤ L)
    (hOn : ∀ σ : ExplicitIndex, rZeroHeight l.1 < |(σ : ℂ).im| → (σ : ℂ).re ≤ 1 / 2)
    (ha : ∀ j : Fin m, rPrimeGapLogRatio (r₀ + j) < a) =>
    grammarTail_uniform_of_following_onLine w r₀ m (T := T) hL hOn ha
  have hTailEnvelopeUnbounded := fun {L Lmax : ℝ} (hB : 0 < followingBudget (rZeroHeight l.1)) (hL : 0 < L) (K : ℝ) =>
    grammarTail_linear_envelope_unbounded (Lmax := Lmax) hB hL K
  -- (VIII) LA PRÉMISSE ASTRA RÉEXAMINÉE (auteur, 2026-10-19 : « reprends cette piste et élabore avec l'état actuel des
  -- théorèmes » ; `AstraSeparation`, définitions historiques de `66162218` / `624a0c53` / `5a4c5efc` transcrites). L'identité
  -- `π/T` d'Astra est intra-Tour ; la séparation inter-Tours au stade `0` est `< π/(2T_e)` sur TOUT passage, ON ou OFF, donc la
  -- prémisse Astra (égalité ou inégalité) est fausse sur tout passage, sur le premier passage authentique, et sur le passage
  -- engagé lui-même (départ ON, historique ON, montée, arrivée basse) ; sa forme à même hauteur ⟺ aucun passage de même
  -- hauteur ⟺ RH ; le théorème laissé ouvert par Astra a toutes ses hypothèses satisfaites sur le passage sortant de même
  -- hauteur ; T2/R-PASS est réfuté (le passage premier du passage de même hauteur n'est pas nul : rang `+ 1`).
  have hAstraIntra := fun (z : TrueZero) (k₀ k₁ : ℤ) => ringJump_logWidth z k₀ k₁
  have hAstraHalfPitch := passage_interMemberLogSeparation_lt p hE hL
  have hAstraEngagedFalse := engaged_astra_inequality_false p hE hOn hV hHist hL hBelow
  have hAstraPremiseRefuted := @astra_premise_refuted
  have hAstraSameHeightIff := astra_sameHeight_premise_iff_riemannHypothesis
  have hAstraOpenSatisfied := fun (q : TZeroPassage) (hqE : 0 < rZeroHeight q.zEarlierMember) (hqH : HorizontalPassage q) =>
    astra_open_hypotheses_satisfied q hqE hqH
  have hRPassRefuted := fun (q : TZeroPassage) (hqE : 0 < rZeroHeight q.zEarlierMember) (hqH : HorizontalPassage q) =>
    rpass_transport_refuted q hqE hqH
  have hAstraLowProfile := low_arrival_astra_profile l hZone
  have hMirrorNullPassage := mirror_pair_null_passage_profile l hZone
  -- (VIII bis) LE CERTIFICAT D'ASTRA AFFÛTÉ ET RÉDUIT (auteur, 2026-10-19 : « une paire de zéros distincts de même hauteur ⟹
  -- séparation < un demi-pas ; ce qui échoue, c'est de lui opposer le pas complet π/T, intra-Tour »). Affûté : à même hauteur
  -- `sep < 1/T²` (toute paire de vrais zéros, `0 < β < 1`), paire miroir comprise ; la réciproque du certificat est fausse
  -- (tout passage vertical a aussi `sep < π/(2T_e)`, `hAstraHalfPitch`). Prémisse de test = PLANCHER `1/T_l² ≤ sep` sur le
  -- passage sortant de `l` : elle ferme le cas bas (`hSepFloorCloses`) ; sa forme à même hauteur ⟺ RH ; sa forme verticale
  -- est fausse sur toute paire ON serrée (écart ≤ 1/2) : elle n'est ni dérivable ni posable ; sa réduction maximale est le but.
  have hAstraSharp := fun (z w : TrueZero) (hT : rZeroHeight w.1 = rZeroHeight z.1) =>
    sameHeight_interMemberLogSeparation_lt_inv_sq z w hT
  have hMirrorSepSharp := mirror_pair_separation_lt_inv_sq l
  have hSepFloorCloses := sep_floor_closes_low_arrival l hZone
  have hSepFloorReduction := sep_floor_premise_reduction l hZone
  have hSepFloorSameHeightIff := sep_floor_sameHeight_iff_riemannHypothesis
  have hCloseOnPairSep := fun (e' l' : TrueZero) (hOnE' : rZeroRadialPosition e'.1 = 1 / 2)
      (hOnL' : rZeroRadialPosition l'.1 = 1 / 2) (hlt : rZeroHeight e'.1 < rZeroHeight l'.1)
      (hClose : rZeroHeight l'.1 ≤ rZeroHeight e'.1 + 1 / 2) =>
    close_onLine_pair_separation_lt_inv_sq e' l' hOnE' hOnL' hlt hClose
  -- (VIII ter) LES TROIS FORCES DE LA CONTRADICTION « AMPLIFICATION MIROIR OFF » (auteur, 2026-10-19, textes collés : régime
  -- ON du premier zéro + contraintes exactes des premiers + largeurs et fréquences des contacts ⟹ impossibilité de
  -- l'amplification miroir ; distinguer amplification OFF / incompatibilité individuelle / impossibilité collective).
  -- Aucun zéro fabriqué, aucune fréquence ON prise pour référence : seule la paire authentique `l`, `l*` est comparée.
  -- (1) amplification OFF = certificat compilé (`hAmpRatio`, `hAmpCertificate`) ; (2) incompatibilité individuelle = le
  -- miroir dans le champ ⟺ `β_l = 1/2`, CARACTÉRISATION du but (`hMirrorFieldIff`), contacts satisfaits par toute `β ≤ 1/2`
  -- (`hContactsAdmit`) ; (3) impossibilité collective : groupe fini compilé (`hFiniteGroup`), complément infini ⟺ borne du
  -- reste d'exposant `< 1 − β_l` (`hInfiniteCloses`), exposant 1 seul acquis (`hAcquiredExp`) ; composition des trois
  -- ingrédients vraie pour toute arrivée basse (`hThreeIngredients`), forme universelle ⟺ RH (`hUniversalIff`).
  have hAmpRatio := fun (x : ℝ) (hx : 0 < x) => mirror_over_low_amplitude_ratio l hx
  have hAmpCertificate := fun (x : ℝ) (hx : 0 < x) hfar =>
    off_amplification_certificate (z₁ := canonicalZero 1) h₁ hZone hx hfar
  have hBothPresent := mirror_pair_both_present l hZone
  have hMirrorFieldIff := fun (hρ : ‖zeroPoint (canonicalZero 1)‖ ≤ ‖zeroPoint l‖) =>
    mirror_insideField_iff_onLine h₁ hZone.le hρ
  have hMirrorFieldCloses := fun (hρ : ‖zeroPoint (canonicalZero 1)‖ ≤ ‖zeroPoint l‖) hm =>
    mirror_captivity_closes h₁ hZone hρ hm
  have hContactsAdmit := contact_constraints_admit_low hL (thm_zeroRadialPosition_positive _) hZone.le
  have hFiniteGroup := fun (H H'' θ C : ℝ) (hz : H < rZeroHeight l.1) (hz' : rZeroHeight l.1 ≤ H'')
      (hθ : θ < 1 - rZeroRadialPosition l.1) => finite_group_noncompensation (C := C) l hz hz' hθ
  have hInfiniteCloses := infinite_complement_closes l
  have hAcquiredExp := acquired_exponent_not_below_mirror l
  have hThreeIngredients := fun (hρ : ‖zeroPoint (canonicalZero 1)‖ ≤ ‖zeroPoint ⟨p.zLaterMember, hL⟩‖) =>
    three_ingredients_any_low_arrival h₁ p hL hV hρ
  have hUniversalIff := universal_no_amplification_iff_riemannHypothesis h₁
  -- (VIII quater) CONSERVATION DE LA DOMINATION DU PREMIER ZÉRO AU COURS DES ÉVÉNEMENTS PREMIERS (auteur, 2026-10-19, huitième
  -- message : « la domination du premier zéro est-elle une borne démontrée pour tous les événements futurs et pour le signal
  -- pertinent ? »). Réponse compilée : (2) oui pour tout membre ON, à tout événement premier et à tout x > 0 (`hOnDominatedEvents`,
  -- `hOnDominationConserved`) ; (4) la croissance du miroir dépasse nécessairement cette domination à un nombre premier au-delà
  -- de l'horizon exact (`hMirrorExceedsAtPrime`) ; (3)–(4) la domination conservée sur la paire de l'arrivée ⟺ `β_l = 1/2`
  -- (`hDomConservedIff`), elle ferme le cas bas (`hDomConservedCloses`) ; pour tous les membres ⟺ RH (`hDomAllIff`) ; pour
  -- le signal collectif au-dessus du départ, aucune domination compilée, la borne √x des suivants ferme (`hCollectiveCloses`).
  have hOnDominatedEvents := fun (w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2) (n : ℕ) =>
    onLine_dominated_at_every_prime_event h₁ w hw n
  have hOnDominationConserved := fun (w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2) =>
    dominationConserved_of_onLine h₁ w hw
  have hMirrorExceedsAtPrime := mirror_exceeds_domination_at_prime (z₁ := canonicalZero 1) h₁ hZone
  have hDomConservedIff := fun (hρ : ‖zeroPoint (canonicalZero 1)‖ ≤ ‖zeroPoint l‖) =>
    dominationConserved_iff_onLine h₁ hZone.le hρ
  have hDomConservedCloses := fun (hρ : ‖zeroPoint (canonicalZero 1)‖ ≤ ‖zeroPoint l‖) hDom =>
    first_off_arrival_impossible_of_domination h₁ hZone hρ hDom
  have hDomAllIff := dominationConserved_all_iff_riemannHypothesis h₁
  have hCollectiveCloses := collective_signal_domination_closes ⟨p.zEarlierMember, hE⟩ l hTe hZone
  -- OBLIGATION, FERMÉE SOUS LA PRÉMISSE (auteur, 2026-10-19, treizième message) : loi de transport grammatical entre le
  -- premier événement de dépassement et le premier événement de la cellule suivante de la Tour d'arrivée (`hRaccord` :
  -- fréquence, rencontres authentiques, besoin d'amplitude des deux cellules successives). Fréquence et rencontres sont
  -- acquises pour toute position radiale ; le besoin entre deux cellules distinctes est ⟺ `β_l = 1/2`
  -- (`grammarTransportAtEvent_iff_onLine`) ; avec l'entrelacement des contacts de l'arrivée sous ceux de la Tour du zéro
  -- initial (`GrammarTransportNested`, rappel de l'auteur) : l'entrelacement borne seulement le facteur radial par le décalage
  -- de hauteur au premier indice (`interlacing_iff_factor_bound`) et tient pour toute arrivée basse dans la fenêtre
  -- (`interlacing_blind_of_window`) ; la loi contredit le certificat de dépassement ; quantifiée ⟺ RH.
  -- CONDITION UNIQUE CORRIGÉE (auteur, 2026-10-19, dix-septième message) : la fréquence de l'arrivée augmente
  -- (`arrival_frequency_rises`) et ses rencontres propres sont entrelacées en deçà de celles de la Tour engagée par la
  -- hauteur seule (`arrival_meetings_inward_by_height`), pour toute position radiale ; la condition (`hRaccord`, UNE
  -- condition) : à la rencontre propre de l'arrivée qui encadre le premier événement de dépassement, le déplacement par
  -- rapport à la Tour engagée est celui de la hausse de fréquence seule, sans part radiale ; la géométrie, démontrée
  -- séparément, donne sous un demi une part radiale strictement positive (`low_arrival_impossible_of_noRadialShift`).
  have hObligation : False := by
    have hlEq : l = ⟨p.zLaterMember, hL⟩ := Subtype.ext hl
    exact low_arrival_impossible_of_noRadialShift _ _ hOn hZone _ (by rw [hlEq]; exact hRaccord)
  exact hObligation


/-- **La plus petite question qui reste** (auteur, 2026-10-15 : « l'amplitude incompatible du signal d'un OFF qui se
trouverait dans la zone < 1/2 ; je ne veux que de l'amplitude dans le lock »). Sous l'ancre, sur un passage qui monte
depuis un membre ON, tout l'historique sous l'arrivée étant ON : un zéro `w` à la hauteur du zéro suivant dont le signal a
une amplitude strictement DÉCROISSANTE le long des premiers (`hDecr`, la zone sous un demi lue sur l'amplitude ; déduite
dans `radial_conservation_anchored` pour l'arrivée elle-même). Acquis en contexte, et eux seuls : (1) la courbe des
premiers est reproduite exactement par la somme des vrais zéros ; (2) aucun remplacement, en amplitude ou en fréquence, ne
la reproduit ; (3) le miroir de `w`, à la même hauteur, a un signal d'amplitude strictement croissante ; (4) la courbe
des premiers impose son amplitude à chaque signal (les écarts imposent, le signal subit) ; (5) amplitude de la courbe
démontrée depuis les seuls poids des premiers : échelle `x` entière (l'échelle de la ligne, mesurée E310–E312 sur douze
fréquences, n'est pas démontrée) ; (6) jusqu'à la hauteur 28, tout signal est d'amplitude constante, donc `w` est au-dessus de 28.
VERROU DU COUPLE (auteur, 2026-10-16) composé en contexte : espacement des rencontres ⟹ fréquence ; position d'une rencontre
⟹ `β` ; rapport des besoins ⟹ `β` ; les deux lectures s'accordent ; à fréquence fixée, besoin constant ⟺ rencontres non
translatées ; une dérive du besoin déplace tous les points de passage ; un changement de fréquence contracte l'espacement sans
translation rigide ; aucune solution diagonale. RESTE, non fermé : la DEMANDE de la courbe des premiers au signal placé à la
hauteur du zéro suivant, en forme de couple : deux rencontres consécutives (positions fixées par `(T, β)`) où le besoin de
synchronisation est le même (sens unique : écarts ⟶ signaux ⟶ position ; aucune lecture ; aucune expérience à zéro fabriqué
n'est une preuve). FRÉQUENCE DÉJÀ OCCUPÉE (auteur, 2026-10-16) composée en contexte : seul candidat OFF en dessous d'une demi,
à une fréquence que les signaux des écarts n'atteignent pas sur l'axe critique. FRÉQUENCES ENGENDRÉES (E321, 2026-10-16)
composées en contexte : rigidités renversées, premiers ⟶ zéro (`Terminal/GeneratedFrequency.lean`). RÉIMPLÉMENTATION
(2026-10-16, après audit : la première version désignait la fréquence et la rencontre par un zéro déjà donné) : les objets
du dernier pas sont écrits depuis le reste des premiers `smoothedRemainder` et la fréquence seules (`PrimeSignalRepresentation`,
`ArithmeticFrequency`, `meetingOf`, `ArithmeticMeeting`), et leur correspondance avec les objets spectraux est démontrée par
l'unicité de la décomposition du reste, sans fixer aucun exposant. But : dans toute représentation du reste des premiers, tout
signal de poids non nul de fréquence `T_w` rencontre l'axe à la position de la ligne,
`ArithmeticMeeting T_w (lineContact T_w 0)`. TROIS OBJETS DISTINCTS (audit collé par l'auteur, 2026-10-16) : ce but porte sur
la rencontre PROPRE de chaque composante (`arithmeticMeeting_individual`), non sur la rencontre du signal collectif avec son fond
(`CollectiveMeeting`, relation sur toutes les composantes à la fois, `collectiveMeeting_component_eq_neg_rest`) ni sur
l'événement premier (`PrimeEvent`, saut de pente `Λ(N)` de la primitive arithmétique, porté par la somme infinie seule : toute
somme finie de composantes est dérivable, `finite_components_differentiableAt`). Les mesures de E321–E322 lisent une rencontre
de la seconde espèce (zéros d'une contribution filtrée du signal collectif, calibrés sur un contrôle ON) : elles ne portent pas ce
but. La flèche manquante est la contrainte que les événements imposent simultanément aux rencontres propres et à leur résultante. -/
theorem off_signal_amplitude_incompatible (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hV : VerticalPassage p) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hHist : ∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2)
    (w : TrueZero) (hw : rZeroHeight w.1 = rZeroHeight p.zLaterMember)
    (hDecr : ∀ x y : ℝ, 1 ≤ x → x < y → pairAmplitude w y < pairAmplitude w x)
    (hRaccord : ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
        NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
          (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩))) : False := by
  -- Interface conservée (2026-10-17) : la décroissance de l'amplitude de `w` donne `β_w < 1/2` ; l'arrivée est la plus basse de
  -- sa fibre (historique ON : un zéro plus bas à la même hauteur la précéderait et serait ON) ; donc l'arrivée est sous un demi,
  -- et la question se ramène sans perte au but minimal `arrival_low_contradiction`.
  have hZone : rZeroRadialPosition w.1 < 1 / 2 := by
    by_contra hge
    push_neg at hge
    have h12 := hDecr 1 2 le_rfl (by norm_num)
    rw [pairAmplitude_eq w one_pos, pairAmplitude_eq w (by norm_num : (0 : ℝ) < 2)] at h12
    have hmono : (1 : ℝ) ^ (rZeroRadialPosition w.1 - 1 / 2) ≤ (2 : ℝ) ^ (rZeroRadialPosition w.1 - 1 / 2) :=
      Real.rpow_le_rpow zero_le_one (by norm_num) (by linarith)
    have hs : 0 < Real.sqrt (rZeroRadialPosition w.1 ^ 2 + rZeroHeight w.1 ^ 2) := by
      apply Real.sqrt_pos.mpr
      have := w.2
      positivity
    have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 2)) hs.le
    linarith
  have hL : 0 < rZeroHeight p.zLaterMember := lt_of_lt_of_le hE (passage_height_le p)
  have hBelow : rZeroRadialPosition p.zLaterMember < 1 / 2 := by
    by_contra hge
    push_neg at hge
    rcases eq_or_ne w.1 p.zLaterMember with heq | hne
    · rw [← heq] at hge; linarith
    have hprec : PZeroMemberPrecedes w.1 p.zLaterMember :=
      (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mpr (Or.inr ⟨hw, by linarith⟩)
    have := hHist w hprec
    linarith
  exact arrival_low_contradiction h₁ p hE hV hOn hHist hL hBelow (hRaccord p hV hOn hHist hE hL)
  -- FERMÉ sous la prémisse minimale (2026-10-19). Historique de la question (2026-10-17) : le déplacement radial de rencontre du signal des premiers de fréquence `T_w` (la hauteur du zéro suivant, `hw`) est
  -- nul : `log(meetingOf p) − log(lineContact T_w 0) = 0` pour tout signal `p` de poids non nul et de fréquence `T_w` dans toute
  -- représentation du reste des premiers `smoothedRemainder`. Le signal n'est désigné que par sa fréquence. Sens unique : écarts
  -- exacts ⟶ fréquence engendrée ⟶ rencontre. La compensation d'un déplacement vertical par un déplacement radial est réalisable
  -- pour la rencontre du départ ; ce qui manque est la raison, lue sur les écarts exacts, pour laquelle la rencontre du signal à
  -- cette fréquence est la rencontre attendue (part radiale nulle). Mesuré (E321–E322) sur des rencontres collectives filtrées,
  -- non sur la rencontre propre. Non démontré. Non fermé.

/-- **Obligation 2, conservation de la partie réelle au passage authentique** (auteur, 2026-10-09). Sous l'ancre, sur un
passage `p : e → l` qui monte depuis un membre ON de hauteur positive, tout membre qui précède l'arrivée étant ON, le
membre atteint conserve la partie réelle. Fermé depuis la plus petite question : le côté haut est exclu (compilé,
`passage_entry_radial_le_half`) ; une arrivée dans la zone sous un demi aurait un signal d'amplitude strictement
décroissante (compilé, `pairAmplitude_eq`), incompatible avec la reproduction (`off_signal_amplitude_incompatible`).
Conditionnel à cette question. -/
theorem radial_conservation_anchored (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hV : VerticalPassage p) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hHist : ∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2)
    (hRaccord : ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
        NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
          (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩))) :
    rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember := by
  have hL : 0 < rZeroHeight p.zLaterMember := lt_of_lt_of_le hE (passage_height_le p)
  have hLe : rZeroRadialPosition p.zLaterMember ≤ 1 / 2 := passage_entry_radial_le_half p hV
  rw [hOn]
  apply le_antisymm hLe
  by_contra h
  have hBelow : rZeroRadialPosition p.zLaterMember < 1 / 2 := lt_of_not_ge h
  have hDecr : ∀ x y : ℝ, 1 ≤ x → x < y →
      pairAmplitude ⟨p.zLaterMember, hL⟩ y < pairAmplitude ⟨p.zLaterMember, hL⟩ x := by
    intro x y hx hxy
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
    rw [pairAmplitude_eq ⟨p.zLaterMember, hL⟩ hx0, pairAmplitude_eq ⟨p.zLaterMember, hL⟩ (lt_trans hx0 hxy)]
    have hs : 0 < Real.sqrt (rZeroRadialPosition p.zLaterMember ^ 2 + rZeroHeight p.zLaterMember ^ 2) := by
      apply Real.sqrt_pos.mpr
      positivity
    apply div_lt_div_of_pos_right _ hs
    have := Real.rpow_lt_rpow_of_neg hx0 hxy (by linarith : rZeroRadialPosition p.zLaterMember - 1 / 2 < 0)
    linarith
  exact off_signal_amplitude_incompatible h₁ p hE hV hOn hHist ⟨p.zLaterMember, hL⟩ rfl hDecr hRaccord

/-- La loi de conservation radiale renforcée (historique entièrement ON sous l'arrivée), sans l'ancre en hypothèse
explicite : conditionnelle à l'ancre (obligation 1) et à l'obligation 2. -/
theorem conservation_law (hRaccord : ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
        NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
          (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩))) :
    ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
    rZeroRadialPosition p.zEarlierMember = 1 / 2 →
    (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
    rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember :=
  fun p hE hV hOn hHist => radial_conservation_anchored anchor_canonical_one p hE hV hOn hHist hRaccord

/-! ## Chaîne unique vers RH (conditionnelle) -/

/-- Chaque membre canonique est ON et chaque passage canonique monte (récurrence du build principal). Conditionnel. -/
theorem canonical_all_onLine (hRaccord : ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
        NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
          (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩))) :
    ∀ n : ℕ, rZeroRadialPosition (canonicalMember n).1 = 1 / 2 :=
  canonical_onLine_of_history_conservation anchor_canonical_one (conservation_law hRaccord)

/-- Chaque passage canonique monte (de l'historique ON, `canonical_vertical_of_history`). Conditionnel. -/
theorem canonical_all_vertical (hRaccord : ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
        NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
          (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩))) :
    ∀ n : ℕ, VerticalPassage (canonicalPassage n) := fun n =>
  canonical_vertical_of_history fun k _ => canonical_all_onLine hRaccord k

/-- Tout membre supérieur est ON (par la récurrence canonique, sans passer par RH). Conditionnel. -/
theorem all_upper_onLine (hRaccord : ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
        NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
          (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩))) :
    ∀ w : TrueZero, rZeroRadialPosition w.1 = 1 / 2 := fun w => by
  obtain ⟨n, rfl⟩ := canonicalMember_surjective w
  exact canonical_all_onLine hRaccord n

/-- **Captivité universelle dans le champ du premier : CONSÉQUENCE démontrée de la conservation, jamais supposée.**
Conditionnel. -/
theorem universal_captivity_anchored (hRaccord : ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
        NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
          (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩))) :
    ∀ w : TrueZero, ∀ u : ℝ, 0 ≤ u →
    pairAmplitude w (Real.exp u) ≤ pairAmplitude (canonicalZero 1) (Real.exp u) :=
  universal_captivity_of_all_onLine anchor_canonical_one (all_upper_onLine hRaccord)

/-- **LA DEMANDE (auteur, 2026-10-28) : la fréquence attendue.** Sur tout passage, toute position radiale, la fréquence du
signal suivant est attendue par les premiers et strictement supérieure à la fréquence courante. C'est l'UNIQUE obligation
ouverte de la chaîne ; elle ne nomme jamais la position radiale. Un miroir n'est pas un signal suivant : il n'apporte aucune
fréquence nouvelle. Ce qu'il reste à démontrer, depuis les seuls écarts des premiers : écarts exacts ⟹ points de rencontre
obligés du signal suivant ⟹ espacement ⟹ fréquence strictement supérieure (`frequency_of_spacing`, `arithmeticFrequency_iff`). -/
def ExpectedFrequencyRises : Prop :=
  ∀ p : TZeroPassage, rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember

/-- **Fermeture directe par la demande** : un passage miroir horizontal a ses deux membres à la même fréquence ; la demande
exige une fréquence strictement supérieure. -/
theorem horizontalMirror_excluded_of_expectedFrequency (hDemand : ExpectedFrequencyRises) (p : TZeroPassage) :
    ¬ HorizontalMirrorRealization p :=
  fun hHMR => (ne_of_lt (hDemand p)) hHMR.1


/-- **NON-INSERTION AUTHENTIQUE ET CASCADE DES CONTACTS (mission de l'auteur, 2026-10-19) : la cascade authentique engagée
depuis le premier zéro ON n'admet aucun passage miroir horizontal.** Énoncé universel : équivalent à l'exclusion horizontale,
donc à RH (`horizontalExclusion_iff_riemannHypothesis`) ; ce n'est pas une réduction démontrée. Démarche : un passage miroir
horizontal porte un zéro hors ligne ; la PREMIÈRE rupture de l'énumération canonique est alors un membre sous un demi atteint
en montant depuis un membre ON, tout l'historique ON (`exists_first_regime_break`, `first_regime_break_profile`) ; le pas qui
le quitte existe (`canonicalPassage`) et y est GELÉ (même hauteur, décalages constants, `low_arrival_freezes_cascade`). Le gel
y est démontré ; le but restant est `False` : il manque une implication indépendante que ce gel contredirait. -/
theorem authentic_engaged_cascade_forbids_insertion (hDemand : ExpectedFrequencyRises) (p : TZeroPassage) :
    ¬ HorizontalMirrorRealization p := by
  intro hHMR
  -- Un passage miroir horizontal porte un zéro hors ligne : RH est fausse.
  have hNot : ¬ RiemannHypothesis := fun hRH => by
    rcases hHMR.2.2 with hOff | hOff
    · exact hOff (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _)
    · exact hOff (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _)
  -- Première rupture authentique : membre canonique `n` sous un demi, tout l'historique ON (aucune insertion).
  obtain ⟨n, hLow, hHist⟩ := exists_first_regime_break hNot
  obtain ⟨_hn1, _hE0, _hOn0, hLater, hV0, _hHistW, _⟩ :=
    first_regime_break_profile anchor_canonical_one hLow hHist
  -- Le pas authentique qui quitte la rupture : `canonicalMember n → canonicalMember (n + 1)`.
  have hJ : (canonicalPassage (n - 1)).zLaterMember = (canonicalPassage n).zEarlierMember := hLater
  have hβ : rZeroRadialPosition (canonicalPassage (n - 1)).zLaterMember < 1 / 2 := hLater ▸ hLow
  have hEq : 0 < rZeroHeight (canonicalPassage n).zEarlierMember := (canonicalMember n).2
  have hLq : 0 < rZeroHeight (canonicalPassage n).zLaterMember := (canonicalMember (n + 1)).2
  -- GEL : le pas sortant garde la hauteur, ses décalages d'entrelacement sont constants.
  have hFreeze := low_arrival_freezes_cascade hJ hV0 hβ hEq hLq
  -- Lecture de fréquence du pas sortant et contacts exacts du membre de rupture.
  have hStepReading := interlacing_frequency_reading ⟨(canonicalPassage n).zEarlierMember, hEq⟩
    ⟨(canonicalPassage n).zLaterMember, hLq⟩ 0
  have hMirror := mirror_contacts_never_coincide (z := canonicalMember n) hLow
  -- RECONSTRUCTION ARITHMÉTIQUE EXACTE (compilé, toute position radiale) sur les deux membres du pas sortant : la contribution
  -- de chacun est imposée par le reste des premiers moins la part fixe des autres vrais zéros, en tout `x > 1`
  -- (`imposed_contribution_eq`) ; sur chaque écart premier, le reste des premiers est la somme de tous les vrais zéros
  -- (`localSynchronization`).
  have hImposedBreak := fun {x : ℝ} (hx : 1 < x) => imposed_contribution_eq (canonicalMember n) hx
  have hImposedNext := fun {x : ℝ} (hx : 1 < x) => imposed_contribution_eq (canonicalMember (n + 1)) hx
  have hGapSync := localSynchronization
  -- CONTRAINTES NOUVELLES (2026-10-25), inconditionnelles, vraies aussi dans le monde témoin (elles ne séparent pas) :
  -- bande sans zéro de rhv3_lean (port PNT+, `ZetaZeroFree`) appliquée à la rupture et à son miroir,
  -- `A/log⁹T < β_n < 1/2 < 1 − β_n < 1 − A/log⁹T` ; profil démontré de toute perturbation OFF (fibre finie, miroir distinct
  -- après la rupture, pas sortant gelé, déficit de comptage ≥ 2, toute sortie en montant depuis la hauteur part d'un membre
  -- `β > 1/2`).
  have hT3 : 3 < rZeroHeight (canonicalMember n).1 := by
    have := low_member_above_15 (canonicalMember n) hLow; linarith
  have hBand := low_member_band_of_height (canonicalMember n) hT3 hLow
  have hProfile := off_disturbance_profile (canonicalMember n) hLow (canonicalPassage (n - 1)) hLater hV0
  -- Le gel est DÉMONTRÉ sur ce pas (`hFreeze` : `δ₁ = δ₀`) ; y demander `δ₁ < δ₀` serait demander `False` déguisé.
  -- Le but est donc `False` tel quel : il manque une implication indépendante (lue sur la reconstruction exacte des
  -- premiers, non sur la position de la rupture) que ce gel contredirait. Sa dérivation depuis la composition
  -- des contraintes du contexte reste ouverte ; ceci ne démontre pas leur compatibilité conjointe avec OFF.
  have hFrozen : interlacingOffset ⟨(canonicalPassage n).zEarlierMember, hEq⟩ ⟨(canonicalPassage n).zLaterMember, hLq⟩ (0 + 1) =
      interlacingOffset ⟨(canonicalPassage n).zEarlierMember, hEq⟩ ⟨(canonicalPassage n).zLaterMember, hLq⟩ 0 := hFreeze.2 0
  -- Raccord géométrique causal : le contact est celui de l'ancrage authentique
  -- de la cellule. La contradiction exige encore le certificat arithmétique
  -- strict `occurrence * exp (π/T) ≤ expectedMinimumPrime` sur ce même objet.
  have hGeometricImplication :
      (occurrence (canonicalMember n) : ℝ) *
          Real.exp (Real.pi / rZeroHeight (canonicalMember n).1) ≤
          (expectedMinimumPrime (canonicalMember n) : ℝ) →
        (pivotPair (canonicalMember n) (occurrence (canonicalMember n))).lastRayContact <
          (expectedMinimumPrime (canonicalMember n) : ℝ) := by
    intro hMargin
    exact ConstraintCorrelation.pivot_upper_below_expected_of_exp_margin
      (canonicalMember n) (by exact_mod_cast (occurrence_prime (canonicalMember n)).pos) hMargin
  -- Implication conditionnelle disponible, NON consommée vers `False` :
  -- ni sa marge ni la lecture de P dans la cellule de S ne sont démontrées.
  -- L'alias hGeometricCell supprimé ne constituait aucune composition.
  -- FERMETURE PAR LA FRÉQUENCE ATTENDUE (auteur, 2026-10-28) : le pas sortant de la rupture est gelé, même fréquence
  -- (`hFreeze`, première composante) ; la demande exige une fréquence strictement supérieure. Tout le contexte ci-dessus
  -- (rupture, miroir, bande, reconstruction, gel) est conservé comme trace : la contradiction ne porte que sur la fréquence.
  have hSameFrequency : rZeroHeight (canonicalPassage n).zEarlierMember =
      rZeroHeight (canonicalPassage n).zLaterMember := hFreeze.1
  exact absurd hSameFrequency (ne_of_lt (hDemand (canonicalPassage n)))

/-- **TDD, CASCADE PAR LA SEULE FRÉQUENCE (auteur, 2026-10-19, dix-septième et dix-huitième messages) : une seule prémisse,
une seule condition, posée comme théorème sans preuve.** Les zéros forment un ensemble stable qui reproduit exactement, à
l'infini, les écarts des premiers ; le besoin passe d'un zéro au suivant : nouvelle hauteur, nouvelle fréquence. Acquis, toute
position radiale, et mis en contexte : le zéro suivant LIT le zéro précédent (`next_zero_reads_previous` : successeur
déterminé, rang suivant, premier minimum attendu du précédent, fréquence du précédent retrouvée depuis l'accroissement de ses
rencontres) et sa fréquence monte (`cascadeIncrement_neg`). Condition : à sa rencontre propre qui encadre le premier événement
de dépassement, le déplacement par rapport au précédent est celui de la hausse de fréquence seule, sans part radiale
(`NoRadialShift`). Contradiction démontrée séparément (`low_arrival_impossible_of_noRadialShift`). Aucun `sorry`, aucune
prémisse nommée, aucune sonde : la chaîne est ROUGE. -/
theorem radius_premise (hDemand : ExpectedFrequencyRises) : ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
        NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
          (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩)) := by
  intro p hV hOn hHist hE hL
  -- LIAISON (auteur, 2026-10-19, dix-huitième message) : le zéro suivant lit le zéro précédent (successeur déterminé, rang
  -- suivant, premier minimum attendu, fréquence du précédent lue sur l'accroissement de ses rencontres), toute position
  -- radiale ; la fréquence monte (accroissement strictement négatif). Il reste : la cascade par la seule fréquence.
  have hReads := next_zero_reads_previous p hE hL
  have hFrequencyUp := cascadeIncrement_neg ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hV
  -- MODE STABLE ENGAGÉ DÈS LE PREMIER ZÉRO (auteur, 2026-10-19, dix-neuvième message) : le premier zéro est ON, son miroir
  -- est annulé (coïncide avec lui) ; le départ du passage est ON.
  have hAnchor : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2 := anchor_canonical_one
  -- STABILITÉ DE LA CASCADE (compilé, toute position radiale) : la part radiale du déplacement des rencontres est la même à
  -- toutes les rencontres ; la cascade la transporte sans la modifier.
  have hStable := radialShiftAt_const ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
  -- ENTRELACEMENT (compilé) : une rencontre exacte donne à tout indice `k ≥ 1` un contact du suivant strictement en deçà de
  -- celui du précédent, déplacé par la seule hausse de fréquence.
  have hInterlaced := fun {k₀ : ℤ} (h : NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ k₀) {k : ℤ}
    (hk : 1 ≤ k) => exact_meetings_interlaced ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hV h hk
  -- CHAÎNE DE LECTURE ET D'ENROULEMENT (auteur, 2026-10-19, vingt et unième message ; compilé, toute position radiale) :
  -- hauteurs et fréquences ordonnées, lecture du précédent, enroulement propre des deux Tours (contacts
  -- `exp((arctan(T/β) + kπ)/T)`, pas `π/T`), enroulement du suivant dans le précédent à l'infini, compensation signée
  -- (colonnes de comptage additives, contribution imposée par le reste des premiers et les autres vrais zéros).
  have hChain := passage_reading_chain p hV hE hL
  -- Pas complet dans une Tour, moins d'un demi-pas entre deux Tours (`interMemberLogSeparation_lt_half_pitch`).
  have hPitch := same_tower_full_pitch_inter_tower_half ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hV.le
  -- La part radiale est positive ou nulle à toutes les rencontres (départ ON, arrivée au plus à un demi).
  have hNonneg := radialShiftAt_nonneg_of_on_departure p hV hE hL hOn
  -- LIAISON D'ENTRELACEMENT (auteur, 2026-10-19, vingt-deuxième message ; compilé, toute position radiale) : lecture de
  -- fréquence par les décalages `δ_k`, décalages strictement décroissants, signe de la contribution du suivant lu sur les
  -- contacts du précédent, même signe des deux contributions au premier contact du suivant, raccord au premier partagé,
  -- lecture récursive du suivant depuis le précédent et deux décalages.
  have hLink := And.intro (interlacing_frequency_reading ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩)
    (And.intro (interlacingOffset_strictAnti ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hV)
    (And.intro (next_sign_at_previous_contact ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩)
    (And.intro (previous_reinforces_at_next_first_contact ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hV.le)
    (And.intro (next_contribution_at_shared_prime p hE hL)
      (recursive_reading ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩)))))
  -- RÉDUCTION DE LA PRÉMISSE (compilé, `noRadialShift_of_one_sided`) : il suffit qu'à UNE rencontre le contact du suivant
  -- ne dépasse pas la position fixée par la seule hausse de fréquence ; l'exactitude à toutes en découle.
  -- CONTINUATION DE LA CASCADE (auteur, 2026-10-19, vingt-troisième message ; compilé) : la condition réduite ⟺ tout pas qui
  -- quitte l'arrivée continue la cascade (décalages d'entrelacement strictement décroissants, fréquence qui monte)
  -- (`cascade_continuation_iff`) ; une première arrivée sous un demi GÈLE la cascade au pas suivant (même hauteur, décalages
  -- constants, `low_arrival_freezes_cascade`), et ce pas existe (`low_arrival_outgoing_exists`).
  have hFreeze := fun (q : TZeroPassage) (hJ : p.zLaterMember = q.zEarlierMember) (hLq : 0 < rZeroHeight q.zLaterMember)
    (hβ : rZeroRadialPosition p.zLaterMember < 1 / 2) => low_arrival_freezes_cascade hJ hV hβ (hJ ▸ hL) hLq
  refine noRadialShift_of_one_sided p hV hE hL hOn ((cascade_continuation_iff p hV hE hL hOn).mpr ?_) _
  intro q hJ hLq k
  -- Lecture de fréquence du pas suivant : `δ_{k+1} − δ_k = π/T_s − π/T_l` ; la hauteur ne recule jamais.
  have hStepReading := interlacing_frequency_reading ⟨q.zEarlierMember, hJ ▸ hL⟩ ⟨q.zLaterMember, hLq⟩ k
  have hHeightLe := passage_height_le q
  -- LA CONTRADICTION UNIQUE, CELLE DES CONTACTS (auteur, 2026-10-19) : la cascade de fréquences place les contacts du zéro
  -- d'après strictement en deçà de ceux du zéro suivant, en laissant la place aux zéros qui suivent (décalages
  -- strictement décroissants) ; une arrivée basse gèlerait la cascade (contacts translatés, décalages constants). Les deux
  -- sont incompatibles : la cascade seule exclut l'arrivée basse.
  have hCascadeContradiction := fun (hδ : interlacingOffset ⟨q.zEarlierMember, hJ ▸ hL⟩ ⟨q.zLaterMember, hLq⟩ (k + 1) <
      interlacingOffset ⟨q.zEarlierMember, hJ ▸ hL⟩ ⟨q.zLaterMember, hLq⟩ k)
    (hβ : rZeroRadialPosition p.zLaterMember < 1 / 2) => (ne_of_lt hδ) ((hFreeze q hJ hLq hβ).2 k)
  -- CASCADE DE FRÉQUENCES, ENSEMBLE COHÉRENT ET STABLE (auteur, 2026-10-19 ; compilé, `FrequencyCascadeStability.lean`) :
  -- la cascade stricte à l'infini ⟺ RH ; le zéro suivant est lié aux deux voisins (prédécesseur et successeur uniques, lecture
  -- de la fréquence du précédent, fréquence du zéro d'après lue depuis la sienne : aucun ajustement) ; un miroir est placé de
  -- manière inégale (deux β miroirs distincts, l'un avant, l'autre après, même fréquence) et rompt la cascade stricte.
  -- Sur la ligne la cascade stricte est démontrée, à tout rang (`strict_frequency_cascade_onLine`) ; seul un miroir hors ligne
  -- pourrait la rompre (`strict_frequency_cascade_iff_riemannHypothesis`).
  have hStrictOnLine := @strict_frequency_step_onLine
  have hStrictCascadeOnLine := strict_frequency_cascade_onLine
  have hStrictCascadeIff := strict_frequency_cascade_iff_riemannHypothesis
  have hBothNeighbours := zero_linked_to_both_neighbours hJ hE hL (hJ ▸ hL) hLq
  have hMirrorInstability := fun (hOff : rZeroRadialPosition p.zLaterMember ≠ 1 / 2) =>
    And.intro (mirror_placed_unequally ⟨p.zLaterMember, hL⟩ hOff) (mirror_creates_instability ⟨p.zLaterMember, hL⟩ hOff)
  -- FERMETURE PAR LA NON-INSERTION AUTHENTIQUE : aucun passage miroir horizontal, donc le pas sortant monte, donc la cascade
  -- continue (`heightProgression_of_horizontalExclusion`, `cascade_step_rises_iff`). Conditionnel au but ouvert ci-dessus.
  exact (cascade_step_rises_iff q _ hLq k).mpr
    (heightProgression_of_horizontalExclusion (fun q h => authentic_engaged_cascade_forbids_insertion hDemand q h) q)

/-- **Terme visé** : `RiemannHypothesis`, par l'ancre, la conservation radiale et la captivité (conséquence). Dépend du
théorème ouvert `radius_premise` : conditionnel, jamais inconditionnel tant que ce but est ouvert. -/
theorem riemannHypothesis_terminal (hDemand : ExpectedFrequencyRises) : RiemannHypothesis :=
  riemannHypothesis_of_captivity_onLine anchor_canonical_one (universal_captivity_anchored (radius_premise hDemand))

/-- **Force de la demande** : elle entraîne RH par la chaîne, et RH l'entraîne (sur la droite, la fréquence monte
strictement à tout pas, `passage_height_lt_of_onLine`). Elle n'est posée qu'en hypothèse ; elle n'est pas dérivée. -/
theorem expectedFrequencyRises_iff_riemannHypothesis : ExpectedFrequencyRises ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_terminal, fun hRH p => passage_height_lt_of_onLine p
    (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _) (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _)⟩

/-- **La prémisse minimale est EXACTEMENT de la force de RH** : elle est impliquée par RH (sous RH tout membre est ON et son
miroir est lui-même, dominé à tout premier : `mirror_dominated_at_primes_of_riemannHypothesis`) et elle entraîne RH par la
chaîne. Elle n'est posée en hypothèse que des théorèmes conditionnels ; elle n'est pas dérivée. -/
theorem mirror_domination_premise_iff_riemannHypothesis :
    (∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
        NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
          (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩))) ↔
    RiemannHypothesis :=
  ⟨fun h => riemannHypothesis_of_captivity_onLine anchor_canonical_one (universal_captivity_anchored h),
   fun hRH p _ hOn _ hE hL =>
    noRadialShift_of_riemannHypothesis _ _ hOn hRH _⟩

/-- **Vacuité de la prémisse sur toute arrivée ON** : elle ne demande rien aux membres ON ; elle ne mord qu'à une première
rupture de régime (arrivée sous un demi, miroir distinct au-dessus). -/
theorem mirror_domination_premise_vacuous_onLine (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hOnE : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hOnL : rZeroRadialPosition p.zLaterMember = 1 / 2) :
    NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
      (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩)) :=
  noRadialShift_of_onLine _ _ hOnE hOnL _

/-- **La forme à un premier (livraison précédente) entraîne la forme à un point** : un premier au-delà de l'horizon est un
point au-delà de l'horizon. -/
theorem localRaccord_premise_of_one_prime_premise
    (hPrime : ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ hL : 0 < rZeroHeight p.zLaterMember, ∃ q : ℕ, Nat.Prime q ∧
        mirrorHorizon (canonicalZero 1) ⟨p.zLaterMember, hL⟩ < q ∧
        ‖zeroTerm (mirrorMember ⟨p.zLaterMember, hL⟩) (q : ℝ)‖ ≤ firstField (canonicalZero 1) (q : ℝ)) :
    ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
        NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
          (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩)) :=
  fun p hV hOn hHist hE hL => (noRadialShift_iff_onLine _ _ hOn _).mpr <| (localRaccord_iff_onLine _ _).mp <| localRaccord_of_one_point anchor_canonical_one _ (passage_entry_radial_le_half p hV)
    (one_point_of_one_prime (hPrime p hV hOn hHist hL))

/-- **La forme universelle (tout premier) entraîne la forme à un point** (point 19 du texte collé, puis onzième message) :
la chaîne n'exige plus que la forme à un point. -/
theorem localRaccord_premise_of_all_primes_premise
    (hAll : ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (hL : 0 < rZeroHeight p.zLaterMember) (q : ℕ), Nat.Prime q →
        ‖zeroTerm (mirrorMember ⟨p.zLaterMember, hL⟩) (q : ℝ)‖ ≤ firstField (canonicalZero 1) (q : ℝ)) :
    ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
        NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
          (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩)) :=
  fun p hV hOn hHist hE hL => (noRadialShift_iff_onLine _ _ hOn _).mpr <| (localRaccord_iff_onLine _ _).mp <| localRaccord_of_one_point anchor_canonical_one _ (passage_entry_radial_le_half p hV)
    (one_point_of_one_prime (one_prime_of_all_primes (hAll p hV hOn hHist hL)))

/-- **La forme d'amplitude à un point (livraison précédente) entraîne la forme de contact** : sur toute arrivée d'un
passage qui monte (`β_l ≤ 1/2`), la domination en un point au-delà de l'horizon donne l'arrivée en ligne, donc le raccord
local. -/
theorem localRaccord_premise_of_one_point_premise
    (hPoint : ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ hL : 0 < rZeroHeight p.zLaterMember, ∃ x : ℝ,
        mirrorHorizon (canonicalZero 1) ⟨p.zLaterMember, hL⟩ < x ∧
        ‖zeroTerm (mirrorMember ⟨p.zLaterMember, hL⟩) x‖ ≤ firstField (canonicalZero 1) x) :
    ∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
        NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
          (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩)) :=
  fun p hV hOn hHist hE hL => (noRadialShift_iff_onLine _ _ hOn _).mpr <| (localRaccord_iff_onLine _ _).mp <| localRaccord_of_one_point anchor_canonical_one _ (passage_entry_radial_le_half p hV)
    (hPoint p hV hOn hHist hL)

/-- **La loi de transport entrelacée et le raccord local de contact sont la même prémisse** (treizième message, avec
l'entrelacement des contacts sous ceux de la Tour du zéro initial) : sur toute arrivée, chacune est ⟺ `β_l = 1/2`. -/
theorem radius_premise_iff_localRaccord_premise :
    (∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
        NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
          (memberStage ⟨p.zLaterMember, hL⟩ (firstExceedPrime (canonicalZero 1) ⟨p.zLaterMember, hL⟩))) ↔
    (∀ p : TZeroPassage, VerticalPassage p → rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      ∀ (_ : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
        LocalRaccord (canonicalZero 1) ⟨p.zLaterMember, hL⟩) :=
  ⟨fun h p hV hOn hHist hE hL => (localRaccord_iff_onLine _ _).mpr
      ((noRadialShift_iff_onLine _ _ hOn _).mp (h p hV hOn hHist hE hL)),
   fun h p hV hOn hHist hE hL => (noRadialShift_iff_onLine _ _ hOn _).mpr
      ((localRaccord_iff_onLine _ _).mp (h p hV hOn hHist hE hL))⟩

#print axioms riemannHypothesis_terminal
#print axioms expectedFrequencyRises_iff_riemannHypothesis
#print axioms horizontalMirror_excluded_of_expectedFrequency
#print axioms radius_premise_iff_localRaccord_premise
#print axioms mirror_domination_premise_iff_riemannHypothesis
#print axioms mirror_domination_premise_vacuous_onLine
#print axioms localRaccord_premise_of_all_primes_premise
#print axioms localRaccord_premise_of_one_prime_premise
#print axioms localRaccord_premise_of_one_point_premise

/-- Poursuite du régime engagé : au-dessus d'un membre ON atteint en montant, tout membre est ON, atteint en montant et
quitté en montant (`engaged_persists_to_infinity`, loi fournie par la conservation radiale). Conditionnel. -/
theorem regime_persists (hDemand : ExpectedFrequencyRises)
    {o : TZeroPassage} (hE : 0 < rZeroHeight o.zLaterMember) (ho : VerticalPassage o)
    (hOn : rZeroRadialPosition o.zLaterMember = 1 / 2) :
    ∀ w : TNonTrivialZetaZero, PZeroMemberPrecedes o.zLaterMember w →
      rZeroRadialPosition w = 1 / 2 ∧
      (∃ q : TZeroPassage, q.zLaterMember = w ∧ VerticalPassage q) ∧
      (∀ q : TZeroPassage, q.zEarlierMember = w → VerticalPassage q ∧ ¬ HorizontalPassage q) :=
  engaged_persists_to_infinity (heightOnly_of_riemannHypothesis (riemannHypothesis_terminal hDemand)) hE ho hOn

/-- Conservation du régime ON : aucun changement de régime à aucune jonction. Conditionnel. -/
theorem regime_conserved (hDemand : ExpectedFrequencyRises) : PNoRegimeChange :=
  noRegimeChange_iff_riemannHypothesis.mpr (riemannHypothesis_terminal hDemand)

/-- Progression par la hauteur : tout passage parti de la moitié supérieure monte. Conditionnel. -/
theorem height_progression (hDemand : ExpectedFrequencyRises) :
    ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p :=
  allVertical_of_noRegimeChange (regime_conserved hDemand)

/-- Forme canonique sans historique : la loi simple découle de la chaîne (`conservation_of_riemannHypothesis`). Conditionnel. -/
theorem radial_conservation_authentic (hDemand : ExpectedFrequencyRises)
    (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hV : VerticalPassage p) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember :=
  conservation_of_riemannHypothesis (riemannHypothesis_terminal hDemand) p hE hV hOn

/-- **Forme de l'auteur** : `VerticalPassage o ∧ o.zLaterMember = p.zEarlierMember ∧ β_e = 1/2 ⟹ β_l = β_e`, par
`engaged_regime_kept` dans sa portée exacte. Conditionnel (conséquence de la chaîne). -/
theorem radial_conservation_engaged (hDemand : ExpectedFrequencyRises)
    {o p : TZeroPassage} (hJ : o.zLaterMember = p.zEarlierMember)
    (ho : VerticalPassage o) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember :=
  engaged_law_of_vertical_law (conservation_of_riemannHypothesis (riemannHypothesis_terminal hDemand)) hJ ho hE hOn

/-- Contrôle : le prolongement du comptage (fermeture disponible du déficit de comptage) découle de la chaîne ; il ne
la remplace pas. Conditionnel. -/
theorem counting_extension_all (hDemand : ExpectedFrequencyRises) (H : ℝ) : CountingExtension H :=
  extension_of_riemannHypothesis (riemannHypothesis_terminal hDemand) H


/-! ## Premiers membres : contrôle composé avec enveloppes, anneaux, symétrie, contacts, passages et grammaire

Directive de l'auteur (2026-10-10) : composer immédiatement le contrôle des premiers membres (`CountingDeficit` §7) avec
les acquis fermés des modules importés, sans les réécrire. Frontière radiale (`OnRadialRing`), ordre des contacts
(`EngagedAllConstraints`, `TowerTwoSidedRoom`) et symétrie normalisée (`EngagedAllConstraints`) restent distincts ; leurs
liens démontrés sont repris tels quels. Fermé : comptages démontrés dans la bibliothèque (consolidation du 2026-10-11). -/





end RHV6Fresh
