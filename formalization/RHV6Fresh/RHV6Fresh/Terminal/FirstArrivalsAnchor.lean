/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.BoxCountHeight
import RHV6Fresh.Terminal.ZetaBox.Final
import RHV6Fresh.Terminal.ZetaBox22.Final
import RHV6Fresh.Terminal.ZetaBox28.Final
import RHV6Fresh.Terminal.CountingDeficit
import RHV6Fresh.Terminal.GrammaticalRaccordJump
import RHV6Fresh.Terminal.ZetaParameters
import RHV6Fresh.Terminal.LocalGlobalGapMatrix
import RHV6Fresh.Terminal.LowNextZeroSignatures
import RHV6Fresh.Terminal.AmplitudeStableSynchronization

/-!
# L'ancre et les trois premières arrivées, objets permanents de l'architecture inverse (E335 ; auteur, 2026-10-18)

Module expérimental distinct, importé, NON composé dans la chaîne. Il ne dépend pas du fichier de la chaîne : les trois
comptages sont recomposés ici depuis les certificats de rectangles de `ζ` (`ZB.Cert.*`, générateurs e192/e196) et le
principe de l'argument (`upperCount_of_zeta_boxes`).

Trois statuts, tenus séparés :

* CERTIFIÉ PAR COMPTAGE, démontré en Lean (`three_arrivals_certified`) :
  - `N(15) = 1`, `N(22) = 2`, `N(28) = 3` ;
  - les trois premiers membres canoniques sont dans les bandes `]0, 15]`, `]15, 22]`, `]22, 28]`, donc `T₁ < T₂ < T₃` ;
  - ils sont sur la ligne et coïncident avec leur miroir ;
  - tout zéro de hauteur `≤ 28` est sur la ligne : aucun OFF supplémentaire dans la région certifiée.

  Ces faits viennent de `ζ` entière (rectangles, enroulement, parité du déficit), non des premiers. E185 et E176 (Arb)
  restent les certificats externes historiques de la première bande et des trois premières.
* IDENTITÉS ANALYTIQUES, vraies pour toute position radiale, appliquées au régime initial (`initial_regime`,
  `initial_normalized_modes`, `initial_contacts_on_line`, `initial_gap_entries_le`) :
  - mode normalisé `cos(T_j u)` d'amplitude un ;
  - contacts égaux aux contacts de ligne ;
  - entrées de la matrice locale bornées par l'enveloppe de ligne.
* ESTIMATIONS NUMÉRIQUES (E335, hors Lean) : `T̂_j`, `d̂_j`, phases, coefficients modaux, depuis les seuls premiers.
  Aucune n'est un terme Lean ; aucune ne remplace un comptage.

Transmission : le régime initial `d₁ = d₂ = d₃ = 0` n'est la prémisse d'aucun énoncé sur la quatrième arrivée. Les propriétés
structurelles (miroir, conjugaison, réalité sur la ligne, premier zéro ON) ne la transmettent pas
(`initial_regime_not_structurally_transmitted`, monde `regimeWitness`). Pour une arrivée suivante de paramètres inconnus, la
matrice locale–globale et les transitions sont satisfaites quelle que soit sa position radiale
(`next_arrival_matrix_any_radial`, `transitions_no_constraint_beyond_telescoping`). La conservation d'amplitude est
caractérisée (`individualAmplitudeRigidity_iff`) et n'est pas dérivée. Le but `arrival_low_contradiction` est inchangé.
-/

namespace RHV6Fresh

open RHV3Lean Complex Filter

/-! ## §1 Comptages des trois premières bandes (recomposés, fermés) -/

/-- `N(15) = 1`, depuis les deux rectangles de la première bande. -/
theorem arrivals_count_fifteen : upperCountWithMultiplicity 15 = 1 := by
  obtain ⟨hZ₁, hZ₂, hW₁, hW₂⟩ := ZB.Cert.zeta_box_certificate
  exact upperCount_of_zeta_boxes (σ₀ := 1 / 4) (t₁ := 1) (T₀ := 15) (T := 15) (K := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hZ₁ hZ₂ hW₁ hW₂ hZ₁ hZ₂
    (by rw [hW₁]; norm_num) hW₂

/-- `N(22) = 2`. -/
theorem arrivals_count_twentytwo : upperCountWithMultiplicity 22 = 2 := by
  obtain ⟨hZ₁₀, hZ₂₀, hW₁₀, hW₂₀⟩ := ZB.Cert.zeta_box_certificate
  obtain ⟨hZ₁, hZ₂, hW₁, hW₂⟩ := ZB.Cert.H22.zeta_box_certificate
  exact upperCount_of_zeta_boxes (σ₀ := 1 / 4) (t₁ := 1) (T₀ := 15) (T := 22) (K := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hZ₁₀ hZ₂₀ hW₁₀ hW₂₀ hZ₁ hZ₂
    (by rw [hW₁]; norm_num) hW₂

/-- `N(28) = 3`. -/
theorem arrivals_count_twentyeight : upperCountWithMultiplicity 28 = 3 := by
  obtain ⟨hZ₁₀, hZ₂₀, hW₁₀, hW₂₀⟩ := ZB.Cert.zeta_box_certificate
  obtain ⟨hZ₁, hZ₂, hW₁, hW₂⟩ := ZB.Cert.H28.zeta_box_certificate
  exact upperCount_of_zeta_boxes (σ₀ := 1 / 4) (t₁ := 1) (T₀ := 15) (T := 28) (K := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hZ₁₀ hZ₂₀ hW₁₀ hW₂₀ hZ₁ hZ₂
    (by rw [hW₁]; norm_num) hW₂

theorem arrivals_count_zero : upperCountWithMultiplicity 0 = 0 := by
  unfold upperCountWithMultiplicity
  rw [Finset.sum_eq_zero]
  intro ρ hρ
  have h := mem_upperWindow.mp hρ
  linarith [h.2.1, h.2.2]

/-! ## §2 Les trois arrivées certifiées par comptage -/

/-- **Trois arrivées certifiées** (comptage, démontré) : bandes de hauteur, ordre strict, ligne, miroir annulé, et aucun
zéro hors de la ligne de hauteur `≤ 28`. -/
theorem three_arrivals_certified :
    (0 < rZeroHeight (canonicalMember 0).1 ∧ rZeroHeight (canonicalMember 0).1 ≤ 15) ∧
    (15 < rZeroHeight (canonicalMember 1).1 ∧ rZeroHeight (canonicalMember 1).1 ≤ 22) ∧
    (22 < rZeroHeight (canonicalMember 2).1 ∧ rZeroHeight (canonicalMember 2).1 ≤ 28) ∧
    (∀ j < 3, rZeroRadialPosition (canonicalMember j).1 = 1 / 2 ∧
      mirrorMember (canonicalMember j) = canonicalMember j) ∧
    (∀ w : TrueZero, rZeroHeight w.1 ≤ 28 → rZeroRadialPosition w.1 = 1 / 2) :=
  first_three_canonical_onLine (by norm_num) (by norm_num) (by norm_num)
    arrivals_count_zero arrivals_count_fifteen arrivals_count_twentytwo arrivals_count_twentyeight

/-- L'ancre : le premier membre canonique (le plus bas de la moitié supérieure) est sur la ligne, coïncide avec son miroir,
et sa hauteur est dans `]0, 15]`. Sa valeur `14,1347…` est une estimation numérique (E335, E185), non un terme Lean. -/
theorem anchor_permanent :
    rZeroRadialPosition (canonicalZero 1).1 = 1 / 2 ∧ mirrorMember (canonicalZero 1) = canonicalZero 1 ∧
      sUpperZerosBelow (canonicalZero 1).1 = ∅ ∧
      0 < rZeroHeight (canonicalZero 1).1 ∧ rZeroHeight (canonicalZero 1).1 ≤ 15 :=
  ⟨(three_arrivals_certified.2.2.2.1 0 (by norm_num)).1, (three_arrivals_certified.2.2.2.1 0 (by norm_num)).2,
    canonicalZero_one_bottom, three_arrivals_certified.1.1, three_arrivals_certified.1.2⟩

/-! ## §3 Le régime initial, explicite -/

/-- **Régime initial** : `T₁ < T₂ < T₃` et `d₁ = d₂ = d₃ = 0` (`d = β − 1/2`), avec la rigidité d'amplitude individuelle
de chacune des trois arrivées. Certifié par comptage ; rien n'y est supposé. -/
theorem initial_regime :
    rZeroHeight (canonicalMember 0).1 < rZeroHeight (canonicalMember 1).1 ∧
    rZeroHeight (canonicalMember 1).1 < rZeroHeight (canonicalMember 2).1 ∧
    (∀ j < 3, rZeroRadialPosition (canonicalMember j).1 - 1 / 2 = 0 ∧
      IndividualAmplitudeRigidity (canonicalMember j)) := by
  obtain ⟨h0, h1, h2, hOn, _⟩ := three_arrivals_certified
  refine ⟨by linarith [h0.2, h1.1], by linarith [h1.2, h2.1], fun j hj => ?_⟩
  have h := (hOn j hj).1
  exact ⟨by rw [h]; ring, (individualAmplitudeRigidity_iff _).mpr h⟩

/-- **Modes normalisés du régime initial** (identité analytique appliquée) : pour chacune des trois arrivées, la densité de
comptage transportée et normalisée est exactement `cos(T_j u)`, d'amplitude un. -/
theorem initial_normalized_modes {j : ℕ} (hj : j < 3) {u : ℝ} (hu : 0 < u) :
    -(u * Real.exp (-u / 2) / 2) * (countingModulationDensity (canonicalMember j) (Real.exp u) * Real.exp u) =
      Real.cos (rZeroHeight (canonicalMember j).1 * u) := by
  rw [normalized_mode_density _ hu, (three_arrivals_certified.2.2.2.1 j hj).1, sub_self, zero_mul, Real.exp_zero,
    one_mul]

/-- **Contacts du régime initial** : les contacts des trois arrivées sont les contacts de ligne de leur hauteur. -/
theorem initial_contacts_on_line {j : ℕ} (hj : j < 3) (k : ℤ) :
    contactMinusAt (canonicalMember j) k = lineContact (rZeroHeight (canonicalMember j).1) k :=
  (contact_eq_line_iff_onLine _ k).mpr (three_arrivals_certified.2.2.2.1 j hj).1

/-- **Entrées de la matrice locale du régime initial** : sur tout écart `[a, b]`, `1 < a`, la contribution d'une des trois
arrivées est bornée par l'enveloppe de ligne `2 a^{−1/2} ∫_a^b dt/log t`. -/
theorem initial_gap_entries_le {j : ℕ} (hj : j < 3) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    |cellModulation (canonicalMember j) a b| ≤ 2 * a ^ (-(1 / 2 : ℝ)) * cellBackground a b :=
  cellModulation_abs_le_onLine _ (three_arrivals_certified.2.2.2.1 j hj).1 ha hab

/-! ## §4 Arrivée suivante de paramètres inconnus -/

/-- **La matrice ne lit pas la position radiale d'une arrivée suivante** : pour tout vrai zéro `z` (toute position radiale)
ajouté à une famille finie, l'identité `D_n = S_{n,N} + R_{n,N}` reste vraie sur tout écart premier, le complément étant
recalculé. Ce que l'ajout change sur l'écart est exactement la colonne de `z` (`gapComplement_insert`). -/
theorem next_arrival_matrix_any_radial [DecidableEq TrueZero] (s : Finset TrueZero) (z : TrueZero) (hz : z ∉ s)
    (C : ℝ → ℝ) (F : TrueZero → ℂ → ℂ) (a b : ℝ) :
    gapComplement C (insert z s) F a b = gapComplement C s F a b -
      (-2 * (F z (zeroPoint z * (Real.log b : ℂ))).re - -2 * (F z (zeroPoint z * (Real.log a : ℂ))).re) :=
  gapComplement_insert hz C F a b

/-- **Le régime initial n'est pas transmis structurellement** : une fonction fixe, avec miroir, conjugaison et réalité
sur la ligne, a un zéro sur la ligne à la hauteur 1, aucun autre à cette hauteur, aucun entre 1 et 2, puis deux jumeaux
hors de la ligne à la hauteur 2 (`regimeWitness_regime_changes`). La conservation, si elle est vraie pour `ζ`, doit lire
les poids exacts des premiers. -/
theorem initial_regime_not_structurally_transmitted :
    regimeWitness (1 / 2 + Complex.I) = 0 ∧
    (∀ s : ℂ, regimeWitness s = 0 → s.im = 1 → s = 1 / 2 + Complex.I) ∧
    (∀ s : ℂ, regimeWitness s = 0 → ¬ (1 < s.im ∧ s.im < 2)) ∧
    regimeWitness (1 / 4 + 2 * Complex.I) = 0 ∧
    regimeWitness (3 / 4 + 2 * Complex.I) = 0 :=
  regimeWitness_regime_changes

/-! ## §5 La première rupture hypothétique : où elle peut être, ce qu'elle coûte, ce qui ne la voit pas -/

/-- Aucun membre bas jusqu'à `28` (`W(28) = 0`), par le comptage des trois bandes. -/
theorem lowCount_twentyeight_eq_zero : lowCount 28 = 0 :=
  (lowCount_eq_zero_iff 28).mpr fun w hw hβ => by
    have := three_arrivals_certified.2.2.2.2 w hw; linarith

/-- **Profil d'une première rupture hypothétique** : tout vrai zéro de position radiale `< 1/2` est au-dessus de `28`, et à
sa hauteur le comptage vaut au moins `5` (les trois arrivées ON, plus le membre bas et son miroir), avec un déficit
`N − N₀ ≥ 2`. Sa colonne dans la matrice locale est bornée sur tout écart par `2 a^{β−1} ∫ dt/log t`, enveloppe plus
FAIBLE que celle de la ligne. Sur tout horizon fini `X`, la signature d'amplitude propre s'efface quand `d → 0`. La
signature discrète (comptage) existe pour toute profondeur ; la signature d'amplitude sur un horizon fini n'en a pas.
Rien de ce profil n'est contradictoire : c'est la forme exacte de ce qu'il faudrait interdire. -/
theorem first_rupture_profile (w : TrueZero) (hβ : rZeroRadialPosition w.1 < 1 / 2) :
    28 < rZeroHeight w.1 ∧ 3 + 2 ≤ upperCountWithMultiplicity (rZeroHeight w.1) ∧
      2 ≤ zeroCountDeficit (rZeroHeight w.1) ∧
      (∀ a b : ℝ, 1 < a → a ≤ b →
        |cellModulation w a b| ≤ 2 * a ^ (rZeroRadialPosition w.1 - 1) * cellBackground a b ∧
        2 * a ^ (rZeroRadialPosition w.1 - 1) * cellBackground a b ≤ 2 * a ^ (-(1 / 2 : ℝ)) * cellBackground a b) := by
  obtain ⟨h1, h2, h3⟩ := low_after_on_band arrivals_count_twentyeight lowCount_twentyeight_eq_zero w hβ
  refine ⟨h1, h2, h3, fun a b ha hab => ⟨cellModulation_abs_le w ha hab, ?_⟩⟩
  have hB := cellBackground_nonneg ha hab
  have hpow : a ^ (rZeroRadialPosition w.1 - 1) ≤ a ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le ha.le (by linarith)
  nlinarith

/-- **Condition nécessaire et suffisante pour interdire la première rupture, sous sa forme exacte** : aucun vrai zéro
n'est bas ⟺ RH. La forme locale (au-dessus de `28`, depuis l'historique ON) est le but `arrival_low_contradiction` de la
chaîne ; sous forme quantifiée elle a la force de RH. Les identités de ce module (matrice, transitions, régime initial)
sont toutes vraies pour une arrivée basse : aucune n'est cette condition. -/
theorem first_rupture_forbidden_iff :
    (∀ w : TrueZero, ¬ rZeroRadialPosition w.1 < 1 / 2) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_all_canonical_onLine fun n _ => by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact h _ hlt
      · have hm := h (mirrorMember (canonicalZero n))
        apply hm
        rw [mirrorMember_radial]
        linarith
  · intro hRH w hw
    have := thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1
    linarith

/-! ## §6 Rupture sous conservation intégrale : compatibilité finie, compatibilité globale -/

/-- **Ce que la reconstruction exacte exclut et ce qu'elle n'exclut pas.** (i) Remplacer, dans la famille authentique, un
point `ρ` (multiplicité `m > 0`) par un autre point `ρ' ≠ ρ` en gardant TOUS les autres membres, les premiers et leurs
poids casse la reconstruction du reste lissé en une abscisse `x > 1` : aucune compensation n'est possible sur le champ
complet (`replacement_not_reconstruct`). (ii) La famille authentique, elle, reconstruit le reste quelle que soit la
position radiale de l'arrivée d'un passage (`authentic_family_reconstructs_any_radial`). Une rupture AUTHENTIQUE n'est donc
pas un remplacement : la conservation intégrale des événements premiers, de leurs poids et de la courbe ne l'interdit pas
par elle-même. Sur un nombre fini de fenêtres, l'identité du complément par d'autres modes est une question d'algèbre
linéaire finie (mesurée par E335) ; elle ne dit rien de la compatibilité globale. -/
theorem rupture_finite_vs_global {ρ ρ' : ℂ} (hne : ρ' ≠ ρ) (hre : ρ.re ≤ 1) (hre' : ρ'.re ≤ 1)
    (him : 0 < ρ.im) (him' : 0 < ρ'.im) {m : ℕ} (hm : 0 < m) {k : ℕ} (hk : 1 ≤ k)
    (p : TZeroPassage) {x : ℝ} (hx : 1 < x) :
    (∃ y : ℝ, 1 < y ∧
      ¬ Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo (smoothedCanonicalAt y) k
        (-pointSmoothedPairContribution m ρ y) (pointSmoothedPairContribution m ρ' y) (j + 1))
        atTop (nhds (normalizedSmoothedRemainder y))) ∧
    (smoothedRemainder x = ∑' σ : ExplicitIndex, nontrivialZeroResidueTerm x σ ∧
      (rZeroRadialPosition p.zLaterMember < 1 / 2 ∨ rZeroRadialPosition p.zLaterMember = 1 / 2 ∨
        1 / 2 < rZeroRadialPosition p.zLaterMember)) :=
  ⟨replacement_not_reconstruct hne hre hre' him him' hm hk, authentic_family_reconstructs_any_radial p hx⟩

end RHV6Fresh

#print axioms RHV6Fresh.three_arrivals_certified
#print axioms RHV6Fresh.anchor_permanent
#print axioms RHV6Fresh.initial_regime
#print axioms RHV6Fresh.initial_normalized_modes
#print axioms RHV6Fresh.initial_contacts_on_line
#print axioms RHV6Fresh.initial_gap_entries_le
#print axioms RHV6Fresh.next_arrival_matrix_any_radial
#print axioms RHV6Fresh.initial_regime_not_structurally_transmitted
#print axioms RHV6Fresh.first_rupture_profile
#print axioms RHV6Fresh.first_rupture_forbidden_iff
#print axioms RHV6Fresh.rupture_finite_vs_global
