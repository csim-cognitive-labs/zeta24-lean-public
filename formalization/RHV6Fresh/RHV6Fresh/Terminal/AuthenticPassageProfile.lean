/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.OnCrossReadings
import RHV6Fresh.Terminal.DoubleRigidity
import RHV6Fresh.Terminal.FirstGainPremise
import RHV6Fresh.Terminal.JointParameterReading
import RHV6Fresh.Terminal.RegimeTrigger
import RHV6Fresh.Terminal.RayCapture
import RHV6Fresh.Terminal.CountingDeficit
import RHV6Fresh.Terminal.MirrorPairExactSum
import RHV6Fresh.Terminal.EngagedClosureVerdict
import RHV6Fresh.Terminal.EngagedPersistence
import RHV6Fresh.Terminal.CanonicalEnumeration
import RHV3Lean.Objects.ZetaSmoothedUnsmoothingArithmeticBridge
import RHV3Lean.Objects.ZetaZeroHeightSummability

/-!
# Profil du passage authentique depuis un membre ON engagé (auteur, 2026-10-09)

Cible réorientée par l'auteur : depuis un membre ON engagé, le prochain membre conserve sa partie réelle, sans
supposer ce prochain membre ON. Ce module réunit, en UNE expression commune et FERMÉE (axiomes standard), tout ce que
le passage authentique `p : e → l` impose dès que `e` est ON et que `p` monte :

1. le membre engagé coïncide avec son miroir `ρ ↦ 1 − ρ̄` (hauteur et multiplicité conservées), et
   `ρ = 1 − ρ̄ ⟺ β = 1/2` ;
2. les contacts authentiques de l'arrivée `C_k = exp((φ + kπ)/T)`, `φ = arctan(T/β)`, et leur intervalle
   `log(C_{k+1}/C_k) = π/T` ;
3. l'enveloppe normalisée `A_ρ(x) = 2x^{β−1/2}/‖ρ‖`, sa forme ON `2/√(1/4 + T²) = 2W/√(π² + W²/4)` (`W = π/T`), le
   rapport des enveloppes `A_l/A_e = x^{β_l − 1/2}·‖ρ_e‖/‖ρ_l‖` ;
4. les obligations canoniques de succession, de rang et de raccord (`engaged_event_restriction`,
   `passage_prime_tower_bond`) ;
5. les sollicitations des événements premiers : `L_r = log(p_{r+1}/p_r)`, `Δθ = T·L_r`,
   `A(p_{r+1})/A(p_r) = e^{(β − 1/2)L_r}`, planchers et alternance mod 6 ;
6. la reconstruction arithmétique exacte et toutes les interactions, instanciées sur le canal lissé normalisé
   (`r_n = R − Σ_{j≤n} c_j`, `D_n = ‖c_n‖² + 2⟨r_n, c_n⟩`, `⟨r_n, c_n⟩ = Σ_{n<j≤N}⟨c_j, c_n⟩ + ⟨r_N, c_n⟩`, résidu conservé),
   et le canal arithmétique de rhv3_lean (`psiRecoveredFromZeros_eq_psi`, `smoothed_formula_recovers_weighted_prime_count`,
   `weighted_zetaZeroMultiplicity_imagSquare_summable`).

Le couplage ON de l'arrivée est ÉQUIVALENT à `λ = 1` (`radialFactor_eq_one_iff`) ; aucune de ces identités ne le dérive :
elles sont vraies pour toute position radiale de l'arrivée (la chaîne unique `Terminal/DemonstrationChain.lean` porte l'obligation).

Fermeture disponible, composée ici : ancre ON du premier membre canonique ∧ loi de conservation radiale sur tout
passage qui monte depuis un membre ON ⟹ tout membre supérieur est ON ⟹ `RiemannHypothesis`
(`riemannHypothesis_of_anchor_and_conservation`) ; la loi est impliquée par RH (`conservation_of_riemannHypothesis`),
elle n'est donc pas plus forte que RH. Le déficit de comptage (`Terminal/CountingDeficit.lean`) reste une fermeture
disponible et un résultat de contrôle ; il ne remplace pas la cible.
-/

namespace RHV6Fresh

open RHV3Lean Finset
open scoped ComplexConjugate InnerProductSpace

/-! ## 1. Le membre engagé coïncide avec son miroir -/

/-- `ρ = 1 − ρ̄ ⟺ β = 1/2` : le point fixe de la réflexion est exactement la ligne. -/
theorem mirror_fixed_iff_onLine (z : TrueZero) :
    zeroPoint z = 1 - conj (zeroPoint z) ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, zeroPoint_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, zeroPoint_re, h]; norm_num
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, zeroPoint_im]; ring

/-- **Le membre engagé coïncide avec son miroir**, hauteur et multiplicité conservées. -/
theorem engaged_mirror_annulled {z : TrueZero} (hOn : rZeroRadialPosition z.1 = 1 / 2) :
    mirrorMember z = z ∧
      zeroPoint z = 1 - conj (zeroPoint z) ∧
      rZeroHeight (mirrorMember z).1 = rZeroHeight z.1 ∧
      zetaZeroMultiplicity (zeroPoint (mirrorMember z)) = zetaZeroMultiplicity (zeroPoint z) := by
  refine ⟨mirrorMember_eq_self_of_onLine hOn, (mirror_fixed_iff_onLine z).mpr hOn, mirrorMember_ordinate z, ?_⟩
  rw [zeroPoint_mirrorMember]
  exact zetaZeroMultiplicity_mirrorPoint z.1.2

/-! ## 2. Contacts authentiques et intervalle -/

/-- **Contacts authentiques** `C_k = exp((arctan(T/β) + kπ)/T)` et intervalle `log(C_{k+1}/C_k) = π/T`. -/
theorem authentic_contacts (z : TrueZero) (k : ℤ) :
    contactMinusAt z k =
        Real.exp ((Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) + (k : ℝ) * Real.pi) /
          rZeroHeight z.1) ∧
      Real.log (contactMinusAt z (k + 1)) - Real.log (contactMinusAt z k) = Real.pi / rZeroHeight z.1 :=
  ⟨contactMinusAt_eq_exp z k, contact_log_step z k⟩

/-! ## 3. Enveloppe normalisée et couplage ON -/

/-- **Enveloppe normalisée** `A_ρ(x) = 2x^{β−1/2}/√(β² + T²)` ; en ligne `2/√(1/4 + T²) = 2W/√(π² + W²/4)`,
`W = π/T`. -/
theorem envelope_coupling (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    pairAmplitude z x = 2 * x ^ (rZeroRadialPosition z.1 - 1 / 2) /
        Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) ∧
      (rZeroRadialPosition z.1 = 1 / 2 →
        pairAmplitude z x = 2 / Real.sqrt (1 / 4 + rZeroHeight z.1 ^ 2) ∧
        pairAmplitude z x = 2 * (towerPitch z / Real.sqrt (Real.pi ^ 2 + towerPitch z ^ 2 / 4)) ∧
        towerPitch z = Real.pi / rZeroHeight z.1) := by
  refine ⟨pairAmplitude_eq z hx, fun hOn => ⟨pairAmplitude_onLine z hOn hx, ?_, rfl⟩⟩
  unfold pairAmplitude
  rw [normalizedRadius_onLine_pitch z hOn hx]

/-! ## 5. Sollicitations des événements premiers -/

/-- **Sollicitations d'un événement premier** `L_r = log(p_{r+1}/p_r)` : `Δθ_ρ = T_ρ L_r`,
`A_ρ(p_{r+1})/A_ρ(p_r) = e^{(β_ρ − 1/2) L_r}`, plancher mod 6 de l'écart ordinaire, classe `∈ {0, 2, 4}`. -/
theorem prime_event_solicitations (z : TrueZero) (r : ℕ) (h3 : 3 < fnPrimeAtRank r) :
    phaseIncrement z r = rZeroHeight z.1 * rPrimeGapLogRatio r ∧
      pairAmplitude z (fnPrimeSuccessor r : ℝ) / pairAmplitude z (fnPrimeAtRank r : ℝ) =
        Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * rPrimeGapLogRatio r) ∧
      classFloor (eventClass r) ≤ nPrimeGap r ∧
      (eventClass r = 0 ∨ eventClass r = 2 ∨ eventClass r = 4) :=
  ⟨phaseIncrement_eq_height_mul_ratio z r, pairAmplitude_prime_step z r, primeGap_ge_classFloor r h3,
    eventClass_mem r h3⟩

/-! ## 6. Reconstruction arithmétique exacte et interactions complètes -/

/-- **Reconstruction exacte du canal lissé normalisé sur un support, et toutes les interactions, résidu conservé** :
`Σ_{j≥1} c_j = R` (HasSum), `D_n = ‖c_n‖² + 2⟨r_n, c_n⟩`, `⟨r_n, c_n⟩ = Σ_{n<j≤N}⟨c_j, c_n⟩ + ⟨r_N, c_n⟩`,
`⟨r_n, c_n⟩ = Σ_{j>n}⟨c_n, c_j⟩` (série). -/
theorem exact_reconstruction_profile {m : ℕ} (xs : Fin m → ℝ) (hxs : ∀ i, 1 < xs i) {n N : ℕ} (hn : 1 ≤ n)
    (hnN : n ≤ N) :
    HasSum (fun j => smoothedCanonicalContributions xs (j + 1)) (normalizedSmoothedRemainderVector xs) ∧
      collectiveGain (smoothedCanonicalContributions xs) (normalizedSmoothedRemainderVector xs) n =
        ‖smoothedCanonicalContributions xs n‖ ^ 2 +
          2 * ⟪partialRemainder (smoothedCanonicalContributions xs) (normalizedSmoothedRemainderVector xs) (n + 1),
            smoothedCanonicalContributions xs n⟫_ℝ ∧
      interaction (smoothedCanonicalContributions xs) (normalizedSmoothedRemainderVector xs) n =
        ∑ j ∈ Finset.Ioc n N, ⟪smoothedCanonicalContributions xs j, smoothedCanonicalContributions xs n⟫_ℝ +
          ⟪partialRemainder (smoothedCanonicalContributions xs) (normalizedSmoothedRemainderVector xs) (N + 1),
            smoothedCanonicalContributions xs n⟫_ℝ ∧
      HasSum (fun j => ⟪smoothedCanonicalContributions xs n, smoothedCanonicalContributions xs (j + n + 1)⟫_ℝ)
        (interaction (smoothedCanonicalContributions xs) (normalizedSmoothedRemainderVector xs) n) :=
  ⟨smoothedCanonical_hasSum xs hxs, collectiveGain_eq_own_add_interaction _ _ hn, interaction_eq_tail_add _ _ hnN,
    smoothedCanonical_interaction_hasSum xs hxs hn⟩

/-- **Canal arithmétique de rhv3_lean** : `ψ` reconstruite depuis les zéros (`x ≥ 2`) et comptage PONDÉRÉ des
puissances de premiers (pas le simple comptage des premiers). -/
theorem arithmetic_recovery_profile {x : ℝ} (hx : 2 ≤ x) :
    psiRecoveredFromZeros x = (Chebyshev.psi x : ℂ) ∧
      PiMangoldtFromZeros x = rPiWeighted x ⌊Real.log x / Real.log 2⌋₊ :=
  ⟨psiRecoveredFromZeros_eq_psi hx, smoothed_formula_recovers_weighted_prime_count hx⟩

/-- **Sommabilité des poids des zéros** `Σ m_ρ/|Im ρ|²` (outil de troncature, rhv3_lean). -/
theorem zero_weight_summable :
    Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) * |(ρ : ℂ).im|⁻¹ ^ (2 : ℕ)) :=
  weighted_zetaZeroMultiplicity_imagSquare_summable

/-! ## 4. L'expression commune au passage authentique -/

/-- **Profil du passage authentique** `p : e → l`, `e` ON, `p` monte : miroir annulé au départ ; `β_l ≤ 1/2` ;
succession, rang `+ 1`, premier partagé, intervalle réduit, fenêtre de phase, facteur `λ ≥ 1`, contacts = contacts de
ligne × `λ` ; liaison première (`M^Z = M`, von Mangoldt, registre) ; contacts authentiques de l'arrivée et intervalle ;
enveloppe ON du départ (deux formes) ; rapport des enveloppes ; sollicitations premières de l'arrivée ; couplage ON de
l'arrivée ⟺ `λ = 1`. Toutes les identités valent pour toute position radiale de l'arrivée : aucune ne la fixe. -/
theorem engaged_passage_profile (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hV : VerticalPassage p)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    mirrorMember ⟨p.zEarlierMember, hE⟩ = ⟨p.zEarlierMember, hE⟩ ∧
    zeroPoint ⟨p.zEarlierMember, hE⟩ = 1 - conj (zeroPoint ⟨p.zEarlierMember, hE⟩) ∧
    rZeroRadialPosition p.zLaterMember ≤ 1 / 2 ∧
    (nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
      expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ = occurrence ⟨p.zLaterMember, hL⟩ ∧
      towerPitch ⟨p.zLaterMember, hL⟩ < towerPitch ⟨p.zEarlierMember, hE⟩ ∧
      linePhase (rZeroHeight p.zLaterMember) ≤ (towerMotionOf ⟨p.zLaterMember, hL⟩).phase ∧
      (towerMotionOf ⟨p.zLaterMember, hL⟩).phase - linePhase (rZeroHeight p.zLaterMember) <
        1 / (2 * rZeroHeight p.zLaterMember) ∧
      1 ≤ radialFactor ⟨p.zLaterMember, hL⟩ ∧
      ∀ k : ℤ, contactMinusAt ⟨p.zLaterMember, hL⟩ k =
        lineContact (rZeroHeight p.zLaterMember) k * radialFactor ⟨p.zLaterMember, hL⟩) ∧
    (occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
      Nat.Prime (occurrence ⟨p.zLaterMember, hL⟩) ∧
      ArithmeticFunction.vonMangoldt (occurrence ⟨p.zLaterMember, hL⟩) =
        Real.log (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) ∧
      occurrencePosition ⟨p.zLaterMember, hL⟩ - occurrencePosition ⟨p.zEarlierMember, hE⟩ =
        raccordShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ +
          rZeroHeight p.zEarlierMember * rPrimeGapLogRatio (nZeroSourceIndex p.zEarlierMember)) ∧
    (∀ k : ℤ, contactMinusAt ⟨p.zLaterMember, hL⟩ k =
        Real.exp ((Real.arctan (rZeroHeight p.zLaterMember / rZeroRadialPosition p.zLaterMember) +
          (k : ℝ) * Real.pi) / rZeroHeight p.zLaterMember) ∧
      Real.log (contactMinusAt ⟨p.zLaterMember, hL⟩ (k + 1)) - Real.log (contactMinusAt ⟨p.zLaterMember, hL⟩ k) =
        Real.pi / rZeroHeight p.zLaterMember) ∧
    (∀ x : ℝ, 0 < x →
      pairAmplitude ⟨p.zEarlierMember, hE⟩ x = 2 / Real.sqrt (1 / 4 + rZeroHeight p.zEarlierMember ^ 2) ∧
      pairAmplitude ⟨p.zEarlierMember, hE⟩ x =
        2 * (towerPitch ⟨p.zEarlierMember, hE⟩ /
          Real.sqrt (Real.pi ^ 2 + towerPitch ⟨p.zEarlierMember, hE⟩ ^ 2 / 4)) ∧
      pairAmplitude ⟨p.zLaterMember, hL⟩ x / pairAmplitude ⟨p.zEarlierMember, hE⟩ x =
        x ^ (rZeroRadialPosition p.zLaterMember - 1 / 2) *
          (‖zeroPoint ⟨p.zEarlierMember, hE⟩‖ / ‖zeroPoint ⟨p.zLaterMember, hL⟩‖)) ∧
    (∀ r : ℕ, 3 < fnPrimeAtRank r →
      phaseIncrement ⟨p.zLaterMember, hL⟩ r = rZeroHeight p.zLaterMember * rPrimeGapLogRatio r ∧
      pairAmplitude ⟨p.zLaterMember, hL⟩ (fnPrimeSuccessor r : ℝ) /
          pairAmplitude ⟨p.zLaterMember, hL⟩ (fnPrimeAtRank r : ℝ) =
        Real.exp ((rZeroRadialPosition p.zLaterMember - 1 / 2) * rPrimeGapLogRatio r) ∧
      classFloor (eventClass r) ≤ nPrimeGap r) ∧
    (radialFactor ⟨p.zLaterMember, hL⟩ = 1 ↔ rZeroRadialPosition p.zLaterMember = 1 / 2) := by
  have hLe : rZeroRadialPosition p.zLaterMember ≤ 1 / 2 := passage_entry_radial_le_half p hV
  obtain ⟨hIdx, hShared, hPitch, hPhLo, hPhHi, hRad, _, hContacts⟩ := engaged_event_restriction p hE hL hV hLe
  obtain ⟨hOcc, hPrime, _, hVM, _, hLedger⟩ := passage_prime_tower_bond p hE hL
  obtain ⟨hMirror, hFixed, _, _⟩ := engaged_mirror_annulled (z := ⟨p.zEarlierMember, hE⟩) hOn
  refine ⟨hMirror, hFixed, hLe, ⟨hIdx, hShared, hPitch, hPhLo, hPhHi, hRad, hContacts⟩,
    ⟨hOcc, hPrime, hVM, hLedger⟩, fun k => authentic_contacts _ k, fun x hx => ?_, fun r h3 => ?_,
    radialFactor_eq_one_iff _⟩
  · obtain ⟨_, hOnForms⟩ := envelope_coupling (⟨p.zEarlierMember, hE⟩ : TrueZero) hx
    obtain ⟨h1, h2, _⟩ := hOnForms hOn
    exact ⟨h1, h2, pairAmplitude_ratio_onLine_first _ _ hOn hx⟩
  · obtain ⟨h1, h2, h3', _⟩ := prime_event_solicitations (⟨p.zLaterMember, hL⟩ : TrueZero) r h3
    exact ⟨h1, h2, h3'⟩

/-! ## 7. Fermeture disponible : ancre ∧ conservation radiale ⟹ RH -/

/-- Depuis le membre le plus bas, ON, le passage sortant monte : un passage de même hauteur arriverait sur un membre
haut dont le miroir, bas et de même hauteur, précéderait le membre le plus bas. -/
theorem bottom_exit_vertical (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hBottom : sUpperZerosBelow p.zEarlierMember = ∅)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) : VerticalPassage p := by
  rcases onLine_exit p hOn with hV | ⟨hH, hUp⟩
  · exact hV
  · exfalso
    have hH' : rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember := hH
    have hMem : zMirrorZero p.zLaterMember ∈ sUpperZerosBelow p.zEarlierMember := by
      refine ⟨?_, ?_⟩
      · rw [thm_mirror_sameHeight, ← hH']; exact hE
      · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
        right
        refine ⟨by rw [thm_mirror_sameHeight, hH'], ?_⟩
        rw [thm_mirror_radialPosition, hOn]
        linarith
    rw [hBottom] at hMem
    exact hMem

/-- Le passage canonique de rang `n` : du membre d'index `n` au membre d'index `n + 1`, consécutifs. -/
noncomputable def canonicalPassage (n : ℕ) : TZeroPassage :=
  ⟨(canonicalMember n).1, (canonicalMember (n + 1)).1, canonicalMember_consecutive n⟩

/-- **Récurrence sur l'énumération canonique** : ancre ON ∧ loi de conservation radiale (sur tout passage qui monte
depuis un membre ON de hauteur positive) ⟹ chaque membre canonique est ON et chaque passage canonique monte. -/
theorem canonical_onLine_of_conservation
    (hAnchor : rZeroRadialPosition (canonicalMember 0).1 = 1 / 2)
    (hLaw : ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember) :
    ∀ n : ℕ, rZeroRadialPosition (canonicalMember n).1 = 1 / 2 ∧ VerticalPassage (canonicalPassage n) := by
  intro n
  induction n with
  | zero =>
    exact ⟨hAnchor, bottom_exit_vertical _ (canonicalMember 0).2 canonicalMember_zero_bottom hAnchor⟩
  | succ n ih =>
    obtain ⟨hOn, hV⟩ := ih
    have hNext : rZeroRadialPosition (canonicalMember (n + 1)).1 = 1 / 2 :=
      (hLaw (canonicalPassage n) (canonicalMember n).2 hV hOn).trans hOn
    exact ⟨hNext, (engaged_regime_kept (p := canonicalPassage n) (q := canonicalPassage (n + 1)) rfl hV hNext).1⟩

/-- **Fermeture disponible** : ancre ON du premier membre canonique ∧ loi de conservation radiale ⟹ `RiemannHypothesis`.
Hypothèses explicites, aucune `def P…` ; la loi est l'obligation 2 de la chaîne unique, non dérivée ici. -/
theorem riemannHypothesis_of_anchor_and_conservation
    (hAnchor : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (hLaw : ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember) :
    RiemannHypothesis := by
  apply thm_riemannHypothesis_of_allUpperOnCriticalLine
  intro w
  obtain ⟨n, rfl⟩ := canonicalMember_surjective w
  exact (canonical_onLine_of_conservation hAnchor hLaw n).1

/-- La loi de conservation radiale est impliquée par RH : elle n'est pas plus forte que RH. -/
theorem conservation_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember :=
  fun p _ hV hOn => heightOnly_of_riemannHypothesis hRH p hV hOn

/-- Forme de l'auteur : depuis un membre ON engagé (atteint par un passage qui monte), la loi se réduit au passage
sortant, qui monte par `engaged_regime_kept`. -/
theorem engaged_law_of_vertical_law
    (hLaw : ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember)
    {o p : TZeroPassage} (hJ : o.zLaterMember = p.zEarlierMember) (ho : VerticalPassage o)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember :=
  hLaw p hE (engaged_regime_kept hJ ho (by rw [hJ]; exact hOn)).1 hOn

/-! ## 8. Le premier membre canonique, conservé explicitement dans chaque raccord (auteur, 2026-10-09)

Sous l'ancre ON `β₁ = 1/2` (hypothèse explicite, certifiée hors Lean, obligation 1 de la chaîne unique), sur tout
passage `p : e → l` qui monte depuis un membre ON : hauteur minimale du premier (aucun membre en dessous, `T₁ ≤ T_e ≤ T_l`) ;
enveloppe fixée `A_1 = 2/√(1/4 + T₁²)` sur tout l'horizon ; domination sur l'enveloppe du départ ON, par unité de multiplicité ;
rapport avec l'arrivée `A_l/A_1 = x^{β_l − 1/2}·‖ρ₁‖/‖ρ_l‖` ; contribution SIGNÉE du premier et retrait exact : après son retrait,
toutes les suivantes restituent ensemble le reste résiduel (série, en toute abscisse et sur tout support), `r_1 = R − c_1`,
`D_1 = 2⟨R, c_1⟩ − ‖c_1‖²` ; ses contacts `C_k = exp((arctan 2T₁ + kπ)/T₁)` et ses phases conservés dans le produit avec chaque
membre, interaction du premier avec le complément INFINI (série convergente), planchers de phase relative par événement.
La captivité universelle dans le champ du premier n'est PAS supposée : elle est la conséquence à démontrer
(`universal_captivity_of_all_onLine`) puis à utiliser (`riemannHypothesis_of_captivity_onLine`). -/

/-- **Contraintes de l'ancre au passage authentique.** Toutes compilées ; aucune ne fixe `β_l`. -/
theorem anchor_constraints_at_passage (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hV : VerticalPassage p) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    sUpperZerosBelow (canonicalZero 1).1 = ∅ ∧
    rZeroHeight (canonicalZero 1).1 ≤ rZeroHeight p.zEarlierMember ∧
    rZeroHeight (canonicalZero 1).1 ≤ rZeroHeight p.zLaterMember ∧
    (∀ u : ℝ, pairAmplitude (canonicalZero 1) (Real.exp u) =
      2 / Real.sqrt (1 / 4 + rZeroHeight (canonicalZero 1).1 ^ 2)) ∧
    (∀ x : ℝ, 0 < x →
      pairAmplitude ⟨p.zEarlierMember, hE⟩ x ≤ pairAmplitude (canonicalZero 1) x ∧
      pairAmplitude ⟨p.zLaterMember, hL⟩ x / pairAmplitude (canonicalZero 1) x =
        x ^ (rZeroRadialPosition p.zLaterMember - 1 / 2) *
          (‖zeroPoint (canonicalZero 1)‖ / ‖zeroPoint ⟨p.zLaterMember, hL⟩‖)) ∧
    (∀ x : ℝ, 1 < x →
      HasSum (fun j : ℕ => normalizedSmoothedPairContribution (canonicalZero (j + 2)) x)
        (normalizedSmoothedRemainder x - normalizedSmoothedPairContribution (canonicalZero 1) x)) ∧
    (∀ {m : ℕ} (xs : Fin m → ℝ), (∀ i, 1 < xs i) →
      HasSum (fun j => smoothedCanonicalContributions xs (j + 2))
        (normalizedSmoothedRemainderVector xs - smoothedCanonicalContributions xs 1) ∧
      partialRemainder (smoothedCanonicalContributions xs) (normalizedSmoothedRemainderVector xs) 2 =
        normalizedSmoothedRemainderVector xs - smoothedCanonicalContributions xs 1 ∧
      collectiveGain (smoothedCanonicalContributions xs) (normalizedSmoothedRemainderVector xs) 1 =
        2 * ⟪normalizedSmoothedRemainderVector xs, smoothedCanonicalContributions xs 1⟫_ℝ -
          ‖smoothedCanonicalContributions xs 1‖ ^ 2 ∧
      HasSum (fun j => ⟪smoothedCanonicalContributions xs 1, smoothedCanonicalContributions xs (j + 2)⟫_ℝ)
        (interaction (smoothedCanonicalContributions xs) (normalizedSmoothedRemainderVector xs) 1)) ∧
    (∀ k : ℤ, contactMinusAt (canonicalZero 1) k =
      Real.exp ((Real.arctan (rZeroHeight (canonicalZero 1).1 / rZeroRadialPosition (canonicalZero 1).1) +
        (k : ℝ) * Real.pi) / rZeroHeight (canonicalZero 1).1)) ∧
    (∀ (w : TrueZero) (x : ℝ), 0 < x →
      normalizedPairContribution (canonicalZero 1) x * normalizedPairContribution w x =
        pairAmplitude (canonicalZero 1) x * pairAmplitude w x / 2 *
          (Real.cos ((rZeroHeight (canonicalZero 1).1 - rZeroHeight w.1) * Real.log x -
              (memberPhase (canonicalZero 1) - memberPhase w)) +
            Real.cos ((rZeroHeight (canonicalZero 1).1 + rZeroHeight w.1) * Real.log x -
              (memberPhase (canonicalZero 1) + memberPhase w)))) ∧
    (∀ r : ℕ, 3 < fnPrimeAtRank r →
      |rZeroHeight p.zLaterMember - rZeroHeight (canonicalZero 1).1| *
          Real.log (1 + (classFloor (eventClass r) : ℝ) / (fnPrimeAtRank r : ℝ)) ≤
        |phaseIncrement ⟨p.zLaterMember, hL⟩ r - phaseIncrement (canonicalZero 1) r|) := by
  obtain ⟨n, hn, hne⟩ := canonicalZero_surjective (⟨p.zEarlierMember, hE⟩ : TrueZero)
  have hTe : rZeroHeight (canonicalZero 1).1 ≤ rZeroHeight p.zEarlierMember := by
    have := canonicalZero_height_mono hn
    rw [hne] at this
    exact this
  refine ⟨canonicalZero_one_bottom, hTe, hTe.trans (passage_height_le p), fun u => firstField_constant_onLine _ h₁,
    fun x hx => ⟨pairAmplitude_onLine_le_of_height h₁ hOn hTe hx, pairAmplitude_ratio_onLine_first _ _ h₁ hx⟩,
    fun x hx => smoothed_first_removed_hasSum hx,
    fun xs hxs => ⟨smoothed_first_removed_vector_hasSum xs hxs, first_removed_eq _ _, collectiveGain_one_eq _ _, ?_⟩,
    fun k => contactMinusAt_eq_exp _ k,
    fun w x hx => normalizedPairContribution_mul _ w hx,
    fun r h3 => relative_phaseIncrement_abs_ge_classFloor ⟨p.zLaterMember, hL⟩ (canonicalZero 1) r h3⟩
  have h := smoothedCanonical_interaction_hasSum xs hxs (n := 1) le_rfl
  simpa using h

/-- **La captivité universelle est une CONSÉQUENCE** : si tout membre supérieur est ON, chaque Tour reste dans le champ du
premier (sous l'ancre). Elle n'est supposée nulle part. -/
theorem universal_captivity_of_all_onLine (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (hAll : ∀ w : TrueZero, rZeroRadialPosition w.1 = 1 / 2) :
    ∀ w : TrueZero, ∀ u : ℝ, 0 ≤ u →
      pairAmplitude w (Real.exp u) ≤ pairAmplitude (canonicalZero 1) (Real.exp u) := by
  rw [captivity_iff_insideField]
  intro w
  obtain ⟨n, hn, rfl⟩ := canonicalZero_surjective w
  exact inside_field_of_onLine h₁ (hAll _) (canonicalZero_height_mono hn)

/-- **Fermeture disponible, en passant par la captivité** : ancre ∧ loi de conservation radiale ⟹ tout membre canonique ON
⟹ captivité universelle (conséquence) ⟹ RH (`riemannHypothesis_of_captivity_onLine`). -/
theorem riemannHypothesis_via_captivity_of_conservation
    (hAnchor : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (hLaw : ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember) :
    RiemannHypothesis := by
  have hAll : ∀ w : TrueZero, rZeroRadialPosition w.1 = 1 / 2 := fun w => by
    obtain ⟨n, rfl⟩ := canonicalMember_surjective w
    exact (canonical_onLine_of_conservation hAnchor hLaw n).1
  exact riemannHypothesis_of_captivity_onLine hAnchor (universal_captivity_of_all_onLine hAnchor hAll)


/-! ## 9. Le premier changement de régime (auteur, 2026-10-09, troisième message)

Le côté HAUT d'un membre atteint par un passage qui monte est exclu par son miroir : bas, à la même hauteur, il le
précéderait dans l'ordre des membres, il serait « le premier à être considéré » (`passage_entry_radial_le_half`,
`mirror_precedes`). C'est compilé à tout passage, et en particulier au deuxième membre canonique depuis l'ancre ON.
Il reste le côté BAS, obligation 2 de la chaîne unique. Prolongement : s'il existait un membre hors ligne, il existerait un PREMIER rang
canonique où le régime change ; ce membre serait BAS ; tous les membres de rang inférieur seraient ON ; le passage canonique
qui l'atteint partirait d'un membre ON de hauteur positive et MONTERAIT ; le déficit de comptage serait nul strictement sous
sa hauteur (`N = N₀`) et au moins un membre bas serait compté à sa hauteur, son miroir le suivant à la même hauteur.
RH ⟺ aucun premier changement de régime. La loi de conservation n'a donc à être démontrée que sur un passage dont TOUT
l'historique est ON : fermeture renforcée. Aucune insertion n'est accordée : le premier changement de régime est un objet
défini sur les vrais membres, obtenu par l'absurde, jamais construit. -/

/-- Un membre HAUT est précédé par son miroir, qui est BAS et à la même hauteur. -/
theorem high_member_mirror_low_precedes {z : TrueZero} (hβ : 1 / 2 < rZeroRadialPosition z.1) :
    rZeroRadialPosition (mirrorMember z).1 < 1 / 2 ∧ PZeroMemberPrecedes (mirrorMember z).1 z.1 := by
  have hm : rZeroRadialPosition (mirrorMember z).1 < 1 / 2 := by rw [mirrorMember_radial]; linarith
  refine ⟨hm, ?_⟩
  rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
  right
  exact ⟨mirrorMember_ordinate z, by rw [mirrorMember_radial]; linarith⟩

/-- **Le deuxième membre canonique n'est pas HAUT** : sous l'ancre ON, le passage canonique de rang `0` monte
(`bottom_exit_vertical`) et son miroir, bas et à la même hauteur, le précéderait. Le côté bas reste l'obligation 2 de la chaîne unique. -/
theorem second_member_not_high (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    VerticalPassage (canonicalPassage 0) ∧ rZeroRadialPosition (canonicalMember 1).1 ≤ 1 / 2 := by
  have hV := bottom_exit_vertical (canonicalPassage 0) (canonicalMember 0).2 canonicalMember_zero_bottom h₁
  exact ⟨hV, passage_entry_radial_le_half _ hV⟩

/-- **Un historique entièrement ON force la montée** : si tous les membres canoniques de rang `≤ m + 1` sont ON, le passage
canonique de rang `m` monte (à hauteur égale l'arrivée serait haute, et son miroir bas la précéderait parmi les rangs ON). -/
theorem canonical_vertical_of_history {m : ℕ}
    (hHist : ∀ k < m + 1, rZeroRadialPosition (canonicalMember k).1 = 1 / 2) :
    VerticalPassage (canonicalPassage m) := by
  have hPrec := (canonicalMember_precedes_iff m (m + 1)).mpr (Nat.lt_succ_self m)
  rw [thm_zeroMemberPrecedes_iff_height_radial_lex] at hPrec
  rcases hPrec with h | ⟨_, h⟩
  · exact h
  · exfalso
    rw [hHist m (Nat.lt_succ_self m)] at h
    obtain ⟨hLow, hP⟩ := high_member_mirror_low_precedes h
    obtain ⟨k, hk⟩ := canonicalMember_surjective (mirrorMember (canonicalMember (m + 1)))
    rw [← hk] at hLow hP
    exact absurd (hHist k ((canonicalMember_precedes_iff k (m + 1)).mp hP)) (ne_of_lt hLow)

/-- **Existence d'un premier changement de régime** : si RH est fausse, il existe un rang canonique `n` dont le membre est
BAS et dont tous les prédécesseurs sont ON (le premier rang hors ligne ne peut pas être haut : son miroir bas le
précéderait). -/
theorem exists_first_regime_break (hNot : ¬ RiemannHypothesis) :
    ∃ n : ℕ, rZeroRadialPosition (canonicalMember n).1 < 1 / 2 ∧
      ∀ k < n, rZeroRadialPosition (canonicalMember k).1 = 1 / 2 := by
  classical
  have hEx : ∃ n, rZeroRadialPosition (canonicalMember n).1 ≠ 1 / 2 := by
    by_contra hAll
    push_neg at hAll
    exact hNot (thm_riemannHypothesis_of_allUpperOnCriticalLine fun w => by
      obtain ⟨n, rfl⟩ := canonicalMember_surjective w
      exact hAll n)
  have hn : rZeroRadialPosition (canonicalMember (Nat.find hEx)).1 ≠ 1 / 2 := Nat.find_spec hEx
  have hmin : ∀ k < Nat.find hEx, rZeroRadialPosition (canonicalMember k).1 = 1 / 2 := fun k hk =>
    not_not.mp (Nat.find_min hEx hk)
  refine ⟨Nat.find hEx, ?_, hmin⟩
  rcases lt_or_gt_of_ne hn with h | h
  · exact h
  · exfalso
    obtain ⟨hLow, hPrec⟩ := high_member_mirror_low_precedes h
    obtain ⟨k, hk⟩ := canonicalMember_surjective (mirrorMember (canonicalMember (Nat.find hEx)))
    rw [← hk] at hLow hPrec
    exact absurd (hmin k ((canonicalMember_precedes_iff k _).mp hPrec)) (ne_of_lt hLow)

/-- **RH ⟺ aucun premier changement de régime.** Caractérisation. -/
theorem riemannHypothesis_iff_no_first_regime_break :
    RiemannHypothesis ↔ ¬ ∃ n : ℕ, rZeroRadialPosition (canonicalMember n).1 < 1 / 2 ∧
      ∀ k < n, rZeroRadialPosition (canonicalMember k).1 = 1 / 2 := by
  constructor
  · rintro hRH ⟨n, hLow, -⟩
    exact (riemannHypothesis_iff_noLowerSide.mp hRH) _ hLow
  · intro h
    by_contra hNot
    exact h (exists_first_regime_break hNot)

/-- **Profil du premier changement de régime** sous l'ancre ON : rang `≥ 1` ; le passage canonique qui atteint le membre
bas part d'un membre ON de hauteur positive et MONTE ; tout membre qui précède l'arrivée est ON ; déficit de comptage nul
et saturation `N = N₀` strictement sous la hauteur d'arrivée ; au moins un membre bas compté à cette hauteur ; le miroir
de l'arrivée la suit à la même hauteur. Tout est lu sur les vrais membres ; rien n'est inséré. -/
theorem first_regime_break_profile (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    {n : ℕ} (hLow : rZeroRadialPosition (canonicalMember n).1 < 1 / 2)
    (hHist : ∀ k < n, rZeroRadialPosition (canonicalMember k).1 = 1 / 2) :
    1 ≤ n ∧
    0 < rZeroHeight (canonicalPassage (n - 1)).zEarlierMember ∧
    rZeroRadialPosition (canonicalPassage (n - 1)).zEarlierMember = 1 / 2 ∧
    (canonicalPassage (n - 1)).zLaterMember = (canonicalMember n).1 ∧
    VerticalPassage (canonicalPassage (n - 1)) ∧
    (∀ w : TrueZero, PZeroMemberPrecedes w.1 (canonicalMember n).1 → rZeroRadialPosition w.1 = 1 / 2) ∧
    (∀ T : ℝ, T < rZeroHeight (canonicalMember n).1 →
      lowCount T = 0 ∧ upperCountWithMultiplicity T = onCount T) ∧
    1 ≤ lowCount (rZeroHeight (canonicalMember n).1) ∧
    PZeroMemberPrecedes (canonicalMember n).1 (mirrorMember (canonicalMember n)).1 := by
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd h₁ (ne_of_lt hLow)
    · exact h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hE : rZeroRadialPosition (canonicalMember m).1 = 1 / 2 := hHist m (Nat.lt_succ_self m)
  have hHistAll : ∀ w : TrueZero, PZeroMemberPrecedes w.1 (canonicalMember (m + 1)).1 →
      rZeroRadialPosition w.1 = 1 / 2 := by
    intro w hw
    obtain ⟨k, rfl⟩ := canonicalMember_surjective w
    exact hHist k ((canonicalMember_precedes_iff k (m + 1)).mp hw)
  have hV : VerticalPassage (canonicalPassage m) := by
    have hPrec := (canonicalMember_precedes_iff m (m + 1)).mpr (Nat.lt_succ_self m)
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex] at hPrec
    rcases hPrec with h | ⟨_, h⟩
    · exact h
    · exfalso
      rw [hE] at h
      exact absurd (lt_trans h hLow) (lt_irrefl _)
  have hBelow : ∀ T : ℝ, T < rZeroHeight (canonicalMember (m + 1)).1 →
      lowCount T = 0 ∧ upperCountWithMultiplicity T = onCount T := by
    intro T hT
    have h0 : lowCount T = 0 := by
      rw [lowCount_eq_zero_iff]
      intro z hz hβ
      have hPrec : PZeroMemberPrecedes z.1 (canonicalMember (m + 1)).1 := by
        rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
        left
        exact lt_of_le_of_lt hz hT
      exact absurd (hHistAll z hPrec) (ne_of_lt hβ)
    exact ⟨h0, (saturation_iff_lowCount_zero T).mpr h0⟩
  exact ⟨hn1, (canonicalMember m).2, hE, rfl, hV, hHistAll, hBelow,
    one_le_lowCount_of_low (canonicalMember (m + 1)) le_rfl hLow, mirror_precedes hLow⟩

/-- **Récurrence renforcée** : ancre ON ∧ conservation radiale sur les passages dont TOUT l'historique est ON ⟹ chaque
membre canonique est ON (récurrence forte ; la montée de chaque passage canonique vient de l'historique,
`canonical_vertical_of_history`). -/
theorem canonical_onLine_of_history_conservation
    (hAnchor : rZeroRadialPosition (canonicalMember 0).1 = 1 / 2)
    (hLaw : ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember) :
    ∀ n : ℕ, rZeroRadialPosition (canonicalMember n).1 = 1 / 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · exact hAnchor
    · have hHist : ∀ k < m + 1, rZeroRadialPosition (canonicalMember k).1 = 1 / 2 := fun k hk => ih k hk
      have hHistAll : ∀ w : TrueZero, PZeroMemberPrecedes w.1 (canonicalPassage m).zLaterMember →
          rZeroRadialPosition w.1 = 1 / 2 := by
        intro w hw
        obtain ⟨k, rfl⟩ := canonicalMember_surjective w
        exact hHist k ((canonicalMember_precedes_iff k (m + 1)).mp hw)
      have hE := hHist m (Nat.lt_succ_self m)
      exact (hLaw (canonicalPassage m) (canonicalMember m).2 (canonical_vertical_of_history hHist) hE hHistAll).trans hE

/-- **Fermeture renforcée** : ancre ON ∧ conservation radiale sur les seuls passages dont TOUT l'historique est ON ⟹ RH.
La loi reçoit en plus de `riemannHypothesis_of_anchor_and_conservation` l'historique entièrement ON sous l'arrivée
(donc, par le profil, le déficit de comptage nul sous sa hauteur). Preuve par le premier changement de régime. -/
theorem riemannHypothesis_of_anchor_and_history_conservation
    (hAnchor : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (hLaw : ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember) :
    RiemannHypothesis := by
  by_contra hNot
  obtain ⟨n, hLow, hHist⟩ := exists_first_regime_break hNot
  obtain ⟨-, hE, hOn, hL, hV, hHistAll, -, -, -⟩ := first_regime_break_profile hAnchor hLow hHist
  have h := hLaw _ hE hV hOn (by rw [hL]; exact hHistAll)
  rw [hL, hOn] at h
  exact absurd h (ne_of_lt hLow)

/-- La loi renforcée est impliquée par la loi simple (elle a une hypothèse de plus) et par RH. -/
theorem history_conservation_of_conservation
    (hLaw : ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember) :
    ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember :=
  fun p hE hV hOn _ => hLaw p hE hV hOn

#print axioms high_member_mirror_low_precedes
#print axioms second_member_not_high
#print axioms canonical_vertical_of_history
#print axioms exists_first_regime_break
#print axioms riemannHypothesis_iff_no_first_regime_break
#print axioms first_regime_break_profile
#print axioms canonical_onLine_of_history_conservation
#print axioms riemannHypothesis_of_anchor_and_history_conservation
#print axioms history_conservation_of_conservation

#print axioms anchor_constraints_at_passage
#print axioms universal_captivity_of_all_onLine
#print axioms riemannHypothesis_via_captivity_of_conservation

#print axioms mirror_fixed_iff_onLine
#print axioms engaged_mirror_annulled
#print axioms authentic_contacts
#print axioms envelope_coupling
#print axioms prime_event_solicitations
#print axioms exact_reconstruction_profile
#print axioms arithmetic_recovery_profile
#print axioms zero_weight_summable
#print axioms engaged_passage_profile
#print axioms bottom_exit_vertical
#print axioms canonical_onLine_of_conservation
#print axioms riemannHypothesis_of_anchor_and_conservation
#print axioms conservation_of_riemannHypothesis
#print axioms engaged_law_of_vertical_law

end RHV6Fresh
