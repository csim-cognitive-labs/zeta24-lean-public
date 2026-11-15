/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.JointParameterReading
import RHV6Fresh.Terminal.FirstZeroField
import RHV6Fresh.Terminal.SymmetricWinding
import RHV6Fresh.Terminal.RayEnergy
import RHV6Fresh.Terminal.CanonicalEnumeration
import RHV6Fresh.Terminal.GrammarWordLoad
import RHV6Fresh.Terminal.RemainderExponent
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.NumberTheory.Chebyshev

/-!
# RHV6Fresh — l'unique prémisse : le premier zéro apporte le plus grand gain dans la reconstruction
collective du reste (auteur, 2026-10-06)

Prémisse MINIMALE, écrite en hypothèse explicite (aucune `def P… : Prop`), sans aucune progression
de hauteur, sans aucune domination d'amplitude, sans aucune décroissance des gains successifs :

> `∀ n ≥ 1, D_n ≤ D_1`, où `D_n = ‖r_{n−1}‖² − ‖r_{n−1} − c_n‖²` est le gain collectif du zéro de
> rang `n` sur un support de mesure fixé, `r_{n−1} = R − Σ_{j<n} c_j`.

Objets (tous définis par leur formule, aucun choisi) :

* `pairContribution z x = −2·Re(x^ρ/ρ) = −2x^β cos(T log x − φ)/√(β² + T²)` : contribution brute
  du zéro regroupée avec son conjugué ;
* `pairAmplitude z x = 2x^{β−1/2}/√(β² + T²)` : amplitude normalisée par l'échelle de la ligne ;
  en ligne `2/√(1/4 + T²) = 2W/√(π² + W²/4)` avec `W = log(C_{k+1}/C_k) = π/T` ;
* `partialRemainder c R n = r_{n−1}`, `collectiveGain c R n = D_n`,
  `followingContributions c n = Σ_{j>n} c_j`, dans un espace préhilbertien réel quelconque
  (le « support de mesure fixé ») ; instance arithmétique : contributions NORMALISÉES par `√x`
  (`normalizedPairContribution = pairContribution/√x`, `normalizedSupportContribution`) sur un
  support fini d'abscisses `xs` avec `∀ i, 1 < xs i`, énumération CANONIQUE des membres par l'index
  zéro-source (`canonicalZero`, `Terminal/CanonicalEnumeration.lean` : rang `1` = index `0`, rang
  `n + 1` = index `n`), multiplicités comme coefficients, reste EXACT normalisé
  (`normalizedRawRemainderVector`, canal brut au milieu des sauts) — corrections de l'auteur du
  2026-10-06 (points 1 à 3).

Démontré : `D_n = 2⟨r_{n−1}, c_n⟩ − ‖c_n‖²` ; SANS aucune hypothèse de convergence,
`D_n = ‖c_n‖² + 2⟨r_n, c_n⟩` avec `r_n = R − Σ_{j≤n} c_j` (`collectiveGain_eq_own_add_interaction`)
;
sous la représentation ORDONNÉE (sommes partielles dans l'ordre canonique tendant vers `R`), `r_n`
est la limite des sommes partielles des suivants et tend vers zéro ; sous `HasSum`,
`r_n = Σ_{j>n} c_j` ; sous la prémisse, la relation collective au rang `n` est bornée par celle du
rang `1` ; en ligne, l'intervalle des contacts et l'amplitude décroissent strictement avec la
hauteur ; fermeture : si chaque amplitude individuelle reste sous celle du premier zéro sur tout
l'horizon, RH (par la réflexion) ; `InsideField z₁ w ⟺ ∀ x ≥ 1, A_w ≤ A_{z₁}`.

Représentation exacte : DÉMONTRÉE pour le canal LISSÉ normalisé (`smoothedCanonical_hasSum`,
contributions `2·Re(−m x^ρ/(ρ(ρ+1)))/√x` du membre canonique et de son conjugué regroupés, somme
absolument convergente, par réindexation `ExplicitIndex ≃ ℕ × Bool`) ; NON DÉMONTRÉE pour le canal
BRUT (`ψ₀(x) − fond = −Σ_ρ x^ρ/ρ`, convergence seulement ordonnée : la base nomme cette identité,
`PM9aMidpointIdentity`, sans la prouver) ; le passage lissé → brut membre par membre est le facteur
`−m/(ρ+1)` (`normalizedSmoothedPairContribution_eq`), qui change l'amplitude et tourne la phase ;
rien ne transporte la convergence absolue de la somme lissée vers la somme brute.

OUVERT, premier raccord, jamais posé en hypothèse d'une fermeture :
`(∀ n ≥ 1, D_n ≤ D_1) ⟹ (∀ w, InsideField (canonicalZero 1) w)`, soit
`∀ w, ∀ x ≥ 1, pairAmplitude w x ≤ pairAmplitude (canonicalZero 1) x` ; manque exact : (1) le
contrôle, depuis la prémisse, de l'interaction `⟨r_n, c_n⟩` à chaque rang
(`norm_le_first_of_interaction`
dit ce qu'il donnerait) ; (2) le passage de la mesure sur le support fixé (`‖c_n‖ ≤ ‖c_1‖`) à la
domination ponctuelle sur tout `x ≥ 1` ; (3) la représentation du canal brut. Ancre ON
(`rZeroRadialPosition (canonicalZero 1).1 = 1/2`) : aucun terme Lean du dépôt ni de zeta23 ;
obligation explicite, non posée.

Compléments de l'auteur (2026-10-06, directive en dix points puis complément grammatical), tous
compilés, aucune hypothèse ajoutée : décomposition exacte du gain `D_n = E_n + 2I_n`,
`D_1 − D_n = (E_1 − E_n) − 2(I_n − I_1)`, `E_n − E_1 = 2(I_1 − I_n) − (D_1 − D_n)`, sous la prémisse
`E_n − E_1 ≤ 2(I_1 − I_n)`, et le contrôle requis identifié exactement
`E_n ≤ E_1 ⟺ 2(I_1 − I_n) ≤ D_1 − D_n` (`ownEnergy_le_first_iff`, `canonical_norm_le_first_iff` ;
la condition `I_1 ≤ I_n` n'est que suffisante) ; produit de deux contributions en paramètres de
phase,
toute position radiale (`pairContribution_mul`, `normalizedPairContribution_mul`,
`canonical_inner_eq_phase_sum`) ; interaction par queue finie sans convergence
(`interaction_eq_tail_add`), limite ordonnée (`interaction_tendsto_of_ordered`), série convergente
pour
le canal lissé (`smoothedCanonical_interaction_hasSum`) ; résultats ON à leur portée
(`weighted_amplitude_onLine_lt_of_height`, à multiplicité égale ; `pairAmplitude_own_contact_step`)
;
phases relatives aux raccords et sur une fenêtre (`relative_phaseIncrement`,
`relative_phase_window_sum`, `relative_phase_window_ge`) ; grammaire compilée réutilisée
(`gapMagnitude`, `eventClass`, `primeGap_eq_magnitude_class`, `eventClass_mem`,
`eventClass_transitions`, `eventClass_alternates`, `primeGapLogRatio_eq_log_one_add`,
`rawAmplitude_prime_step`, `rawEnergy_prime_step`, `pairAmplitude_prime_step`, `onLine_prime_step`,
`phaseIncrement_window_sum`, `window_sum_by_classes`, `window_class_zero_by_state`,
`window_channel_lock`, `beat_arguments_prime_step`, `primeSupport_admissible`,
`canonical_inner_primeSupport`, `constant_height_window_abel`). Portées à ne pas dépasser (revue de
l'auteur, 2026-10-06) : `constant_height_window_abel` est une identité télescopique sur une
constante réelle, elle ne construit aucune suite de vrais zéros et ne justifie pas « les premiers
n'exigent aucune progression de hauteur » ; `canonical_inner_primeSupport` développe le produit
scalaire sur des premiers choisis par une fonction arbitraire, il ne transporte rien depuis le
support fixé ;
`relative_phase_window_ge` contient l'écart des hauteurs en facteur, il mesure son effet sans le
produire. NON dérivés : la chaîne canaux → borne des interactions → contrainte de hauteur (aucune
borne démontrée sur les sommes oscillantes de cosinus) ; la borne `2(I_1 − I_n) ≤ D_1 − D_n` depuis
la prémisse ; le passage de l'énergie sur le support fixé à la domination ponctuelle ; le raccord
gain maximal → domination individuelle.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean
open scoped InnerProductSpace

/-! ## 1. Contribution brute d'un zéro, regroupée avec son conjugué -/

/-- **Contribution brute du zéro `z` regroupée avec son conjugué** : `c(x) = −2·Re(x^ρ/ρ)`. -/
noncomputable def pairContribution (z : TrueZero) (x : ℝ) : ℝ := -2 * (zeroTerm z x).re

/-- Support du zéro : `‖ρ‖ = √(β² + T²)`. -/
theorem zeroPoint_norm_eq_sqrt_sum (z : TrueZero) :
    ‖zeroPoint z‖ = Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (zeroPoint z)), zeroPoint_norm_sq]

/-- La contribution regroupée est l'opposé de la somme du terme et du terme conjugué. -/
theorem pairContribution_eq_neg_pair {z : TrueZero} {x : ℝ} (hx : 0 < x) :
    ((pairContribution z x : ℝ) : ℂ) =
      -(zeroTerm z x + (x : ℂ) ^ (starRingEnd ℂ (zeroPoint z)) / starRingEnd ℂ (zeroPoint z)) := by
  rw [pair_term_real hx]
  unfold pairContribution
  push_cast
  ring

/-- **Formule exacte** : `c(x) = −2x^β cos(T log x − φ)/√(β² + T²)`, `φ = arctan(T/β)`. -/
theorem pairContribution_eq {z : TrueZero} {x : ℝ} (hx : 0 < x) :
    pairContribution z x =
      -2 * x ^ rZeroRadialPosition z.1 /
        Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) *
        Real.cos (rZeroHeight z.1 * Real.log x -
          Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1)) := by
  unfold pairContribution
  rw [zeroTerm_re_eq_cos_towerPosition hx, pi_mul_towerPosition, zeroPoint_norm_eq_sqrt_sum,
    towerMotion_phase]
  ring

/-- **Aux contacts, la contribution atteint son amplitude, avec le signe `(−1)^k`** :
`c(C_k) = −2(−1)^k C_k^β/√(β² + T²)`. -/
theorem pairContribution_at_contact (z : TrueZero) (k : ℤ) :
    pairContribution z (contactMinusAt z k) =
      -2 * (-1 : ℝ) ^ k * (contactMinusAt z k) ^ rZeroRadialPosition z.1 /
        Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) := by
  unfold pairContribution
  rw [ray_energy, zeroPoint_norm_eq_sqrt_sum]
  ring

/-- En tout point, la contribution ne dépasse pas deux fois l'amplitude brute du terme. -/
theorem abs_pairContribution_le (z : TrueZero) (x : ℝ) :
    |pairContribution z x| ≤ 2 * ‖zeroTerm z x‖ := by
  unfold pairContribution
  rw [abs_mul, abs_neg, abs_two]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)

/-- Aux contacts, l'égalité : les contacts sont les phases où la contribution atteint son amplitude
maximale. -/
theorem abs_pairContribution_at_contact (z : TrueZero) (k : ℤ) :
    |pairContribution z (contactMinusAt z k)| = 2 * ‖zeroTerm z (contactMinusAt z k)‖ := by
  unfold pairContribution
  rw [zeroTerm_re_at_contact, abs_mul, abs_neg, abs_two, abs_mul, abs_of_nonneg (norm_nonneg _),
    abs_zpow, abs_neg, abs_one, one_zpow, one_mul]

/-! ## 2. Amplitude normalisée par l'échelle de la ligne -/

/-- **Amplitude normalisée** : `A(x) = 2x^{β−1/2}/√(β² + T²)`, deux fois le rayon normalisé. -/
noncomputable def pairAmplitude (z : TrueZero) (x : ℝ) : ℝ := 2 * normalizedRadius z x

theorem pairAmplitude_eq (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    pairAmplitude z x = 2 * x ^ (rZeroRadialPosition z.1 - 1 / 2) /
      Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) := by
  unfold pairAmplitude
  rw [normalizedRadius_eq z hx, zeroPoint_norm_eq_sqrt_sum, mul_div_assoc]

/-- L'amplitude normalisée est l'amplitude brute ramenée à l'échelle `√x`. -/
theorem pairAmplitude_eq_abs_div (z : TrueZero) (x : ℝ) :
    pairAmplitude z x = 2 * ‖zeroTerm z x‖ / Real.sqrt x := by
  unfold pairAmplitude normalizedRadius
  ring

/-- **En ligne** : `A = 2/√(1/4 + T²)`, constante le long de l'axe. -/
theorem pairAmplitude_onLine (z : TrueZero) (hz : rZeroRadialPosition z.1 = 1 / 2) {x : ℝ}
    (hx : 0 < x) : pairAmplitude z x = 2 / Real.sqrt (1 / 4 + rZeroHeight z.1 ^ 2) := by
  unfold pairAmplitude
  rw [normalizedRadius_onLine z hz hx]
  unfold onRadius
  rw [add_comm]
  ring

/-- **Intervalle logarithmique des contacts** : `W = log(C_{k+1}/C_k) = π/T`. -/
theorem contact_interval_eq (z : TrueZero) (k : ℤ) :
    Real.log (contactMinusAt z (k + 1) / contactMinusAt z k) = Real.pi / rZeroHeight z.1 := by
  rw [Real.log_div (contactMinusAt_positive z (k + 1)).ne' (contactMinusAt_positive z k).ne',
    contact_log_step]
  rfl

/-- **Relation exacte amplitude–contacts, en ligne** : `A = 2W/√(π² + W²/4)`,
`W = log(C_{k+1}/C_k)`. -/
theorem pairAmplitude_onLine_contact_interval (z : TrueZero)
    (hz : rZeroRadialPosition z.1 = 1 / 2) (k : ℤ) {x : ℝ} (hx : 0 < x) :
    pairAmplitude z x =
      2 * Real.log (contactMinusAt z (k + 1) / contactMinusAt z k) /
        Real.sqrt (Real.pi ^ 2 +
          (Real.log (contactMinusAt z (k + 1) / contactMinusAt z k)) ^ 2 / 4) := by
  unfold pairAmplitude
  rw [normalizedRadius_onLine_pitch z hz hx, contact_interval_eq, mul_div_assoc]
  rfl

/-- **Quand la hauteur augmente, l'intervalle des contacts diminue** (toute position radiale). -/
theorem contact_interval_lt_of_height {z w : TrueZero} (hT : rZeroHeight z.1 < rZeroHeight w.1)
    (k : ℤ) :
    Real.log (contactMinusAt w (k + 1) / contactMinusAt w k) <
      Real.log (contactMinusAt z (k + 1) / contactMinusAt z k) := by
  rw [contact_interval_eq, contact_interval_eq]
  exact div_lt_div_of_pos_left Real.pi_pos z.2 hT

/-- **Parmi les zéros en ligne, l'amplitude diminue strictement avec la hauteur** : domination de
l'amplitude individuelle du premier zéro parmi les ON. -/
theorem pairAmplitude_onLine_lt_of_height {z w : TrueZero}
    (hz : rZeroRadialPosition z.1 = 1 / 2) (hw : rZeroRadialPosition w.1 = 1 / 2)
    (hT : rZeroHeight z.1 < rZeroHeight w.1) {x : ℝ} (hx : 0 < x) :
    pairAmplitude w x < pairAmplitude z x := by
  unfold pairAmplitude
  rw [normalizedRadius_onLine z hz hx, normalizedRadius_onLine w hw hx]
  exact mul_lt_mul_of_pos_left (onRadius_strictAnti z.2.le hT) (by norm_num)

/-! ## 3. Gains collectifs sur un support de mesure fixé -/

variable {V : Type*} [NormedAddCommGroup V]

/-- **Reste partiel** `r_{n−1} = R − Σ_{j<n} c_j` (indices `1 ≤ j < n`). -/
noncomputable def partialRemainder (c : ℕ → V) (R : V) (n : ℕ) : V :=
  R - ∑ j ∈ Finset.Ico 1 n, c j

/-- **Gain collectif du rang `n`** : `D_n = ‖r_{n−1}‖² − ‖r_{n−1} − c_n‖²`. -/
noncomputable def collectiveGain (c : ℕ → V) (R : V) (n : ℕ) : ℝ :=
  ‖partialRemainder c R n‖ ^ 2 - ‖partialRemainder c R n - c n‖ ^ 2

/-- **Somme des contributions suivantes** `Σ_{j>n} c_j`. -/
noncomputable def followingContributions (c : ℕ → V) (n : ℕ) : V := ∑' j, c (j + n + 1)

theorem partialRemainder_one (c : ℕ → V) (R : V) : partialRemainder c R 1 = R := by
  unfold partialRemainder
  simp

/-- Le reste partiel avance d'une contribution à chaque rang. -/
theorem partialRemainder_succ (c : ℕ → V) (R : V) {n : ℕ} (hn : 1 ≤ n) :
    partialRemainder c R (n + 1) = partialRemainder c R n - c n := by
  unfold partialRemainder
  rw [Finset.sum_Ico_succ_top hn, sub_sub]

/-- **`D_n = ‖r_{n−1}‖² − ‖r_n‖²`** : la décroissance de l'énergie du reste à la marche `n`. -/
theorem collectiveGain_eq_energy_drop (c : ℕ → V) (R : V) {n : ℕ} (hn : 1 ≤ n) :
    collectiveGain c R n = ‖partialRemainder c R n‖ ^ 2 - ‖partialRemainder c R (n + 1)‖ ^ 2 := by
  rw [collectiveGain, partialRemainder_succ c R hn]

/-- Sous la représentation exacte `R = Σ_{j≥1} c_j`, le reste partiel est la queue `Σ_{j≥n} c_j`. -/
theorem partialRemainder_hasSum {c : ℕ → V} {R : V} (hRep : HasSum (fun j => c (j + 1)) R) {n : ℕ}
    (hn : 1 ≤ n) : HasSum (fun j => c (j + n)) (partialRemainder c R n) := by
  have h : HasSum (fun j => c (j + (n - 1) + 1)) (R - ∑ i ∈ Finset.range (n - 1), c (i + 1)) :=
    (hasSum_nat_add_iff' (n - 1)).mpr hRep
  have hfun : (fun j => c (j + (n - 1) + 1)) = fun j => c (j + n) := by
    funext j
    congr 1
    omega
  have hsum : ∑ i ∈ Finset.range (n - 1), c (i + 1) = ∑ j ∈ Finset.Ico 1 n, c j := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by rw [add_comm]
  rw [hfun, hsum] at h
  exact h

/-- La queue au-delà du rang `n` : `Σ_{j>n} c_j = r_{n−1} − c_n`. -/
theorem followingContributions_hasSum {c : ℕ → V} {R : V} (hRep : HasSum (fun j => c (j + 1)) R)
    {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun j => c (j + n + 1)) (partialRemainder c R n - c n) := by
  have h : HasSum (fun j => c (j + 1 + n))
      (partialRemainder c R n - ∑ i ∈ Finset.range 1, c (i + n)) :=
    (hasSum_nat_add_iff' 1).mpr (partialRemainder_hasSum hRep hn)
  rw [Finset.sum_range_one, zero_add] at h
  have hfun : (fun j => c (j + 1 + n)) = fun j => c (j + n + 1) := by
    funext j
    congr 1
    omega
  rwa [hfun] at h

/-- `r_{n−1} = c_n + Σ_{j>n} c_j`. -/
theorem partialRemainder_eq_add_following {c : ℕ → V} {R : V}
    (hRep : HasSum (fun j => c (j + 1)) R) {n : ℕ} (hn : 1 ≤ n) :
    partialRemainder c R n = c n + followingContributions c n := by
  unfold followingContributions
  rw [(followingContributions_hasSum hRep hn).tsum_eq]
  abel

variable [InnerProductSpace ℝ V]

/-- **Première relation exacte** : `D_n = 2⟨r_{n−1}, c_n⟩ − ‖c_n‖²`. -/
theorem collectiveGain_eq (c : ℕ → V) (R : V) (n : ℕ) :
    collectiveGain c R n = 2 * ⟪partialRemainder c R n, c n⟫_ℝ - ‖c n‖ ^ 2 := by
  unfold collectiveGain
  rw [norm_sub_sq_real]
  ring

/-- **Relation collective exacte** : sous la représentation exacte du reste par la somme convergente
des contributions, `D_n = ‖c_n‖² + 2⟨Σ_{j>n} c_j, c_n⟩`. Le gain dépend de l'amplitude propre et de
l'interaction de phase avec tous les suivants. -/
theorem collectiveGain_collective {c : ℕ → V} {R : V} (hRep : HasSum (fun j => c (j + 1)) R) {n : ℕ}
    (hn : 1 ≤ n) :
    collectiveGain c R n = ‖c n‖ ^ 2 + 2 * ⟪followingContributions c n, c n⟫_ℝ := by
  rw [collectiveGain_eq, partialRemainder_eq_add_following hRep hn, inner_add_left,
    real_inner_self_eq_norm_sq]
  ring

/-! ## 4. L'unique prémisse `∀ n ≥ 1, D_n ≤ D_1` et ce qu'elle donne -/

/-- **Sous l'unique prémisse**, la relation collective au rang `n` est bornée par celle du rang
`1` :
`‖c_n‖² + 2⟨Σ_{j>n} c_j, c_n⟩ ≤ ‖c_1‖² + 2⟨Σ_{j>1} c_j, c_1⟩`. La prémisse ne dit rien de chaque
amplitude isolément : l'interaction de phase y entre à chaque rang. -/
theorem firstGain_collective_relation {c : ℕ → V} {R : V} (hRep : HasSum (fun j => c (j + 1)) R)
    (hGain : ∀ n : ℕ, 1 ≤ n → collectiveGain c R n ≤ collectiveGain c R 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖c n‖ ^ 2 + 2 * ⟪followingContributions c n, c n⟫_ℝ ≤
      ‖c 1‖ ^ 2 + 2 * ⟪followingContributions c 1, c 1⟫_ℝ := by
  rw [← collectiveGain_collective hRep hn, ← collectiveGain_collective hRep le_rfl]
  exact hGain n hn

/-- **Sous l'unique prémisse**, l'amplitude propre du rang `n` est bornée par le premier gain
diminué
de sa propre interaction : `‖c_n‖² ≤ D_1 − 2⟨Σ_{j>n} c_j, c_n⟩`. -/
theorem firstGain_amplitude_bound {c : ℕ → V} {R : V} (hRep : HasSum (fun j => c (j + 1)) R)
    (hGain : ∀ n : ℕ, 1 ≤ n → collectiveGain c R n ≤ collectiveGain c R 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖c n‖ ^ 2 ≤ collectiveGain c R 1 - 2 * ⟪followingContributions c n, c n⟫_ℝ := by
  have h := hGain n hn
  rw [collectiveGain_collective hRep hn] at h
  linarith

/-- **Lecture, pas obligation** : sous l'unique prémisse, si l'interaction de phase du rang `n` avec
ses suivants est au moins celle du rang `1` avec les siens, alors `‖c_n‖ ≤ ‖c_1‖` sur le support.
L'hypothèse d'interaction n'est pas dérivée : c'est exactement ce que le raccord ouvert doit
fournir. -/
theorem norm_le_first_of_interaction {c : ℕ → V} {R : V} (hRep : HasSum (fun j => c (j + 1)) R)
    (hGain : ∀ n : ℕ, 1 ≤ n → collectiveGain c R n ≤ collectiveGain c R 1) {n : ℕ} (hn : 1 ≤ n)
    (hI : ⟪followingContributions c 1, c 1⟫_ℝ ≤ ⟪followingContributions c n, c n⟫_ℝ) :
    ‖c n‖ ≤ ‖c 1‖ := by
  have h := firstGain_collective_relation hRep hGain hn
  have hsq : ‖c n‖ ^ 2 ≤ ‖c 1‖ ^ 2 := by linarith
  by_contra hlt
  push Not at hlt
  nlinarith [norm_nonneg (c 1), norm_nonneg (c n)]

/-! ## 4bis. Les mêmes identités SANS hypothèse de convergence, et la représentation ordonnée
(correction 3 : « n'utilise pas `HasSum` pour remplacer une convergence seulement ordonnée ») -/

/-- **Le gain est l'énergie propre plus l'interaction avec le reste après le rang** :
`D_n = ‖c_n‖² + 2⟨r_n, c_n⟩`, `r_n = R − Σ_{j≤n} c_j`. Identité algébrique, aucune convergence. -/
theorem collectiveGain_eq_own_add_interaction (c : ℕ → V) (R : V) {n : ℕ} (hn : 1 ≤ n) :
    collectiveGain c R n = ‖c n‖ ^ 2 + 2 * ⟪partialRemainder c R (n + 1), c n⟫_ℝ := by
  rw [collectiveGain_eq, partialRemainder_succ c R hn, inner_sub_left, real_inner_self_eq_norm_sq]
  ring

omit [InnerProductSpace ℝ V] in
/-- **Représentation ordonnée** : si les sommes partielles dans l'ordre des rangs tendent vers `R`
(convergence seulement ordonnée), le reste après le rang `N` tend vers zéro. -/
theorem partialRemainder_tendsto_zero {c : ℕ → V} {R : V}
    (hRep : Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, c (j + 1)) Filter.atTop (nhds R)) :
    Filter.Tendsto (fun N => partialRemainder c R (N + 1)) Filter.atTop (nhds 0) := by
  have hfun : (fun N => partialRemainder c R (N + 1)) =
      fun N => R - ∑ j ∈ Finset.range N, c (j + 1) := by
    funext N
    unfold partialRemainder
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [add_comm]
  rw [hfun]
  simpa using (tendsto_const_nhds (x := R)).sub hRep

omit [InnerProductSpace ℝ V] in
/-- Sous la représentation ordonnée, le reste après le rang `n` est la **limite des sommes
partielles
des suivants** : `r_n = lim_N Σ_{n<j≤N} c_j`. -/
theorem following_partial_sums_tendsto {c : ℕ → V} {R : V}
    (hRep : Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, c (j + 1)) Filter.atTop (nhds R))
    (n : ℕ) :
    Filter.Tendsto (fun N => ∑ j ∈ Finset.Ico (n + 1) (N + 1), c j) Filter.atTop
      (nhds (partialRemainder c R (n + 1))) := by
  have key : ∀ᶠ N in Filter.atTop, ∑ j ∈ Finset.Ico (n + 1) (N + 1), c j =
      partialRemainder c R (n + 1) - partialRemainder c R (N + 1) := by
    filter_upwards [Filter.eventually_ge_atTop n] with N hN
    unfold partialRemainder
    rw [← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ n + 1) (by omega : n + 1 ≤ N + 1)]
    abel
  refine Filter.Tendsto.congr' ?_ (by
    simpa using (tendsto_const_nhds (x := partialRemainder c R (n + 1))).sub
      (partialRemainder_tendsto_zero hRep))
  filter_upwards [key] with N hN
  exact hN.symm

omit [InnerProductSpace ℝ V] in
/-- `HasSum` donne la représentation ordonnée ; la réciproque n'est pas disponible. -/
theorem ordered_of_hasSum {c : ℕ → V} {R : V} (hRep : HasSum (fun j => c (j + 1)) R) :
    Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, c (j + 1)) Filter.atTop (nhds R) :=
  hRep.tendsto_sum_nat

omit [InnerProductSpace ℝ V] in
/-- Sous `HasSum`, le reste après le rang `n` est la somme des suivants. -/
theorem partialRemainder_succ_eq_following {c : ℕ → V} {R : V}
    (hRep : HasSum (fun j => c (j + 1)) R) {n : ℕ} (hn : 1 ≤ n) :
    partialRemainder c R (n + 1) = followingContributions c n := by
  rw [partialRemainder_succ c R hn, partialRemainder_eq_add_following hRep hn]
  abel

/-- **Sous l'unique prémisse, sans aucune hypothèse de convergence** : la relation collective au
rang
`n` (énergie propre + interaction avec le reste après le rang) est bornée par celle du rang `1`. -/
theorem firstGain_relation (c : ℕ → V) (R : V)
    (hGain : ∀ n : ℕ, 1 ≤ n → collectiveGain c R n ≤ collectiveGain c R 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖c n‖ ^ 2 + 2 * ⟪partialRemainder c R (n + 1), c n⟫_ℝ ≤
      ‖c 1‖ ^ 2 + 2 * ⟪partialRemainder c R 2, c 1⟫_ℝ := by
  have h := hGain n hn
  rwa [collectiveGain_eq_own_add_interaction c R hn,
    collectiveGain_eq_own_add_interaction c R le_rfl] at h

/-- **Lecture par l'interaction, sans convergence** : si l'interaction du rang `n` avec son reste
est
au moins celle du rang `1`, `‖c_n‖ ≤ ‖c_1‖` sur le support. L'hypothèse d'interaction est le
contrôle que la prémisse ne fournit pas d'elle-même ; elle n'est pas dérivée. -/
theorem norm_le_first_of_interaction_ordered (c : ℕ → V) (R : V)
    (hGain : ∀ n : ℕ, 1 ≤ n → collectiveGain c R n ≤ collectiveGain c R 1) {n : ℕ} (hn : 1 ≤ n)
    (hInt : ⟪partialRemainder c R 2, c 1⟫_ℝ ≤ ⟪partialRemainder c R (n + 1), c n⟫_ℝ) :
    ‖c n‖ ≤ ‖c 1‖ := by
  have h := firstGain_relation c R hGain hn
  have hsq : ‖c n‖ ^ 2 ≤ ‖c 1‖ ^ 2 := by linarith
  by_contra hlt
  push Not at hlt
  nlinarith [norm_nonneg (c 1), norm_nonneg (c n)]

/-! ## 5. Correction 1 : la contribution normalisée par `√x` sur un support d'abscisses `> 1` -/

/-- **Contribution normalisée** : la contribution brute ramenée à l'échelle de la ligne, `c(x)/√x`.
`pairContribution` reste la contribution brute. -/
noncomputable def normalizedPairContribution (z : TrueZero) (x : ℝ) : ℝ :=
  pairContribution z x / Real.sqrt x

theorem normalizedPairContribution_eq_re (z : TrueZero) (x : ℝ) :
    normalizedPairContribution z x = -2 * (zeroTerm z x).re / Real.sqrt x := rfl

/-- La contribution normalisée ne dépasse jamais l'amplitude normalisée. -/
theorem abs_normalizedPairContribution_le (z : TrueZero) (x : ℝ) :
    |normalizedPairContribution z x| ≤ pairAmplitude z x := by
  unfold normalizedPairContribution
  rw [pairAmplitude_eq_abs_div, abs_div, abs_of_nonneg (Real.sqrt_nonneg x)]
  exact div_le_div_of_nonneg_right (abs_pairContribution_le z x) (Real.sqrt_nonneg x)

/-- Aux contacts, la contribution normalisée atteint l'amplitude normalisée. -/
theorem abs_normalizedPairContribution_at_contact (z : TrueZero) (k : ℤ) :
    |normalizedPairContribution z (contactMinusAt z k)| = pairAmplitude z (contactMinusAt z k) := by
  unfold normalizedPairContribution
  rw [pairAmplitude_eq_abs_div, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_pairContribution_at_contact]

/-- **Vecteur de contribution normalisée sur un support fini d'abscisses** `xs` : la seule
contribution
utilisée dans l'instance arithmétique des gains. Mêmes abscisses, mêmes poids, même normalisation à
tous les rangs. -/
noncomputable def normalizedSupportContribution {m : ℕ} (xs : Fin m → ℝ) (z : TrueZero) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => normalizedPairContribution z (xs i)

theorem normalizedSupportContribution_apply {m : ℕ} (xs : Fin m → ℝ) (z : TrueZero) (i : Fin m) :
    normalizedSupportContribution xs z i = normalizedPairContribution z (xs i) := rfl

/-- L'énergie normalisée sur le support est la somme des carrés des contributions normalisées. -/
theorem normalizedSupportContribution_normSq {m : ℕ} (xs : Fin m → ℝ) (z : TrueZero) :
    ‖normalizedSupportContribution xs z‖ ^ 2 = ∑ i, normalizedPairContribution z (xs i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [normalizedSupportContribution_apply, Real.norm_eq_abs, sq_abs]

/-- Sur le support, l'énergie normalisée d'un membre est bornée par la somme des carrés de son
amplitude normalisée aux abscisses. -/
theorem normalizedSupportContribution_normSq_le {m : ℕ} (xs : Fin m → ℝ) (z : TrueZero) :
    ‖normalizedSupportContribution xs z‖ ^ 2 ≤ ∑ i, pairAmplitude z (xs i) ^ 2 := by
  rw [normalizedSupportContribution_normSq]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← sq_abs (normalizedPairContribution _ _)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_normalizedPairContribution_le _ _) 2

/-! ## 6. Corrections 2 et 3 : énumération canonique, reste exact normalisé, instance de la
prémisse -/

/-- **Contribution canonique de rang `n`** : multiplicité × contribution normalisée du membre
canonique
de rang `n` (`canonicalZero n`, index zéro-source `n − 1`, `Terminal/CanonicalEnumeration.lean`). La
multiplicité est le coefficient de l'identité arithmétique retenue (`zetaZeroMultiplicity`) ; la
simplicité n'est supposée nulle part. -/
noncomputable def canonicalContributions {m : ℕ} (xs : Fin m → ℝ) (n : ℕ) :
    EuclideanSpace ℝ (Fin m) :=
  (zetaZeroMultiplicity (zeroPoint (canonicalZero n)) : ℝ) •
    normalizedSupportContribution xs (canonicalZero n)

/-- Le membre de rang `1` de l'instance est l'ancre des théorèmes de fermeture. -/
theorem canonicalContributions_first_anchor : sUpperZerosBelow (canonicalZero 1).1 = ∅ :=
  canonicalZero_one_bottom

/-- Le canal brut **au milieu des sauts** : `ψ₀(x) = (ψ(x) + ψ(x⁻))/2`. -/
noncomputable def chebyshevMidpoint (x : ℝ) : ℝ :=
  (1 / 2) * (Chebyshev.psi x + Filter.limUnder (nhdsWithin x (Set.Iio x)) Chebyshev.psi)

/-- Le fond du canal brut : `x − log 2π − ½ log(1 − x⁻²)`. -/
noncomputable def rawBackground (x : ℝ) : ℝ :=
  x - Real.log (2 * Real.pi) - (1 / 2) * Real.log (1 - x⁻¹ ^ 2)

/-- **Le reste exact du canal brut** : `ψ₀(x) −` fond, écrit avec les seuls premiers. -/
noncomputable def rawRemainder (x : ℝ) : ℝ := chebyshevMidpoint x - rawBackground x

/-- Le reste exact normalisé par `√x`. -/
noncomputable def normalizedRawRemainder (x : ℝ) : ℝ := rawRemainder x / Real.sqrt x

/-- **Le vecteur du reste exact normalisé aux abscisses du support** : le `R` de l'instance. -/
noncomputable def normalizedRawRemainderVector {m : ℕ} (xs : Fin m → ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => normalizedRawRemainder (xs i)

theorem normalizedRawRemainderVector_apply {m : ℕ} (xs : Fin m → ℝ) (i : Fin m) :
    normalizedRawRemainderVector xs i = normalizedRawRemainder (xs i) := rfl

/-- **La prémisse sur les objets arithmétiques corrigés** (support d'abscisses `> 1`, contributions
canoniques normalisées, reste exact normalisé) : la relation collective de chaque rang est bornée
par
celle du rang `1`, et l'énergie normalisée de chaque rang est bornée par ses amplitudes. Aucune
convergence n'est supposée ; la représentation du reste brut par les contributions (ordonnée) reste
une obligation identifiée, non posée ici. -/
theorem firstGain_canonical {m : ℕ} (xs : Fin m → ℝ) (hxs : ∀ i, 1 < xs i)
    (hGain : ∀ n : ℕ, 1 ≤ n →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1)
    {n : ℕ} (hn : 1 ≤ n) :
    (‖canonicalContributions xs n‖ ^ 2 +
        2 * ⟪partialRemainder (canonicalContributions xs) (normalizedRawRemainderVector xs) (n + 1),
          canonicalContributions xs n⟫_ℝ ≤
      ‖canonicalContributions xs 1‖ ^ 2 +
        2 * ⟪partialRemainder (canonicalContributions xs) (normalizedRawRemainderVector xs) 2,
          canonicalContributions xs 1⟫_ℝ) ∧
    ‖canonicalContributions xs n‖ ^ 2 ≤
      (zetaZeroMultiplicity (zeroPoint (canonicalZero n)) : ℝ) ^ 2 *
      ∑ i, pairAmplitude (canonicalZero n) (xs i) ^ 2 := by
  refine ⟨firstGain_relation _ _ hGain hn, ?_⟩
  have _ := hxs
  unfold canonicalContributions
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_left (normalizedSupportContribution_normSq_le xs _) (sq_nonneg _)

/-- **Lecture par l'interaction sur l'instance** : si l'interaction du rang `n` avec son reste est
au
moins celle du rang `1`, l'énergie normalisée du rang `n` reste sous celle du rang `1`. L'hypothèse
d'interaction n'est pas dérivée de la prémisse. -/
theorem canonical_norm_le_first_of_interaction {m : ℕ} (xs : Fin m → ℝ)
    (hGain : ∀ n : ℕ, 1 ≤ n →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1)
    {n : ℕ} (hn : 1 ≤ n)
    (hInt : ⟪partialRemainder (canonicalContributions xs) (normalizedRawRemainderVector xs) 2,
        canonicalContributions xs 1⟫_ℝ ≤
      ⟪partialRemainder (canonicalContributions xs) (normalizedRawRemainderVector xs) (n + 1),
        canonicalContributions xs n⟫_ℝ) :
    ‖canonicalContributions xs n‖ ≤ ‖canonicalContributions xs 1‖ :=
  norm_le_first_of_interaction_ordered _ _ hGain hn hInt

/-! ## 7. Le canal lissé : représentation exacte DÉMONTRÉE dans l'ordre canonique -/

/-- Contribution lissée normalisée du membre et de son conjugué : `2·Re(−m x^ρ/(ρ(ρ+1)))/√x`. -/
noncomputable def normalizedSmoothedPairContribution (z : TrueZero) (x : ℝ) : ℝ :=
  2 * (nontrivialZeroResidueTerm x (memberIndex z)).re / Real.sqrt x

/-- Le reste lissé normalisé : `Re(smoothedRemainder x)/√x`. -/
noncomputable def normalizedSmoothedRemainder (x : ℝ) : ℝ := (smoothedRemainder x).re / Real.sqrt x

/-- **Passage lissé → brut, membre par membre** : la contribution lissée normalisée est la partie
réelle
du facteur de lissage `−m/(ρ+1)` appliqué à la Tour brute, ramenée à `√x` ; le facteur change
l'amplitude et tourne la phase (`residueTerm_im_at_own_contact_ne_zero`). Rien ne transporte la
convergence absolue de la somme lissée vers la somme brute. -/
theorem normalizedSmoothedPairContribution_eq (z : TrueZero) (x : ℝ) :
    normalizedSmoothedPairContribution z x =
      2 * (smoothingFactor z * zeroTerm z x).re / Real.sqrt x := by
  unfold normalizedSmoothedPairContribution
  rw [residueTerm_eq_smoothingFactor_mul]

/-- Le terme lissé du conjugué est le conjugué du terme lissé (`x > 0`). -/
theorem residueTerm_conjIndex (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    nontrivialZeroResidueTerm x (conjIndex z) =
      (starRingEnd ℂ) (nontrivialZeroResidueTerm x (memberIndex z)) := by
  unfold nontrivialZeroResidueTerm conjIndex memberIndex
  simp only
  rw [zetaZeroMultiplicity_conj (zeroPoint_isNontrivial z).1, ← perronKernel_conj hx]
  simp

/-- **Représentation exacte du reste lissé normalisé, démontrée, dans l'ordre canonique** : la somme
sur `n` des contributions lissées normalisées du membre canonique d'index `n` (regroupé avec son
conjugué) converge (absolument) vers le reste lissé normalisé, `x > 1`. -/
theorem normalizedSmoothedPairContribution_hasSum {x : ℝ} (hx : 1 < x) :
    HasSum (fun n : ℕ => normalizedSmoothedPairContribution (canonicalMember n) x)
      (normalizedSmoothedRemainder x) := by
  have hx0 : 0 < x := by linarith
  have hS : HasSum (fun σ : ExplicitIndex => nontrivialZeroResidueTerm x σ)
      (smoothedRemainder x) := by
    rw [smoothedRemainder_eq_tsum_residueTerm hx]
    exact (nontrivial_zero_residue_series_summable hx).hasSum
  have hRe := Complex.hasSum_re hS
  have hE : HasSum (fun p : ℕ × Bool => (nontrivialZeroResidueTerm x (indexEquiv.symm p)).re)
      (smoothedRemainder x).re :=
    (Equiv.hasSum_iff indexEquiv.symm).mpr hRe
  have hF : HasSum
      (fun n : ℕ => 2 * (nontrivialZeroResidueTerm x (memberIndex (canonicalMember n))).re)
      (smoothedRemainder x).re := by
    refine hE.prod_fiberwise fun n => ?_
    have h := hasSum_fintype
      fun b : Bool => (nontrivialZeroResidueTerm x (indexEquiv.symm (n, b))).re
    convert h using 1
    rw [Fintype.sum_bool, indexEquiv_symm_true, indexEquiv_symm_false, residueTerm_conjIndex _ hx0,
      Complex.conj_re]
    ring
  unfold normalizedSmoothedPairContribution normalizedSmoothedRemainder
  exact hF.div_const _

/-- Vecteur de contribution lissée normalisée sur le support. -/
noncomputable def normalizedSmoothedSupportContribution {m : ℕ} (xs : Fin m → ℝ) (z : TrueZero) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => normalizedSmoothedPairContribution z (xs i)

/-- Contribution lissée canonique de rang `n`. -/
noncomputable def smoothedCanonicalContributions {m : ℕ} (xs : Fin m → ℝ) (n : ℕ) :
    EuclideanSpace ℝ (Fin m) :=
  normalizedSmoothedSupportContribution xs (canonicalZero n)

/-- Le vecteur du reste lissé normalisé aux abscisses du support. -/
noncomputable def normalizedSmoothedRemainderVector {m : ℕ} (xs : Fin m → ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => normalizedSmoothedRemainder (xs i)

/-- **Représentation exacte sur le support, démontrée** : `HasSum` des contributions lissées
canoniques
(rangs `≥ 1`) vers le vecteur du reste lissé normalisé, pour tout support d'abscisses `> 1`. -/
theorem smoothedCanonical_hasSum {m : ℕ} (xs : Fin m → ℝ) (hxs : ∀ i, 1 < xs i) :
    HasSum (fun j => smoothedCanonicalContributions xs (j + 1))
      (normalizedSmoothedRemainderVector xs) := by
  have h : HasSum (fun j => fun i => normalizedSmoothedPairContribution (canonicalMember j) (xs i))
      (fun i => normalizedSmoothedRemainder (xs i)) :=
    Pi.hasSum.mpr fun i => normalizedSmoothedPairContribution_hasSum (hxs i)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.hasSum'
    (f := fun j => fun i => normalizedSmoothedPairContribution (canonicalMember j) (xs i))
    (x := fun i => normalizedSmoothedRemainder (xs i))).mpr h

/-- **La prémisse sur le canal lissé, représentation démontrée** : `D_n = ‖c_n‖² + 2⟨Σ_{j>n} c_j,
c_n⟩`
avec la somme des suivants au sens de `HasSum`, et la relation collective de chaque rang bornée par
celle du rang `1`. -/
theorem firstGain_smoothed_collective {m : ℕ} (xs : Fin m → ℝ) (hxs : ∀ i, 1 < xs i)
    (hGain : ∀ n : ℕ, 1 ≤ n →
      collectiveGain (smoothedCanonicalContributions xs) (normalizedSmoothedRemainderVector xs) n ≤
        collectiveGain (smoothedCanonicalContributions xs) (normalizedSmoothedRemainderVector xs) 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖smoothedCanonicalContributions xs n‖ ^ 2 +
        2 * ⟪followingContributions (smoothedCanonicalContributions xs) n,
          smoothedCanonicalContributions xs n⟫_ℝ ≤
      ‖smoothedCanonicalContributions xs 1‖ ^ 2 +
        2 * ⟪followingContributions (smoothedCanonicalContributions xs) 1,
          smoothedCanonicalContributions xs 1⟫_ℝ :=
  firstGain_collective_relation (smoothedCanonical_hasSum xs hxs) hGain hn

/-! ## 8. Fermeture : domination individuelle ⟹ RH ; la conclusion du raccord ouvert est
`∀ w, InsideField (canonicalZero 1) w` -/


/-! ## 8. Décomposition exacte du gain : énergie propre, interaction, marge (directive de l'auteur,
2026-10-06, point 3) — identités algébriques, aucune hypothèse de convergence -/

/-- **Énergie propre** du rang `n` sur le support : `E_n = ‖c_n‖²`. -/
noncomputable def ownEnergy (c : ℕ → V) (n : ℕ) : ℝ := ‖c n‖ ^ 2

/-- **Interaction** du rang `n` avec le reste après ce rang : `I_n = ⟨r_n, c_n⟩`,
`r_n = R − Σ_{j≤n} c_j = partialRemainder c R (n + 1)`. -/
noncomputable def interaction (c : ℕ → V) (R : V) (n : ℕ) : ℝ :=
  ⟪partialRemainder c R (n + 1), c n⟫_ℝ

/-- `D_n = E_n + 2 I_n`. -/
theorem collectiveGain_eq_ownEnergy_add_interaction (c : ℕ → V) (R : V) {n : ℕ} (hn : 1 ≤ n) :
    collectiveGain c R n = ownEnergy c n + 2 * interaction c R n :=
  collectiveGain_eq_own_add_interaction c R hn

/-- **La marge de la prémisse, décomposée** : `D_1 − D_n = (E_1 − E_n) − 2(I_n − I_1)`. -/
theorem gain_margin_eq (c : ℕ → V) (R : V) {n : ℕ} (hn : 1 ≤ n) :
    collectiveGain c R 1 - collectiveGain c R n =
      (ownEnergy c 1 - ownEnergy c n) - 2 * (interaction c R n - interaction c R 1) := by
  rw [collectiveGain_eq_ownEnergy_add_interaction c R hn,
    collectiveGain_eq_ownEnergy_add_interaction c R le_rfl]
  ring

/-- **L'excès d'énergie propre, exactement** : `E_n − E_1 = 2(I_1 − I_n) − (D_1 − D_n)`. -/
theorem ownEnergy_diff_eq (c : ℕ → V) (R : V) {n : ℕ} (hn : 1 ≤ n) :
    ownEnergy c n - ownEnergy c 1 =
      2 * (interaction c R 1 - interaction c R n) -
        (collectiveGain c R 1 - collectiveGain c R n) := by
  rw [gain_margin_eq c R hn]
  ring

/-- **Sous la prémisse** : `E_n − E_1 ≤ 2(I_1 − I_n)`. -/
theorem ownEnergy_diff_le_of_gain (c : ℕ → V) (R : V)
    (hGain : ∀ n : ℕ, 1 ≤ n → collectiveGain c R n ≤ collectiveGain c R 1) {n : ℕ} (hn : 1 ≤ n) :
    ownEnergy c n - ownEnergy c 1 ≤ 2 * (interaction c R 1 - interaction c R n) := by
  rw [ownEnergy_diff_eq c R hn]
  linarith [hGain n hn]

/-- **Le contrôle requis, identifié exactement** : `E_n ≤ E_1 ⟺ 2(I_1 − I_n) ≤ D_1 − D_n`. La marge
`D_1 − D_n ≥ 0` est la prémisse elle-même ; cette équivalence nomme la borne à établir, elle ne la
démontre pas. La condition `I_1 ≤ I_n` (hypothèse de `norm_le_first_of_interaction_ordered`) est
suffisante, pas nécessaire. -/
theorem ownEnergy_le_first_iff (c : ℕ → V) (R : V) {n : ℕ} (hn : 1 ≤ n) :
    ownEnergy c n ≤ ownEnergy c 1 ↔
      2 * (interaction c R 1 - interaction c R n) ≤
        collectiveGain c R 1 - collectiveGain c R n := by
  have h := ownEnergy_diff_eq c R hn
  constructor <;> intro h' <;> linarith

/-- La même équivalence, lue sur les normes : `‖c_n‖ ≤ ‖c_1‖ ⟺ 2(I_1 − I_n) ≤ D_1 − D_n`. -/
theorem norm_le_first_iff_interaction_margin (c : ℕ → V) (R : V) {n : ℕ} (hn : 1 ≤ n) :
    ‖c n‖ ≤ ‖c 1‖ ↔
      2 * (interaction c R 1 - interaction c R n) ≤
        collectiveGain c R 1 - collectiveGain c R n := by
  rw [← ownEnergy_le_first_iff c R hn]
  unfold ownEnergy
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).symm

/-- `I_1 ≤ I_n` entraîne le contrôle requis sous la prémisse (suffisance, non nécessité). -/
theorem interaction_margin_of_interaction_ordered (c : ℕ → V) (R : V)
    (hGain : ∀ n : ℕ, 1 ≤ n → collectiveGain c R n ≤ collectiveGain c R 1) {n : ℕ} (hn : 1 ≤ n)
    (hInt : interaction c R 1 ≤ interaction c R n) :
    2 * (interaction c R 1 - interaction c R n) ≤
      collectiveGain c R 1 - collectiveGain c R n := by
  linarith [hGain n hn]

/-- **Sur l'instance canonique** : `‖c_n‖ ≤ ‖c_1‖ ⟺ 2(I_1 − I_n) ≤ D_1 − D_n`, avec les objets
réellement définis (contributions canoniques normalisées, reste exact normalisé). -/
theorem canonical_norm_le_first_iff {m : ℕ} (xs : Fin m → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ‖canonicalContributions xs n‖ ≤ ‖canonicalContributions xs 1‖ ↔
      2 * (interaction (canonicalContributions xs) (normalizedRawRemainderVector xs) 1 -
            interaction (canonicalContributions xs) (normalizedRawRemainderVector xs) n) ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1 -
          collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n :=
  norm_le_first_iff_interaction_margin _ _ hn

/-- **Sous la prémisse, sur l'instance** : `E_n − E_1 ≤ 2(I_1 − I_n)`. -/
theorem canonical_ownEnergy_diff_le {m : ℕ} (xs : Fin m → ℝ)
    (hGain : ∀ n : ℕ, 1 ≤ n →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ownEnergy (canonicalContributions xs) n - ownEnergy (canonicalContributions xs) 1 ≤
      2 * (interaction (canonicalContributions xs) (normalizedRawRemainderVector xs) 1 -
        interaction (canonicalContributions xs) (normalizedRawRemainderVector xs) n) :=
  ownEnergy_diff_le_of_gain _ _ hGain hn

/-! ## 9. Décomposition des interactions en paramètres de phase (directive, point 4) : produit de
deux contributions, pour TOUTE position radiale -/

/-- **Enveloppe brute** d'un membre : `a_z(x) = 2x^β/√(β² + T²)` ; `c_z(x) = −a_z(x) cos(T log x −
φ)`. -/
noncomputable def pairEnvelope (z : TrueZero) (x : ℝ) : ℝ :=
  2 * x ^ rZeroRadialPosition z.1 / Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2)

/-- **Phase** d'un membre : `φ_z = arctan(T/β)` (la phase de sa Tour). -/
noncomputable def memberPhase (z : TrueZero) : ℝ :=
  Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1)

theorem memberPhase_eq_towerPhase (z : TrueZero) : memberPhase z = (towerMotionOf z).phase :=
  (towerMotion_phase z).symm

/-- `c_z(x) = −a_z(x) · cos(T_z log x − φ_z)`. -/
theorem pairContribution_eq_envelope_cos (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    pairContribution z x =
      -(pairEnvelope z x) * Real.cos (rZeroHeight z.1 * Real.log x - memberPhase z) := by
  rw [pairContribution_eq hx]
  unfold pairEnvelope memberPhase
  ring

/-- L'enveloppe brute est positive. -/
theorem pairEnvelope_pos (z : TrueZero) {x : ℝ} (hx : 0 < x) : 0 < pairEnvelope z x := by
  unfold pairEnvelope
  have hT : 0 < rZeroHeight z.1 := z.2
  have hx' := Real.rpow_pos_of_pos hx (rZeroRadialPosition z.1)
  exact div_pos (by linarith) (Real.sqrt_pos.mpr (by positivity))

/-- Amplitude normalisée = enveloppe brute / `√x`. -/
theorem pairAmplitude_eq_envelope_div (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    pairAmplitude z x = pairEnvelope z x / Real.sqrt x := by
  rw [pairAmplitude_eq_abs_div, norm_zeroTerm_eq z hx, zeroPoint_norm_eq_sqrt_sum]
  unfold pairEnvelope
  ring

/-- **Produit de deux contributions brutes** (toute position radiale, aucun membre supposé ON) :
`c_z(x) c_w(x) = (a_z a_w / 2)·[cos((T_z − T_w) log x − (φ_z − φ_w)) + cos((T_z + T_w) log x − (φ_z
+ φ_w))]`. -/
theorem pairContribution_mul (z w : TrueZero) {x : ℝ} (hx : 0 < x) :
    pairContribution z x * pairContribution w x =
      pairEnvelope z x * pairEnvelope w x / 2 *
        (Real.cos ((rZeroHeight z.1 - rZeroHeight w.1) * Real.log x -
            (memberPhase z - memberPhase w)) +
          Real.cos ((rZeroHeight z.1 + rZeroHeight w.1) * Real.log x -
            (memberPhase z + memberPhase w))) := by
  rw [pairContribution_eq_envelope_cos z hx, pairContribution_eq_envelope_cos w hx]
  have h1 : (rZeroHeight z.1 - rZeroHeight w.1) * Real.log x - (memberPhase z - memberPhase w) =
      (rZeroHeight z.1 * Real.log x - memberPhase z) -
        (rZeroHeight w.1 * Real.log x - memberPhase w) := by ring
  have h2 : (rZeroHeight z.1 + rZeroHeight w.1) * Real.log x - (memberPhase z + memberPhase w) =
      (rZeroHeight z.1 * Real.log x - memberPhase z) +
        (rZeroHeight w.1 * Real.log x - memberPhase w) := by ring
  rw [h1, h2, ← Real.two_mul_cos_mul_cos]
  ring

/-- **Produit de deux contributions normalisées** : `(c_z/√x)(c_w/√x) = (A_z A_w / 2)·[cos(…) +
cos(…)]`. -/
theorem normalizedPairContribution_mul (z w : TrueZero) {x : ℝ} (hx : 0 < x) :
    normalizedPairContribution z x * normalizedPairContribution w x =
      pairAmplitude z x * pairAmplitude w x / 2 *
        (Real.cos ((rZeroHeight z.1 - rZeroHeight w.1) * Real.log x -
            (memberPhase z - memberPhase w)) +
          Real.cos ((rZeroHeight z.1 + rZeroHeight w.1) * Real.log x -
            (memberPhase z + memberPhase w))) := by
  unfold normalizedPairContribution
  rw [pairAmplitude_eq_envelope_div z hx, pairAmplitude_eq_envelope_div w hx,
    div_mul_div_comm, pairContribution_mul z w hx, div_mul_div_comm]
  ring

/-- **Le produit scalaire de deux contributions canoniques sur le support fini**, comme somme exacte
des produits de phase aux abscisses du support, avec les multiplicités et la normalisation
réellement
définies : `⟨c_n, c_j⟩ = m_n m_j Σ_i (A_n A_j / 2)(x_i)·[cos(…) + cos(…)]`. -/
theorem canonical_inner_eq_phase_sum {m : ℕ} (xs : Fin m → ℝ) (hxs : ∀ i, 1 < xs i) (n j : ℕ) :
    ⟪canonicalContributions xs n, canonicalContributions xs j⟫_ℝ =
      (zetaZeroMultiplicity (zeroPoint (canonicalZero n)) : ℝ) *
        (zetaZeroMultiplicity (zeroPoint (canonicalZero j)) : ℝ) *
        ∑ i, pairAmplitude (canonicalZero n) (xs i) * pairAmplitude (canonicalZero j) (xs i) / 2 *
          (Real.cos ((rZeroHeight (canonicalZero n).1 - rZeroHeight (canonicalZero j).1) *
                Real.log (xs i) - (memberPhase (canonicalZero n) - memberPhase (canonicalZero j))) +
            Real.cos ((rZeroHeight (canonicalZero n).1 + rZeroHeight (canonicalZero j).1) *
                Real.log (xs i) -
                (memberPhase (canonicalZero n) + memberPhase (canonicalZero j)))) := by
  unfold canonicalContributions
  rw [inner_smul_left, inner_smul_right, PiLp.inner_apply, mul_assoc]
  simp only [RCLike.inner_apply, conj_trivial, normalizedSupportContribution_apply]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := normalizedPairContribution_mul (canonicalZero n) (canonicalZero j)
    (by linarith [hxs i] : (0 : ℝ) < xs i)
  first | rw [h] | rw [mul_comm, h]

/-! ## 10. Interaction par queue finie (directive, point 4) : décomposition exacte, puis limite
ordonnée, puis canal lissé -/

/-- **Queue finie** `Q_{n,N} = Σ_{j=n+1}^{N} c_j`. -/
noncomputable def tailSum (c : ℕ → V) (n N : ℕ) : V := ∑ j ∈ Finset.Ioc n N, c j

/-- `⟨Q_{n,N}, c_n⟩ = Σ_{j=n+1}^{N} ⟨c_j, c_n⟩` : décomposition finie, aucune hypothèse analytique.
-/
theorem inner_tailSum (c : ℕ → V) (n N : ℕ) :
    ⟪tailSum c n N, c n⟫_ℝ = ∑ j ∈ Finset.Ioc n N, ⟪c j, c n⟫_ℝ := by
  unfold tailSum
  rw [sum_inner]

omit [InnerProductSpace ℝ V] in
/-- Le reste après le rang `n` est la queue finie jusqu'à `N` plus le reste après `N` (`n ≤ N`). -/
theorem partialRemainder_eq_tailSum_add (c : ℕ → V) (R : V) {n N : ℕ} (hnN : n ≤ N) :
    partialRemainder c R (n + 1) = tailSum c n N + partialRemainder c R (N + 1) := by
  unfold partialRemainder tailSum
  have h : ∑ j ∈ Finset.Ico 1 (n + 1), c j + ∑ j ∈ Finset.Ico (n + 1) (N + 1), c j =
      ∑ j ∈ Finset.Ico 1 (N + 1), c j :=
    Finset.sum_Ico_consecutive _ (by omega) (by omega)
  have hIoc : Finset.Ioc n N = Finset.Ico (n + 1) (N + 1) := by
    ext j; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hIoc, ← h]
  abel

/-- **L'interaction, exactement, par queue finie** : `I_n = ⟨Q_{n,N}, c_n⟩ + ⟨r_N, c_n⟩`. -/
theorem interaction_eq_tail_add (c : ℕ → V) (R : V) {n N : ℕ} (hnN : n ≤ N) :
    interaction c R n =
      ∑ j ∈ Finset.Ioc n N, ⟪c j, c n⟫_ℝ + ⟪partialRemainder c R (N + 1), c n⟫_ℝ := by
  unfold interaction
  rw [partialRemainder_eq_tailSum_add c R hnN, inner_add_left, inner_tailSum]

/-- **Sous la représentation ORDONNÉE** (sommes partielles dans l'ordre canonique tendant vers `R`),
l'interaction est la limite des interactions de queue finie : `⟨Q_{n,N}, c_n⟩ → I_n`. Aucun
`HasSum`. -/
theorem interaction_tendsto_of_ordered {c : ℕ → V} {R : V}
    (hRep : Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, c (j + 1)) Filter.atTop (nhds R))
    (n : ℕ) :
    Filter.Tendsto (fun N => ∑ j ∈ Finset.Ioc n N, ⟪c j, c n⟫_ℝ) Filter.atTop
      (nhds (interaction c R n)) := by
  have h : Filter.Tendsto (fun N => ⟪∑ j ∈ Finset.Ico (n + 1) (N + 1), c j, c n⟫_ℝ)
      Filter.atTop (nhds ⟪partialRemainder c R (n + 1), c n⟫_ℝ) :=
    (following_partial_sums_tendsto hRep n).inner tendsto_const_nhds
  have hIoc : ∀ N, Finset.Ioc n N = Finset.Ico (n + 1) (N + 1) := by
    intro N; ext j; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  refine h.congr fun N => ?_
  rw [hIoc, ← sum_inner]

/-- **Canal à représentation absolument convergente** (`HasSum`, cas du canal lissé) : l'interaction
est la somme de la série des produits scalaires avec les suivants. -/
theorem interaction_hasSum {c : ℕ → V} {R : V} (hRep : HasSum (fun j => c (j + 1)) R) {n : ℕ}
    (hn : 1 ≤ n) :
    HasSum (fun j => ⟪c n, c (j + n + 1)⟫_ℝ) (interaction c R n) := by
  unfold interaction
  rw [partialRemainder_succ c R hn, real_inner_comm]
  exact (innerSL ℝ (c n)).hasSum (followingContributions_hasSum hRep hn)

/-- Sur l'instance canonique du canal LISSÉ (représentation démontrée), l'interaction du rang `n`
est
la somme convergente de ses produits scalaires avec tous les suivants. -/
theorem smoothedCanonical_interaction_hasSum {m : ℕ} (xs : Fin m → ℝ) (hxs : ∀ i, 1 < xs i)
    {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun j => ⟪smoothedCanonicalContributions xs n,
        smoothedCanonicalContributions xs (j + n + 1)⟫_ℝ)
      (interaction (smoothedCanonicalContributions xs) (normalizedSmoothedRemainderVector xs) n) :=
  interaction_hasSum (smoothedCanonical_hasSum xs hxs) hn

/-! ## 11. Résultats ON à leur portée exacte (directive, point 5) : amplitude par unité de
multiplicité, coefficient total, pas des contacts -/

/-- La multiplicité d'un vrai zéro est au moins un. -/
theorem canonical_multiplicity_pos (n : ℕ) :
    0 < (zetaZeroMultiplicity (zeroPoint (canonicalZero n)) : ℝ) := by
  exact_mod_cast zetaZeroMultiplicity_pos (canonicalZero n).1.2.1

/-- La contribution canonique en une abscisse est multiplicité × contribution normalisée : le
coefficient total se sépare de l'amplitude par unité de multiplicité. -/
theorem canonicalContributions_apply {m : ℕ} (xs : Fin m → ℝ) (n : ℕ) (i : Fin m) :
    canonicalContributions xs n i =
      (zetaZeroMultiplicity (zeroPoint (canonicalZero n)) : ℝ) *
        normalizedPairContribution (canonicalZero n) (xs i) := rfl

/-- **ON, à multiplicité ÉGALE** : la hauteur plus grande donne l'amplitude pondérée strictement
plus
petite. Sans égalité des multiplicités, aucune conclusion sur la contribution pondérée. -/
theorem weighted_amplitude_onLine_lt_of_height {z w : TrueZero}
    (hz : rZeroRadialPosition z.1 = 1 / 2) (hw : rZeroRadialPosition w.1 = 1 / 2)
    (hT : rZeroHeight z.1 < rZeroHeight w.1)
    (hm : zetaZeroMultiplicity (zeroPoint z) = zetaZeroMultiplicity (zeroPoint w)) {x : ℝ}
    (hx : 0 < x) :
    (zetaZeroMultiplicity (zeroPoint w) : ℝ) * pairAmplitude w x <
      (zetaZeroMultiplicity (zeroPoint z) : ℝ) * pairAmplitude z x := by
  rw [hm]
  have hpos : (0 : ℝ) < zetaZeroMultiplicity (zeroPoint w) := by
    exact_mod_cast zetaZeroMultiplicity_pos w.1.2.1
  exact mul_lt_mul_of_pos_left (pairAmplitude_onLine_lt_of_height hz hw hT hx) hpos

/-- **Pas de l'amplitude entre deux contacts propres**, toute position radiale :
`A(C_{k+1})/A(C_k) = e^{(β − 1/2) π/T}` (conséquence des paramètres, pas une contrainte nouvelle).
-/
theorem pairAmplitude_own_contact_step (z : TrueZero) (k : ℤ) :
    pairAmplitude z (contactMinusAt z (k + 1)) / pairAmplitude z (contactMinusAt z k) =
      Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * (Real.pi / rZeroHeight z.1)) := by
  unfold pairAmplitude
  rw [mul_div_mul_left _ _ (two_ne_zero), normalizedRadius_own_contact_step]
  rfl

/-! ## 12. Progression première et phases relatives aux raccords canoniques (directive, point 6) -/

/-- **Phase relative de deux membres entre deux abscisses** : la différence des arguments du terme
de battement `(T_z − T_w) log x − (φ_z − φ_w)` entre `x` et `y` est `(T_z − T_w) log(y/x)`. -/
theorem relative_phase_diff (z w : TrueZero) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ((rZeroHeight z.1 - rZeroHeight w.1) * Real.log y - (memberPhase z - memberPhase w)) -
      ((rZeroHeight z.1 - rZeroHeight w.1) * Real.log x - (memberPhase z - memberPhase w)) =
      (rZeroHeight z.1 - rZeroHeight w.1) * Real.log (y / x) := by
  rw [Real.log_div hy.ne' hx.ne']
  ring

/-- **Au raccord de rang `k`** (`p_k → p_{k+1}`) : `Δθ_{z,w} = (T_z − T_w) log(p_{k+1}/p_k)`,
différence des progressions de phase propres `Δθ_z − Δθ_w` (identité acquise `Δθ_z = T_z
log(p_{k+1}/p_k)`). -/
theorem relative_phaseIncrement (z w : TrueZero) (k : ℕ) :
    phaseIncrement z k - phaseIncrement w k =
      (rZeroHeight z.1 - rZeroHeight w.1) * rPrimeGapLogRatio k := by
  rw [phaseIncrement_eq_height_mul_ratio, phaseIncrement_eq_height_mul_ratio]
  ring

/-- **Sur une fenêtre de `m` événements**, les phases relatives télescopent :
`Σ_{j<m} (Δθ_z − Δθ_w)(n + j) = (T_z − T_w) log(p_{n+m}/p_n)`. -/
theorem relative_phase_window_sum (z w : TrueZero) (n m : ℕ) :
    ∑ j ∈ Finset.range m, (phaseIncrement z (n + j) - phaseIncrement w (n + j)) =
      (rZeroHeight z.1 - rZeroHeight w.1) *
        (Real.log (fnPrimeAtRank (n + m) : ℝ) - Real.log (fnPrimeAtRank n : ℝ)) := by
  rw [← primeGapLogRatio_window_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => relative_phaseIncrement z w (n + j)

/-- **Plancher de la phase relative sur une fenêtre paire** (écarts `2, 4` : `p_{n+m} − p_n ≥ 3m`
pour `p_n > 3`) : `|T_z − T_w| · log(1 + 3m/p_n) ≤ |Σ_{j<m} (Δθ_z − Δθ_w)(n + j)|`. Portée exacte :
l'écart des hauteurs `|T_z − T_w|` figure en facteur dans le plancher ; le théorème mesure l'effet
de cet écart sur la phase relative, il ne produit pas cet écart. Rien sur le signe du cosinus ni
sur une hausse de hauteur. -/
theorem relative_phase_window_ge (z w : TrueZero) (n m : ℕ) (hm : Even m)
    (h3 : 3 < fnPrimeAtRank n) :
    |rZeroHeight z.1 - rZeroHeight w.1| * Real.log (1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ)) ≤
      |∑ j ∈ Finset.range m, (phaseIncrement z (n + j) - phaseIncrement w (n + j))| := by
  rw [relative_phase_window_sum, abs_mul]
  have h0 : (0 : ℝ) < (fnPrimeAtRank n : ℝ) := by exact_mod_cast thm_primeAtRank_pos n
  have hm' : (0 : ℝ) < (fnPrimeAtRank (n + m) : ℝ) := by exact_mod_cast thm_primeAtRank_pos _
  have hlog : Real.log (1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ)) ≤
      Real.log (fnPrimeAtRank (n + m) : ℝ) - Real.log (fnPrimeAtRank n : ℝ) := by
    rw [← Real.log_div hm'.ne' h0.ne']
    exact primeWindow_log_ge n m hm h3
  have hnn : 0 ≤ Real.log (1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ)) :=
    Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  calc |rZeroHeight z.1 - rZeroHeight w.1| * Real.log (1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ))
      ≤ |rZeroHeight z.1 - rZeroHeight w.1| *
          (Real.log (fnPrimeAtRank (n + m) : ℝ) - Real.log (fnPrimeAtRank n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    _ ≤ |rZeroHeight z.1 - rZeroHeight w.1| *
          |Real.log (fnPrimeAtRank (n + m) : ℝ) - Real.log (fnPrimeAtRank n : ℝ)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)

/-- **Les phases relatives aux raccords canoniques** : pour deux rangs `n < j`, le battement entre
`z_n` et `z_j` avance, de l'abscisse `x` à `y`, de `(T_n − T_j) log(y/x)` ; en particulier, d'un
premier
au suivant, de `(T_n − T_j) log(p_{k+1}/p_k)`. (Instance de `relative_phase_diff`.) -/
theorem canonical_relative_phase_step (n j k : ℕ) :
    ((rZeroHeight (canonicalZero n).1 - rZeroHeight (canonicalZero j).1) *
        Real.log (fnPrimeSuccessor k : ℝ) -
        (memberPhase (canonicalZero n) - memberPhase (canonicalZero j))) -
      ((rZeroHeight (canonicalZero n).1 - rZeroHeight (canonicalZero j).1) *
        Real.log (fnPrimeAtRank k : ℝ) -
        (memberPhase (canonicalZero n) - memberPhase (canonicalZero j))) =
      (rZeroHeight (canonicalZero n).1 - rZeroHeight (canonicalZero j).1) *
        rPrimeGapLogRatio k := by
  have h0 : (0 : ℝ) < (fnPrimeAtRank k : ℝ) := by exact_mod_cast thm_primeAtRank_pos k
  have h1 : (0 : ℝ) < (fnPrimeSuccessor k : ℝ) := by
    unfold fnPrimeSuccessor; exact_mod_cast thm_primeAtRank_pos _
  rw [relative_phase_diff _ _ h0 h1]
  rfl

/-! ## 13. La grammaire compilée reliée aux paramètres des contributions (complément de l'auteur,
2026-10-06) : écart = `6·magnitude + classe`, sollicitation logarithmique, pas d'amplitude par
événement, fenêtres par canaux, liaison support premier ↔ support de la prémisse.
Objets réutilisés, aucune grammaire parallèle : `GoodMod6`, `state6`, `gapClass6`
(`Grammar/Mod6Rigidity.lean`), `fnPrimeAtRank`, `fnPrimeSuccessor`, `nPrimeGap`, `rPrimeGapLogRatio`
(rhv3_lean), `phaseIncrement` (`Terminal/InterTowerExcess.lean`), `stateIndicator`, `abMinusBa`
(`Terminal/GrammarWordLoad.lean`), planchers de fenêtre (`Terminal/WindowProgression.lean`). -/

/-- **Magnitude grammaticale** de l'événement `r` : `m_r = ⌊g_r/6⌋`, `g_r = p_{r+1} − p_r`.
Distincte
de la multiplicité d'un zéro (`zetaZeroMultiplicity`). -/
noncomputable def gapMagnitude (r : ℕ) : ℕ := nPrimeGap r / 6

/-- **Classe de l'événement `r`** : `a_r = g_r mod 6 = gapClass6 p_r p_{r+1}`. -/
noncomputable def eventClass (r : ℕ) : ℕ := gapClass6 (fnPrimeAtRank r) (fnPrimeSuccessor r)

theorem eventClass_eq_mod (r : ℕ) : eventClass r = nPrimeGap r % 6 := rfl

/-- **`g_r = 6 m_r + a_r`** : l'écart se lit par sa magnitude et sa classe. -/
theorem primeGap_eq_magnitude_class (r : ℕ) :
    nPrimeGap r = 6 * gapMagnitude r + eventClass r := by
  unfold gapMagnitude; rw [eventClass_eq_mod]; exact (Nat.div_add_mod _ _).symm

/-- **La classe vaut `0`, `2` ou `4`** dès que `p_r > 3` (deux états, quatre transitions dont deux
maintiens de classe `0`). -/
theorem eventClass_mem (r : ℕ) (h3 : 3 < fnPrimeAtRank r) :
    eventClass r = 0 ∨ eventClass r = 2 ∨ eventClass r = 4 :=
  gapClass6_mem (prime_goodMod6 _ (thm_primeAtRank_isPrime r) h3)
    (prime_goodMod6 _ (thm_primeAtRank_isPrime (r + 1))
      (lt_trans h3 (thm_primeAtRank_lt_successor r)))
    (thm_primeAtRank_lt_successor r).le

/-- Les deux maintiens sont distincts : classe `0` avec état `A` (`p ≡ 5`) ou état `B` (`p ≡ 1`) ;
les deux changements sont `A → B` (classe `2`) et `B → A` (classe `4`). -/
theorem eventClass_transitions (r : ℕ) (h3 : 3 < fnPrimeAtRank r) :
    (eventClass r = 0 ↔ state6 (fnPrimeAtRank r) = state6 (fnPrimeSuccessor r)) ∧
    (eventClass r = 2 ↔ state6 (fnPrimeAtRank r) = false ∧ state6 (fnPrimeSuccessor r) = true) ∧
    (eventClass r = 4 ↔ state6 (fnPrimeAtRank r) = true ∧ state6 (fnPrimeSuccessor r) = false) := by
  have hp := prime_goodMod6 _ (thm_primeAtRank_isPrime r) h3
  have hq := prime_goodMod6 _ (thm_primeAtRank_isPrime (r + 1))
    (lt_trans h3 (thm_primeAtRank_lt_successor r))
  have hle := (thm_primeAtRank_lt_successor r).le
  exact ⟨gapClass6_eq_zero_iff hp hq hle, gapClass6_eq_two_iff hp hq hle,
    gapClass6_eq_four_iff hp hq hle⟩

/-- **Alternance des changements** : deux événements consécutifs de classe non nulle ont des classes
différentes (`2` puis `4` ou `4` puis `2`). -/
theorem eventClass_alternates (r : ℕ) (h3 : 3 < fnPrimeAtRank r) (h1 : eventClass r ≠ 0)
    (h2 : eventClass (r + 1) ≠ 0) : eventClass r ≠ eventClass (r + 1) := by
  have hlt1 : fnPrimeAtRank r < fnPrimeAtRank (r + 1) := thm_primeAtRank_lt_successor r
  have hlt2 : fnPrimeAtRank (r + 1) < fnPrimeAtRank (r + 2) := thm_primeAtRank_lt_successor (r + 1)
  exact primeGapClass6_alternates (thm_primeAtRank_isPrime r) (thm_primeAtRank_isPrime (r + 1))
    (thm_primeAtRank_isPrime (r + 2)) h3 (lt_trans h3 hlt1) (lt_trans (lt_trans h3 hlt1) hlt2)
    hlt1.le hlt2.le h1 h2

/-- **Sollicitation logarithmique d'un événement** : `L_r = log(p_{r+1}/p_r) = log(1 + (6m_r +
a_r)/p_r)`. -/
theorem primeGapLogRatio_eq_log_one_add (r : ℕ) :
    rPrimeGapLogRatio r =
      Real.log (1 + (6 * (gapMagnitude r : ℝ) + (eventClass r : ℝ)) / (fnPrimeAtRank r : ℝ)) := by
  unfold rPrimeGapLogRatio
  have h0 : (0 : ℝ) < (fnPrimeAtRank r : ℝ) := by exact_mod_cast thm_primeAtRank_pos r
  have hg : (fnPrimeSuccessor r : ℝ) =
      fnPrimeAtRank r + (6 * (gapMagnitude r : ℝ) + eventClass r) := by
    have h := primeGap_eq_magnitude_class r
    unfold nPrimeGap at h
    have hlt := thm_primeAtRank_lt_successor r
    have : fnPrimeSuccessor r = fnPrimeAtRank r + (6 * gapMagnitude r + eventClass r) := by omega
    rw [this]; push_cast; ring
  rw [hg]
  congr 1
  field_simp

/-- **Phase traversée à hauteur fixée** sur l'événement `r` : `Δθ_{n,r} = T_n L_r` (identité
acquise,
`phaseIncrement_eq_height_mul_ratio`) ; elle n'est pas une progression de hauteur. -/
theorem phaseIncrement_eq_height_mul_logRatio (z : TrueZero) (r : ℕ) :
    phaseIncrement z r = rZeroHeight z.1 * rPrimeGapLogRatio r :=
  phaseIncrement_eq_height_mul_ratio z r

/-- **Pas de l'amplitude BRUTE par événement** : `B_n(p_{r+1})/B_n(p_r) = e^{β_n L_r}`. -/
theorem rawAmplitude_prime_step (z : TrueZero) (r : ℕ) :
    ‖zeroTerm z (fnPrimeSuccessor r : ℝ)‖ / ‖zeroTerm z (fnPrimeAtRank r : ℝ)‖ =
      Real.exp (rZeroRadialPosition z.1 * rPrimeGapLogRatio r) := by
  have h0 : (0 : ℝ) < (fnPrimeAtRank r : ℝ) := by exact_mod_cast thm_primeAtRank_pos r
  have h1 : (0 : ℝ) < (fnPrimeSuccessor r : ℝ) := by
    unfold fnPrimeSuccessor; exact_mod_cast thm_primeAtRank_pos _
  rw [norm_zeroTerm_eq z h0, norm_zeroTerm_eq z h1]
  unfold rPrimeGapLogRatio
  rw [mul_comm, Real.exp_mul, Real.exp_log (div_pos h1 h0), Real.div_rpow h1.le h0.le]
  have hN := norm_zeroPoint_pos z
  have hr := Real.rpow_pos_of_pos h0 (rZeroRadialPosition z.1)
  field_simp

/-- **Énergie brute par événement** : `B_n(p_{r+1})²/B_n(p_r)² = e^{2β_n L_r}`. -/
theorem rawEnergy_prime_step (z : TrueZero) (r : ℕ) :
    ‖zeroTerm z (fnPrimeSuccessor r : ℝ)‖ ^ 2 / ‖zeroTerm z (fnPrimeAtRank r : ℝ)‖ ^ 2 =
      Real.exp (2 * rZeroRadialPosition z.1 * rPrimeGapLogRatio r) := by
  rw [← div_pow, rawAmplitude_prime_step, ← Real.exp_nat_mul]
  push_cast; ring_nf

/-- **Pas de l'amplitude NORMALISÉE par événement** : `A_n(p_{r+1})/A_n(p_r) = e^{(β_n − 1/2) L_r}`,
toute position radiale. -/
theorem pairAmplitude_prime_step (z : TrueZero) (r : ℕ) :
    pairAmplitude z (fnPrimeSuccessor r : ℝ) / pairAmplitude z (fnPrimeAtRank r : ℝ) =
      Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * rPrimeGapLogRatio r) := by
  have h0 : (0 : ℝ) < (fnPrimeAtRank r : ℝ) := by exact_mod_cast thm_primeAtRank_pos r
  have h1 : (0 : ℝ) < (fnPrimeSuccessor r : ℝ) := by
    unfold fnPrimeSuccessor; exact_mod_cast thm_primeAtRank_pos _
  unfold pairAmplitude
  rw [mul_div_mul_left _ _ two_ne_zero, normalizedRadius_ratio z h0 h1]
  unfold rPrimeGapLogRatio
  rw [mul_comm, Real.exp_mul, Real.exp_log (div_pos h1 h0)]

/-- **Régime ON** : l'amplitude normalisée ne bouge pas d'un événement à l'autre ; la sollicitation
agit sur la seule phase, `Δθ_{n,r} = T_n L_r`. -/
theorem onLine_prime_step (z : TrueZero) (hz : rZeroRadialPosition z.1 = 1 / 2) (r : ℕ) :
    pairAmplitude z (fnPrimeSuccessor r : ℝ) / pairAmplitude z (fnPrimeAtRank r : ℝ) = 1 ∧
      phaseIncrement z r = rZeroHeight z.1 * rPrimeGapLogRatio r := by
  refine ⟨?_, phaseIncrement_eq_height_mul_ratio z r⟩
  rw [pairAmplitude_prime_step, hz]; simp

/-- **Fenêtre** : `Σ_{r=a}^{a+m−1} Δθ_{n,r} = T_n log(p_{a+m}/p_a)`. -/
theorem phaseIncrement_window_sum (z : TrueZero) (a m : ℕ) :
    ∑ j ∈ Finset.range m, phaseIncrement z (a + j) =
      rZeroHeight z.1 *
        (Real.log (fnPrimeAtRank (a + m) : ℝ) - Real.log (fnPrimeAtRank a : ℝ)) := by
  rw [← primeGapLogRatio_window_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => phaseIncrement_eq_height_mul_ratio z (a + j)

/-- **Décomposition d'une somme de fenêtre par les trois classes** (`0`, `2`, `4`), pour toute
grandeur `f` attachée aux événements : `Σ_r f r = Σ_{a_r = 0} f r + Σ_{a_r = 2} f r + Σ_{a_r = 4} f
r`,
dès que `p_a > 3`. -/
theorem window_sum_by_classes (f : ℕ → ℝ) (a m : ℕ) (h3 : 3 < fnPrimeAtRank a) :
    ∑ j ∈ Finset.range m, f (a + j) =
      ∑ j ∈ (Finset.range m).filter (fun j => eventClass (a + j) = 0), f (a + j) +
      ∑ j ∈ (Finset.range m).filter (fun j => eventClass (a + j) = 2), f (a + j) +
      ∑ j ∈ (Finset.range m).filter (fun j => eventClass (a + j) = 4), f (a + j) := by
  have hmem : ∀ j, eventClass (a + j) = 0 ∨ eventClass (a + j) = 2 ∨ eventClass (a + j) = 4 := by
    intro j
    exact eventClass_mem (a + j)
      (lt_of_lt_of_le h3 (thm_primeAtRank_strictMono.monotone (Nat.le_add_right a j)))
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range m) (fun j => eventClass (a + j) = 0),
    ← Finset.sum_filter_add_sum_filter_not
      ((Finset.range m).filter (fun j => ¬ eventClass (a + j) = 0))
      (fun j => eventClass (a + j) = 2),
    Finset.filter_filter, Finset.filter_filter, add_assoc]
  congr 2
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj, -, h⟩; exact ⟨hj, h⟩
    · rintro ⟨hj, h⟩; exact ⟨hj, by omega, h⟩
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj, h0, h2⟩
      refine ⟨hj, ?_⟩
      rcases hmem j with h | h | h
      · exact absurd h h0
      · exact absurd h h2
      · exact h
    · rintro ⟨hj, h⟩; exact ⟨hj, by omega, by omega⟩

/-- Les maintiens (classe `0`) se séparent en deux canaux distincts selon l'état conservé
(`A → A`, `B → B`). -/
theorem window_class_zero_by_state (f : ℕ → ℝ) (a m : ℕ) :
    ∑ j ∈ (Finset.range m).filter (fun j => eventClass (a + j) = 0), f (a + j) =
      ∑ j ∈ (Finset.range m).filter
          (fun j => eventClass (a + j) = 0 ∧ state6 (fnPrimeAtRank (a + j)) = true), f (a + j) +
      ∑ j ∈ (Finset.range m).filter
          (fun j => eventClass (a + j) = 0 ∧ ¬ state6 (fnPrimeAtRank (a + j)) = true),
        f (a + j) := by
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.range m).filter (fun j => eventClass (a + j) = 0))
    (fun j => state6 (fnPrimeAtRank (a + j)) = true), Finset.filter_filter, Finset.filter_filter]

/-- **Verrou des canaux de changement sur une fenêtre** : `|#(A→B) − #(B→A)| ≤ 1` (réutilisé,
`prime_ab_ba_channel_lock`). -/
theorem window_channel_lock (a m : ℕ) :
    |∑ j ∈ Finset.range m,
      abMinusBa (state6 (fnPrimeAtRank (a + j))) (state6 (fnPrimeAtRank (a + (j + 1))))| ≤ 1 :=
  prime_ab_ba_channel_lock a m

/-- **Les deux arguments du produit de phase avancent, d'un événement au suivant, de
`(T_n − T_j) L_r` et `(T_n + T_j) L_r`** : c'est l'entrée exacte de la grammaire dans les
interactions. -/
theorem beat_arguments_prime_step (z w : TrueZero) (r : ℕ) :
    ((rZeroHeight z.1 - rZeroHeight w.1) * Real.log (fnPrimeSuccessor r : ℝ) -
        (memberPhase z - memberPhase w)) -
      ((rZeroHeight z.1 - rZeroHeight w.1) * Real.log (fnPrimeAtRank r : ℝ) -
        (memberPhase z - memberPhase w)) =
      (rZeroHeight z.1 - rZeroHeight w.1) * rPrimeGapLogRatio r ∧
    ((rZeroHeight z.1 + rZeroHeight w.1) * Real.log (fnPrimeSuccessor r : ℝ) -
        (memberPhase z + memberPhase w)) -
      ((rZeroHeight z.1 + rZeroHeight w.1) * Real.log (fnPrimeAtRank r : ℝ) -
        (memberPhase z + memberPhase w)) =
      (rZeroHeight z.1 + rZeroHeight w.1) * rPrimeGapLogRatio r := by
  have h0 : (0 : ℝ) < (fnPrimeAtRank r : ℝ) := by exact_mod_cast thm_primeAtRank_pos r
  have h1 : (0 : ℝ) < (fnPrimeSuccessor r : ℝ) := by
    unfold fnPrimeSuccessor; exact_mod_cast thm_primeAtRank_pos _
  unfold rPrimeGapLogRatio
  rw [Real.log_div h1.ne' h0.ne']
  constructor <;> ring

/-- **Un support de premiers est un support admissible de la prémisse** : `∀ i, 1 < p_{k(i)}`.
Portée exacte : les abscisses `p_{k(i)}` sont sélectionnées par une fonction `k` arbitraire ; ce
théorème vérifie l'admissibilité d'un tel support, il ne relie pas le support fixé de la prémisse à
une abscisse quelconque de l'axe. Sur un support de premiers consécutifs, les produits de phase
avancent selon `beat_arguments_prime_step`. -/
theorem primeSupport_admissible {m : ℕ} (k : Fin m → ℕ) :
    ∀ i, (1 : ℝ) < (fnPrimeAtRank (k i) : ℝ) := by
  intro i
  have := thm_primeAtRank_ge_two (k i)
  exact_mod_cast this

/-- **Produit scalaire sur un support de premiers, par phases** : instance de
`canonical_inner_eq_phase_sum` sur `xs i = p_{k(i)}`. Portée exacte : développement du produit
scalaire sur des premiers sélectionnés par une fonction `k` arbitraire ; il ne démontre pas le
transport depuis le support fixé de la prémisse vers chaque abscisse `x ≥ 1` (obligation ouverte,
tableau des dépendances du statut). -/
theorem canonical_inner_primeSupport {m : ℕ} (k : Fin m → ℕ) (n j : ℕ) :
    ⟪canonicalContributions (fun i => (fnPrimeAtRank (k i) : ℝ)) n,
        canonicalContributions (fun i => (fnPrimeAtRank (k i) : ℝ)) j⟫_ℝ =
      (zetaZeroMultiplicity (zeroPoint (canonicalZero n)) : ℝ) *
        (zetaZeroMultiplicity (zeroPoint (canonicalZero j)) : ℝ) *
        ∑ i, pairAmplitude (canonicalZero n) (fnPrimeAtRank (k i) : ℝ) *
            pairAmplitude (canonicalZero j) (fnPrimeAtRank (k i) : ℝ) / 2 *
          (Real.cos ((rZeroHeight (canonicalZero n).1 - rZeroHeight (canonicalZero j).1) *
                Real.log (fnPrimeAtRank (k i) : ℝ) -
                (memberPhase (canonicalZero n) - memberPhase (canonicalZero j))) +
            Real.cos ((rZeroHeight (canonicalZero n).1 + rZeroHeight (canonicalZero j).1) *
                Real.log (fnPrimeAtRank (k i) : ℝ) -
                (memberPhase (canonicalZero n) + memberPhase (canonicalZero j)))) :=
  canonical_inner_eq_phase_sum _ (primeSupport_admissible k) n j

/-- **Identité d'Abel d'une fenêtre à hauteur constante** (instance de `window_abel_all_sameHeight`
sur une constante réelle `c`). Portée exacte : une constante réelle satisfait l'identité
télescopique de toute fenêtre. Ce théorème ne construit aucune suite de vrais zéros en ligne à
hauteur constante, ne reproduit aucun reste arithmétique et n'utilise pas la prémisse ; il ne
justifie donc pas la phrase générale « les premiers n'exigent aucune progression de hauteur ». Il
établit seulement que l'identité d'Abel seule, jointe aux bornes premières, ne force pas une hausse
de hauteur. -/
theorem constant_height_window_abel (c : ℝ) (n m : ℕ) :
    ∑ j ∈ Finset.range m, c * rPrimeGapLogRatio (n + j) +
      ∑ j ∈ Finset.range m, (c - c) * Real.log (fnPrimeAtRank (n + (j + 1)) : ℝ) =
      c * Real.log (fnPrimeAtRank (n + m) : ℝ) - c * Real.log (fnPrimeAtRank n : ℝ) :=
  window_abel_all_sameHeight c n m

/-! ## 14. Fermeture depuis la domination individuelle (conclusion du raccord ouvert) -/

/-- Comparer deux amplitudes normalisées en `x > 0`, c'est comparer les deux Tours brutes en `x`. -/
theorem pairAmplitude_le_iff (z w : TrueZero) {x : ℝ} (hx : 0 < x) :
    pairAmplitude w x ≤ pairAmplitude z x ↔ ‖zeroTerm w x‖ ≤ ‖zeroTerm z x‖ := by
  rw [pairAmplitude_eq_abs_div, pairAmplitude_eq_abs_div,
    div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr hx)]
  exact ⟨fun h => le_of_mul_le_mul_left h (by norm_num),
    fun h => mul_le_mul_of_nonneg_left h (by norm_num)⟩

/-- **La conclusion recherchée, lue en amplitudes** : `w` est dans le champ de `z₁` ⟺ l'amplitude
normalisée de `w` reste sous celle de `z₁` sur tout `x ≥ 1`. -/
theorem insideField_iff_pairAmplitude (z₁ w : TrueZero) :
    InsideField z₁ w ↔ ∀ x : ℝ, 1 ≤ x → pairAmplitude w x ≤ pairAmplitude z₁ x := by
  unfold InsideField firstField
  exact forall_congr' fun x => forall_congr' fun hx =>
    (pairAmplitude_le_iff z₁ w (by linarith)).symm

/-- **Fermeture** : si chaque amplitude individuelle reste sous celle d'un même zéro `z₁` sur tout
l'horizon `x > 0`, l'hypothèse de Riemann suit, rien n'étant supposé sur `z₁` (son miroir est aussi
dominé, donc `β₁ = 1/2`, puis chaque zéro a la partie réelle de `z₁`). -/
theorem riemannHypothesis_of_individual_domination {z₁ : TrueZero}
    (hDom : ∀ w : TrueZero, ∀ x : ℝ, 0 < x → pairAmplitude w x ≤ pairAmplitude z₁ x) :
    RiemannHypothesis :=
  riemannHypothesis_of_whole_winding fun w x hx => (pairAmplitude_le_iff z₁ w hx).mp (hDom w x hx)

/-- **Fermeture depuis le premier zéro en ligne, sur `x ≥ 1` seulement** : si chaque amplitude reste
sous celle du premier ON sur l'axe des premiers, RH (champ du premier zéro et réflexion). -/
theorem riemannHypothesis_of_individual_domination_onLine {z₁ : TrueZero}
    (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hDom : ∀ w : TrueZero, ∀ x : ℝ, 1 ≤ x → pairAmplitude w x ≤ pairAmplitude z₁ x) :
    RiemannHypothesis :=
  riemannHypothesis_of_first_field h₁ fun w x hx =>
    (pairAmplitude_le_iff z₁ w (by linarith)).mp (hDom w x hx)

/-- **Caractérisation** : pour le premier zéro, la domination individuelle sur tout l'horizon
équivaut
à RH. Elle nomme la conclusion du raccord ouvert ; elle ne la dérive pas. -/
theorem individual_domination_iff_riemannHypothesis {z₁ : TrueZero}
    (hFirst : sUpperZerosBelow z₁.1 = ∅) :
    (∀ w : TrueZero, ∀ x : ℝ, 0 < x → pairAmplitude w x ≤ pairAmplitude z₁ x) ↔
      RiemannHypothesis := by
  rw [← whole_winding_in_first_iff_riemannHypothesis hFirst]
  exact forall_congr' fun w => forall_congr' fun x => forall_congr' fun hx =>
    pairAmplitude_le_iff z₁ w hx

/-- La domination individuelle donne l'enroulement entier sur tout passage (par RH), donc tout ce
que
les modules antérieurs établissaient sous cette obligation. -/
theorem whole_winding_all_passages_of_individual_domination {z₁ : TrueZero}
    (hDom : ∀ w : TrueZero, ∀ x : ℝ, 0 < x → pairAmplitude w x ≤ pairAmplitude z₁ x) :
    ∀ p : TZeroPassage, ∀ (hE : 0 < rZeroHeight p.zEarlierMember)
      (hL : 0 < rZeroHeight p.zLaterMember), ∀ x : ℝ, 0 < x →
      ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖ :=
  whole_winding_all_passages_of_riemannHypothesis (riemannHypothesis_of_individual_domination hDom)

/-! ## 14. Réduction de la prémisse (auteur, 2026-10-06 : « le premier zéro est le plus fort sur la
ligne ») — ce que les formules démontrent, et ce qui reste posé

Les formules de l'auteur sont compilées ici : enveloppe ON décroissante en hauteur (forme large),
rapport des enveloppes pour toute position radiale, enveloppe de la contribution lissée. Elles
établissent la DOMINATION INDIVIDUELLE du premier membre canonique parmi les membres EN LIGNE
(premier membre en ligne supposé : ancre ON, aucun terme Lean). Elles n'établissent pas le gain
collectif maximal (l'interaction `I_n` reste à borner) ni la domination d'un membre hors du champ.
La prémisse est donc RÉDUITE : elle n'est posée qu'aux rangs dont le membre n'est pas déjà dans le
champ du premier ; aux rangs en ligne elle ne demande rien (antécédent faux par théorème). -/

/-- **Parmi les zéros en ligne, l'amplitude ne croît pas avec la hauteur** (forme large de
`pairAmplitude_onLine_lt_of_height`) : `T_z ≤ T_w ⟹ A_w(x) ≤ A_z(x)`, tout `x > 0`. -/
theorem pairAmplitude_onLine_le_of_height {z w : TrueZero}
    (hz : rZeroRadialPosition z.1 = 1 / 2) (hw : rZeroRadialPosition w.1 = 1 / 2)
    (hT : rZeroHeight z.1 ≤ rZeroHeight w.1) {x : ℝ} (hx : 0 < x) :
    pairAmplitude w x ≤ pairAmplitude z x := by
  unfold pairAmplitude
  rw [normalizedRadius_onLine z hz hx, normalizedRadius_onLine w hw hx]
  exact mul_le_mul_of_nonneg_left (onRadius_anti z.2.le hT) (by norm_num)

/-- **Rapport des enveloppes normalisées, toute position radiale** :
`A_w(x)/A_{z₁}(x) = x^{β_w − β₁} · ‖ρ₁‖/‖ρ_w‖`. -/
theorem pairAmplitude_ratio (z₁ w : TrueZero) {x : ℝ} (hx : 0 < x) :
    pairAmplitude w x / pairAmplitude z₁ x =
      x ^ (rZeroRadialPosition w.1 - rZeroRadialPosition z₁.1) *
        (‖zeroPoint z₁‖ / ‖zeroPoint w‖) := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  rw [← tower_field_ratio z₁ w hx, pairAmplitude_eq_abs_div, pairAmplitude_eq_abs_div]
  unfold firstField
  rw [div_div_div_cancel_right₀ hs, mul_div_mul_left _ _ (two_ne_zero' ℝ)]

/-- **Premier zéro en ligne** : `A_w(x)/A_1(x) = x^{β_w − 1/2} · ‖ρ₁‖/‖ρ_w‖`. La hauteur supérieure
atténue le coefficient constant ; seule une partie réelle `β_w ≠ 1/2` fait varier le facteur en `x`
(croissant si `β_w > 1/2`). C'est exactement ce que le raccord doit exclure, depuis le reste et la
grammaire : non dérivé ici. -/
theorem pairAmplitude_ratio_onLine_first (z₁ w : TrueZero)
    (h₁ : rZeroRadialPosition z₁.1 = 1 / 2) {x : ℝ} (hx : 0 < x) :
    pairAmplitude w x / pairAmplitude z₁ x =
      x ^ (rZeroRadialPosition w.1 - 1 / 2) * (‖zeroPoint z₁‖ / ‖zeroPoint w‖) := by
  rw [pairAmplitude_ratio z₁ w hx, h₁]

/-- La hauteur ne décroît pas le long des rangs canoniques `≥ 1`. -/
theorem canonicalZero_height_mono {m n : ℕ} (h : m ≤ n) :
    rZeroHeight (canonicalZero m).1 ≤ rZeroHeight (canonicalZero n).1 := by
  unfold canonicalZero
  exact canonicalMember_height_mono (by omega)

/-- **Le premier zéro est le plus fort sur la ligne, dans l'énumération canonique** : premier membre
en ligne et membre de rang `n` en ligne ⟹ `A_n(x) ≤ A_1(x)` pour tout `x > 0`. -/
theorem canonical_onLine_amplitude_le_first (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) (hOn : rZeroRadialPosition (canonicalZero n).1 = 1 / 2) {x : ℝ}
    (hx : 0 < x) :
    pairAmplitude (canonicalZero n) x ≤ pairAmplitude (canonicalZero 1) x :=
  pairAmplitude_onLine_le_of_height h₁ hOn (canonicalZero_height_mono hn) hx

/-- **Tout rang canonique en ligne est dans le champ du premier** (premier membre en ligne) : la
conclusion du raccord est un THÉORÈME aux rangs en ligne. -/
theorem canonical_onLine_insideField (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) (hOn : rZeroRadialPosition (canonicalZero n).1 = 1 / 2) :
    InsideField (canonicalZero 1) (canonicalZero n) :=
  inside_field_of_onLine h₁ hOn (canonicalZero_height_mono hn)

/-- **Enveloppe de la contribution lissée normalisée, toute position radiale** :
`|a_z(x)/√x| ≤ 2m · x^{β−1/2}/(√(β² + T²)·√((β+1)² + T²))`. -/
theorem abs_normalizedSmoothedPairContribution_le (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    |normalizedSmoothedPairContribution z x| ≤
      2 * (zetaZeroMultiplicity (zeroPoint z) : ℝ) * x ^ (rZeroRadialPosition z.1 - 1 / 2) /
        (Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) *
          Real.sqrt ((rZeroRadialPosition z.1 + 1) ^ 2 + rZeroHeight z.1 ^ 2)) := by
  unfold normalizedSmoothedPairContribution
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hre : |(nontrivialZeroResidueTerm x (memberIndex z)).re| ≤
      ‖nontrivialZeroResidueTerm x (memberIndex z)‖ := Complex.abs_re_le_norm _
  rw [residueTerm_norm_joint z hx] at hre
  have hpow : x ^ (rZeroRadialPosition z.1 - 1 / 2) = x ^ rZeroRadialPosition z.1 / Real.sqrt x := by
    rw [Real.rpow_sub hx, ← Real.sqrt_eq_rpow]
  rw [hpow]
  have h2 : 2 * |(nontrivialZeroResidueTerm x (memberIndex z)).re| ≤
      2 * (zetaZeroMultiplicity (zeroPoint z) : ℝ) * x ^ rZeroRadialPosition z.1 /
        (Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) *
          Real.sqrt ((rZeroRadialPosition z.1 + 1) ^ 2 + rZeroHeight z.1 ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hre (by norm_num : (0 : ℝ) ≤ 2)
    calc _ ≤ _ := this
      _ = _ := by ring
  calc |2 * (nontrivialZeroResidueTerm x (memberIndex z)).re / Real.sqrt x|
      = 2 * |(nontrivialZeroResidueTerm x (memberIndex z)).re| / Real.sqrt x := by
        rw [abs_div, abs_mul, abs_two, abs_of_pos hs]
    _ ≤ (2 * (zetaZeroMultiplicity (zeroPoint z) : ℝ) * x ^ rZeroRadialPosition z.1 /
        (Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) *
          Real.sqrt ((rZeroRadialPosition z.1 + 1) ^ 2 + rZeroHeight z.1 ^ 2))) / Real.sqrt x :=
        div_le_div_of_nonneg_right h2 hs.le
    _ = _ := by ring

/-- **Enveloppe lissée EN LIGNE** : `|a_n/√x| ≤ 2m/(√(1/4 + T²)·√(9/4 + T²))`, constante le long de
l'axe. -/
theorem abs_normalizedSmoothedPairContribution_onLine_le (z : TrueZero)
    (hz : rZeroRadialPosition z.1 = 1 / 2) {x : ℝ} (hx : 0 < x) :
    |normalizedSmoothedPairContribution z x| ≤
      2 * (zetaZeroMultiplicity (zeroPoint z) : ℝ) /
        (Real.sqrt (1 / 4 + rZeroHeight z.1 ^ 2) * Real.sqrt (9 / 4 + rZeroHeight z.1 ^ 2)) := by
  have h := abs_normalizedSmoothedPairContribution_le z hx
  rw [hz, sub_self, Real.rpow_zero, mul_one] at h
  have e1 : ((1 : ℝ) / 2) ^ 2 + rZeroHeight z.1 ^ 2 = 1 / 4 + rZeroHeight z.1 ^ 2 := by norm_num
  have e2 : ((1 : ℝ) / 2 + 1) ^ 2 + rZeroHeight z.1 ^ 2 = 9 / 4 + rZeroHeight z.1 ^ 2 := by norm_num
  rwa [e1, e2] at h

/-- **L'enveloppe lissée ON décroît avec la hauteur** : `S ≤ T ⟹ env(T) ≤ env(S)`. Le premier zéro
domine individuellement aussi dans le canal lissé, parmi les ON. -/
theorem smoothed_onLine_envelope_anti {S T : ℝ} (hS : 0 ≤ S) (h : S ≤ T) :
    2 / (Real.sqrt (1 / 4 + T ^ 2) * Real.sqrt (9 / 4 + T ^ 2)) ≤
      2 / (Real.sqrt (1 / 4 + S ^ 2) * Real.sqrt (9 / 4 + S ^ 2)) := by
  have hsq : S ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hS h 2
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_le_sqrt (by linarith))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- **La prémisse réduite est impliquée par la prémisse** : il suffit de la poser aux rangs dont le
membre n'est pas déjà dans le champ du premier membre canonique. -/
theorem gain_restricted_of_gain {m : ℕ} (xs : Fin m → ℝ)
    (hGain : ∀ n : ℕ, 1 ≤ n →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1) :
    ∀ n : ℕ, 1 ≤ n → ¬ InsideField (canonicalZero 1) (canonicalZero n) →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1 :=
  fun n hn _ => hGain n hn

/-- **Aux rangs en ligne, la prémisse réduite ne demande rien** : son antécédent est faux (le rang
est dans le champ par théorème), donc toute conclusion y est acquise sans la prémisse. -/
theorem gain_restricted_vacuous_onLine (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) (hOn : rZeroRadialPosition (canonicalZero n).1 = 1 / 2) (P : Prop) :
    ¬ InsideField (canonicalZero 1) (canonicalZero n) → P :=
  fun hNot => (hNot (canonical_onLine_insideField h₁ hn hOn)).elim

/-- Un rang hors du champ du premier (premier en ligne) n'est pas en ligne : la prémisse réduite ne
porte que sur des membres dont la position radiale n'est pas un demi. Elle ne suppose aucun tel
membre ; elle est vide s'il n'y en a pas. -/
theorem not_onLine_of_not_insideField (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) (hNot : ¬ InsideField (canonicalZero 1) (canonicalZero n)) :
    rZeroRadialPosition (canonicalZero n).1 ≠ 1 / 2 :=
  fun hOn => hNot (canonical_onLine_insideField h₁ hn hOn)

/-- **Sous la prémisse réduite**, au rang `n` hors du champ : `E_n − E_1 ≤ 2(I_1 − I_n)`. -/
theorem canonical_ownEnergy_diff_le_of_restricted {m : ℕ} (xs : Fin m → ℝ) (hm : 0 < m)
    (hGainRes : ∀ n : ℕ, 1 ≤ n → ¬ InsideField (canonicalZero 1) (canonicalZero n) →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1)
    {n : ℕ} (hn : 1 ≤ n) (hNot : ¬ InsideField (canonicalZero 1) (canonicalZero n)) :
    ownEnergy (canonicalContributions xs) n - ownEnergy (canonicalContributions xs) 1 ≤
      2 * (interaction (canonicalContributions xs) (normalizedRawRemainderVector xs) 1 -
        interaction (canonicalContributions xs) (normalizedRawRemainderVector xs) n) := by
  have _ := hm
  rw [ownEnergy_diff_eq _ _ hn]
  linarith [hGainRes n hn hNot]

/-- **Sous la prémisse réduite**, lecture par l'interaction au rang hors du champ : `I_1 ≤ I_n ⟹
‖c_n‖ ≤ ‖c_1‖`. L'hypothèse d'interaction n'est pas dérivée. -/
theorem canonical_norm_le_first_of_interaction_restricted {m : ℕ} (xs : Fin m → ℝ) (hm : 0 < m)
    (hGainRes : ∀ n : ℕ, 1 ≤ n → ¬ InsideField (canonicalZero 1) (canonicalZero n) →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1)
    {n : ℕ} (hn : 1 ≤ n) (hNot : ¬ InsideField (canonicalZero 1) (canonicalZero n))
    (hInt : interaction (canonicalContributions xs) (normalizedRawRemainderVector xs) 1 ≤
      interaction (canonicalContributions xs) (normalizedRawRemainderVector xs) n) :
    ‖canonicalContributions xs n‖ ≤ ‖canonicalContributions xs 1‖ := by
  have _ := hm
  rw [canonical_norm_le_first_iff xs hn]
  linarith [hGainRes n hn hNot]

/-- **Fermeture en rangs canoniques** : premier membre en ligne et chaque rang `≥ 1` dans son champ
⟹ RH (tout zéro est un rang canonique). -/
theorem riemannHypothesis_of_canonical_insideField
    (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (hAll : ∀ n : ℕ, 1 ≤ n → InsideField (canonicalZero 1) (canonicalZero n)) :
    RiemannHypothesis :=
  riemannHypothesis_of_first_field h₁ fun w => by
    obtain ⟨n, hn, rfl⟩ := canonicalZero_surjective w
    exact hAll n hn

/-- **Le raccord ouvert, sous la prémisse réduite** : `hLink` est le raccord lui-même (de la prémisse
réduite, chaque rang est dans le champ), posé ici en hypothèse pour exhiber la composition ; il n'est
pas dérivé. Avec l'ancre ON, il donne RH. Correction de l'auteur (2026-10-07, point 1) : ce théorème
reçoit le raccord en hypothèse et son corps l'applique ; il est une COMPOSITION, pas « la prémisse
seule entraîne RH ». Support non vide exigé (point 4). -/
theorem riemannHypothesis_of_restricted_gain_link {m : ℕ} (xs : Fin m → ℝ) (hm : 0 < m)
    (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (hGainRes : ∀ n : ℕ, 1 ≤ n → ¬ InsideField (canonicalZero 1) (canonicalZero n) →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1)
    (hLink : (∀ n : ℕ, 1 ≤ n → ¬ InsideField (canonicalZero 1) (canonicalZero n) →
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
          collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1) →
      ∀ n : ℕ, 1 ≤ n → InsideField (canonicalZero 1) (canonicalZero n)) :
    RiemannHypothesis := by
  have _ := hm
  exact riemannHypothesis_of_canonical_insideField h₁ (hLink hGainRes)

/-! ## 15. Quatre corrections de l'auteur (2026-10-07) et la cible d'interdiction de compensation

1. La fermeture `riemannHypothesis_of_restricted_gain_link` reçoit le raccord `hLink` en
   hypothèse et l'applique : c'est une composition, pas « la prémisse seule entraîne RH »
   (docstring corrigée).
2. La réduction AFFAIBLIT la prémisse (`gain_restricted_of_gain`) ; elle ne la démontre pas. La
   domination des enveloppes ON et le gain collectif maximal sont deux propriétés distinctes. Sur
   une configuration entièrement en ligne, la prémisse réduite est vide sous l'ancre
   (`gain_restricted_of_all_onLine`) : une observation entièrement ON ne teste pas les rangs où elle
   s'applique.
3. `pairAmplitude` ne contient pas la multiplicité ; `canonicalContributions` la contient. La
   domination ON du premier est par unité de multiplicité ; pondérée, elle exige `m_n ≤ m_1`
   (`canonical_onLine_weighted_le_first`).
4. Un support vide rend vecteurs et gains nuls, donc la prémisse automatiquement vraie
   (`collectiveGain_support_empty`, `gain_restricted_of_support_empty`) ; les porteurs exigent
   désormais `0 < m`. Un support non vide ne donne pas, à lui seul, le passage à toutes les
   abscisses.
Cible de preuve (auteur) : `E_n > E_1 ⟹ 2(I_1 − I_n) < E_n − E_1`, incompatible avec la borne sous
la prémisse (`compensation_bound_incompatible`) ; sous cette borne elle équivaut à `E_n ≤ E_1`
(`compensation_target_iff_ownEnergy_le`). Elle n'est l'hypothèse d'aucune fermeture vers RH. -/

/-- **Correction 2** : si tous les rangs canoniques sont en ligne (le premier compris), la prémisse
réduite est vraie sans rien demander, pour tout support et tout reste : une configuration
entièrement ON ne teste pas les rangs où elle s'applique. -/
theorem gain_restricted_of_all_onLine {m : ℕ} (xs : Fin m → ℝ)
    (hAllOn : ∀ n : ℕ, 1 ≤ n → rZeroRadialPosition (canonicalZero n).1 = 1 / 2) :
    ∀ n : ℕ, 1 ≤ n → ¬ InsideField (canonicalZero 1) (canonicalZero n) →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1 :=
  fun n hn hNot => (hNot (canonical_onLine_insideField (hAllOn 1 le_rfl) hn (hAllOn n hn))).elim

/-- Tous les rangs canoniques en ligne, c'est RH elle-même : le cas où la prémisse réduite est vide
est exactement la conclusion. -/
theorem riemannHypothesis_of_all_canonical_onLine
    (hAllOn : ∀ n : ℕ, 1 ≤ n → rZeroRadialPosition (canonicalZero n).1 = 1 / 2) :
    RiemannHypothesis :=
  riemannHypothesis_of_canonical_insideField (hAllOn 1 le_rfl) fun n hn =>
    canonical_onLine_insideField (hAllOn 1 le_rfl) hn (hAllOn n hn)

/-- **Correction 3** : domination pondérée ON du premier, sous `m_n ≤ m_1` seulement. Sans cette
hypothèse sur les multiplicités, `A_n ≤ A_1` ne dit rien de `m_n A_n` contre `m_1 A_1`. -/
theorem canonical_onLine_weighted_le_first (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) (hOn : rZeroRadialPosition (canonicalZero n).1 = 1 / 2)
    (hm : zetaZeroMultiplicity (zeroPoint (canonicalZero n)) ≤
      zetaZeroMultiplicity (zeroPoint (canonicalZero 1))) {x : ℝ} (hx : 0 < x) :
    (zetaZeroMultiplicity (zeroPoint (canonicalZero n)) : ℝ) * pairAmplitude (canonicalZero n) x ≤
      (zetaZeroMultiplicity (zeroPoint (canonicalZero 1)) : ℝ) *
        pairAmplitude (canonicalZero 1) x := by
  have hA : 0 ≤ pairAmplitude (canonicalZero n) x := by
    unfold pairAmplitude; exact mul_nonneg (by norm_num) (normalizedRadius_pos _ hx).le
  exact mul_le_mul (by exact_mod_cast hm) (canonical_onLine_amplitude_le_first h₁ hn hOn hx) hA
    (canonical_multiplicity_pos 1).le

/-- L'énergie propre sur le support est bornée par l'enveloppe pondérée :
`‖c_n‖² ≤ m_n² Σ_i A_n(x_i)²` (sans prémisse). -/
theorem canonical_normSq_le_envelope {m : ℕ} (xs : Fin m → ℝ) (n : ℕ) :
    ‖canonicalContributions xs n‖ ^ 2 ≤
      (zetaZeroMultiplicity (zeroPoint (canonicalZero n)) : ℝ) ^ 2 *
        ∑ i, pairAmplitude (canonicalZero n) (xs i) ^ 2 := by
  unfold canonicalContributions
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_left (normalizedSupportContribution_normSq_le xs _) (sq_nonneg _)

/-- **Correction 3, sur le support** : au rang en ligne, sous `m_n ≤ m_1`, l'enveloppe pondérée du
rang `n` est sous celle du premier ; aucune borne inférieure de `‖c_1‖` n'est disponible (phases),
donc rien n'est conclu sur `‖c_n‖ ≤ ‖c_1‖`. -/
theorem canonical_onLine_envelope_le_first {m : ℕ} (xs : Fin m → ℝ) (hxs : ∀ i, 1 < xs i)
    (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) (hOn : rZeroRadialPosition (canonicalZero n).1 = 1 / 2)
    (hm : zetaZeroMultiplicity (zeroPoint (canonicalZero n)) ≤
      zetaZeroMultiplicity (zeroPoint (canonicalZero 1))) :
    ‖canonicalContributions xs n‖ ^ 2 ≤
      (zetaZeroMultiplicity (zeroPoint (canonicalZero 1)) : ℝ) ^ 2 *
        ∑ i, pairAmplitude (canonicalZero 1) (xs i) ^ 2 := by
  refine (canonical_normSq_le_envelope xs n).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hx : 0 < xs i := lt_trans zero_lt_one (hxs i)
  rw [← mul_pow, ← mul_pow]
  have hA : 0 ≤ (zetaZeroMultiplicity (zeroPoint (canonicalZero n)) : ℝ) *
      pairAmplitude (canonicalZero n) (xs i) := by
    unfold pairAmplitude
    exact mul_nonneg (canonical_multiplicity_pos n).le
      (mul_nonneg (by norm_num) (normalizedRadius_pos _ hx).le)
  exact pow_le_pow_left₀ hA (canonical_onLine_weighted_le_first h₁ hn hOn hm hx) 2

/-- **Correction 4** : sur un support vide, toute norme est nulle. -/
theorem norm_eq_zero_of_fin_zero (v : EuclideanSpace ℝ (Fin 0)) : ‖v‖ = 0 := by
  rw [EuclideanSpace.norm_eq]; simp

/-- Sur un support vide, tout gain collectif est nul. -/
theorem collectiveGain_support_empty (c : ℕ → EuclideanSpace ℝ (Fin 0))
    (R : EuclideanSpace ℝ (Fin 0)) (n : ℕ) : collectiveGain c R n = 0 := by
  unfold collectiveGain
  rw [norm_eq_zero_of_fin_zero, norm_eq_zero_of_fin_zero]; ring

/-- **Correction 4** : sur un support vide, la prémisse (à tout rang) est automatiquement vraie. -/
theorem gain_of_support_empty (xs : Fin 0 → ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1 := by
  intro n _
  rw [collectiveGain_support_empty, collectiveGain_support_empty]

/-- **Correction 4** : sur un support vide, la prémisse réduite est automatiquement vraie ; c'est
pourquoi les porteurs exigent `0 < m`. -/
theorem gain_restricted_of_support_empty (xs : Fin 0 → ℝ) :
    ∀ n : ℕ, 1 ≤ n → ¬ InsideField (canonicalZero 1) (canonicalZero n) →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1 :=
  gain_restricted_of_gain xs (gain_of_support_empty xs)

/-- **La cible d'interdiction de compensation** `E_n > E_1 ⟹ 2(I_1 − I_n) < E_n − E_1` et la borne
sous la prémisse `E_n − E_1 ≤ 2(I_1 − I_n)` sont incompatibles dès que `E_n > E_1` : ensemble elles
donnent `E_n ≤ E_1`. La cible est une cible de preuve ; elle n'est l'hypothèse d'aucune fermeture
vers RH. -/
theorem compensation_bound_incompatible (c : ℕ → V) (R : V) {n : ℕ}
    (hBound : ownEnergy c n - ownEnergy c 1 ≤ 2 * (interaction c R 1 - interaction c R n))
    (hTarget : ownEnergy c 1 < ownEnergy c n →
      2 * (interaction c R 1 - interaction c R n) < ownEnergy c n - ownEnergy c 1) :
    ownEnergy c n ≤ ownEnergy c 1 := by
  by_contra h
  push_neg at h
  linarith [hTarget h]

/-- Sous la borne de la prémisse, la cible d'interdiction de compensation ÉQUIVAUT à `E_n ≤ E_1` :
elle n'est pas plus faible que la borne individuelle d'énergie. -/
theorem compensation_target_iff_ownEnergy_le (c : ℕ → V) (R : V) {n : ℕ}
    (hBound : ownEnergy c n - ownEnergy c 1 ≤ 2 * (interaction c R 1 - interaction c R n)) :
    (ownEnergy c 1 < ownEnergy c n →
      2 * (interaction c R 1 - interaction c R n) < ownEnergy c n - ownEnergy c 1) ↔
      ownEnergy c n ≤ ownEnergy c 1 := by
  constructor
  · exact compensation_bound_incompatible c R hBound
  · intro h hlt
    exact absurd hlt (not_lt.mpr h)

/-- **Sur l'instance canonique, au rang hors du champ** : prémisse réduite + cible d'interdiction de
compensation ⟹ `E_n ≤ E_1` sur le support fixé (pas la domination à toute abscisse). -/
theorem canonical_ownEnergy_le_first_of_no_compensation {m : ℕ} (xs : Fin m → ℝ) (hm : 0 < m)
    (hGainRes : ∀ n : ℕ, 1 ≤ n → ¬ InsideField (canonicalZero 1) (canonicalZero n) →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1)
    {n : ℕ} (hn : 1 ≤ n) (hNot : ¬ InsideField (canonicalZero 1) (canonicalZero n))
    (hTarget : ownEnergy (canonicalContributions xs) 1 < ownEnergy (canonicalContributions xs) n →
      2 * (interaction (canonicalContributions xs) (normalizedRawRemainderVector xs) 1 -
            interaction (canonicalContributions xs) (normalizedRawRemainderVector xs) n) <
        ownEnergy (canonicalContributions xs) n - ownEnergy (canonicalContributions xs) 1) :
    ownEnergy (canonicalContributions xs) n ≤ ownEnergy (canonicalContributions xs) 1 :=
  compensation_bound_incompatible _ _
    (canonical_ownEnergy_diff_le_of_restricted xs hm hGainRes hn hNot) hTarget

/-! ## 16. Cible de captivité sur tout l'horizon, interaction complète et détection sur le support
(directive de l'auteur, 2026-10-07 : « la reconstruction exacte des écarts arithmétiques oblige
toutes
les vraies Tours à rester captives du champ fixe du premier zéro ON, sur tout l'horizon »)

Ce que cette section compile, à sa portée exacte :
* la cible de captivité dans la forme de l'auteur, `∀ w, ∀ u ≥ 0, A_w(e^u) ≤ A_1` ; elle ÉQUIVAUT à
  « chaque vrai zéro est dans le champ du premier » (`captivity_iff_insideField`) et, sous l'ancre
  ON
  du premier, elle entraîne RH (`riemannHypothesis_of_captivity_onLine`) : la conservation du régime
  et la fermeture sont des conséquences disponibles de la captivité, la captivité n'est pas dérivée
  ;
* l'interaction complète, queue finie ET résidu : toute borne doit couvrir les deux termes ; la
  seule
  borne compilée est l'inégalité triangulaire avec Cauchy–Schwarz sur le résidu
  (`interaction_abs_le_tail_add_residual`) ; aucune borne QUANTITATIVE des sommes oscillantes ;
* le cas `T_n = T_j` : l'argument de différence n'avance pas, le produit garde un terme constant
  `cos(φ_n − φ_j)` (`normalizedPairContribution_mul_sameHeight`) ; aucune séparation des hauteurs
  n'est supposée ;
* la contradiction visée `¬ InsideField ⟹ D_1 < D_n` écrite comme OBLIGATION : avec la prémisse
  réduite elle donne chaque rang dans le champ (`canonical_insideField_of_gain_excess`, composition
  dont l'hypothèse `hExcess` est la cible, jamais une hypothèse à ajouter à une fermeture) ; son
  équivalent en énergie et interaction (`gain_excess_iff`) ;
* détection sur le support : un dépassement du champ par un membre `β_w ≥ 1/2` en une abscisse
  persiste
  à toute abscisse plus grande (`exceedance_persists`, par `pairAmplitude_ratio_onLine_first`), donc
  toute abscisse du support fixé au-delà du premier dépassement lit l'ENVELOPPE de `w` au-dessus de
  celle du premier (`exceedance_detected_on_support`) ; c'est l'enveloppe qui est lue, pas la
  contribution `c_w(x_i)` (sa phase peut l'annuler) ; un support fixé AVANT le membre ne contient
  pas
  nécessairement une telle abscisse. -/

/-- L'amplitude normalisée est strictement positive sur `x > 0`. -/
theorem pairAmplitude_pos (z : TrueZero) {x : ℝ} (hx : 0 < x) : 0 < pairAmplitude z x := by
  rw [pairAmplitude_eq_envelope_div z hx]
  exact div_pos (pairEnvelope_pos z hx) (Real.sqrt_pos.mpr hx)

/-- **Cible de captivité, forme logarithmique de l'auteur** (`u = log x`, `u ≥ 0`) : pour un zéro
`w`, `∀ u ≥ 0, A_w(e^u) ≤ A_{z₁}(e^u)` ⟺ `InsideField z₁ w`. -/
theorem captivity_log_iff_insideField (z₁ w : TrueZero) :
    (∀ u : ℝ, 0 ≤ u → pairAmplitude w (Real.exp u) ≤ pairAmplitude z₁ (Real.exp u)) ↔
      InsideField z₁ w := by
  rw [insideField_iff_pairAmplitude]
  constructor
  · intro h x hx
    have := h (Real.log x) (Real.log_nonneg hx)
    rwa [Real.exp_log (by linarith)] at this
  · intro h u hu
    exact h (Real.exp u) (Real.one_le_exp hu)

/-- **Captivité de toutes les Tours** ⟺ chaque vrai zéro est dans le champ de `z₁`. -/
theorem captivity_iff_insideField (z₁ : TrueZero) :
    (∀ w : TrueZero, ∀ u : ℝ, 0 ≤ u →
        pairAmplitude w (Real.exp u) ≤ pairAmplitude z₁ (Real.exp u)) ↔
      ∀ w : TrueZero, InsideField z₁ w :=
  forall_congr' fun w => captivity_log_iff_insideField z₁ w

/-- **Sous l'ancre ON de `z₁`, le champ est la constante `A_1 = 2/√(1/4 + T₁²)`** sur tout `x > 0`.
-/
theorem firstField_constant_onLine (z₁ : TrueZero) (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    {u : ℝ} :
    pairAmplitude z₁ (Real.exp u) = 2 / Real.sqrt (1 / 4 + rZeroHeight z₁.1 ^ 2) :=
  pairAmplitude_onLine z₁ h₁ (Real.exp_pos u)

/-- **La fermeture est une conséquence disponible de la captivité** : sous l'ancre ON de `z₁`, la
captivité de toutes les Tours sur `u ≥ 0` entraîne RH. La captivité n'est pas dérivée ici. -/
theorem riemannHypothesis_of_captivity_onLine {z₁ : TrueZero}
    (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hCap : ∀ w : TrueZero, ∀ u : ℝ, 0 ≤ u →
      pairAmplitude w (Real.exp u) ≤ pairAmplitude z₁ (Real.exp u)) :
    RiemannHypothesis :=
  riemannHypothesis_of_individual_domination_onLine h₁ fun w x hx =>
    (insideField_iff_pairAmplitude z₁ w).mp ((captivity_log_iff_insideField z₁ w).mp (hCap w)) x hx

/-- **Borne de l'interaction complète, queue finie ET résidu** :
`|I_n| ≤ Σ_{n<j≤N} |⟨c_j, c_n⟩| + ‖r_N‖·‖c_n‖`. La seule borne compilée ; elle ne borne pas les
sommes
oscillantes elles-mêmes (chaque `|⟨c_j, c_n⟩|` reste à estimer) ni le résidu autrement que par
Cauchy–Schwarz. -/
theorem interaction_abs_le_tail_add_residual (c : ℕ → V) (R : V) {n N : ℕ} (hnN : n ≤ N) :
    |interaction c R n| ≤
      ∑ j ∈ Finset.Ioc n N, |⟪c j, c n⟫_ℝ| + ‖partialRemainder c R (N + 1)‖ * ‖c n‖ := by
  rw [interaction_eq_tail_add c R hnN]
  refine (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) ?_)
  exact abs_real_inner_le_norm _ _

/-- **La contradiction visée, en énergie et interaction** : `D_1 < D_n ⟺ 0 < (E_n − E_1) − 2(I_1 −
I_n)`.
-/
theorem gain_excess_iff (c : ℕ → V) (R : V) {n : ℕ} (hn : 1 ≤ n) :
    collectiveGain c R 1 < collectiveGain c R n ↔
      0 < (ownEnergy c n - ownEnergy c 1) - 2 * (interaction c R 1 - interaction c R n) := by
  have h := gain_margin_eq c R hn
  constructor <;> intro hlt <;> linarith

/-- **Cas `T_n = T_j`** : l'argument de différence n'avance pas ; le produit garde le terme constant
`cos(φ_z − φ_w)` et un seul terme oscillant à la fréquence `2T`. Aucune séparation des hauteurs
n'est supposée ailleurs. -/
theorem normalizedPairContribution_mul_sameHeight (z w : TrueZero)
    (hT : rZeroHeight z.1 = rZeroHeight w.1) {x : ℝ} (hx : 0 < x) :
    normalizedPairContribution z x * normalizedPairContribution w x =
      pairAmplitude z x * pairAmplitude w x / 2 *
        (Real.cos (memberPhase z - memberPhase w) +
          Real.cos (2 * rZeroHeight w.1 * Real.log x - (memberPhase z + memberPhase w))) := by
  rw [normalizedPairContribution_mul z w hx, hT, sub_self, zero_mul, zero_sub, Real.cos_neg,
    two_mul]

/-- **L'obligation d'excès composée avec la prémisse réduite** : si, à tout rang hors du champ, le
gain
du rang dépasse strictement celui du premier (`hExcess`, la CIBLE de preuve de l'auteur, non
dérivée),
la prémisse réduite force chaque rang dans le champ. Composition ; `hExcess` n'est l'hypothèse
d'aucune fermeture vers RH. -/
theorem canonical_insideField_of_gain_excess {m : ℕ} (xs : Fin m → ℝ)
    (hGainRes : ∀ n : ℕ, 1 ≤ n → ¬ InsideField (canonicalZero 1) (canonicalZero n) →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1)
    (hExcess : ∀ n : ℕ, 1 ≤ n → ¬ InsideField (canonicalZero 1) (canonicalZero n) →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1 <
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n) :
    ∀ n : ℕ, 1 ≤ n → InsideField (canonicalZero 1) (canonicalZero n) := by
  intro n hn
  by_contra hNot
  exact absurd (hGainRes n hn hNot) (not_le.mpr (hExcess n hn hNot))

/-- **Hors du champ ⟺ une abscisse `x ≥ 1` où l'enveloppe de `w` dépasse celle de `z₁`.** -/
theorem not_insideField_iff_exists_exceedance (z₁ w : TrueZero) :
    ¬ InsideField z₁ w ↔ ∃ x : ℝ, 1 ≤ x ∧ pairAmplitude z₁ x < pairAmplitude w x := by
  rw [insideField_iff_pairAmplitude]
  simp only [not_forall, not_le, exists_prop]

/-- **Persistance d'un dépassement** : `z₁` en ligne, `β_w ≥ 1/2` ; si l'enveloppe de `w` dépasse
celle
de `z₁` en `x > 0`, elle la dépasse en toute abscisse `x' ≥ x` (le rapport `x^{β_w −
1/2}·‖ρ₁‖/‖ρ_w‖`
ne décroît pas). -/
theorem exceedance_persists {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hw : 1 / 2 ≤ rZeroRadialPosition w.1) {x x' : ℝ} (hx : 0 < x) (hxx' : x ≤ x')
    (hEx : pairAmplitude z₁ x < pairAmplitude w x) :
    pairAmplitude z₁ x' < pairAmplitude w x' := by
  have hx' : 0 < x' := lt_of_lt_of_le hx hxx'
  have hA1 : 0 < pairAmplitude z₁ x := pairAmplitude_pos z₁ hx
  have hA1' : 0 < pairAmplitude z₁ x' := pairAmplitude_pos z₁ hx'
  have hr : 1 < pairAmplitude w x / pairAmplitude z₁ x := (one_lt_div hA1).mpr hEx
  have hr' : pairAmplitude w x / pairAmplitude z₁ x ≤
      pairAmplitude w x' / pairAmplitude z₁ x' := by
    rw [pairAmplitude_ratio_onLine_first z₁ w h₁ hx, pairAmplitude_ratio_onLine_first z₁ w h₁ hx']
    refine mul_le_mul_of_nonneg_right ?_ (div_nonneg (norm_nonneg _) (norm_nonneg _))
    exact Real.rpow_le_rpow hx.le hxx' (by linarith)
  exact (one_lt_div hA1').mp (lt_of_lt_of_le hr hr')

/-- **Détection sur le support fixé** : si `w` (`β_w ≥ 1/2`) dépasse le champ du premier (en ligne)
en
`x₀ ≥ 1`, toute abscisse `xs i ≥ x₀` du support lit l'enveloppe de `w` au-dessus de celle du
premier. Lecture de l'ENVELOPPE, pas de la contribution ; un support fixé avant le membre n'a pas
nécessairement une abscisse au-delà de `x₀`. -/
theorem exceedance_detected_on_support {m : ℕ} (xs : Fin m → ℝ) {z₁ w : TrueZero}
    (h₁ : rZeroRadialPosition z₁.1 = 1 / 2) (hw : 1 / 2 ≤ rZeroRadialPosition w.1)
    {x₀ : ℝ} (hx₀ : 1 ≤ x₀) (hEx : pairAmplitude z₁ x₀ < pairAmplitude w x₀)
    {i : Fin m} (hi : x₀ ≤ xs i) :
    pairAmplitude z₁ (xs i) < pairAmplitude w (xs i) :=
  exceedance_persists h₁ hw (by linarith) hi hEx


/-! ## 17. Couplage rétrécissement–fréquence–amplitude dans le régime ON (directive de l'auteur,
2026-10-07)

Relations ON : `W(T) = π/T` (intervalle logarithmique entre contacts), `f(T) = T/π` (fréquence par
unité de logarithme), `A(T) = 2/√(1/4 + T²)` (enveloppe). Entre deux hauteurs `T_n < T_{n+1}` :
`W_{n+1}/W_n = T_n/T_{n+1}`, `f_{n+1}/f_n = T_{n+1}/T_n`, `A_{n+1}/A_n = √((1/4 + T_n²)/(1/4 +
T_{n+1}²))`.
Compilé ici : ces trois rapports sont des fonctions des hauteurs seules (`onLine_coupling_ratios`) ;
l'atténuation de l'enveloppe est STRICTEMENT plus lente que le rétrécissement des cellules et
strictement
inférieure à un (`onLine_amplitude_ratio_between`) ; le nombre de cellules parcourues par un membre
dans
une fenêtre première est la sollicitation exacte divisée par `π`, `(T_n/π)·log(p_fin/p_début)`
(`window_cells_eq`), et le rapport des cellules parcourues par deux membres est le rapport des
hauteurs,
indépendant de la fenêtre (`window_cells_ratio`). DÉMONTRÉ : l'augmentation de la fréquence et le
rétrécissement sont acquis dès que la hauteur augmente. NON DÉMONTRÉ : toute « accélération »
(variation
de ces rapports d'un passage au suivant), qui exigerait une loi sur la suite des hauteurs ; toute
borne
reliant ce couplage aux sommes oscillantes des interactions. -/

/-- **Les trois rapports ON sont des fonctions des hauteurs seules.** -/
theorem onLine_coupling_ratios {z w : TrueZero} (hz : rZeroRadialPosition z.1 = 1 / 2)
    (hw : rZeroRadialPosition w.1 = 1 / 2) {x : ℝ} (hx : 0 < x) :
    (Real.pi / rZeroHeight w.1) / (Real.pi / rZeroHeight z.1) = rZeroHeight z.1 / rZeroHeight w.1 ∧
    (rZeroHeight w.1 / Real.pi) / (rZeroHeight z.1 / Real.pi) = rZeroHeight w.1 / rZeroHeight z.1 ∧
    pairAmplitude w x / pairAmplitude z x =
      Real.sqrt (1 / 4 + rZeroHeight z.1 ^ 2) / Real.sqrt (1 / 4 + rZeroHeight w.1 ^ 2) := by
  have hTz : 0 < rZeroHeight z.1 := z.2
  have hTw : 0 < rZeroHeight w.1 := w.2
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · rw [pairAmplitude_onLine z hz hx, pairAmplitude_onLine w hw hx]
    have h1 : 0 < Real.sqrt (1 / 4 + rZeroHeight z.1 ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have h2 : 0 < Real.sqrt (1 / 4 + rZeroHeight w.1 ^ 2) := Real.sqrt_pos.mpr (by positivity)
    field_simp

/-- **L'enveloppe s'atténue strictement moins vite que les cellules ne rétrécissent** : pour
`T_z < T_w` en ligne, `T_z/T_w < A_w/A_z < 1`. -/
theorem onLine_amplitude_ratio_between {z w : TrueZero} (hz : rZeroRadialPosition z.1 = 1 / 2)
    (hw : rZeroRadialPosition w.1 = 1 / 2) (hT : rZeroHeight z.1 < rZeroHeight w.1) {x : ℝ}
    (hx : 0 < x) :
    rZeroHeight z.1 / rZeroHeight w.1 < pairAmplitude w x / pairAmplitude z x ∧
      pairAmplitude w x / pairAmplitude z x < 1 := by
  have hTz : 0 < rZeroHeight z.1 := z.2
  have hTw : 0 < rZeroHeight w.1 := w.2
  have hAz : 0 < pairAmplitude z x := pairAmplitude_pos z hx
  refine ⟨?_, (div_lt_one hAz).mpr (pairAmplitude_onLine_lt_of_height hz hw hT hx)⟩
  rw [(onLine_coupling_ratios hz hw hx).2.2]
  have ha : (0 : ℝ) < 1 / 4 + rZeroHeight z.1 ^ 2 := by positivity
  have hb : (0 : ℝ) < 1 / 4 + rZeroHeight w.1 ^ 2 := by positivity
  refine lt_of_pow_lt_pow_left₀ 2 (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ?_
  rw [div_pow, div_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le,
    div_lt_div_iff₀ (by positivity) hb]
  nlinarith [mul_pos hTz hTw]

/-- **Cellules parcourues dans une fenêtre première** `[p_a, p_{a+m}]` : la sollicitation exacte
`Σ_r Δθ_{n,r} = T_n·log(p_{a+m}/p_a)` divisée par `π`. -/
theorem window_cells_eq (z : TrueZero) (a m : ℕ) :
    (∑ j ∈ Finset.range m, phaseIncrement z (a + j)) / Real.pi =
      rZeroHeight z.1 / Real.pi *
        (Real.log (fnPrimeAtRank (a + m) : ℝ) - Real.log (fnPrimeAtRank a : ℝ)) := by
  rw [phaseIncrement_window_sum]
  ring

/-- **Le rapport des cellules parcourues par deux membres dans une même fenêtre est le rapport des
hauteurs**, quelle que soit la fenêtre (dès qu'elle contient au moins un écart). -/
theorem window_cells_ratio (z w : TrueZero) (a m : ℕ) (hm : 0 < m) :
    ((∑ j ∈ Finset.range m, phaseIncrement w (a + j)) / Real.pi) /
        ((∑ j ∈ Finset.range m, phaseIncrement z (a + j)) / Real.pi) =
      rZeroHeight w.1 / rZeroHeight z.1 := by
  rw [window_cells_eq, window_cells_eq]
  have hTz : 0 < rZeroHeight z.1 := z.2
  have hlt : (fnPrimeAtRank a : ℝ) < fnPrimeAtRank (a + m) := by
    exact_mod_cast thm_primeAtRank_strictMono (by omega : a < a + m)
  have hpos : (0 : ℝ) < fnPrimeAtRank a := by exact_mod_cast thm_primeAtRank_pos a
  have hL : 0 < Real.log (fnPrimeAtRank (a + m) : ℝ) - Real.log (fnPrimeAtRank a : ℝ) := by
    have := Real.log_lt_log hpos hlt
    linarith
  field_simp


/-! ## 18. Chaînes de Tours : télescopage des gains, interaction interne / externe / résidu,
invariance de la troncature, coût d'un masquage, progression cumulée (directive de l'auteur,
2026-10-08, E183)

Identités et inégalités DÉMONTRÉES depuis les objets acquis, toute position radiale, aucune
convergence, aucune hypothèse de régime :
* sur une chaîne de rangs `a ≤ n < b`, la somme des gains collectifs est la chute d'énergie du
  reste entre les deux bouts (`chain_gain_telescope`) ;
* l'interaction d'un rang `n` d'une chaîne `[n, b]` se découpe EXACTEMENT en interaction interne à
  la chaîne, interaction avec les membres extérieurs jusqu'à `N` et résidu après `N`
  (`interaction_eq_chain_add_external_add_residual`) ;
* à support et rang fixés, changer la troncature `N` ne change pas l'interaction complète, seulement
  sa répartition entre queue finie et résidu (`interaction_tail_decomposition_truncation_invariant`,
  correction de l'auteur) ;
* COÛT D'UN MASQUAGE : si le gain d'un rang ne dépasse pas celui du premier (`D_n ≤ D_1`), alors
  `E_n − D_1 ≤ −2 I_n` et, par Cauchy–Schwarz, `‖c_n‖² − D_1 ≤ 2‖r_n‖‖c_n‖` : une énergie propre
  au-dessus de `D_1` ne reste masquée dans la reconstruction collective qu'au prix d'une interaction
  négative d'au moins `(E_n − D_1)/2`, donc d'un reste après le rang de norme au moins
  `(‖c_n‖² − D_1)/(2‖c_n‖)` (`masked_gain_requires_interaction`, `masked_gain_requires_residual`) ;
  sur l'instance canonique, sous la prémisse réduite, à tout rang hors du champ
  (`canonical_masked_exceedance_requires_residual`) ; c'est une CONSÉQUENCE de la prémisse, elle ne
  donne pas l'obligation d'excès `¬ InsideField ⟹ D_1 < D_n`, qui reste non dérivée ;
* progression de hauteur sur une chaîne : la progression cumulée est la somme des pas
  (`cumulative_height_eq_sum_steps`), strictement positive si chaque pas l'est
  (`cumulative_height_pos_of_strict`) ; une progression cumulée positive n'exclut PAS un pas de
  hauteur nulle (`cumulative_pos_not_strict_witness`) : la vérification doit porter sur chaque pas ;
* le rétrécissement cumulé des intervalles sur une chaîne télescope (`pitch_chain_telescope`).
Aucune séparation minimale des hauteurs, aucune borne des sommes oscillantes, aucune obligation
d'excès n'est posée ni dérivée ici. -/

section Chains

omit [InnerProductSpace ℝ V] in
/-- **Télescopage des gains sur une chaîne** `1 ≤ a ≤ b` :
`Σ_{a≤n<b} D_n = ‖partialRemainder a‖² − ‖partialRemainder b‖²`. -/
theorem chain_gain_telescope (c : ℕ → V) (R : V) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, collectiveGain c R n =
      ‖partialRemainder c R a‖ ^ 2 - ‖partialRemainder c R b‖ ^ 2 := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih, collectiveGain_eq_energy_drop c R (ha.trans hab)]
    ring

/-- **Interaction d'un rang `n` d'une chaîne `[n, b]`** : interne à la chaîne, externe jusqu'à `N`,
résidu après `N` (`n ≤ b ≤ N`). -/
theorem interaction_eq_chain_add_external_add_residual (c : ℕ → V) (R : V) {n b N : ℕ}
    (hnb : n ≤ b) (hbN : b ≤ N) :
    interaction c R n =
      ∑ j ∈ Finset.Ioc n b, ⟪c j, c n⟫_ℝ + ∑ j ∈ Finset.Ioc b N, ⟪c j, c n⟫_ℝ +
        ⟪partialRemainder c R (N + 1), c n⟫_ℝ := by
  rw [interaction_eq_tail_add c R (hnb.trans hbN),
    ← Finset.sum_Ioc_consecutive (fun j => ⟪c j, c n⟫_ℝ) hnb hbN]

/-- **Invariance de la troncature** : à support et rang fixés, deux troncatures `N`, `N'` donnent la
même interaction complète ; seule la répartition entre queue finie et résidu change. -/
theorem interaction_tail_decomposition_truncation_invariant (c : ℕ → V) (R : V) {n N N' : ℕ}
    (hnN : n ≤ N) (hnN' : n ≤ N') :
    ∑ j ∈ Finset.Ioc n N, ⟪c j, c n⟫_ℝ + ⟪partialRemainder c R (N + 1), c n⟫_ℝ =
      ∑ j ∈ Finset.Ioc n N', ⟪c j, c n⟫_ℝ + ⟪partialRemainder c R (N' + 1), c n⟫_ℝ := by
  rw [← interaction_eq_tail_add c R hnN, ← interaction_eq_tail_add c R hnN']

/-- **Coût d'un masquage, en interaction** : `D_n ≤ D_1 ⟹ E_n − D_1 ≤ −2 I_n`. -/
theorem masked_gain_requires_interaction (c : ℕ → V) (R : V) {n : ℕ} (hn : 1 ≤ n)
    (hD : collectiveGain c R n ≤ collectiveGain c R 1) :
    ownEnergy c n - collectiveGain c R 1 ≤ -(2 * interaction c R n) := by
  have h := collectiveGain_eq_ownEnergy_add_interaction c R hn
  linarith

/-- **Coût d'un masquage, en norme du reste** : `D_n ≤ D_1 ⟹ ‖c_n‖² − D_1 ≤ 2‖r_n‖‖c_n‖`
(Cauchy–Schwarz sur `I_n = ⟨r_n, c_n⟩`). -/
theorem masked_gain_requires_residual (c : ℕ → V) (R : V) {n : ℕ} (hn : 1 ≤ n)
    (hD : collectiveGain c R n ≤ collectiveGain c R 1) :
    ‖c n‖ ^ 2 - collectiveGain c R 1 ≤ 2 * (‖partialRemainder c R (n + 1)‖ * ‖c n‖) := by
  have h := masked_gain_requires_interaction c R hn hD
  have hCS := abs_real_inner_le_norm (partialRemainder c R (n + 1)) (c n)
  have hneg := neg_abs_le ⟪partialRemainder c R (n + 1), c n⟫_ℝ
  unfold ownEnergy at h
  unfold interaction at h
  linarith

/-- **Sur l'instance canonique, sous la prémisse réduite** : à tout rang hors du champ du premier,
`‖c_n‖² − D_1 ≤ 2‖r_n‖‖c_n‖`. Conséquence de la prémisse ; elle n'en est pas la dérivation et ne
donne pas l'obligation d'excès. -/
theorem canonical_masked_exceedance_requires_residual {m : ℕ} (xs : Fin m → ℝ)
    (hGainRes : ∀ n : ℕ, 1 ≤ n → ¬ InsideField (canonicalZero 1) (canonicalZero n) →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1)
    {n : ℕ} (hn : 1 ≤ n) (hNot : ¬ InsideField (canonicalZero 1) (canonicalZero n)) :
    ‖canonicalContributions xs n‖ ^ 2 -
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1 ≤
      2 * (‖partialRemainder (canonicalContributions xs) (normalizedRawRemainderVector xs)
        (n + 1)‖ * ‖canonicalContributions xs n‖) :=
  masked_gain_requires_residual _ _ hn (hGainRes n hn hNot)

end Chains

/-- **Progression cumulée = somme des pas** sur une chaîne de `k` passages depuis le rang `a`. -/
theorem cumulative_height_eq_sum_steps (T : ℕ → ℝ) (a k : ℕ) :
    T (a + k) - T a = ∑ i ∈ Finset.range k, (T (a + i + 1) - T (a + i)) := by
  have h := Finset.sum_range_sub (fun i => T (a + i)) k
  simp only [add_zero, ← add_assoc] at h
  exact h.symm

/-- **Chaque pas strictement positif ⟹ progression cumulée strictement positive.** -/
theorem cumulative_height_pos_of_strict (T : ℕ → ℝ) (a k : ℕ) (hk : 0 < k)
    (hStrict : ∀ i, i < k → T (a + i) < T (a + i + 1)) : 0 < T (a + k) - T a := by
  rw [cumulative_height_eq_sum_steps]
  apply Finset.sum_pos
  · intro i hi
    linarith [hStrict i (Finset.mem_range.mp hi)]
  · exact Finset.nonempty_range_iff.mpr hk.ne'

/-- **Une progression cumulée positive n'exclut pas un pas de hauteur nulle** : témoin `0, 0, 1`
(deux passages, progression cumulée `1`, premier pas nul). La vérification doit porter sur chaque
pas. -/
theorem cumulative_pos_not_strict_witness :
    ∃ T : ℕ → ℝ, 0 < T (0 + 2) - T 0 ∧ T (0 + 0) = T (0 + 0 + 1) := by
  refine ⟨fun n => if n = 2 then 1 else 0, ?_, ?_⟩ <;> norm_num

/-- **Rétrécissement cumulé des intervalles sur une chaîne** : `Σ_{i<k} (W_{a+i} − W_{a+i+1}) =
W_a − W_{a+k}`, les intervalles `W = π/T` d'une suite quelconque de vrais zéros. -/
theorem pitch_chain_telescope (z : ℕ → TrueZero) (a k : ℕ) :
    ∑ i ∈ Finset.range k, (towerPitch (z (a + i)) - towerPitch (z (a + i + 1))) =
      towerPitch (z a) - towerPitch (z (a + k)) := by
  have h := Finset.sum_range_sub' (fun i => towerPitch (z (a + i))) k
  simp only [add_zero, ← add_assoc] at h
  exact h

#print axioms chain_gain_telescope
#print axioms interaction_eq_chain_add_external_add_residual
#print axioms interaction_tail_decomposition_truncation_invariant
#print axioms masked_gain_requires_interaction
#print axioms masked_gain_requires_residual
#print axioms canonical_masked_exceedance_requires_residual
#print axioms cumulative_height_eq_sum_steps
#print axioms cumulative_height_pos_of_strict
#print axioms cumulative_pos_not_strict_witness
#print axioms pitch_chain_telescope


/-! ## 19. Variations obligatoires de la grammaire mod 6 et leurs impacts sur les arguments
(directive de l'auteur, 2026-10-08 : « tiens compte des variations obligatoires définies dans la
grammaire ; tous les modulo 6 vérifiés »)

Compilé ici, depuis la grammaire acquise (`primeGap_eq_magnitude_class`, `eventClass_mem`,
`eventClass_alternates`, `alternating_two_step_gap`, `state_return_iff_two_step_mod6`,
`window_channel_lock`, `primeAtRank_even_window_ge`, `relative_phase_window_ge`) :
* PLANCHER PAR CLASSE : un maintien (`a_r = 0`) impose `g_r ≥ 6`, un changement `AB` (`a_r = 2`)
  impose `g_r ≥ 2`, un changement `BA` (`a_r = 4`) impose `g_r ≥ 4` (`primeGap_ge_classFloor`) ;
* la classe lit la transition d'état : `a = 2 ⟺ A → B`, `a = 4 ⟺ B → A`, `a = 0 ⟺ état gardé`
  (déjà compilé, `Grammar/Mod6Rigidity.lean` : `gapClass6_eq_two_iff`, `gapClass6_eq_four_iff`,
  `gapClass6_eq_zero_iff`) ;
* IMPACT SUR LA SOLLICITATION : `L_r ≥ log(1 + plancher(a_r)/p_r)` (`primeGapLogRatio_ge_classFloor`)
  et, pour deux membres, l'écart des avances de phase à l'événement `r` vaut au moins
  `|T_z − T_w| · log(1 + plancher(a_r)/p_r)` (`relative_phaseIncrement_abs_ge_classFloor`) : c'est la
  variation OBLIGATOIRE de l'argument de différence imposée par la grammaire à chaque événement ;
  l'argument de somme avance d'au moins `(T_z + T_w) · log(1 + plancher(a_r)/p_r)`
  (`sum_phaseIncrement_ge_classFloor`).
Ces planchers mesurent l'effet de la grammaire sur les deux arguments ; ils ne bornent pas les sommes
oscillantes et ne donnent aucune obligation d'excès. -/

/-- **Plancher d'écart d'une classe** : `6` pour un maintien, `a` pour un changement. -/
def classFloor (a : ℕ) : ℕ := if a = 0 then 6 else a

theorem classFloor_zero : classFloor 0 = 6 := rfl
theorem classFloor_two : classFloor 2 = 2 := rfl
theorem classFloor_four : classFloor 4 = 4 := rfl

/-- Deux premiers consécutifs sont distincts : l'écart est strictement positif. -/
theorem nPrimeGap_pos (r : ℕ) : 0 < nPrimeGap r :=
  Nat.sub_pos_of_lt (thm_primeAtRank_lt_successor r)

/-- **Plancher par classe** : `g_r ≥ 6` si `a_r = 0`, `g_r ≥ 2` si `a_r = 2`, `g_r ≥ 4` si `a_r = 4`
(`p_r > 3`). -/
theorem primeGap_ge_classFloor (r : ℕ) (h3 : 3 < fnPrimeAtRank r) :
    classFloor (eventClass r) ≤ nPrimeGap r := by
  have h := primeGap_eq_magnitude_class r
  have hpos := nPrimeGap_pos r
  rcases eventClass_mem r h3 with h0 | h2 | h4
  · rw [h0] at h ⊢; rw [classFloor_zero]; omega
  · rw [h2] at h ⊢; rw [classFloor_two]; omega
  · rw [h4] at h ⊢; rw [classFloor_four]; omega

/-- **Plancher de la sollicitation par classe** : `L_r ≥ log(1 + plancher(a_r)/p_r)`. -/
theorem primeGapLogRatio_ge_classFloor (r : ℕ) (h3 : 3 < fnPrimeAtRank r) :
    Real.log (1 + (classFloor (eventClass r) : ℝ) / (fnPrimeAtRank r : ℝ)) ≤
      rPrimeGapLogRatio r := by
  rw [primeGapLogRatio_eq_log_one_add]
  have h0 : (0 : ℝ) < (fnPrimeAtRank r : ℝ) := by exact_mod_cast thm_primeAtRank_pos r
  have hle : (classFloor (eventClass r) : ℝ) ≤ 6 * (gapMagnitude r : ℝ) + (eventClass r : ℝ) := by
    have h := primeGap_ge_classFloor r h3
    rw [primeGap_eq_magnitude_class r] at h
    exact_mod_cast h
  apply Real.log_le_log
  · positivity
  · gcongr

/-- Le plancher logarithmique d'une classe est positif ou nul. -/
theorem log_classFloor_nonneg (r : ℕ) :
    0 ≤ Real.log (1 + (classFloor (eventClass r) : ℝ) / (fnPrimeAtRank r : ℝ)) :=
  Real.log_nonneg (le_add_of_nonneg_right (by positivity))

/-- **Variation obligatoire de l'argument de différence à l'événement `r`** :
`|ΔΘ_z − ΔΘ_w| ≥ |T_z − T_w| · log(1 + plancher(a_r)/p_r)`. -/
theorem relative_phaseIncrement_abs_ge_classFloor (z w : TrueZero) (r : ℕ)
    (h3 : 3 < fnPrimeAtRank r) :
    |rZeroHeight z.1 - rZeroHeight w.1| *
        Real.log (1 + (classFloor (eventClass r) : ℝ) / (fnPrimeAtRank r : ℝ)) ≤
      |phaseIncrement z r - phaseIncrement w r| := by
  rw [relative_phaseIncrement, abs_mul,
    abs_of_nonneg ((log_classFloor_nonneg r).trans (primeGapLogRatio_ge_classFloor r h3))]
  exact mul_le_mul_of_nonneg_left (primeGapLogRatio_ge_classFloor r h3) (abs_nonneg _)

/-- **Variation obligatoire de l'argument de somme à l'événement `r`** :
`ΔΘ_z + ΔΘ_w ≥ (T_z + T_w) · log(1 + plancher(a_r)/p_r)`. -/
theorem sum_phaseIncrement_ge_classFloor (z w : TrueZero) (r : ℕ) (h3 : 3 < fnPrimeAtRank r) :
    (rZeroHeight z.1 + rZeroHeight w.1) *
        Real.log (1 + (classFloor (eventClass r) : ℝ) / (fnPrimeAtRank r : ℝ)) ≤
      phaseIncrement z r + phaseIncrement w r := by
  rw [phaseIncrement_eq_height_mul_ratio, phaseIncrement_eq_height_mul_ratio, ← add_mul]
  have hz : 0 < rZeroHeight z.1 := z.2
  have hw : 0 < rZeroHeight w.1 := w.2
  exact mul_le_mul_of_nonneg_left (primeGapLogRatio_ge_classFloor r h3) (by linarith)

#print axioms nPrimeGap_pos
#print axioms primeGap_ge_classFloor
#print axioms primeGapLogRatio_ge_classFloor
#print axioms log_classFloor_nonneg
#print axioms relative_phaseIncrement_abs_ge_classFloor
#print axioms sum_phaseIncrement_ge_classFloor


#print axioms gain_restricted_of_all_onLine
#print axioms riemannHypothesis_of_all_canonical_onLine
#print axioms canonical_onLine_weighted_le_first
#print axioms canonical_normSq_le_envelope
#print axioms canonical_onLine_envelope_le_first
#print axioms norm_eq_zero_of_fin_zero
#print axioms collectiveGain_support_empty
#print axioms gain_of_support_empty
#print axioms gain_restricted_of_support_empty
#print axioms compensation_bound_incompatible
#print axioms compensation_target_iff_ownEnergy_le
#print axioms canonical_ownEnergy_le_first_of_no_compensation

#print axioms pairAmplitude_onLine_le_of_height
#print axioms pairAmplitude_ratio
#print axioms canonicalZero_height_mono
#print axioms canonical_onLine_amplitude_le_first
#print axioms canonical_onLine_insideField
#print axioms abs_normalizedSmoothedPairContribution_le
#print axioms smoothed_onLine_envelope_anti
#print axioms not_onLine_of_not_insideField
#print axioms canonical_ownEnergy_diff_le_of_restricted
#print axioms canonical_norm_le_first_of_interaction_restricted
#print axioms pairAmplitude_ratio_onLine_first
#print axioms abs_normalizedSmoothedPairContribution_onLine_le
#print axioms gain_restricted_of_gain
#print axioms gain_restricted_vacuous_onLine
#print axioms riemannHypothesis_of_canonical_insideField
#print axioms riemannHypothesis_of_restricted_gain_link

#print axioms pairContribution_eq
#print axioms pairContribution_at_contact
#print axioms pairAmplitude_onLine_contact_interval
#print axioms pairAmplitude_onLine_lt_of_height
#print axioms collectiveGain_eq
#print axioms collectiveGain_collective
#print axioms firstGain_collective_relation
#print axioms firstGain_amplitude_bound
#print axioms collectiveGain_eq_own_add_interaction
#print axioms following_partial_sums_tendsto
#print axioms firstGain_relation
#print axioms abs_normalizedPairContribution_le
#print axioms firstGain_canonical
#print axioms canonicalContributions_first_anchor
#print axioms normalizedSmoothedPairContribution_hasSum
#print axioms smoothedCanonical_hasSum
#print axioms firstGain_smoothed_collective
#print axioms collectiveGain_eq_ownEnergy_add_interaction
#print axioms gain_margin_eq
#print axioms ownEnergy_diff_eq
#print axioms ownEnergy_diff_le_of_gain
#print axioms ownEnergy_le_first_iff
#print axioms norm_le_first_iff_interaction_margin
#print axioms canonical_norm_le_first_iff
#print axioms canonical_ownEnergy_diff_le
#print axioms pairContribution_mul
#print axioms normalizedPairContribution_mul
#print axioms canonical_inner_eq_phase_sum
#print axioms interaction_eq_tail_add
#print axioms interaction_tendsto_of_ordered
#print axioms interaction_hasSum
#print axioms smoothedCanonical_interaction_hasSum
#print axioms weighted_amplitude_onLine_lt_of_height
#print axioms pairAmplitude_own_contact_step
#print axioms relative_phaseIncrement
#print axioms relative_phase_window_sum
#print axioms relative_phase_window_ge
#print axioms canonical_relative_phase_step
#print axioms primeGap_eq_magnitude_class
#print axioms eventClass_mem
#print axioms eventClass_alternates
#print axioms primeGapLogRatio_eq_log_one_add
#print axioms rawAmplitude_prime_step
#print axioms pairAmplitude_prime_step
#print axioms onLine_prime_step
#print axioms phaseIncrement_window_sum
#print axioms window_sum_by_classes
#print axioms window_channel_lock
#print axioms beat_arguments_prime_step
#print axioms canonical_inner_primeSupport
#print axioms insideField_iff_pairAmplitude
#print axioms riemannHypothesis_of_individual_domination
#print axioms riemannHypothesis_of_individual_domination_onLine
#print axioms individual_domination_iff_riemannHypothesis
#print axioms pairAmplitude_pos
#print axioms captivity_log_iff_insideField
#print axioms captivity_iff_insideField
#print axioms firstField_constant_onLine
#print axioms riemannHypothesis_of_captivity_onLine
#print axioms interaction_abs_le_tail_add_residual
#print axioms gain_excess_iff
#print axioms normalizedPairContribution_mul_sameHeight
#print axioms canonical_insideField_of_gain_excess
#print axioms not_insideField_iff_exists_exceedance
#print axioms exceedance_persists
#print axioms exceedance_detected_on_support
#print axioms onLine_coupling_ratios
#print axioms onLine_amplitude_ratio_between
#print axioms window_cells_eq
#print axioms window_cells_ratio

/-! ## 20. Retrait exact du premier membre : intervalle signé, troncature et résidu, borne démontrée
de la queue dans le canal lissé, compensation nécessaire contre majoration acquise (directive de
l'auteur, 2026-10-08, points 2, 5 et 7 ; E184)

Tout est écrit sur les objets déjà définis : `S = R − c_1 = partialRemainder c R 2`, queue finie
`S_N = tailSum c 1 N = Σ_{j=2}^{N} c_j`, résidu `ε_N = partialRemainder c R (N + 1) = R − Σ_{j≤N} c_j`.
* **Retrait signé** : de `R = c_1 + S` et `|R| ≤ B` on tire `−B − c_1 ≤ S ≤ B − c_1`
  (`signed_removal_bounds`, forme tronquée `signed_removal_truncated_bounds`) ; l'intervalle signé
  est translaté par `c_1`, non rétréci : la somme des deux marges vaut `2B` quelle que soit `c_1`
  (`signed_margins_sum`) ; il est contenu dans l'intervalle symétrique `[−B − |c_1|, B + |c_1|]`
  (`signed_interval_subset_symmetric`) et il n'est PAS `[−(B − |c_1|), B − |c_1|]`
  (`signed_interval_not_abs_witness`).
* **Vecteur** : `partialRemainder c R 2 = R − c_1` (`first_removed_eq`),
  `R − c_1 = S_N + ε_N` (`first_removed_eq_tail_add_residual`), normes
  (`first_removed_norm_le`, `first_removed_norm_ge`) ; le gain du premier ne dépend que de `R` et
  `c_1` : toute perturbation des autres contributions le laisse inchangé
  (`collectiveGain_one_eq`, `collectiveGain_one_congr`).
* **Canal lissé, représentation acquise** : la borne DÉMONTRÉE du reste lissé (`Λ ≥ 0` + Chebyshev,
  `smoothedRemainder_linear_growth`) donne `|R̃(x)| ≤ C√x` pour `x > 1`
  (`normalizedSmoothedRemainder_abs_le_sqrt`) et le retrait signé du premier membre canonique
  (`smoothed_first_removed_signed_bounds`) ; `S̃ = Σ_{n≥2} c̃_n` (`smoothed_first_removed_hasSum`,
  sur le support `smoothed_first_removed_vector_hasSum`) ; sommabilité ABSOLUE dans l'ordre canonique
  (`normalizedSmoothedPairContribution_abs_summable`) ; **borne démontrée du résidu de troncature**
  `|ε̃_N(x)| ≤ Σ_{j≥N} |c̃_j(x)|` (`smoothed_residual_abs_le_tsum`), chaque terme borné pour `x ≥ 1`,
  toute position radiale, par `2m√x/(‖ρ‖‖ρ+1‖)` grâce à `β ≤ 1` (`smoothed_term_abs_le_sqrt`) :
  cette borne est distincte de la valeur du résidu calculée par différence.
* **Chaînes** : `Σ_{a≤n<b} 2I_n = ‖r_a‖² − ‖r_b‖² − Σ E_n` (`chain_interaction_telescope`).
* **Compensation nécessaire contre majoration acquise** : `D_n ≤ D_1 ⟺ (E_n − D_1)/2 ≤ −I_n`
  (`masked_gain_iff_interaction`) ; sous `D_n ≤ D_1`, la compensation nécessaire `(E_n − D_1)/2` ne
  dépasse pas la seule majoration acquise de la compensation possible,
  `Σ_{n<j≤N} |⟨c_j, c_n⟩| + ‖r_N‖‖c_n‖` (`masked_exceedance_le_acquired_bound`). L'inégalité qui
  reste à démontrer est l'inverse strict pour un rang hors du champ :
  `Σ_{n<j≤N} |⟨c_j, c_n⟩| + ‖r_N‖‖c_n‖ < (E_n − D_1)/2`, soit une majoration des sommes oscillantes
  et du résidu plus petite que la compensation requise ; aucune borne compilée ne la fournit.
Aucune hypothèse nouvelle ; aucune de ces identités n'entre dans une fermeture vers RH. -/

/-- **Retrait signé du premier terme** : `R = c₁ + S`, `|R| ≤ B` ⟹ `−B − c₁ ≤ S ≤ B − c₁`. -/
theorem signed_removal_bounds {R c₁ S B : ℝ} (h : R = c₁ + S) (hB : |R| ≤ B) :
    -B - c₁ ≤ S ∧ S ≤ B - c₁ := by
  rcases abs_le.mp hB with ⟨h1, h2⟩
  constructor <;> linarith

/-- **Forme tronquée** : `R = c₁ + S_N + ε_N` ⟹ `−B − c₁ ≤ S_N + ε_N ≤ B − c₁` ; le résidu est conservé
dans l'intervalle, il n'est pas remplacé par une borne. -/
theorem signed_removal_truncated_bounds {R c₁ SN εN B : ℝ} (h : R = c₁ + SN + εN) (hB : |R| ≤ B) :
    -B - c₁ ≤ SN + εN ∧ SN + εN ≤ B - c₁ :=
  signed_removal_bounds (by rw [h]; ring) hB

/-- **Les deux marges** (distance à la limite haute, distance à la limite basse) ont pour somme `2B`,
quelle que soit `c₁` : le retrait translate l'intervalle, il ne le rétrécit pas. -/
theorem signed_margins_sum (c₁ S B : ℝ) : ((B - c₁) - S) + (S - (-B - c₁)) = 2 * B := by ring

/-- L'intervalle signé est contenu dans l'intervalle symétrique `[−B − |c₁|, B + |c₁|]`. -/
theorem signed_interval_subset_symmetric (c₁ B : ℝ) : -B - |c₁| ≤ -B - c₁ ∧ B - c₁ ≤ B + |c₁| := by
  constructor <;> linarith [le_abs_self c₁, neg_abs_le c₁]

/-- **L'intervalle signé n'est pas `[−(B − |c₁|), B − |c₁|]`** : témoin `R = 0`, `c₁ = −1`, `S = 1`,
`B = 0` ; `S ≤ B − |c₁|` est faux. -/
theorem signed_interval_not_abs_witness :
    ∃ R c₁ S B : ℝ, R = c₁ + S ∧ |R| ≤ B ∧ ¬ (S ≤ B - |c₁|) :=
  ⟨0, -1, 1, 0, by norm_num, by norm_num, by norm_num⟩

omit [InnerProductSpace ℝ V] in
/-- `S = R − c_1` est le reste après le rang `1`. -/
theorem first_removed_eq (c : ℕ → V) (R : V) : partialRemainder c R 2 = R - c 1 := by
  rw [partialRemainder_succ c R le_rfl, partialRemainder_one]

omit [InnerProductSpace ℝ V] in
/-- **Décomposition avec résidu** : `R − c_1 = S_N + ε_N`, `S_N = Σ_{j=2}^{N} c_j`,
`ε_N = R − Σ_{j≤N} c_j` (`1 ≤ N`). -/
theorem first_removed_eq_tail_add_residual (c : ℕ → V) (R : V) {N : ℕ} (hN : 1 ≤ N) :
    R - c 1 = tailSum c 1 N + partialRemainder c R (N + 1) := by
  rw [← first_removed_eq, partialRemainder_eq_tailSum_add c R hN]

omit [InnerProductSpace ℝ V] in
/-- Marge haute en norme : `‖R‖ ≤ B ⟹ ‖R − c_1‖ ≤ B + ‖c_1‖`. -/
theorem first_removed_norm_le (c : ℕ → V) (R : V) {B : ℝ} (hB : ‖R‖ ≤ B) :
    ‖R - c 1‖ ≤ B + ‖c 1‖ :=
  (norm_sub_le _ _).trans (add_le_add hB le_rfl)

omit [InnerProductSpace ℝ V] in
/-- Marge basse en norme : `‖R‖ ≤ B ⟹ ‖c_1‖ − B ≤ ‖R − c_1‖`. -/
theorem first_removed_norm_ge (c : ℕ → V) (R : V) {B : ℝ} (hB : ‖R‖ ≤ B) :
    ‖c 1‖ - B ≤ ‖R - c 1‖ := by
  have h := norm_sub_norm_le (c 1) R
  rw [← norm_neg (c 1 - R), neg_sub] at h
  linarith

/-- **Le gain du premier ne lit que `R` et `c_1`** : `D_1 = 2⟨R, c_1⟩ − ‖c_1‖²`. -/
theorem collectiveGain_one_eq (c : ℕ → V) (R : V) :
    collectiveGain c R 1 = 2 * ⟪R, c 1⟫_ℝ - ‖c 1‖ ^ 2 := by
  rw [collectiveGain_eq, partialRemainder_one]

/-- **Invariance du gain du premier** : deux familles de contributions de même premier terme ont le
même `D_1` sur le même reste ; toute perturbation des autres membres le laisse inchangé. -/
theorem collectiveGain_one_congr (c c' : ℕ → V) (R : V) (h : c 1 = c' 1) :
    collectiveGain c R 1 = collectiveGain c' R 1 := by
  rw [collectiveGain_one_eq, collectiveGain_one_eq, h]

/-- **Borne DÉMONTRÉE du reste lissé normalisé** : `∃ C, ∀ x > 1, |R̃(x)| ≤ C√x`, depuis `Λ ≥ 0` et
Chebyshev (`smoothedRemainder_linear_growth`). Canal lissé ; démontrée ; `x > 1`. -/
theorem normalizedSmoothedRemainder_abs_le_sqrt :
    ∃ C : ℝ, ∀ x : ℝ, 1 < x → |normalizedSmoothedRemainder x| ≤ C * Real.sqrt x := by
  obtain ⟨C, hC⟩ := smoothedRemainder_linear_growth
  refine ⟨C, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  unfold normalizedSmoothedRemainder
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  calc |(smoothedRemainder x).re| ≤ ‖smoothedRemainder x‖ := Complex.abs_re_le_norm _
    _ ≤ C * x ^ (1 : ℝ) := hC x hx
    _ = C * Real.sqrt x * Real.sqrt x := by rw [Real.rpow_one, mul_assoc, Real.mul_self_sqrt hx0.le]

/-- **Retrait signé du premier membre canonique dans le canal lissé**, sous la borne démontrée :
`−C√x − c̃_1(x) ≤ R̃(x) − c̃_1(x) ≤ C√x − c̃_1(x)` pour tout `x > 1`. -/
theorem smoothed_first_removed_signed_bounds :
    ∃ C : ℝ, ∀ x : ℝ, 1 < x →
      -(C * Real.sqrt x) - normalizedSmoothedPairContribution (canonicalZero 1) x ≤
          normalizedSmoothedRemainder x - normalizedSmoothedPairContribution (canonicalZero 1) x ∧
        normalizedSmoothedRemainder x - normalizedSmoothedPairContribution (canonicalZero 1) x ≤
          C * Real.sqrt x - normalizedSmoothedPairContribution (canonicalZero 1) x := by
  obtain ⟨C, hC⟩ := normalizedSmoothedRemainder_abs_le_sqrt
  exact ⟨C, fun x hx => signed_removal_bounds (by ring) (hC x hx)⟩

/-- **`S̃ = Σ_{n≥2} c̃_n`** : la somme des contributions lissées normalisées des rangs `≥ 2` converge
vers le reste lissé normalisé privé du premier membre canonique (`x > 1`). -/
theorem smoothed_first_removed_hasSum {x : ℝ} (hx : 1 < x) :
    HasSum (fun j : ℕ => normalizedSmoothedPairContribution (canonicalZero (j + 2)) x)
      (normalizedSmoothedRemainder x - normalizedSmoothedPairContribution (canonicalZero 1) x) := by
  have h := (hasSum_nat_add_iff' 1).mpr (normalizedSmoothedPairContribution_hasSum hx)
  rw [Finset.sum_range_one] at h
  exact h

/-- La même somme sur le support fixé : `HasSum (c̃_{j+2}) (R̃ − c̃_1)`. -/
theorem smoothed_first_removed_vector_hasSum {m : ℕ} (xs : Fin m → ℝ) (hxs : ∀ i, 1 < xs i) :
    HasSum (fun j => smoothedCanonicalContributions xs (j + 2))
      (normalizedSmoothedRemainderVector xs - smoothedCanonicalContributions xs 1) := by
  have h := followingContributions_hasSum (smoothedCanonical_hasSum xs hxs) le_rfl
  rwa [partialRemainder_one] at h

/-- **Sommabilité absolue dans l'ordre canonique** des contributions lissées normalisées (`x > 1`). -/
theorem normalizedSmoothedPairContribution_abs_summable {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ => |normalizedSmoothedPairContribution (canonicalMember n) x| := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hN : Summable fun σ : ExplicitIndex => ‖nontrivialZeroResidueTerm x σ‖ :=
    (nontrivial_zero_residue_series_summable hx).norm
  have hE : Summable fun p : ℕ × Bool => ‖nontrivialZeroResidueTerm x (indexEquiv.symm p)‖ :=
    (Equiv.summable_iff indexEquiv.symm).mpr hN
  have hG : HasSum (fun n : ℕ => ∑ b : Bool, ‖nontrivialZeroResidueTerm x (indexEquiv.symm (n, b))‖)
      (∑' p : ℕ × Bool, ‖nontrivialZeroResidueTerm x (indexEquiv.symm p)‖) :=
    hE.hasSum.prod_fiberwise fun n => hasSum_fintype _
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => ?_)
    (hG.summable.mul_left (2 / Real.sqrt x))
  rw [Fintype.sum_bool, indexEquiv_symm_true]
  unfold normalizedSmoothedPairContribution
  rw [abs_div, abs_mul, abs_two, abs_of_pos hs, div_le_iff₀ hs]
  have h1 := Complex.abs_re_le_norm (nontrivialZeroResidueTerm x (memberIndex (canonicalMember n)))
  have h2 := norm_nonneg (nontrivialZeroResidueTerm x (indexEquiv.symm (n, false)))
  have h3 : 2 / Real.sqrt x * (‖nontrivialZeroResidueTerm x (memberIndex (canonicalMember n))‖ +
      ‖nontrivialZeroResidueTerm x (indexEquiv.symm (n, false))‖) * Real.sqrt x =
      2 * (‖nontrivialZeroResidueTerm x (memberIndex (canonicalMember n))‖ +
        ‖nontrivialZeroResidueTerm x (indexEquiv.symm (n, false))‖) := by
    field_simp
  rw [h3]
  nlinarith

/-- **Borne DÉMONTRÉE du résidu de troncature, canal lissé** : pour tout `N`,
`|R̃(x) − Σ_{n<N} c̃_n(x)| ≤ Σ_{j≥N} |c̃_j(x)|` (`x > 1`) ; distincte de la valeur calculée par différence. -/
theorem smoothed_residual_abs_le_tsum {x : ℝ} (hx : 1 < x) (N : ℕ) :
    |normalizedSmoothedRemainder x -
        ∑ n ∈ Finset.range N, normalizedSmoothedPairContribution (canonicalMember n) x| ≤
      ∑' j : ℕ, |normalizedSmoothedPairContribution (canonicalMember (j + N)) x| := by
  set f : ℕ → ℝ := fun n => normalizedSmoothedPairContribution (canonicalMember n) x with hf
  have hT : HasSum (fun j => f (j + N))
      (normalizedSmoothedRemainder x - ∑ n ∈ Finset.range N, f n) :=
    (hasSum_nat_add_iff' N).mpr (normalizedSmoothedPairContribution_hasSum hx)
  have hA0 : Summable fun n => ‖f n‖ := by
    have := normalizedSmoothedPairContribution_abs_summable hx
    simpa only [hf, Real.norm_eq_abs] using this
  have hA : Summable fun j => ‖f (j + N)‖ := (summable_nat_add_iff N).mpr hA0
  have h := norm_tsum_le_tsum_norm hA
  rw [hT.tsum_eq] at h
  simpa only [hf, Real.norm_eq_abs] using h

/-- **Chaque terme lissé normalisé est borné par `2m√x/(‖ρ‖‖ρ+1‖)` pour `x ≥ 1`**, toute position
radiale, grâce à la bande `β ≤ 1` depuis les premiers (`radial_strip_from_primes`). -/
theorem smoothed_term_abs_le_sqrt (z : TrueZero) {x : ℝ} (hx : 1 ≤ x) :
    |normalizedSmoothedPairContribution z x| ≤
      2 * (zetaZeroMultiplicity (zeroPoint z) : ℝ) * x ^ (1 / 2 : ℝ) /
        (Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) *
          Real.sqrt ((rZeroRadialPosition z.1 + 1) ^ 2 + rZeroHeight z.1 ^ 2)) := by
  have hx0 : 0 < x := by linarith
  refine (abs_normalizedSmoothedPairContribution_le z hx0).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le hx (by linarith [(radial_strip_from_primes z).2])

/-- **Interactions complètes par chaîne** : `Σ_{a≤n<b} 2I_n = ‖r_a‖² − ‖r_b‖² − Σ_{a≤n<b} E_n`. -/
theorem chain_interaction_telescope (c : ℕ → V) (R : V) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, 2 * interaction c R n =
      ‖partialRemainder c R a‖ ^ 2 - ‖partialRemainder c R b‖ ^ 2 -
        ∑ n ∈ Finset.Ico a b, ownEnergy c n := by
  have h := chain_gain_telescope c R ha hab
  have hs : ∑ n ∈ Finset.Ico a b, collectiveGain c R n =
      ∑ n ∈ Finset.Ico a b, (ownEnergy c n + 2 * interaction c R n) :=
    Finset.sum_congr rfl fun n hn =>
      collectiveGain_eq_ownEnergy_add_interaction c R (ha.trans (Finset.mem_Ico.mp hn).1)
  rw [Finset.sum_add_distrib] at hs
  linarith

/-- **Masquage ⟺ compensation nécessaire** : `D_n ≤ D_1 ⟺ (E_n − D_1)/2 ≤ −I_n`. -/
theorem masked_gain_iff_interaction (c : ℕ → V) (R : V) {n : ℕ} (hn : 1 ≤ n) :
    collectiveGain c R n ≤ collectiveGain c R 1 ↔
      (ownEnergy c n - collectiveGain c R 1) / 2 ≤ -interaction c R n := by
  have h := collectiveGain_eq_ownEnergy_add_interaction c R hn
  unfold ownEnergy interaction at *
  constructor <;> intro h' <;> linarith

/-- **Compensation nécessaire ≤ majoration acquise** : sous `D_n ≤ D_1`, `(E_n − D_1)/2 ≤
Σ_{n<j≤N} |⟨c_j, c_n⟩| + ‖r_N‖‖c_n‖`. L'inégalité manquante pour exclure le masquage d'un rang hors
du champ est l'inverse strict ; aucune borne compilée ne la fournit. -/
theorem masked_exceedance_le_acquired_bound (c : ℕ → V) (R : V) {n N : ℕ} (hn : 1 ≤ n)
    (hnN : n ≤ N) (hD : collectiveGain c R n ≤ collectiveGain c R 1) :
    (ownEnergy c n - collectiveGain c R 1) / 2 ≤
      ∑ j ∈ Finset.Ioc n N, |⟪c j, c n⟫_ℝ| + ‖partialRemainder c R (N + 1)‖ * ‖c n‖ := by
  have h1 := (masked_gain_iff_interaction c R hn).mp hD
  have h2 := interaction_abs_le_tail_add_residual c R hnN
  have h3 := neg_le_abs (interaction c R n)
  linarith

#print axioms signed_removal_bounds
#print axioms signed_removal_truncated_bounds
#print axioms signed_margins_sum
#print axioms signed_interval_subset_symmetric
#print axioms signed_interval_not_abs_witness
#print axioms first_removed_eq
#print axioms first_removed_eq_tail_add_residual
#print axioms first_removed_norm_le
#print axioms first_removed_norm_ge
#print axioms collectiveGain_one_eq
#print axioms collectiveGain_one_congr
#print axioms normalizedSmoothedRemainder_abs_le_sqrt
#print axioms smoothed_first_removed_signed_bounds
#print axioms smoothed_first_removed_hasSum
#print axioms smoothed_first_removed_vector_hasSum
#print axioms normalizedSmoothedPairContribution_abs_summable
#print axioms smoothed_residual_abs_le_tsum
#print axioms smoothed_term_abs_le_sqrt
#print axioms chain_interaction_telescope
#print axioms masked_gain_iff_interaction
#print axioms masked_exceedance_le_acquired_bound

/-! ## 21. Réduction par le miroir : où la prémisse mord exactement, et ce qui lie les zéros au premier
(auteur, 2026-10-08 : « prouver que les zéros sont liés par leurs contraintes et captifs du premier »)

Tout est sous l'ancre ON du premier membre canonique (hypothèse `h₁`, aucun terme Lean). Démontré ici :
hors du champ ⟺ membre HAUT (`β > 1/2`) ou support plus petit que celui du premier (`‖ρ_w‖ < ‖ρ₁‖`) ;
ce second cas est une BANDE FINE : membre bas, hauteur strictement entre `T₁` et `√(T₁² + 1/4)`, soit à
moins de `1/(8T₁)` au-dessus du premier ; tout membre bas au-delà de cette marge est captif par théorème ;
tout membre haut sort du champ par théorème ; dans toute paire miroir hors ligne de hauteur `≥ ‖ρ₁‖`,
exactement un membre est captif, le bas. Conséquences sur la prémisse : elle n'a à être posée qu'aux rangs
HAUTS (`hGainUp`), forme impliquée par la prémisse réduite (`gain_upper_of_restricted`) et impliquée par RH
elle-même (`gain_upper_of_riemannHypothesis` : sous RH il n'y a aucun rang haut, la prémisse est vide) ;
la bande fine n'y figure plus (chaque rang de la bande a pour miroir un rang haut). Le raccord restant
est exactement : à un rang haut, la prémisse au miroir est contredite (`upper_gain_link_iff_refutation`) ;
« chaque rang haut dans le champ » dit qu'il n'y a aucun rang haut (`upper_insideField_iff_no_upper`),
ce qui ⟺ RH (`no_upper_canonical_iff_riemannHypothesis`). Rien ici ne dérive la prémisse ni le raccord ;
la réduction AFFAIBLIT la prémisse et réduit le raccord aux seuls rangs hauts. -/

section MirrorReduction

/-- **Un membre haut n'est pas dans le champ d'un zéro en ligne** : à grande abscisse sa Tour dépasse
(`exponent_le_of_inside`). -/
theorem upper_not_insideField {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hw : 1 / 2 < rZeroRadialPosition w.1) : ¬ InsideField z₁ w := by
  intro hIn
  have h := exponent_le_of_inside (norm_zeroPoint_pos w) (norm_zeroPoint_pos z₁)
    (fun x hx => by
      have := hIn x hx
      unfold firstField at this
      rwa [norm_zeroTerm_eq w (by linarith), norm_zeroTerm_eq z₁ (by linarith)] at this)
  rw [h₁] at h
  linarith

/-- **Un membre de support strictement plus petit que celui de `z₁` n'est pas dans son champ** : lu en
`x = 1`, où les Tours valent `1/‖ρ‖`. -/
theorem small_support_not_insideField {z₁ w : TrueZero} (hρ : ‖zeroPoint w‖ < ‖zeroPoint z₁‖) :
    ¬ InsideField z₁ w := by
  intro hIn
  have h := hIn 1 le_rfl
  unfold firstField at h
  rw [norm_zeroTerm_eq w one_pos, norm_zeroTerm_eq z₁ one_pos, Real.one_rpow, Real.one_rpow] at h
  have := (one_div_le_one_div (norm_zeroPoint_pos w) (norm_zeroPoint_pos z₁)).mp h
  linarith

/-- **Hors du champ, exactement** (premier en ligne) : membre haut, ou support plus petit que celui du
premier. Le sens réciproque est la prison par les paramètres (`lower_member_prisoner`). -/
theorem not_insideField_iff_upper_or_small {z₁ w : TrueZero}
    (h₁ : rZeroRadialPosition z₁.1 = 1 / 2) :
    ¬ InsideField z₁ w ↔
      1 / 2 < rZeroRadialPosition w.1 ∨ ‖zeroPoint w‖ < ‖zeroPoint z₁‖ := by
  constructor
  · intro hNot
    by_contra hcon
    push Not at hcon
    exact hNot (lower_member_prisoner h₁ hcon.1 hcon.2)
  · rintro (h | h)
    · exact upper_not_insideField h₁ h
    · exact small_support_not_insideField h

/-- **La bande fine** : un membre au moins aussi haut que le zéro en ligne `z₁` et de support plus petit
est un membre BAS, de hauteur `T_w² < T₁² + 1/4`. -/
theorem small_support_band {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hT : rZeroHeight z₁.1 ≤ rZeroHeight w.1) (hρ : ‖zeroPoint w‖ < ‖zeroPoint z₁‖) :
    rZeroRadialPosition w.1 < 1 / 2 ∧
      rZeroHeight w.1 ^ 2 < rZeroHeight z₁.1 ^ 2 + 1 / 4 := by
  have h1 := zeroPoint_norm_sq z₁
  have h2 := zeroPoint_norm_sq w
  rw [h₁] at h1
  have hsq : ‖zeroPoint w‖ ^ 2 < ‖zeroPoint z₁‖ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hρ)
      (add_pos_of_nonneg_of_pos (norm_nonneg (zeroPoint w)) (norm_zeroPoint_pos z₁))]
  rw [h1, h2] at hsq
  have hβ0 : 0 < rZeroRadialPosition w.1 := thm_zeroRadialPosition_positive w.1
  have hT1 : 0 < rZeroHeight z₁.1 := z₁.2
  have hTsq : rZeroHeight z₁.1 ^ 2 ≤ rZeroHeight w.1 ^ 2 := pow_le_pow_left₀ hT1.le hT 2
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (rZeroRadialPosition w.1)]

/-- **Largeur de la bande fine** : un membre de support plus petit que celui du premier est à moins de
`1/(8T₁)` au-dessus de lui. -/
theorem small_support_height_lt {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hT : rZeroHeight z₁.1 ≤ rZeroHeight w.1) (hρ : ‖zeroPoint w‖ < ‖zeroPoint z₁‖) :
    rZeroHeight w.1 < rZeroHeight z₁.1 + 1 / (8 * rZeroHeight z₁.1) := by
  have hb := (small_support_band h₁ hT hρ).2
  have hT1 : 0 < rZeroHeight z₁.1 := z₁.2
  by_contra hcon
  push Not at hcon
  have hsq : (rZeroHeight z₁.1 + 1 / (8 * rZeroHeight z₁.1)) ^ 2 ≤ rZeroHeight w.1 ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcon 2
  have hexp : (rZeroHeight z₁.1 + 1 / (8 * rZeroHeight z₁.1)) ^ 2 =
      rZeroHeight z₁.1 ^ 2 + 1 / 4 + 1 / (64 * rZeroHeight z₁.1 ^ 2) := by
    field_simp
    ring
  have hpos : 0 < 1 / (64 * rZeroHeight z₁.1 ^ 2) := by positivity
  linarith

/-- **Captif par la hauteur seule** : un membre bas dont la hauteur vérifie `T_w² ≥ T₁² + 1/4` est dans le
champ du zéro en ligne `z₁`, quelle que soit sa position radiale `≤ 1/2`. -/
theorem lower_captive_of_height {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hβ : rZeroRadialPosition w.1 ≤ 1 / 2)
    (hT : rZeroHeight z₁.1 ^ 2 + 1 / 4 ≤ rZeroHeight w.1 ^ 2) : InsideField z₁ w := by
  apply lower_member_prisoner h₁ hβ
  have h1 := zeroPoint_norm_sq z₁
  have h2 := zeroPoint_norm_sq w
  rw [h₁] at h1
  have hsq : ‖zeroPoint z₁‖ ^ 2 ≤ ‖zeroPoint w‖ ^ 2 := by
    rw [h1, h2]; nlinarith [sq_nonneg (rZeroRadialPosition w.1)]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq

/-- **Captif au-delà de la marge** : un membre bas à au moins `1/(8T₁)` au-dessus du premier est captif. -/
theorem lower_captive_of_height_margin {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hβ : rZeroRadialPosition w.1 ≤ 1 / 2)
    (hT : rZeroHeight z₁.1 + 1 / (8 * rZeroHeight z₁.1) ≤ rZeroHeight w.1) : InsideField z₁ w := by
  apply lower_captive_of_height h₁ hβ
  have hT1 : 0 < rZeroHeight z₁.1 := z₁.2
  have hsq : (rZeroHeight z₁.1 + 1 / (8 * rZeroHeight z₁.1)) ^ 2 ≤ rZeroHeight w.1 ^ 2 :=
    pow_le_pow_left₀ (by positivity) hT 2
  have hexp : (rZeroHeight z₁.1 + 1 / (8 * rZeroHeight z₁.1)) ^ 2 =
      rZeroHeight z₁.1 ^ 2 + 1 / 4 + 1 / (64 * rZeroHeight z₁.1 ^ 2) := by
    field_simp
    ring
  have hpos : 0 < 1 / (64 * rZeroHeight z₁.1 ^ 2) := by positivity
  linarith

/-- **Paire miroir hors ligne, à hauteur `≥ ‖ρ₁‖`** : captif ⟺ membre bas. -/
theorem mirror_pair_captive_iff_lower {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hH : ‖zeroPoint z₁‖ ≤ rZeroHeight w.1) (hOff : rZeroRadialPosition w.1 ≠ 1 / 2) :
    InsideField z₁ w ↔ rZeroRadialPosition w.1 < 1 / 2 := by
  constructor
  · intro hIn
    rcases lt_or_gt_of_ne hOff with h | h
    · exact h
    · exact (upper_not_insideField h₁ h hIn).elim
  · intro h
    exact inside_field_of_parameters (by rw [h₁]; exact h.le)
      (hH.trans (height_le_zeroPoint_norm w))

/-- **Dans toute paire miroir hors ligne de hauteur `≥ ‖ρ₁‖`, exactement un membre est captif** : les deux
membres sont liés par le champ du premier, l'un dedans, l'autre dehors. -/
theorem mirror_pair_exactly_one_captive {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hH : ‖zeroPoint z₁‖ ≤ rZeroHeight w.1) (hOff : rZeroRadialPosition w.1 ≠ 1 / 2) :
    (InsideField z₁ w ∧ ¬ InsideField z₁ (mirrorMember w)) ∨
      (¬ InsideField z₁ w ∧ InsideField z₁ (mirrorMember w)) := by
  have hHm : ‖zeroPoint z₁‖ ≤ rZeroHeight (mirrorMember w).1 := by
    rw [mirrorMember_ordinate]; exact hH
  have hOffm : rZeroRadialPosition (mirrorMember w).1 ≠ 1 / 2 := by
    rw [mirrorMember_radial]; intro h; apply hOff; linarith
  rw [mirror_pair_captive_iff_lower h₁ hH hOff, mirror_pair_captive_iff_lower h₁ hHm hOffm,
    mirrorMember_radial]
  rcases lt_or_gt_of_ne hOff with h | h
  · exact Or.inl ⟨h, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith⟩

/-- **Rangs canoniques de la bande fine** (premier en ligne) : un rang `≥ 1` de support plus petit que le
premier est un membre bas, STRICTEMENT plus haut que le premier (à hauteur égale il le précéderait dans
l'ordre lexicographique, contre `canonicalZero_one_bottom`), de hauteur `T_n² < T₁² + 1/4`. -/
theorem canonical_small_support_band (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) (hρ : ‖zeroPoint (canonicalZero n)‖ < ‖zeroPoint (canonicalZero 1)‖) :
    rZeroRadialPosition (canonicalZero n).1 < 1 / 2 ∧
      rZeroHeight (canonicalZero 1).1 < rZeroHeight (canonicalZero n).1 ∧
      rZeroHeight (canonicalZero n).1 ^ 2 < rZeroHeight (canonicalZero 1).1 ^ 2 + 1 / 4 := by
  have hT := canonicalZero_height_mono hn
  obtain ⟨hβ, hsq⟩ := small_support_band h₁ hT hρ
  refine ⟨hβ, ?_, hsq⟩
  rcases hT.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hmem : (canonicalZero n).1 ∈ sUpperZerosBelow (canonicalZero 1).1 :=
      ⟨(canonicalZero n).2, (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mpr
        (Or.inr ⟨heq.symm, by rw [h₁]; exact hβ⟩)⟩
    rw [canonicalZero_one_bottom] at hmem
    exact hmem

/-- **Rang canonique bas captif** dès que sa hauteur dépasse celle du premier de `1/(8T₁)`. -/
theorem canonical_lower_captive_of_margin (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    {n : ℕ} (hβ : rZeroRadialPosition (canonicalZero n).1 ≤ 1 / 2)
    (hT : rZeroHeight (canonicalZero 1).1 + 1 / (8 * rZeroHeight (canonicalZero 1).1) ≤
      rZeroHeight (canonicalZero n).1) :
    InsideField (canonicalZero 1) (canonicalZero n) :=
  lower_captive_of_height_margin h₁ hβ hT

/-- Le miroir de tout rang canonique est un rang canonique. -/
theorem exists_canonical_mirror_rank (n : ℕ) :
    ∃ m : ℕ, 1 ≤ m ∧ canonicalZero m = mirrorMember (canonicalZero n) :=
  canonicalZero_surjective _

/-- **Le miroir d'un rang de la bande fine est un rang HAUT** : exclure les rangs hauts exclut la bande. -/
theorem band_rank_mirror_upper (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) (hρ : ‖zeroPoint (canonicalZero n)‖ < ‖zeroPoint (canonicalZero 1)‖) :
    ∃ m : ℕ, 1 ≤ m ∧ canonicalZero m = mirrorMember (canonicalZero n) ∧
      1 / 2 < rZeroRadialPosition (canonicalZero m).1 := by
  obtain ⟨m, hm, hmw⟩ := exists_canonical_mirror_rank n
  refine ⟨m, hm, hmw, ?_⟩
  rw [hmw, mirrorMember_radial]
  linarith [(canonical_small_support_band h₁ hn hρ).1]

/-- **Aucun rang haut ⟺ RH** : par le miroir, l'absence de membre haut est l'absence de membre hors
ligne ; réciproquement RH place chaque rang sur la ligne. -/
theorem no_upper_canonical_iff_riemannHypothesis :
    (∀ n : ℕ, 1 ≤ n → rZeroRadialPosition (canonicalZero n).1 ≤ 1 / 2) ↔ RiemannHypothesis := by
  constructor
  · intro hUp
    apply thm_riemannHypothesis_of_allUpperOnCriticalLine
    intro w
    obtain ⟨n, hn, hw⟩ := canonicalZero_surjective w
    have h1 : rZeroRadialPosition w.1 ≤ 1 / 2 := by rw [← hw]; exact hUp n hn
    obtain ⟨m, hm, hmw⟩ := canonicalZero_surjective (mirrorMember w)
    have h2 : rZeroRadialPosition (mirrorMember w).1 ≤ 1 / 2 := by rw [← hmw]; exact hUp m hm
    rw [mirrorMember_radial] at h2
    linarith
  · intro hRH n _
    exact (thm_zeroRadialPosition_half_of_riemannHypothesis hRH (canonicalZero n).1).le

/-- **Le raccord aux rangs hauts est l'absence de rang haut** : un rang haut n'est jamais dans le champ
(théorème), donc « chaque rang haut est dans le champ » dit exactement qu'il n'y en a aucun. -/
theorem upper_insideField_iff_no_upper (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    (∀ n : ℕ, 1 ≤ n → 1 / 2 < rZeroRadialPosition (canonicalZero n).1 →
        InsideField (canonicalZero 1) (canonicalZero n)) ↔
      ∀ n : ℕ, 1 ≤ n → rZeroRadialPosition (canonicalZero n).1 ≤ 1 / 2 := by
  constructor
  · intro h n hn
    by_contra hlt
    push Not at hlt
    exact upper_not_insideField h₁ hlt (h n hn hlt)
  · intro h n hn hlt
    exact ((not_lt.mpr (h n hn)) hlt).elim

/-- **Fermeture depuis les seuls rangs hauts** : premier en ligne et chaque rang haut dans son champ ⟹ RH.
Les rangs bas et la bande fine n'ont pas à être traités : la bande a pour miroir des rangs hauts. -/
theorem riemannHypothesis_of_upper_canonical_insideField
    (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (hUp : ∀ n : ℕ, 1 ≤ n → 1 / 2 < rZeroRadialPosition (canonicalZero n).1 →
      InsideField (canonicalZero 1) (canonicalZero n)) : RiemannHypothesis :=
  no_upper_canonical_iff_riemannHypothesis.mp ((upper_insideField_iff_no_upper h₁).mp hUp)

/-- **Prémisse au miroir, impliquée par la prémisse réduite** (premier en ligne) : il suffit de poser
`D_n ≤ D_1` aux rangs HAUTS, puisqu'un rang haut est hors du champ. -/
theorem gain_upper_of_restricted {m : ℕ} (xs : Fin m → ℝ)
    (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (hGainRes : ∀ n : ℕ, 1 ≤ n → ¬ InsideField (canonicalZero 1) (canonicalZero n) →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1) :
    ∀ n : ℕ, 1 ≤ n → 1 / 2 < rZeroRadialPosition (canonicalZero n).1 →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1 :=
  fun n hn hup => hGainRes n hn (upper_not_insideField h₁ hup)

/-- **Ce que la prémisse réduite demandait de plus** que la prémisse au miroir : les seuls rangs de la
bande fine (support plus petit que celui du premier, membre bas à moins de `1/(8T₁)` au-dessus). -/
theorem restricted_bites_iff (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) (n : ℕ) :
    ¬ InsideField (canonicalZero 1) (canonicalZero n) ↔
      1 / 2 < rZeroRadialPosition (canonicalZero n).1 ∨
        ‖zeroPoint (canonicalZero n)‖ < ‖zeroPoint (canonicalZero 1)‖ :=
  not_insideField_iff_upper_or_small h₁

/-- **RH implique la prémisse au miroir** : sous RH aucun rang n'est haut, la prémisse est vide. La prémisse
est donc au plus aussi forte que RH ; elle ne peut pas être fausse si RH est vraie. -/
theorem gain_upper_of_riemannHypothesis {m : ℕ} (xs : Fin m → ℝ) (hRH : RiemannHypothesis) :
    ∀ n : ℕ, 1 ≤ n → 1 / 2 < rZeroRadialPosition (canonicalZero n).1 →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1 :=
  fun n hn hup => ((not_lt.mpr (no_upper_canonical_iff_riemannHypothesis.mpr hRH n hn)) hup).elim

/-- **Composition avec la prémisse au miroir** : premier en ligne, prémisse aux rangs hauts, raccord aux
rangs hauts en hypothèse ⟹ RH. Le raccord `hLinkUp` n'est pas dérivé ; c'est une composition. -/
theorem riemannHypothesis_of_upper_gain_link {m : ℕ} (xs : Fin m → ℝ) (hm : 0 < m)
    (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (hGainUp : ∀ n : ℕ, 1 ≤ n → 1 / 2 < rZeroRadialPosition (canonicalZero n).1 →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1)
    (hLinkUp : (∀ n : ℕ, 1 ≤ n → 1 / 2 < rZeroRadialPosition (canonicalZero n).1 →
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
          collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1) →
      ∀ n : ℕ, 1 ≤ n → 1 / 2 < rZeroRadialPosition (canonicalZero n).1 →
        InsideField (canonicalZero 1) (canonicalZero n)) :
    RiemannHypothesis := by
  have _ := hm
  exact riemannHypothesis_of_upper_canonical_insideField h₁ (hLinkUp hGainUp)

/-- **Forme exacte du raccord restant** : le raccord aux rangs hauts ⟺ « sous la prémisse au miroir, aucun
rang n'est haut », c'est-à-dire : à un rang haut, `D_n ≤ D_1` est contredit par la reconstruction. -/
theorem upper_gain_link_iff_refutation {m : ℕ} (xs : Fin m → ℝ)
    (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    ((∀ n : ℕ, 1 ≤ n → 1 / 2 < rZeroRadialPosition (canonicalZero n).1 →
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
          collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1) →
      ∀ n : ℕ, 1 ≤ n → 1 / 2 < rZeroRadialPosition (canonicalZero n).1 →
        InsideField (canonicalZero 1) (canonicalZero n)) ↔
    ((∀ n : ℕ, 1 ≤ n → 1 / 2 < rZeroRadialPosition (canonicalZero n).1 →
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
          collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1) →
      ∀ n : ℕ, 1 ≤ n → ¬ 1 / 2 < rZeroRadialPosition (canonicalZero n).1) := by
  constructor
  · intro h hG n hn hup
    exact upper_not_insideField h₁ hup (h hG n hn hup)
  · intro h hG n hn hup
    exact (h hG n hn hup).elim

/-- **Sous la prémisse au miroir, à un rang haut : contrainte d'énergie et d'interaction** (identité de
section 20) : `(E_n − D_1)/2 ≤ −I_n`, et la compensation nécessaire ne dépasse pas la majoration acquise. -/
theorem upper_gain_requires_interaction {m : ℕ} (xs : Fin m → ℝ)
    (hGainUp : ∀ n : ℕ, 1 ≤ n → 1 / 2 < rZeroRadialPosition (canonicalZero n).1 →
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) n ≤
        collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1)
    {n : ℕ} (hn : 1 ≤ n) (hup : 1 / 2 < rZeroRadialPosition (canonicalZero n).1) :
    (ownEnergy (canonicalContributions xs) n -
      collectiveGain (canonicalContributions xs) (normalizedRawRemainderVector xs) 1) / 2 ≤
      - interaction (canonicalContributions xs) (normalizedRawRemainderVector xs) n :=
  (masked_gain_iff_interaction _ _ hn).mp (hGainUp n hn hup)

end MirrorReduction

#print axioms upper_not_insideField
#print axioms small_support_not_insideField
#print axioms not_insideField_iff_upper_or_small
#print axioms small_support_band
#print axioms small_support_height_lt
#print axioms lower_captive_of_height
#print axioms lower_captive_of_height_margin
#print axioms mirror_pair_captive_iff_lower
#print axioms mirror_pair_exactly_one_captive
#print axioms canonical_small_support_band
#print axioms canonical_lower_captive_of_margin
#print axioms exists_canonical_mirror_rank
#print axioms band_rank_mirror_upper
#print axioms no_upper_canonical_iff_riemannHypothesis
#print axioms upper_insideField_iff_no_upper
#print axioms riemannHypothesis_of_upper_canonical_insideField
#print axioms gain_upper_of_restricted
#print axioms restricted_bites_iff
#print axioms gain_upper_of_riemannHypothesis
#print axioms riemannHypothesis_of_upper_gain_link
#print axioms upper_gain_link_iff_refutation
#print axioms upper_gain_requires_interaction

/-! ## 22. Transmission du défaut à toute la suite (auteur, 2026-10-08, point 5 : « formaliser la transmission du
défaut à toute la suite : `r'_k = r_k − Δ`, `I'_k = I_k − ⟨Δ, c_k⟩`, `D'_k = D_k − 2⟨Δ, c_k⟩` ; respecter les indices
après insertion de deux membres distincts »).

Deux formes, toutes deux des identités algébriques sans convergence :

* **défaut du reste** : la famille `c` est inchangée, le reste est `R − Δ` ; tout reste partiel, toute interaction et
  tout gain lisent le défaut `Δ` au même rang (`partialRemainder_defect`, `interaction_defect`,
  `collectiveGain_defect`) ;
* **insertion de deux membres distincts** `d₁, d₂` aux rangs `p, p + 1` (`insertTwo`), le reste `R` étant conservé
  (il est reconstruit par les vrais membres, les membres insérés n'y figurent pas) : les rangs `< p` sont inchangés,
  les rangs `≥ p` reculent de deux et lisent le défaut `Δ = d₁ + d₂` : `r'_{k+2} = r_k − Δ`,
  `I'_{k+2} = I_k − ⟨Δ, c_k⟩`, `D'_{k+2} = D_k − 2⟨Δ, c_k⟩` (`insertTwo_partialRemainder_shift`,
  `insertTwo_interaction_shift`, `insertTwo_collectiveGain_shift`) ; le gain du premier est invariant dès `2 ≤ p`
  (`insertTwo_collectiveGain_one`) ; les gains des deux membres insérés sont calculés
  (`insertTwo_collectiveGain_first`, `insertTwo_collectiveGain_second`) et leur somme télescope
  (`insertTwo_pair_gain_sum`) ; sous la représentation ordonnée des vrais membres, le résidu de la famille insérée
  tend vers `−Δ` et non vers zéro (`insertTwo_residual_tendsto`) : le défaut de reconstruction est lu par le résidu ;
  la condition de masquage après insertion, à un rang `k ≥ p`, est exactement `D_k − D_1 ≤ 2⟨Δ, c_k⟩`
  (`insertTwo_masked_iff`).

Ces identités valent pour toute famille et tout `Δ` ; elles ne supposent rien sur la position radiale et ne
contiennent aucune borne analytique (E184 corrigée : perturbations à deux membres distincts, indices décalés). -/

section DefectTransmission

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
/-- **`r'_k = r_k − Δ`** : un défaut `Δ` du reste est transmis tel quel à tout reste partiel. -/
theorem partialRemainder_defect (c : ℕ → V) (R Δ : V) (k : ℕ) :
    partialRemainder c (R - Δ) k = partialRemainder c R k - Δ := by
  unfold partialRemainder
  abel

/-- **`I'_k = I_k − ⟨Δ, c_k⟩`**. -/
theorem interaction_defect (c : ℕ → V) (R Δ : V) (k : ℕ) :
    interaction c (R - Δ) k = interaction c R k - ⟪Δ, c k⟫_ℝ := by
  unfold interaction
  rw [partialRemainder_defect, inner_sub_left]

/-- **`D'_k = D_k − 2⟨Δ, c_k⟩`**. -/
theorem collectiveGain_defect (c : ℕ → V) (R Δ : V) (k : ℕ) :
    collectiveGain c (R - Δ) k = collectiveGain c R k - 2 * ⟪Δ, c k⟫_ℝ := by
  rw [collectiveGain_eq, collectiveGain_eq, partialRemainder_defect, inner_sub_left]
  ring

/-- **Insertion de deux membres distincts** `d₁, d₂` aux rangs `p` et `p + 1` ; les rangs `≥ p` de la famille
initiale reculent de deux. -/
noncomputable def insertTwo (c : ℕ → V) (p : ℕ) (d₁ d₂ : V) : ℕ → V := fun j =>
  if j < p then c j else if j = p then d₁ else if j = p + 1 then d₂ else c (j - 2)

omit [InnerProductSpace ℝ V] in
theorem insertTwo_lt (c : ℕ → V) (p : ℕ) (d₁ d₂ : V) {j : ℕ} (h : j < p) :
    insertTwo c p d₁ d₂ j = c j := by
  simp [insertTwo, h]

omit [InnerProductSpace ℝ V] in
theorem insertTwo_self (c : ℕ → V) (p : ℕ) (d₁ d₂ : V) : insertTwo c p d₁ d₂ p = d₁ := by
  simp [insertTwo]

omit [InnerProductSpace ℝ V] in
theorem insertTwo_succ (c : ℕ → V) (p : ℕ) (d₁ d₂ : V) : insertTwo c p d₁ d₂ (p + 1) = d₂ := by
  simp [insertTwo]

omit [InnerProductSpace ℝ V] in
/-- **Décalage des indices** : le rang `k ≥ p` de la famille initiale est le rang `k + 2` après insertion. -/
theorem insertTwo_shift (c : ℕ → V) (p : ℕ) (d₁ d₂ : V) {k : ℕ} (h : p ≤ k) :
    insertTwo c p d₁ d₂ (k + 2) = c k := by
  have h1 : ¬ k + 2 < p := by omega
  have h2 : k + 2 ≠ p := by omega
  have h3 : k + 2 ≠ p + 1 := by omega
  simp [insertTwo, h1, h2, h3]

omit [InnerProductSpace ℝ V] in
/-- Avant l'insertion (`k ≤ p`), le reste partiel est inchangé. -/
theorem insertTwo_partialRemainder_le (c : ℕ → V) (R : V) (p : ℕ) (d₁ d₂ : V) {k : ℕ} (hk : k ≤ p) :
    partialRemainder (insertTwo c p d₁ d₂) R k = partialRemainder c R k := by
  unfold partialRemainder
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  exact insertTwo_lt c p d₁ d₂ (by omega)

omit [InnerProductSpace ℝ V] in
/-- **`r'_{k+2} = r_k − Δ`**, `Δ = d₁ + d₂`, pour tout `k ≥ p ≥ 1`. -/
theorem insertTwo_partialRemainder_shift (c : ℕ → V) (R : V) {p : ℕ} (hp : 1 ≤ p) (d₁ d₂ : V)
    {k : ℕ} (hk : p ≤ k) :
    partialRemainder (insertTwo c p d₁ d₂) R (k + 2) = partialRemainder c R k - (d₁ + d₂) := by
  induction k, hk using Nat.le_induction with
  | base =>
    rw [partialRemainder_succ _ R (by omega), partialRemainder_succ _ R hp,
      insertTwo_partialRemainder_le c R p d₁ d₂ le_rfl, insertTwo_self, insertTwo_succ]
    abel
  | succ k hk ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, partialRemainder_succ _ R (by omega), ih,
      insertTwo_shift c p d₁ d₂ hk, partialRemainder_succ c R (by omega)]
    abel

/-- **`I'_{k+2} = I_k − ⟨Δ, c_k⟩`** pour `k ≥ p ≥ 1`. -/
theorem insertTwo_interaction_shift (c : ℕ → V) (R : V) {p : ℕ} (hp : 1 ≤ p) (d₁ d₂ : V)
    {k : ℕ} (hk : p ≤ k) :
    interaction (insertTwo c p d₁ d₂) R (k + 2) = interaction c R k - ⟪d₁ + d₂, c k⟫_ℝ := by
  unfold interaction
  rw [show k + 2 + 1 = (k + 1) + 2 by ring, insertTwo_partialRemainder_shift c R hp d₁ d₂ (by omega),
    insertTwo_shift c p d₁ d₂ hk, inner_sub_left]

/-- **`D'_{k+2} = D_k − 2⟨Δ, c_k⟩`** pour `k ≥ p ≥ 1`. -/
theorem insertTwo_collectiveGain_shift (c : ℕ → V) (R : V) {p : ℕ} (hp : 1 ≤ p) (d₁ d₂ : V)
    {k : ℕ} (hk : p ≤ k) :
    collectiveGain (insertTwo c p d₁ d₂) R (k + 2) =
      collectiveGain c R k - 2 * ⟪d₁ + d₂, c k⟫_ℝ := by
  rw [collectiveGain_eq, collectiveGain_eq, insertTwo_partialRemainder_shift c R hp d₁ d₂ hk,
    insertTwo_shift c p d₁ d₂ hk, inner_sub_left]
  ring

omit [InnerProductSpace ℝ V] in
/-- Les rangs `k < p` gardent leur gain. -/
theorem insertTwo_collectiveGain_lt (c : ℕ → V) (R : V) (p : ℕ) (d₁ d₂ : V) {k : ℕ} (hk : k < p) :
    collectiveGain (insertTwo c p d₁ d₂) R k = collectiveGain c R k := by
  unfold collectiveGain
  rw [insertTwo_partialRemainder_le c R p d₁ d₂ hk.le, insertTwo_lt c p d₁ d₂ hk]

/-- Les rangs `k` avec `k + 1 ≤ p` gardent leur interaction. -/
theorem insertTwo_interaction_lt (c : ℕ → V) (R : V) (p : ℕ) (d₁ d₂ : V) {k : ℕ} (hk : k + 1 ≤ p) :
    interaction (insertTwo c p d₁ d₂) R k = interaction c R k := by
  unfold interaction
  rw [insertTwo_partialRemainder_le c R p d₁ d₂ hk, insertTwo_lt c p d₁ d₂ (by omega)]

omit [InnerProductSpace ℝ V] in
/-- **Le gain du premier est invariant** par toute insertion après lui (`2 ≤ p`). -/
theorem insertTwo_collectiveGain_one (c : ℕ → V) (R : V) {p : ℕ} (hp : 2 ≤ p) (d₁ d₂ : V) :
    collectiveGain (insertTwo c p d₁ d₂) R 1 = collectiveGain c R 1 :=
  insertTwo_collectiveGain_lt c R p d₁ d₂ (by omega)

/-- Gain du premier membre inséré : `D'_p = 2⟨r_{p−1}, d₁⟩ − ‖d₁‖²`. -/
theorem insertTwo_collectiveGain_first (c : ℕ → V) (R : V) (p : ℕ) (d₁ d₂ : V) :
    collectiveGain (insertTwo c p d₁ d₂) R p = 2 * ⟪partialRemainder c R p, d₁⟫_ℝ - ‖d₁‖ ^ 2 := by
  rw [collectiveGain_eq, insertTwo_partialRemainder_le c R p d₁ d₂ le_rfl, insertTwo_self]

/-- Gain du second membre inséré : `D'_{p+1} = 2⟨r_{p−1} − d₁, d₂⟩ − ‖d₂‖²` (`1 ≤ p`). -/
theorem insertTwo_collectiveGain_second (c : ℕ → V) (R : V) {p : ℕ} (hp : 1 ≤ p) (d₁ d₂ : V) :
    collectiveGain (insertTwo c p d₁ d₂) R (p + 1) =
      2 * ⟪partialRemainder c R p - d₁, d₂⟫_ℝ - ‖d₂‖ ^ 2 := by
  rw [collectiveGain_eq, partialRemainder_succ _ R hp, insertTwo_partialRemainder_le c R p d₁ d₂ le_rfl,
    insertTwo_self, insertTwo_succ]

omit [InnerProductSpace ℝ V] in
/-- **Les deux gains insérés télescopent** : `D'_p + D'_{p+1} = ‖r_{p−1}‖² − ‖r_{p−1} − Δ‖²` (`1 ≤ p`). -/
theorem insertTwo_pair_gain_sum (c : ℕ → V) (R : V) {p : ℕ} (hp : 1 ≤ p) (d₁ d₂ : V) :
    collectiveGain (insertTwo c p d₁ d₂) R p + collectiveGain (insertTwo c p d₁ d₂) R (p + 1) =
      ‖partialRemainder c R p‖ ^ 2 - ‖partialRemainder c R p - (d₁ + d₂)‖ ^ 2 := by
  rw [collectiveGain_eq_energy_drop _ R hp, collectiveGain_eq_energy_drop _ R (by omega),
    insertTwo_partialRemainder_le c R p d₁ d₂ le_rfl,
    show p + 1 + 1 = p + 2 by ring, insertTwo_partialRemainder_shift c R hp d₁ d₂ le_rfl]
  ring

omit [InnerProductSpace ℝ V] in
/-- **Le défaut de reconstruction est lu par le résidu** : sous la représentation ordonnée des vrais membres
(`Σ_{j≤N} c_j → R`), le résidu de la famille insérée tend vers `−Δ`, non vers zéro. -/
theorem insertTwo_residual_tendsto {c : ℕ → V} {R : V}
    (hRep : Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, c (j + 1)) Filter.atTop (nhds R))
    {p : ℕ} (hp : 1 ≤ p) (d₁ d₂ : V) :
    Filter.Tendsto (fun N => partialRemainder (insertTwo c p d₁ d₂) R (N + 3)) Filter.atTop
      (nhds (-(d₁ + d₂))) := by
  have h0 := partialRemainder_tendsto_zero hRep
  have h1 : Filter.Tendsto (fun N => partialRemainder c R (N + 1) - (d₁ + d₂)) Filter.atTop
      (nhds (0 - (d₁ + d₂))) := h0.sub tendsto_const_nhds
  rw [zero_sub] at h1
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop p] with N hN
  rw [show N + 3 = (N + 1) + 2 by ring, insertTwo_partialRemainder_shift c R hp d₁ d₂ (by omega)]

/-- **Masquage après insertion** (`2 ≤ p ≤ k`) : `D'_{k+2} ≤ D'_1 ⟺ D_k − D_1 ≤ 2⟨Δ, c_k⟩`. La condition de
masquage d'un rang ultérieur lit exactement le défaut `Δ` projeté sur sa contribution. -/
theorem insertTwo_masked_iff (c : ℕ → V) (R : V) {p : ℕ} (hp : 2 ≤ p) (d₁ d₂ : V) {k : ℕ} (hk : p ≤ k) :
    collectiveGain (insertTwo c p d₁ d₂) R (k + 2) ≤ collectiveGain (insertTwo c p d₁ d₂) R 1 ↔
      collectiveGain c R k - collectiveGain c R 1 ≤ 2 * ⟪d₁ + d₂, c k⟫_ℝ := by
  rw [insertTwo_collectiveGain_shift c R (by omega) d₁ d₂ hk, insertTwo_collectiveGain_one c R hp]
  constructor <;> intro h <;> linarith

end DefectTransmission

#print axioms partialRemainder_defect
#print axioms interaction_defect
#print axioms collectiveGain_defect
#print axioms insertTwo_shift
#print axioms insertTwo_partialRemainder_shift
#print axioms insertTwo_interaction_shift
#print axioms insertTwo_collectiveGain_shift
#print axioms insertTwo_collectiveGain_one
#print axioms insertTwo_collectiveGain_first
#print axioms insertTwo_collectiveGain_second
#print axioms insertTwo_pair_gain_sum
#print axioms insertTwo_residual_tendsto
#print axioms insertTwo_masked_iff

end RHV6Fresh
