/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GapTranslationInvariance
import RHV6Fresh.Terminal.PairCurvature
import RHV6Fresh.Terminal.FirstGainPremise

/-!
# Courbure collective d'une paire miroir et observable des premiers (texte de l'auteur, 2026-10-19)

Trois niveaux, séparés comme le demande le texte :

* **géométrique** (démontré) : une translation `h` multiplie l'amplitude projetée d'un mode par `e^{(β−1/2)h}`
  (`GapTranslationInvariance`) ; pour une **paire miroir** `β = 1/2 ± δ` les deux rapports ont un produit `1`, ce qui
  n'est pas une contradiction mais impose d'étudier la paire COLLECTIVEMENT : `e^{−δu}e^{iTu} + e^{δu}e^{iTu} =
  2cosh(δu)e^{iTu}` (`mirrorMode_add`), enveloppe de courbure `δ²cosh(δu) > 0` ;
* **spectral** (relation analytique) : les contributions des zéros reconstruisent la courbe des premiers
  (`smoothedRemainder_eq_tsum_residueTerm`) ; la projection d'une somme FINIE est la somme des projections ;
* **arithmétique** (NON démontré) : les écarts exacts imposent une amplitude constante à chaque composante.

Objet remplacé (§4 du texte) : au lieu de demander `|P_{a+h}| ≥ |P_a|` sur un mode (faux sous OFF), on écrit l'observable
collective `Q(a, T)` depuis le reste des premiers seuls, et le **test décisif** (§5) : la différence seconde
`𝒞(a, h, T) = Q(a+h) − 2Q(a) + Q(a−h)`. Pour la paire miroir isolée à sa fréquence, la différence seconde vaut
`2(cosh(δh) − 1)·(A_δ(a) + A_{−δ}(a)) ≥ 0`, nulle ⟺ `δ = 0`. Les autres fréquences contribuent aussi à `𝒞` ;
rien ici ne suppose `𝒞 = 0`. Plancher grammatical : sur un écart de classe `c`, `2(cosh(δL_r) − 1) ≥
(δ log(1 + plancher(c)/p_r))²`.
-/

namespace RHV6Fresh

open scoped BigOperators
open RHV3Lean MeasureTheory

/-! ## §1 Différence seconde et paire miroir -/

/-- Différence seconde d'une fonction réelle au pas `h`. -/
def secondDifference (f : ℝ → ℝ) (a h : ℝ) : ℝ := f (a + h) - 2 * f a + f (a - h)

/-- Mode collectif d'une paire miroir de profondeur `d` à la fréquence `T`. -/
noncomputable def pairMode (d T u : ℝ) : ℂ := complexMode d T u + complexMode (-d) T u

/-- Enveloppe collective `2cosh(du)` : la paire OFF n'a pas d'enveloppe constante. -/
theorem pairMode_eq_cosh (d T u : ℝ) :
    pairMode d T u = 2 * (Real.cosh (d * u) : ℂ) * complexMode 0 T u :=
  mirrorMode_add d T u

/-- Module de la paire : `2cosh(du)`. -/
theorem pairMode_norm (d T u : ℝ) : ‖pairMode d T u‖ = 2 * Real.cosh (d * u) := by
  rw [pairMode_eq_cosh, norm_mul, norm_mul, complexMode_norm, zero_mul, Real.exp_zero, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (by linarith [Real.one_le_cosh (d * u)])]
  norm_num

/-- Courbure de l'enveloppe : `cosh(δ(a+h)) − 2cosh(δa) + cosh(δ(a−h)) = 2cosh(δa)(cosh(δh) − 1)`. -/
theorem cosh_secondDifference (δ a h : ℝ) :
    secondDifference (fun u => Real.cosh (δ * u)) a h = 2 * Real.cosh (δ * a) * (Real.cosh (δ * h) - 1) := by
  unfold secondDifference
  simp only [mul_add, mul_sub, Real.cosh_add, Real.cosh_sub]
  ring

/-- Amplitude fenêtrée de la paire à sa propre fréquence. -/
noncomputable def pairAmplitudeWindow (d a L : ℝ) : ℝ := windowAmplitude d a L + windowAmplitude (-d) a L

theorem pairAmplitudeWindow_pos (d a : ℝ) {L : ℝ} (hL : 0 < L) : 0 < pairAmplitudeWindow d a L :=
  add_pos (windowAmplitude_pos d a hL) (windowAmplitude_pos (-d) a hL)

theorem pairMode_filter_intervalIntegrable (d T a L T' : ℝ) :
    IntervalIntegrable (fun u => pairMode d T u * Complex.exp (-((T' : ℂ) * Complex.I * (u : ℂ))))
      volume a (a + L) := by
  apply Continuous.intervalIntegrable
  unfold pairMode complexMode
  apply Continuous.mul
  · apply Continuous.add
    · exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    · exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  · exact Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul Complex.continuous_ofReal))

theorem complexMode_filter_intervalIntegrable (d T a L T' : ℝ) :
    IntervalIntegrable (fun u => complexMode d T u * Complex.exp (-((T' : ℂ) * Complex.I * (u : ℂ))))
      volume a (a + L) := by
  apply Continuous.intervalIntegrable
  unfold complexMode
  apply Continuous.mul
  · exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  · exact Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul Complex.continuous_ofReal))

/-- Projection de la paire à sa propre fréquence : réelle, `A_d(a) + A_{−d}(a)`. -/
theorem windowProjection_pairMode (d T a L : ℝ) :
    windowProjection (pairMode d T) a L T = (pairAmplitudeWindow d a L : ℂ) := by
  have h := windowProjection_add (complexMode d T) (complexMode (-d) T) a L T
    (complexMode_filter_intervalIntegrable d T a L T) (complexMode_filter_intervalIntegrable (-d) T a L T)
  unfold pairMode pairAmplitudeWindow
  rw [h, windowProjection_mode, windowProjection_mode]
  push_cast; ring

/-- **Différence seconde de la paire à sa fréquence** : `2(cosh(dh) − 1)·(A_d(a) + A_{−d}(a))`. -/
theorem pairAmplitudeWindow_secondDifference (d a L h : ℝ) :
    secondDifference (fun a => pairAmplitudeWindow d a L) a h =
      2 * (Real.cosh (d * h) - 1) * pairAmplitudeWindow d a L := by
  simp only [secondDifference, pairAmplitudeWindow]
  have h1 := windowAmplitude_translate d a L h
  have h2 := windowAmplitude_translate (-d) a L h
  have h3 : windowAmplitude d (a - h) L = Real.exp (d * -h) * windowAmplitude d a L := by
    rw [sub_eq_add_neg]; exact windowAmplitude_translate d a L (-h)
  have h4 : windowAmplitude (-d) (a - h) L = Real.exp (-d * -h) * windowAmplitude (-d) a L := by
    rw [sub_eq_add_neg]; exact windowAmplitude_translate (-d) a L (-h)
  rw [h1, h2, h3, h4, Real.cosh_eq]
  simp only [neg_mul, mul_neg, neg_neg]
  ring

/-- La courbure collective de la paire est positive. -/
theorem pair_curvature_nonneg (d a L h : ℝ) (hL : 0 < L) :
    0 ≤ secondDifference (fun a => pairAmplitudeWindow d a L) a h := by
  rw [pairAmplitudeWindow_secondDifference]
  have := Real.one_le_cosh (d * h)
  have := pairAmplitudeWindow_pos d a hL
  positivity

/-- **Courbure nulle ⟺ profondeur nulle** (fenêtre non dégénérée, pas `h ≠ 0`). -/
theorem pair_curvature_eq_zero_iff (d a : ℝ) {L h : ℝ} (hL : 0 < L) (hh : h ≠ 0) :
    secondDifference (fun a => pairAmplitudeWindow d a L) a h = 0 ↔ d = 0 := by
  rw [pairAmplitudeWindow_secondDifference]
  have hA := pairAmplitudeWindow_pos d a hL
  constructor
  · intro h0
    have hc : Real.cosh (d * h) - 1 = 0 := by
      rcases mul_eq_zero.mp h0 with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · norm_num at h2
        · exact h2
      · exact absurd h1 hA.ne'
    by_contra hd
    have : 1 < Real.cosh (d * h) := Real.one_lt_cosh.mpr (mul_ne_zero hd hh)
    linarith
  · rintro rfl; simp

/-- Plancher quadratique : `2(cosh(dh) − 1) ≥ (dh)²` (depuis `radialCurvature_ge_sq` au réel `e^h`). -/
theorem two_cosh_sub_one_ge_sq (d h : ℝ) : (d * h) ^ 2 ≤ 2 * (Real.cosh (d * h) - 1) := by
  have := radialCurvature_ge_sq (Real.exp h) d
  unfold radialCurvature at this
  rwa [Real.log_exp] at this

/-! ## §2 Paire miroir d'un vrai zéro -/

/-- Mode collectif d'un vrai zéro et de son miroir (même hauteur, profondeurs opposées). -/
noncomputable def zeroPairMode (z : TrueZero) (u : ℝ) : ℂ := zeroMode z u + zeroMode (mirrorMember z) u

theorem zeroPairMode_eq (z : TrueZero) (u : ℝ) :
    zeroPairMode z u = pairMode (rZeroRadialPosition z.1 - 1 / 2) (rZeroHeight z.1) u := by
  unfold zeroPairMode pairMode zeroMode
  rw [mirrorMember_radial, mirrorMember_ordinate]
  congr 2; ring

/-- Projection de la paire d'un vrai zéro à sa fréquence. -/
theorem zeroPairMode_windowProjection (z : TrueZero) (a L : ℝ) :
    windowProjection (zeroPairMode z) a L (rZeroHeight z.1) =
      (pairAmplitudeWindow (rZeroRadialPosition z.1 - 1 / 2) a L : ℂ) := by
  have : zeroPairMode z = pairMode (rZeroRadialPosition z.1 - 1 / 2) (rZeroHeight z.1) :=
    funext (zeroPairMode_eq z)
  rw [this, windowProjection_pairMode]

/-- **Signature de courbure d'un vrai zéro** : la différence seconde de la projection de sa paire, à sa fréquence,
est nulle sur une fenêtre non dégénérée et un pas non nul ⟺ le zéro est sur la ligne (caractérisation). -/
theorem zero_pair_curvature_eq_zero_iff (z : TrueZero) (a : ℝ) {L h : ℝ} (hL : 0 < L) (hh : h ≠ 0) :
    secondDifference (fun a => ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖) a h = 0 ↔
      rZeroRadialPosition z.1 = 1 / 2 := by
  have hn : ∀ a, ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖ =
      pairAmplitudeWindow (rZeroRadialPosition z.1 - 1 / 2) a L := by
    intro a
    rw [zeroPairMode_windowProjection, Complex.norm_real,
      Real.norm_of_nonneg (pairAmplitudeWindow_pos _ a hL).le]
  simp_rw [hn]
  rw [pair_curvature_eq_zero_iff _ a hL hh, sub_eq_zero]

/-- Sous un demi, la courbure de la paire est strictement positive sur tout écart premier. -/
theorem low_zero_pair_curvature_pos (z : TrueZero) (hz : rZeroRadialPosition z.1 < 1 / 2) (r : ℕ) (a : ℝ)
    {L : ℝ} (hL : 0 < L) :
    0 < secondDifference (fun a => ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖) a
      (rPrimeGapLogRatio r) := by
  have hne : rPrimeGapLogRatio r ≠ 0 := (thm_primeGapLogRatio_pos r).ne'
  rcases (pair_curvature_nonneg (rZeroRadialPosition z.1 - 1 / 2) a L (rPrimeGapLogRatio r) hL).lt_or_eq
    with h | h
  · have hn : ∀ a, ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖ =
        pairAmplitudeWindow (rZeroRadialPosition z.1 - 1 / 2) a L := by
      intro a
      rw [zeroPairMode_windowProjection, Complex.norm_real,
        Real.norm_of_nonneg (pairAmplitudeWindow_pos _ a hL).le]
    simp_rw [hn]; exact h
  · exfalso
    have := (pair_curvature_eq_zero_iff (rZeroRadialPosition z.1 - 1 / 2) a hL hne).mp h.symm
    linarith

/-! ## §3 Plancher grammatical de la signature par classe de transition -/

/-- **Plancher grammatical de la courbure** : sur l'écart de rang `r` (`p_r > 3`), de classe `eventClass r`
(maintien `0`, changements `2` ou `4`), la signature `2(cosh(δL_r) − 1)` est minorée par
`(δ·log(1 + plancher(classe)/p_r))²`. La grammaire exacte (classe, taille) entre ici par la translation. -/
theorem pair_curvature_gap_floor (d : ℝ) (r : ℕ) (h3 : 3 < fnPrimeAtRank r) :
    (d * Real.log (1 + (classFloor (eventClass r) : ℝ) / (fnPrimeAtRank r : ℝ))) ^ 2 ≤
      2 * (Real.cosh (d * rPrimeGapLogRatio r) - 1) := by
  have hfloor := primeGapLogRatio_ge_classFloor r h3
  have hpos : 0 ≤ Real.log (1 + (classFloor (eventClass r) : ℝ) / (fnPrimeAtRank r : ℝ)) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ (classFloor (eventClass r) : ℝ) / (fnPrimeAtRank r : ℝ) := by positivity
    linarith
  calc (d * Real.log (1 + (classFloor (eventClass r) : ℝ) / (fnPrimeAtRank r : ℝ))) ^ 2
      = d ^ 2 * Real.log (1 + (classFloor (eventClass r) : ℝ) / (fnPrimeAtRank r : ℝ)) ^ 2 := by ring
    _ ≤ d ^ 2 * rPrimeGapLogRatio r ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg d)
        exact pow_le_pow_left₀ hpos hfloor 2
    _ = (d * rPrimeGapLogRatio r) ^ 2 := by ring
    _ ≤ 2 * (Real.cosh (d * rPrimeGapLogRatio r) - 1) := two_cosh_sub_one_ge_sq d _

/-- Différence seconde de la paire d'un zéro sur l'écart de rang `r`, minorée par le plancher grammatical fois
l'amplitude de la paire (identité géométrique + grammaire, toute position radiale). -/
theorem zero_pair_curvature_gap_floor (z : TrueZero) (r : ℕ) (h3 : 3 < fnPrimeAtRank r) (a : ℝ) {L : ℝ}
    (hL : 0 < L) :
    ((rZeroRadialPosition z.1 - 1 / 2) *
        Real.log (1 + (classFloor (eventClass r) : ℝ) / (fnPrimeAtRank r : ℝ))) ^ 2 *
      pairAmplitudeWindow (rZeroRadialPosition z.1 - 1 / 2) a L ≤
    secondDifference (fun a => pairAmplitudeWindow (rZeroRadialPosition z.1 - 1 / 2) a L) a
      (rPrimeGapLogRatio r) := by
  rw [pairAmplitudeWindow_secondDifference]
  exact mul_le_mul_of_nonneg_right (pair_curvature_gap_floor _ r h3) (pairAmplitudeWindow_pos _ a hL).le

/-! ## §4 Observable collective côté premiers et décomposition finie exacte -/

/-- **Observable collective** `Q(a, L, T)` : projection fenêtrée du reste lissé des premiers normalisé par `√x`,
`u = log x`. Écrite depuis les premiers seuls (aucun zéro dans l'énoncé). -/
noncomputable def collectiveProjection (a L T : ℝ) : ℂ :=
  windowProjection (fun u => (smoothedRemainder (Real.exp u) / (Real.exp (u / 2) : ℂ))) a L T

/-- **Test décisif** (§5 du texte) : différence seconde de l'observable collective au pas `h`. Entièrement déterminée
par les premiers ; rien ne suppose qu'elle est nulle. -/
noncomputable def collectiveCurvature (a L h T : ℝ) : ℂ :=
  collectiveProjection (a + h) L T - 2 * collectiveProjection a L T + collectiveProjection (a - h) L T

/-- Complément d'une famille finie de vrais zéros dans le signal normalisé des premiers. -/
noncomputable def collectiveComplement (s : Finset TrueZero) (u : ℝ) : ℂ :=
  (smoothedRemainder (Real.exp u) / (Real.exp (u / 2) : ℂ)) - ∑ z ∈ s, zeroMode z u

/-- **Décomposition finie exacte** : `Q = Σ_{z ∈ s} P(mode z) + P(complément)` dès que le signal des premiers filtré est
intégrable sur la fenêtre (identité, aucun échange avec la somme infinie, aucune borne du complément). -/
theorem collectiveProjection_finite_split (s : Finset TrueZero) (a L T : ℝ)
    (hInt : IntervalIntegrable (fun u => (smoothedRemainder (Real.exp u) / (Real.exp (u / 2) : ℂ)) *
      Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ)))) volume a (a + L)) :
    collectiveProjection a L T =
      ∑ z ∈ s, windowProjection (zeroMode z) a L T + windowProjection (collectiveComplement s) a L T := by
  have hsum : IntervalIntegrable (fun u => (∑ z ∈ s, zeroMode z u) *
      Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ)))) volume a (a + L) := by
    have hsum0 := IntervalIntegrable.sum s fun z _ => zeroMode_filter_intervalIntegrable z a L T
    have heq : (∑ i ∈ s, fun u => zeroMode i u * Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ)))) =
        fun u => (∑ i ∈ s, zeroMode i u) * Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ))) := by
      funext u; simp [Finset.sum_apply, Finset.sum_mul]
    rw [heq] at hsum0; exact hsum0
  have hcomp : IntervalIntegrable (fun u => collectiveComplement s u *
      Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ)))) volume a (a + L) := by
    unfold collectiveComplement
    simp_rw [sub_mul]
    exact hInt.sub hsum
  have h := windowProjection_add (fun u => ∑ z ∈ s, zeroMode z u) (collectiveComplement s) a L T hsum hcomp
  rw [← windowProjection_finset_sum, ← h]
  unfold collectiveProjection collectiveComplement
  congr 1; funext u; ring

open Classical in
/-- La courbure collective se découpe de même : paire du zéro + courbure du reste (identité). -/
theorem collectiveCurvature_split_pair (z : TrueZero) (a L h T : ℝ)
    (hInt : ∀ a : ℝ, IntervalIntegrable (fun u => (smoothedRemainder (Real.exp u) / (Real.exp (u / 2) : ℂ)) *
      Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ)))) volume a (a + L))
    (hz : mirrorMember z ≠ z) :
    collectiveCurvature a L h T =
      (windowProjection (zeroPairMode z) (a + h) L T - 2 * windowProjection (zeroPairMode z) a L T +
        windowProjection (zeroPairMode z) (a - h) L T) +
      (windowProjection (collectiveComplement {z, mirrorMember z}) (a + h) L T -
        2 * windowProjection (collectiveComplement {z, mirrorMember z}) a L T +
        windowProjection (collectiveComplement {z, mirrorMember z}) (a - h) L T) := by
  have hpair : ∀ a, windowProjection (zeroPairMode z) a L T =
      ∑ w ∈ ({z, mirrorMember z} : Finset TrueZero), windowProjection (zeroMode w) a L T := by
    intro a
    rw [← windowProjection_finset_sum]
    congr 1; funext u
    rw [Finset.sum_pair hz.symm]
    rfl
  unfold collectiveCurvature
  rw [collectiveProjection_finite_split {z, mirrorMember z} (a + h) L T (hInt _),
    collectiveProjection_finite_split {z, mirrorMember z} a L T (hInt _),
    collectiveProjection_finite_split {z, mirrorMember z} (a - h) L T (hInt _), hpair, hpair, hpair]
  ring

/-! ## §5 Forme fermante (courbure de la paire du zéro atteint) -/

/-- **Forme fermante minimale par la courbure** : si, pour UNE fenêtre non dégénérée et UN écart premier, la différence
seconde de la projection de la paire du zéro atteint, à sa fréquence, est nulle, alors `False` sous un demi.
Son antécédent n'est déduit d'aucun fait des premiers ; quantifié sur tous les zéros il a la force de RH. -/
theorem pair_curvature_closes (z : TrueZero) (hz : rZeroRadialPosition z.1 < 1 / 2) :
    (∃ (r : ℕ) (a L : ℝ), 0 < L ∧
      secondDifference (fun a => ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖) a
        (rPrimeGapLogRatio r) = 0) → False := by
  rintro ⟨r, a, L, hL, h0⟩
  exact absurd h0 (low_zero_pair_curvature_pos z hz r a hL).ne'

/-! ## §6 Schéma « grammaire ⟹ B_G, OFF ⟹ ¬B_G » (fermeture proposée en 30 lignes, 2026-10-19) -/

/-- Amplitude fenêtrée d'un mode à partir de la fenêtre en `0` : `A_d(a) = e^{da} A_d(0)`. -/
theorem windowAmplitude_from_zero (d a L : ℝ) :
    windowAmplitude d a L = Real.exp (d * a) * windowAmplitude d 0 L := by
  have := windowAmplitude_translate d 0 L a
  rwa [zero_add] at this

/-- **OFF ⟹ ¬B_G (côté analytique, démontré)** : sous un demi, la différence seconde de la paire du zéro, à sa
fréquence, au pas d'un écart premier, n'est bornée par aucune constante le long des translations `a`. -/
theorem off_pair_curvature_unbounded (z : TrueZero) (hz : rZeroRadialPosition z.1 < 1 / 2) (r : ℕ) {L : ℝ}
    (hL : 0 < L) (K : ℝ) :
    ∃ a : ℝ, K < secondDifference
      (fun a => ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖) a (rPrimeGapLogRatio r) := by
  set d := rZeroRadialPosition z.1 - 1 / 2 with hd
  have hδ : 0 < -d := by rw [hd]; linarith
  have hn : ∀ a, ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖ = pairAmplitudeWindow d a L := by
    intro a
    rw [zeroPairMode_windowProjection, Complex.norm_real, Real.norm_of_nonneg (pairAmplitudeWindow_pos _ a hL).le]
  simp_rw [hn, pairAmplitudeWindow_secondDifference]
  set c := 2 * (Real.cosh (d * rPrimeGapLogRatio r) - 1) with hc
  have hcpos : 0 < c := by
    rw [hc]
    have : 1 < Real.cosh (d * rPrimeGapLogRatio r) :=
      Real.one_lt_cosh.mpr (mul_ne_zero (by linarith) (thm_primeGapLogRatio_pos r).ne')
    linarith
  set w := windowAmplitude (-d) 0 L with hw
  have hwpos : 0 < w := windowAmplitude_pos (-d) 0 hL
  -- choisir `a` avec `e^{(−d) a} > K / (c w)`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, K / (c * w) < Real.exp ((-d) * a) := by
    refine ⟨(Real.log (max (K / (c * w)) 1) + 1) / (-d), ?_⟩
    rw [mul_div_cancel₀ _ hδ.ne']
    calc K / (c * w) ≤ max (K / (c * w)) 1 := le_max_left _ _
      _ = Real.exp (Real.log (max (K / (c * w)) 1)) := (Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))).symm
      _ < Real.exp (Real.log (max (K / (c * w)) 1) + 1) := Real.exp_lt_exp.mpr (by linarith)
  refine ⟨a, ?_⟩
  have hmul : K < c * (Real.exp ((-d) * a) * w) := by
    have := (div_lt_iff₀ (mul_pos hcpos hwpos)).mp ha
    linarith [mul_comm (c * w) (Real.exp ((-d) * a))]
  have hA : Real.exp ((-d) * a) * w ≤ pairAmplitudeWindow d a L := by
    unfold pairAmplitudeWindow
    rw [windowAmplitude_from_zero (-d) a L]
    linarith [windowAmplitude_pos d a hL]
  calc K < c * (Real.exp ((-d) * a) * w) := hmul
    _ ≤ c * pairAmplitudeWindow d a L := mul_le_mul_of_nonneg_left hA hcpos.le

/-- Forme « deux lemmes » sur la paire seule : toute borne `B_G` de la courbure de la paire le long des translations
(lemme arithmétique à découvrir) est contredite sous un demi (lemme analytique, démontré). -/
theorem pair_curvature_bound_closes (z : TrueZero) (hz : rZeroRadialPosition z.1 < 1 / 2) (r : ℕ) {L : ℝ}
    (hL : 0 < L)
    (hBound : ∃ K : ℝ, ∀ a : ℝ, secondDifference
      (fun a => ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖) a (rPrimeGapLogRatio r) ≤ K) :
    False := by
  obtain ⟨K, hK⟩ := hBound
  obtain ⟨a, ha⟩ := off_pair_curvature_unbounded z hz r hL K
  exact absurd (hK a) (not_le.mpr ha)

open Classical in
/-- **Schéma collectif** : si la courbure COLLECTIVE des premiers (observable `𝒞`, premiers seuls) ET la courbure du
complément de la paire sont bornées le long des translations, à la fréquence du zéro et au pas d'un écart premier,
alors `False` sous un demi. La première borne est le lemme arithmétique `B_G` à découvrir ; la seconde est la borne du
complément (ligne 25 du texte) ; aucune des deux n'est démontrée ici. -/
theorem collective_curvature_two_lemma_closes (z : TrueZero) (hz : rZeroRadialPosition z.1 < 1 / 2) (r : ℕ)
    {L : ℝ} (hL : 0 < L)
    (hInt : ∀ a : ℝ, IntervalIntegrable (fun u => (smoothedRemainder (Real.exp u) / (Real.exp (u / 2) : ℂ)) *
      Complex.exp (-((rZeroHeight z.1 : ℂ) * Complex.I * (u : ℂ)))) volume a (a + L))
    (hCollective : ∃ K : ℝ, ∀ a : ℝ, ‖collectiveCurvature a L (rPrimeGapLogRatio r) (rZeroHeight z.1)‖ ≤ K)
    (hRest : ∃ K : ℝ, ∀ a : ℝ,
      ‖windowProjection (collectiveComplement {z, mirrorMember z}) (a + rPrimeGapLogRatio r) L (rZeroHeight z.1) -
        2 * windowProjection (collectiveComplement {z, mirrorMember z}) a L (rZeroHeight z.1) +
        windowProjection (collectiveComplement {z, mirrorMember z}) (a - rPrimeGapLogRatio r) L (rZeroHeight z.1)‖
        ≤ K) : False := by
  obtain ⟨K₁, hK₁⟩ := hCollective
  obtain ⟨K₂, hK₂⟩ := hRest
  refine pair_curvature_bound_closes z hz r hL ⟨K₁ + K₂, fun a => ?_⟩
  have hsplit := collectiveCurvature_split_pair z a L (rPrimeGapLogRatio r) (rZeroHeight z.1) hInt
    (mirrorMember_ne hz)
  have hn : ∀ a, ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖ =
      pairAmplitudeWindow (rZeroRadialPosition z.1 - 1 / 2) a L := by
    intro a
    rw [zeroPairMode_windowProjection, Complex.norm_real, Real.norm_of_nonneg (pairAmplitudeWindow_pos _ a hL).le]
  have hreal : ∀ a, windowProjection (zeroPairMode z) a L (rZeroHeight z.1) =
      ((pairAmplitudeWindow (rZeroRadialPosition z.1 - 1 / 2) a L : ℝ) : ℂ) := fun a => zeroPairMode_windowProjection z a L
  simp only [secondDifference, hn]
  have hpairC : windowProjection (zeroPairMode z) (a + rPrimeGapLogRatio r) L (rZeroHeight z.1) -
      2 * windowProjection (zeroPairMode z) a L (rZeroHeight z.1) +
      windowProjection (zeroPairMode z) (a - rPrimeGapLogRatio r) L (rZeroHeight z.1) =
      ((pairAmplitudeWindow (rZeroRadialPosition z.1 - 1 / 2) (a + rPrimeGapLogRatio r) L -
        2 * pairAmplitudeWindow (rZeroRadialPosition z.1 - 1 / 2) a L +
        pairAmplitudeWindow (rZeroRadialPosition z.1 - 1 / 2) (a - rPrimeGapLogRatio r) L : ℝ) : ℂ) := by
    rw [hreal, hreal, hreal]; push_cast; ring
  have hle : ‖windowProjection (zeroPairMode z) (a + rPrimeGapLogRatio r) L (rZeroHeight z.1) -
      2 * windowProjection (zeroPairMode z) a L (rZeroHeight z.1) +
      windowProjection (zeroPairMode z) (a - rPrimeGapLogRatio r) L (rZeroHeight z.1)‖ ≤ K₁ + K₂ := by
    have h1 := hK₁ a
    have h2 := hK₂ a
    have heq : windowProjection (zeroPairMode z) (a + rPrimeGapLogRatio r) L (rZeroHeight z.1) -
        2 * windowProjection (zeroPairMode z) a L (rZeroHeight z.1) +
        windowProjection (zeroPairMode z) (a - rPrimeGapLogRatio r) L (rZeroHeight z.1) =
        collectiveCurvature a L (rPrimeGapLogRatio r) (rZeroHeight z.1) -
        (windowProjection (collectiveComplement {z, mirrorMember z}) (a + rPrimeGapLogRatio r) L (rZeroHeight z.1) -
          2 * windowProjection (collectiveComplement {z, mirrorMember z}) a L (rZeroHeight z.1) +
          windowProjection (collectiveComplement {z, mirrorMember z}) (a - rPrimeGapLogRatio r) L
            (rZeroHeight z.1)) := by
      rw [hsplit]; ring
    rw [heq]
    exact le_trans (norm_sub_le _ _) (add_le_add h1 h2)
  rw [hpairC, Complex.norm_real] at hle
  exact le_trans (le_abs_self _) hle

end RHV6Fresh
