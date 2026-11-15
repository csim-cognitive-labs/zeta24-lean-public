/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.InversePrimeSpectral
import RHV6Fresh.Terminal.HarmonicRestoringLaw
import RHV6Fresh.Terminal.FirstGainPremise
import RHV6Fresh.Direct.MirrorCount
import RHV6Fresh.Direct.PairTowers

/-!
# Invariance radiale par translation grammaticale (E343 → proposition mathématique, 2026-10-19)

Texte de travail de l'auteur (30 lignes, 2026-10-19) : « E343 retrouve douze modes depuis les écarts premiers sans fixer
`T`, `β` ni les amplitudes ; les trois premiers donnent `β̂ ≈ 1/2` ; la propriété recherchée doit relier cette position
commune aux événements premiers. » Lignes 13–22 : dans `u = log x`, un mode isolé `e^{(β−1/2+iT)u}` projeté sur deux
fenêtres translatées de `h` donne un rapport d'amplitude `e^{(β−1/2)h}`, qui vaut `1` exactement quand `β = 1/2`.
Lignes 23–27 : les translations `h_n = log(p_{n+1}/p_n)` sont produites par la grammaire ; une arrivée sous un demi a un
rapport `< 1`, son miroir `> 1`, à la même fréquence.

Ce module compile ces énoncés exactement, sans rien fixer :
* la projection fenêtrée `P_a(T)[f] = ∫_a^{a+L} f(u) e^{−iTu} du` ;
* pour le mode normalisé d'un vrai zéro (`complexMode (β−1/2) T`, dont la partie réelle est la densité de comptage
  normalisée d'`InversePrimeSpectral`), `P_{a+h} = e^{(β−1/2)h} P_a` et `P_a > 0` sur toute fenêtre non dégénérée ;
* invariance sous UNE translation `h ≠ 0` ⟺ `β = 1/2` (caractérisation, aucune loi) ;
* forme grammaticale : `h = L_r = log(p_{r+1}/p_r) > 0`, rapport = celui de `pairAmplitude_prime_step` ;
* sous un demi : rapport `< 1` ; miroir : même fréquence, rapport `> 1` (dérives opposées, ligne 26) ;
* linéarité : la projection d'une somme finie de modes est la somme des projections (aucun échange avec la somme infinie
  n'est démontré ici) ;
* formes fermantes : l'invariance d'un seul couple de fenêtres translaté d'un seul écart exclut l'arrivée sous un demi ;
  la loi quantifiée sur tous les vrais zéros ⟺ RH.

Statut (ligne 28 du texte) : la loi « les modes authentiques extraits de `dμ` conservent leur amplitude projetée sous
translation grammaticale » n'est PAS déduite des sauts et écarts exacts ; elle est écrite, caractérisée et composée dans la
chaîne comme forme fermante. Le but `:484` reste `False`.
-/

namespace RHV6Fresh

open RHV3Lean MeasureTheory

/-! ## §1 Projection fenêtrée et mode normalisé -/

/-- Projection fenêtrée à la fréquence `T` d'un signal `f` en `u = log x`, sur la fenêtre `[a, a + L]`. -/
noncomputable def windowProjection (f : ℝ → ℂ) (a L T : ℝ) : ℂ :=
  ∫ u in a..a + L, f u * Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ)))

/-- Mode normalisé d'un vrai zéro : `e^{(β−1/2)u} e^{iTu}` (sa partie réelle est `e^{(β−1/2)u} cos(Tu)`, la densité de
comptage normalisée d'`InversePrimeSpectral`). -/
noncomputable def zeroMode (z : TrueZero) (u : ℝ) : ℂ :=
  complexMode (rZeroRadialPosition z.1 - 1 / 2) (rZeroHeight z.1) u

/-- Fidélité au plan du comptage : la partie réelle du mode normalisé est exactement la densité de comptage du zéro,
transportée en `u = log x` et normalisée par `−u e^{−u/2}/2` (`normalized_mode_density`). -/
theorem zeroMode_re_eq_counting_density (z : TrueZero) {u : ℝ} (hu : 0 < u) :
    (zeroMode z u).re =
      -(u * Real.exp (-u / 2) / 2) * (countingModulationDensity z (Real.exp u) * Real.exp u) := by
  rw [normalized_mode_density z hu]
  unfold zeroMode
  rw [complexMode_eq]
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- Le mode fois le filtre à sa propre fréquence est l'exponentielle réelle `e^{du}`. -/
theorem complexMode_mul_filter (d T u : ℝ) :
    complexMode d T u * Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ))) = (Real.exp (d * u) : ℂ) := by
  unfold complexMode
  rw [← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- Amplitude fenêtrée réelle d'un mode d'exposant `d` : `∫_a^{a+L} e^{du} du`. -/
noncomputable def windowAmplitude (d a L : ℝ) : ℝ := ∫ u in a..a + L, Real.exp (d * u)

/-- La projection d'un mode à sa fréquence est son amplitude fenêtrée réelle. -/
theorem windowProjection_mode (d T a L : ℝ) :
    windowProjection (complexMode d T) a L T = (windowAmplitude d a L : ℂ) := by
  unfold windowProjection windowAmplitude
  simp_rw [complexMode_mul_filter]
  exact intervalIntegral.integral_ofReal

/-- Sur une fenêtre non dégénérée, l'amplitude fenêtrée est strictement positive. -/
theorem windowAmplitude_pos (d a : ℝ) {L : ℝ} (hL : 0 < L) : 0 < windowAmplitude d a L := by
  unfold windowAmplitude
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  · intro x _; exact Real.exp_pos _
  · linarith

/-! ## §2 Rapport de translation : `e^{(β−1/2)h}` -/

/-- **Translation d'une fenêtre** : `∫_{a+h}^{a+h+L} e^{du} du = e^{dh} ∫_a^{a+L} e^{du} du`. -/
theorem windowAmplitude_translate (d a L h : ℝ) :
    windowAmplitude d (a + h) L = Real.exp (d * h) * windowAmplitude d a L := by
  unfold windowAmplitude
  have hshift : (a + h) + L = (a + L) + h := by ring
  rw [hshift, ← intervalIntegral.integral_comp_add_right (fun u => Real.exp (d * u)) h]
  simp_rw [mul_add, Real.exp_add, mul_comm (Real.exp (d * _)) (Real.exp (d * h))]
  rw [intervalIntegral.integral_const_mul]

/-- **Rapport de translation de la projection** (ligne 16 du texte) : `P_{a+h}(T) = e^{(β−1/2)h} P_a(T)`. -/
theorem windowProjection_mode_translate (d T a L h : ℝ) :
    windowProjection (complexMode d T) (a + h) L T =
      (Real.exp (d * h) : ℂ) * windowProjection (complexMode d T) a L T := by
  rw [windowProjection_mode, windowProjection_mode, windowAmplitude_translate]
  push_cast; ring

/-- Module du rapport : `‖P_{a+h}‖ = e^{dh} ‖P_a‖`. -/
theorem windowProjection_mode_translate_norm (d T a L h : ℝ) :
    ‖windowProjection (complexMode d T) (a + h) L T‖ =
      Real.exp (d * h) * ‖windowProjection (complexMode d T) a L T‖ := by
  rw [windowProjection_mode_translate, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

/-- **Invariance sous une translation `h ≠ 0` ⟺ exposant nul** (lignes 17, 21–22 : caractérisation, aucune loi). -/
theorem windowProjection_translation_invariant_iff (d T a : ℝ) {L h : ℝ} (hL : 0 < L) (hh : h ≠ 0) :
    ‖windowProjection (complexMode d T) (a + h) L T‖ = ‖windowProjection (complexMode d T) a L T‖ ↔ d = 0 := by
  rw [windowProjection_mode_translate_norm, windowProjection_mode, Complex.norm_real,
    Real.norm_of_nonneg (windowAmplitude_pos d a hL).le]
  have hpos := windowAmplitude_pos d a hL
  constructor
  · intro h1
    have h2 : Real.exp (d * h) = 1 := by
      have := mul_right_cancel₀ hpos.ne' (h1.trans (one_mul _).symm)
      exact this
    rw [Real.exp_eq_one_iff] at h2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd h3 hh
  · intro h1; rw [h1, zero_mul, Real.exp_zero, one_mul]

/-! ## §3 Le mode d'un vrai zéro -/

/-- Pour un vrai zéro : invariance sous une translation `h ≠ 0`, fenêtre non dégénérée ⟺ `β = 1/2`. -/
theorem zeroMode_translation_invariant_iff (z : TrueZero) (a : ℝ) {L h : ℝ} (hL : 0 < L) (hh : h ≠ 0) :
    ‖windowProjection (zeroMode z) (a + h) L (rZeroHeight z.1)‖ =
        ‖windowProjection (zeroMode z) a L (rZeroHeight z.1)‖ ↔
      rZeroRadialPosition z.1 = 1 / 2 := by
  unfold zeroMode
  rw [windowProjection_translation_invariant_iff _ _ _ hL hh, sub_eq_zero]

/-- Rapport de translation du mode d'un vrai zéro : `e^{(β−1/2)h}`. -/
theorem zeroMode_translate_norm (z : TrueZero) (a L h : ℝ) :
    ‖windowProjection (zeroMode z) (a + h) L (rZeroHeight z.1)‖ =
      Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * h) * ‖windowProjection (zeroMode z) a L (rZeroHeight z.1)‖ :=
  windowProjection_mode_translate_norm _ _ _ _ _

/-- La projection du mode d'un vrai zéro à sa fréquence n'est jamais nulle sur une fenêtre non dégénérée. -/
theorem zeroMode_windowProjection_ne_zero (z : TrueZero) (a : ℝ) {L : ℝ} (hL : 0 < L) :
    windowProjection (zeroMode z) a L (rZeroHeight z.1) ≠ 0 := by
  unfold zeroMode
  rw [windowProjection_mode]
  exact_mod_cast (windowAmplitude_pos _ a hL).ne'

/-! ## §4 Translation grammaticale : `h = L_r = log(p_{r+1}/p_r)` (lignes 23–27) -/

/-- **Rapport grammatical** : la translation d'un écart premier donne le rapport `e^{(β−1/2)L_r}`, celui de
`pairAmplitude_prime_step` (même nombre, lu sur la projection fenêtrée). -/
theorem zeroMode_gap_translate (z : TrueZero) (r : ℕ) (a L : ℝ) :
    ‖windowProjection (zeroMode z) (a + rPrimeGapLogRatio r) L (rZeroHeight z.1)‖ =
      (pairAmplitude z (fnPrimeSuccessor r : ℝ) / pairAmplitude z (fnPrimeAtRank r : ℝ)) *
        ‖windowProjection (zeroMode z) a L (rZeroHeight z.1)‖ := by
  rw [zeroMode_translate_norm, pairAmplitude_prime_step]

/-- **Arrivée sous un demi** (ligne 24) : sur toute translation grammaticale, la projection décroît strictement. -/
theorem low_zeroMode_gap_translate_lt (z : TrueZero) (hz : rZeroRadialPosition z.1 < 1 / 2) (r : ℕ) (a : ℝ)
    {L : ℝ} (hL : 0 < L) :
    ‖windowProjection (zeroMode z) (a + rPrimeGapLogRatio r) L (rZeroHeight z.1)‖ <
      ‖windowProjection (zeroMode z) a L (rZeroHeight z.1)‖ := by
  rw [zeroMode_translate_norm]
  have hP : 0 < ‖windowProjection (zeroMode z) a L (rZeroHeight z.1)‖ :=
    norm_pos_iff.mpr (zeroMode_windowProjection_ne_zero z a hL)
  have hexp : Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * rPrimeGapLogRatio r) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (by linarith) (thm_primeGapLogRatio_pos r)
  calc _ < 1 * ‖windowProjection (zeroMode z) a L (rZeroHeight z.1)‖ := by
        exact mul_lt_mul_of_pos_right hexp hP
    _ = _ := one_mul _

/-- **Miroir** (ligne 25) : même fréquence, projection strictement croissante sur toute translation grammaticale. -/
theorem mirror_zeroMode_gap_translate_gt (z : TrueZero) (hz : rZeroRadialPosition z.1 < 1 / 2) (r : ℕ) (a : ℝ)
    {L : ℝ} (hL : 0 < L) :
    rZeroHeight (mirrorMember z).1 = rZeroHeight z.1 ∧
      ‖windowProjection (zeroMode (mirrorMember z)) a L (rZeroHeight (mirrorMember z).1)‖ <
        ‖windowProjection (zeroMode (mirrorMember z)) (a + rPrimeGapLogRatio r) L
          (rZeroHeight (mirrorMember z).1)‖ := by
  refine ⟨mirrorMember_ordinate z, ?_⟩
  rw [zeroMode_translate_norm]
  have hP : 0 < ‖windowProjection (zeroMode (mirrorMember z)) a L (rZeroHeight (mirrorMember z).1)‖ :=
    norm_pos_iff.mpr (zeroMode_windowProjection_ne_zero _ a hL)
  have hexp : 1 < Real.exp ((rZeroRadialPosition (mirrorMember z).1 - 1 / 2) * rPrimeGapLogRatio r) := by
    rw [Real.one_lt_exp_iff, mirrorMember_radial]
    exact mul_pos (by linarith) (thm_primeGapLogRatio_pos r)
  calc _ = 1 * ‖windowProjection (zeroMode (mirrorMember z)) a L (rZeroHeight (mirrorMember z).1)‖ :=
        (one_mul _).symm
    _ < _ := mul_lt_mul_of_pos_right hexp hP

/-- **Dérives opposées à la même fréquence** (ligne 26) : produit des deux rapports grammaticaux = 1. -/
theorem mirror_pair_gap_ratios_product (z : TrueZero) (r : ℕ) :
    Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * rPrimeGapLogRatio r) *
      Real.exp ((rZeroRadialPosition (mirrorMember z).1 - 1 / 2) * rPrimeGapLogRatio r) = 1 := by
  rw [← Real.exp_add, mirrorMember_radial, Real.exp_eq_one_iff]; ring

/-! ## §5 Linéarité (somme finie de modes) -/

theorem windowProjection_add (f g : ℝ → ℂ) (a L T : ℝ)
    (hf : IntervalIntegrable (fun u => f u * Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ)))) volume a (a + L))
    (hg : IntervalIntegrable (fun u => g u * Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ)))) volume a (a + L)) :
    windowProjection (fun u => f u + g u) a L T = windowProjection f a L T + windowProjection g a L T := by
  unfold windowProjection
  simp_rw [add_mul]
  exact intervalIntegral.integral_add hf hg

/-- Le mode d'un vrai zéro fois le filtre est continu, donc intégrable sur toute fenêtre. -/
theorem zeroMode_filter_intervalIntegrable (z : TrueZero) (a L T : ℝ) :
    IntervalIntegrable (fun u => zeroMode z u * Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ)))) volume a (a + L) := by
  apply Continuous.intervalIntegrable
  unfold zeroMode complexMode
  apply Continuous.mul
  · exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  · exact Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul Complex.continuous_ofReal))

/-- **Linéarité** : la projection d'une somme FINIE de modes de vrais zéros est la somme des projections. Aucun échange
avec la somme infinie de la formule explicite n'est affirmé. -/
theorem windowProjection_finset_sum (s : Finset TrueZero) (a L T : ℝ) :
    windowProjection (fun u => ∑ z ∈ s, zeroMode z u) a L T = ∑ z ∈ s, windowProjection (zeroMode z) a L T := by
  unfold windowProjection
  simp_rw [Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum fun z _ => zeroMode_filter_intervalIntegrable z a L T

/-! ## §6 Loi candidate (ligne 19) et formes fermantes -/

/-- **Invariance radiale grammaticale** d'un vrai zéro : la projection de son mode à sa fréquence garde le même module
sous toute translation d'un écart premier `L_r`, sur toute fenêtre non dégénérée. Loi CANDIDATE (ligne 19), non déduite. -/
def GrammaticalRadialInvariance (z : TrueZero) : Prop :=
  ∀ (r : ℕ) (a L : ℝ), 0 < L →
    ‖windowProjection (zeroMode z) (a + rPrimeGapLogRatio r) L (rZeroHeight z.1)‖ =
      ‖windowProjection (zeroMode z) a L (rZeroHeight z.1)‖

/-- La loi candidate ⟺ `β = 1/2` : caractérisation (ligne 22). -/
theorem grammaticalRadialInvariance_iff (z : TrueZero) :
    GrammaticalRadialInvariance z ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro h
    exact (zeroMode_translation_invariant_iff z 0 one_pos (thm_primeGapLogRatio_pos 0).ne').mp (h 0 0 1 one_pos)
  · intro h r a L _
    exact (zeroMode_translation_invariant_iff z a (by linarith) (thm_primeGapLogRatio_pos r).ne').mpr h

/-- **Forme fermante minimale** : UNE fenêtre non dégénérée, UNE translation d'un écart premier, une seule égalité de
modules, excluent une arrivée sous un demi. -/
theorem single_gap_translation_invariance_closes (z : TrueZero) (hz : rZeroRadialPosition z.1 < 1 / 2) :
    (∃ (r : ℕ) (a L : ℝ), 0 < L ∧
      ‖windowProjection (zeroMode z) (a + rPrimeGapLogRatio r) L (rZeroHeight z.1)‖ =
        ‖windowProjection (zeroMode z) a L (rZeroHeight z.1)‖) → False := by
  rintro ⟨r, a, L, hL, h⟩
  exact absurd (low_zeroMode_gap_translate_lt z hz r a hL) (by rw [h]; exact lt_irrefl _)

/-- Il suffit même que la projection ne DÉCROISSE pas sur une translation grammaticale. -/
theorem single_gap_translation_nondecrease_closes (z : TrueZero) (hz : rZeroRadialPosition z.1 < 1 / 2) :
    (∃ (r : ℕ) (a L : ℝ), 0 < L ∧
      ‖windowProjection (zeroMode z) a L (rZeroHeight z.1)‖ ≤
        ‖windowProjection (zeroMode z) (a + rPrimeGapLogRatio r) L (rZeroHeight z.1)‖) → False := by
  rintro ⟨r, a, L, hL, h⟩
  exact absurd h (not_le.mpr (low_zeroMode_gap_translate_lt z hz r a hL))

/-- La loi candidate quantifiée sur tous les vrais zéros ⟺ RH (lignes 27–29 : la démontrer depuis les écarts exacts,
c'est démontrer RH ; elle n'est l'hypothèse d'aucune fermeture). -/
theorem grammaticalRadialInvariance_all_iff :
    (∀ z : TrueZero, GrammaticalRadialInvariance z) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_all_canonical_onLine fun n _ => (grammaticalRadialInvariance_iff _).mp (h _)
  · intro hRH z
    exact (grammaticalRadialInvariance_iff z).mpr (thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1)

#print axioms windowProjection_mode_translate
#print axioms zeroMode_translation_invariant_iff
#print axioms low_zeroMode_gap_translate_lt
#print axioms mirror_zeroMode_gap_translate_gt
#print axioms windowProjection_finset_sum
#print axioms single_gap_translation_invariance_closes
#print axioms grammaticalRadialInvariance_all_iff

end RHV6Fresh
