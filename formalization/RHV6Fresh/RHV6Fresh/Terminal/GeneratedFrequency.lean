/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.OccupiedFrequency
import RHV6Fresh.Terminal.ContactSensitivity
import RHV6Fresh.Terminal.GrammaticalRaccordJump
import RHV6Fresh.Terminal.SpectralUniqueness
import RHV6Fresh.Terminal.RemainderRepresentation
import RHV6Fresh.Terminal.StageCell
import RHV6Fresh.Terminal.RayCapture
import RHV3Lean.Objects.ZetaSmoothedUnsmoothingP5
import RHV6Fresh.Terminal.AuthenticPassageProfile
import RHV6Fresh.Terminal.PrimeGrammarQuantitative

/-!
# Des écarts exacts vers les fréquences engendrées et leurs points de rencontre (E321, auteur, 2026-10-16 ;
# réimplémentation du 2026-10-16 après audit)

Mission de l'auteur, mot pour mot : « la seule flèche manquante est celle des écarts exacts vers les fréquences engendrées et
leurs points de rencontre (aucune en dessous d'une demi) » ; « écrire, côté premiers, que les écarts exacts n'engendrent aucune
fréquence à rencontre sous une demi » ; « dériver les rigidités dans l'autre sens : premiers vers zéro ».

## Ce que l'audit du 2026-10-16 a relevé, et ce que ce module corrige

La première version (commit `5efc0669` et suivants) décrivait ses objets comme « écrits depuis la courbe des premiers » alors que
leur définition partait d'un zéro déjà donné : `GeneratedFrequency T := ∃ z : TrueZero, T_z = T` (un zéro à la hauteur `T`), et
`MeetingOnLine T` (tout zéro de hauteur `T` a sa rencontre à la position de la ligne) est la propriété cherchée, non une
conséquence. Le dernier pas de la chaîne (`frequencyTaken_of_meeting_on_line`) demandait donc exactement `β_w = 1/2`, écrit sur le
zéro `w`. La flèche « premiers ⟶ fréquence ⟶ rencontre » n'était pas réalisée par ces définitions.

Correction (section 0 et section 6) : les objets sont maintenant définis depuis le RESTE DES PREMIERS `smoothedRemainder x`
(`Σ_{n<x} Λ(n)(1 − n/x) − fond`, premiers seuls, `Terminal/ArithmeticReading.lean`), sans aucun zéro dans leur énoncé :
* une **représentation du reste des premiers** `PrimeSignalRepresentation ι` : une famille de signaux `(point, poids)` dont la
  somme reproduit `smoothedRemainder x` pour tout `x > 1` ;
* une **fréquence engendrée par les premiers** `ArithmeticFrequency T` : toute représentation du reste des premiers porte un
  signal de poids non nul de fréquence `|Im| = T` ;
* le **point de rencontre d'un signal** `meetingOf p = exp(arctan(Im p / Re p) / Im p)` : où le signal `x^p` rencontre l'axe
  algébrique (indice `0`), fonction du seul point ; invariant par conjugaison (un signal réel = point et conjugué) ;
* la **rencontre arithmétique** `ArithmeticMeeting T c` : dans toute représentation du reste des premiers, tout signal de poids
  non nul de fréquence `T` rencontre l'axe en `c`.
Ces objets ne désignent un signal que par sa fréquence, jamais par sa position radiale (la désigner par `(T, β)` présupposerait
ce que l'on cherche).

Correspondance DÉMONTRÉE avec les objets spectraux, par l'unicité de la décomposition du reste (`Terminal/SpectralUniqueness.lean`,
aucun exposant fixé) : `ArithmeticFrequency T ⟺ GeneratedFrequency T` (`arithmeticFrequency_iff`) ; le point de rencontre d'un
zéro est `meetingOf` de son point (`contactMinusAt_eq_meetingOf`) ; la position de la ligne est `meetingOf` du point de la ligne à
cette fréquence (`lineContact_eq_meetingOf`) ; `ArithmeticMeeting T (position de la ligne) ⟺ MeetingOnLine T`
(`arithmeticMeeting_iff_meetingOnLine`) ; rencontre arithmétique au-delà de la position de la ligne ⟺ signal en dessous d'une demi
(`arithmetic_meeting_beyond_line_iff_low`) ; la loi « toute fréquence engendrée par les premiers a sa rencontre arithmétique à la
position de la ligne » ⟺ RH (`arithmeticMeeting_law_iff_riemannHypothesis`).

Ce que la correspondance ne fait pas : elle ne contient pas `β = 1/2`. L'unicité retrouve chaque signal tel qu'il est (sa
fréquence, sa position radiale, son poids), elle ne fixe pas sa position radiale. La flèche manquante est donc exactement, côté
premiers : la rencontre arithmétique à la fréquence du zéro suivant est à la position de la ligne. C'est le but ouvert de la
chaîne (`off_signal_amplitude_incompatible`), écrit sur `smoothedRemainder` et la fréquence seules.

## Objets spectraux conservés (forme sur les zéros)
`GeneratedFrequency T` (un zéro de hauteur `T`), `MeetingOnLine T` (PROPRIÉTÉ À ÉTABLIR : tout zéro de hauteur `T` a sa rencontre
à la position de la ligne), `SingleSignal T`, `NoMeetingBelow` ; rigidités renversées (toutes démontrées, toute position radiale) :
`radial_from_meeting`, `radial_from_need_ratio`, `meeting_on_line_iff`, `meeting_below_iff_low`, `meetingOnLine_iff_fiber_onLine`,
`singleSignal_iff_meetingOnLine`, `meeting_shift_detects`, `meeting_shift_blind` (résolution d'une mesure finie, pas une
démonstration), `noMeetingBelow_iff_riemannHypothesis`, `singleSignal_law_iff_riemannHypothesis`,
`frequencyTaken_of_meeting_on_line`, `frequencyTaken_of_meetingOnLine`.

Mesuré (E321, premiers seuls, vingt fréquences) : rencontre à la position de la ligne et un seul signal, aux résolutions
consignées ; la lecture de la rencontre y est calibrée sur un contrôle ON (termes exacts des zéros publiés à `β = 1/2`) : la
définition `meetingOf` ci-dessus est l'objet exact que cette lecture approche, indépendant de toute calibration. Non démontré :
la rencontre arithmétique sur la ligne à la fréquence du zéro suivant.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 0. Objets écrits depuis le reste des premiers (aucun zéro dans leur énoncé) -/

/-- **Représentation du reste des premiers par des signaux** : une famille de points distincts du plan (`Re ≤ 1`, localement
finie, hors de `0` et `−1`) et de poids absolument sommables (après division par `p(p+1)`) dont la somme reproduit le reste
lissé DES PREMIERS `smoothedRemainder x` pour tout `x > 1`. Le côté droit est écrit avec les seuls poids `Λ(n)`. -/
structure PrimeSignalRepresentation (ι : Type*) where
  point : ι → ℂ
  weight : ι → ℂ
  injective : Function.Injective point
  re_le_one : ∀ i, (point i).re ≤ 1
  ne_zero : ∀ i, point i ≠ 0 ∧ point i + 1 ≠ 0
  locallyFinite : ∀ R : ℝ, {i | ‖point i‖ ≤ R}.Finite
  summable : Summable fun i => ‖weight i / (point i * (point i + 1))‖
  reproduces : ∀ x : ℝ, 1 < x → ∑' i, weight i * Perron.f x (point i) = smoothedRemainder x

/-- Une représentation du reste des premiers est une représentation du canal compilé : la reproduction exacte de la courbe
des premiers par les vrais zéros (`smoothedRemainder_eq_tsum_residueTerm`) fait le pont. -/
def PrimeSignalRepresentation.toSpectral {ι : Type*} (Rep : PrimeSignalRepresentation ι) :
    SpectralRepresentation ι where
  point := Rep.point
  weight := Rep.weight
  injective := Rep.injective
  re_le_one := Rep.re_le_one
  ne_zero := Rep.ne_zero
  locallyFinite := Rep.locallyFinite
  summable := Rep.summable
  represents := fun x hx => by rw [Rep.reproduces x hx, smoothedRemainder_eq_tsum_residueTerm hx]

/-- Réciproquement, toute représentation du canal compilé reproduit le reste des premiers. -/
def SpectralRepresentation.toPrime {ι : Type*} (Rep : SpectralRepresentation ι) :
    PrimeSignalRepresentation ι where
  point := Rep.point
  weight := Rep.weight
  injective := Rep.injective
  re_le_one := Rep.re_le_one
  ne_zero := Rep.ne_zero
  locallyFinite := Rep.locallyFinite
  summable := Rep.summable
  reproduces := fun x hx => by rw [Rep.represents x hx, smoothedRemainder_eq_tsum_residueTerm hx]

/-- **La représentation vraie du reste des premiers** : les zéros non triviaux, avec les poids `−m(ρ)`. -/
noncomputable def primeTrueRepresentation : PrimeSignalRepresentation ExplicitIndex where
  point ρ := (ρ : ℂ)
  weight ρ := -(zetaZeroMultiplicity (ρ : ℂ) : ℂ)
  injective := Subtype.coe_injective
  re_le_one := explicitIndex_re_le_one
  ne_zero := explicitIndex_ne_zero
  locallyFinite := explicitIndex_locallyFinite
  summable := trueRepresentation.summable
  reproduces := fun x hx => by
    rw [smoothedRemainder_eq_tsum_residueTerm hx]
    exact trueRepresentation.represents x hx

/-- **Point de rencontre d'un signal** : l'abscisse où le signal `x^p` rencontre l'axe algébrique à l'indice `0`,
`exp(arctan(Im p / Re p) / Im p)`. Fonction du seul point. -/
noncomputable def meetingOf (p : ℂ) : ℝ := Real.exp (Real.arctan (p.im / p.re) / p.im)

/-- Un signal réel est porté par un point et son conjugué : ils ont le même point de rencontre. -/
theorem meetingOf_conj (p : ℂ) : meetingOf (starRingEnd ℂ p) = meetingOf p := by
  unfold meetingOf
  simp only [Complex.conj_re, Complex.conj_im]
  rw [neg_div, Real.arctan_neg, neg_div_neg_eq]

/-- Le point de rencontre ne lit du point que sa fréquence `|Im p|` et sa position radiale `Re p`. -/
theorem meetingOf_abs_im (p : ℂ) :
    meetingOf p = Real.exp (Real.arctan (|p.im| / p.re) / |p.im|) := by
  unfold meetingOf
  rcases le_or_gt 0 p.im with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, neg_div, Real.arctan_neg, neg_div_neg_eq]

/-- **Fréquence engendrée par les premiers** : toute représentation du reste des premiers porte un signal de poids non nul de
fréquence `T`. Rien d'autre que `smoothedRemainder` et `T` n'entre dans cet énoncé. -/
def ArithmeticFrequency (T : ℝ) : Prop :=
  ∀ Rep : PrimeSignalRepresentation ExplicitIndex, ∃ i, Rep.weight i ≠ 0 ∧ |(Rep.point i).im| = T

/-- **Rencontre arithmétique** : dans toute représentation du reste des premiers, tout signal de poids non nul de fréquence
`T` rencontre l'axe en `c`. Le signal n'est désigné que par sa fréquence. -/
def ArithmeticMeeting (T c : ℝ) : Prop :=
  ∀ Rep : PrimeSignalRepresentation ExplicitIndex, ∀ i, Rep.weight i ≠ 0 → |(Rep.point i).im| = T →
    meetingOf (Rep.point i) = c

/-! ## 1. Objets spectraux (forme sur les zéros) -/

/-- **Fréquence engendrée, forme spectrale** : un zéro de hauteur `T`. Équivalente à la forme côté premiers
`ArithmeticFrequency T` (`arithmeticFrequency_iff`), par l'unicité de la décomposition du reste. -/
def GeneratedFrequency (T : ℝ) : Prop := ∃ z : TrueZero, rZeroHeight z.1 = T

theorem generatedFrequency_of_zero (z : TrueZero) : GeneratedFrequency (rZeroHeight z.1) := ⟨z, rfl⟩

/-- **Rencontre sur la ligne à la fréquence `T`** : tout zéro de hauteur `T` a sa rencontre d'indice `0` à la position de la
ligne. PROPRIÉTÉ À ÉTABLIR (⟺ toute la fibre de `T` sur la ligne, `meetingOnLine_iff_fiber_onLine`), jamais une conséquence
des définitions ; sa forme côté premiers est `ArithmeticMeeting T (lineContact T 0)` (`arithmeticMeeting_iff_meetingOnLine`). -/
def MeetingOnLine (T : ℝ) : Prop :=
  ∀ z : TrueZero, rZeroHeight z.1 = T → contactMinusAt z 0 = lineContact T 0

/-- **Un seul signal à la fréquence `T`** : tous les zéros de cette hauteur partagent leur rencontre. -/
def SingleSignal (T : ℝ) : Prop :=
  ∀ z v : TrueZero, rZeroHeight z.1 = T → rZeroHeight v.1 = T → contactMinusAt z 0 = contactMinusAt v 0

/-- **Aucune fréquence engendrée n'a de rencontre en dessous d'une demi** (forme spectrale ; ⟺ RH). -/
def NoMeetingBelow : Prop := ∀ T : ℝ, GeneratedFrequency T → MeetingOnLine T

/-! ## 2. Rigidités renversées : la rencontre impose la position radiale -/

/-- **R2 renversée** : la position de la rencontre d'un signal engendré impose sa position radiale,
`β = T · cot(T log C_0)`. -/
theorem radial_from_meeting (z : TrueZero) :
    rZeroRadialPosition z.1 = rZeroHeight z.1 * Real.cot (rZeroHeight z.1 * Real.log (contactMinusAt z 0)) :=
  (inversion_radial z 0).symm

/-- **R3 renversée** : le rapport des besoins à deux rencontres consécutives impose la position radiale,
`β = 1/2 + (T/π) · log(besoin(C_1)/besoin(C_0))`. -/
theorem radial_from_need_ratio (z : TrueZero) :
    rZeroRadialPosition z.1 = rZeroHeight z.1 / Real.pi *
      Real.log (pairAmplitude z (contactMinusAt z (0 + 1)) / pairAmplitude z (contactMinusAt z 0)) + 1 / 2 := by
  rw [← two_radial_readings_agree z 0, inversion_radial]

/-- **Rencontre à la position de la ligne ⟺ signal sur la ligne.** -/
theorem meeting_on_line_iff (z : TrueZero) :
    contactMinusAt z 0 = lineContact (rZeroHeight z.1) 0 ↔ rZeroRadialPosition z.1 = 1 / 2 :=
  contact_eq_line_iff_onLine z 0

/-- **Rencontre sous une demi** : la rencontre du signal est au-delà de la position de la ligne (translation `λ > 1`) ⟺ le
signal est en dessous d'une demi. -/
theorem meeting_below_iff_low (z : TrueZero) :
    lineContact (rZeroHeight z.1) 0 < contactMinusAt z 0 ↔ rZeroRadialPosition z.1 < 1 / 2 := by
  rw [contact_eq_line_mul_radial, ← radialFactor_gt_one_iff]
  have hpos := lineContact_pos (rZeroHeight z.1) 0
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    have := mul_le_mul_of_nonneg_left hle hpos.le
    rw [mul_one] at this
    exact absurd h (not_lt.mpr this)
  · intro h
    have := mul_lt_mul_of_pos_left h hpos
    rwa [mul_one] at this

/-! ## 3. Un seul signal par fréquence ⟺ rencontre sur la ligne -/

/-- Rencontre sur la ligne à une fréquence ⟺ tous les zéros de cette hauteur sont sur la ligne. -/
theorem meetingOnLine_iff_fiber_onLine (T : ℝ) :
    MeetingOnLine T ↔ ∀ z : TrueZero, rZeroHeight z.1 = T → rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro h z hz
    have := h z hz
    rw [← hz] at this
    exact (meeting_on_line_iff z).mp this
  · intro h z hz
    have := (meeting_on_line_iff z).mpr (h z hz)
    rwa [hz] at this

theorem singleSignal_of_meetingOnLine {T : ℝ} (h : MeetingOnLine T) : SingleSignal T :=
  fun z v hz hv => by rw [h z hz, h v hv]

/-- **Un seul signal ⟹ rencontre sur la ligne** : le miroir de tout signal engendré à `T` est engendré à `T` ; une rencontre
commune force `β = 1 − β` (verrou du couple). -/
theorem meetingOnLine_of_singleSignal {T : ℝ} (h : SingleSignal T) : MeetingOnLine T := by
  rw [meetingOnLine_iff_fiber_onLine]
  intro z hz
  have hm : rZeroHeight (mirrorMember z).1 = T := by rw [mirrorMember_ordinate, hz]
  have hc := h (mirrorMember z) z hm hz
  have hr := radial_of_meeting_point (mirrorMember z) z (by rw [mirrorMember_ordinate]) 0 (by rw [hc])
  rw [mirrorMember_radial] at hr
  linarith

theorem singleSignal_iff_meetingOnLine (T : ℝ) : SingleSignal T ↔ MeetingOnLine T :=
  ⟨meetingOnLine_of_singleSignal, singleSignal_of_meetingOnLine⟩

/-! ## 4. Ce qu'une mesure finie établit (résolution de E321) -/

/-- **Détection** : une translation de la rencontre lue à la précision `ε` détecte tout signal de position radiale
`β ≤ 1/2 − ε(T² + 1/4)`. -/
theorem meeting_shift_detects (z : TrueZero) {ε : ℝ} (hε : 0 ≤ ε)
    (h : rZeroRadialPosition z.1 ≤ 1 / 2 - ε * (rZeroHeight z.1 ^ 2 + 1 / 4)) :
    ε ≤ Real.log (radialFactor z) := by
  have hT2 : 0 < rZeroHeight z.1 ^ 2 + 1 / 4 := by positivity
  have hlow : rZeroRadialPosition z.1 ≤ 1 / 2 := by
    have := mul_nonneg hε hT2.le
    linarith
  have hb := (log_radialFactor_bounds_of_low z hlow).1
  have : ε ≤ (1 / 2 - rZeroRadialPosition z.1) / (rZeroHeight z.1 ^ 2 + 1 / 4) := by
    rw [le_div_iff₀ hT2]; linarith
  linarith

/-- **Aveuglement** : la même lecture ne voit aucun signal de position radiale `β ≥ 1/2 − εT²` (sa translation est sous `ε`) :
une mesure finie n'exclut jamais une position radiale arbitrairement proche d'une demi. -/
theorem meeting_shift_blind (z : TrueZero) {ε : ℝ}
    (hlow : rZeroRadialPosition z.1 ≤ 1 / 2)
    (h : 1 / 2 - ε * rZeroHeight z.1 ^ 2 ≤ rZeroRadialPosition z.1) :
    Real.log (radialFactor z) ≤ ε := by
  have hT2 : 0 < rZeroHeight z.1 ^ 2 := by have := z.2; positivity
  have hb := (log_radialFactor_bounds_of_low z hlow).2
  have : (1 / 2 - rZeroRadialPosition z.1) / rZeroHeight z.1 ^ 2 ≤ ε := by
    rw [div_le_iff₀ hT2]; linarith
  linarith

/-! ## 5. Force de la loi spectrale, et réduction de la chaîne -/

/-- **Aucune fréquence engendrée à rencontre sous une demi ⟺ RH.** -/
theorem noMeetingBelow_iff_riemannHypothesis : NoMeetingBelow ↔ RiemannHypothesis := by
  constructor
  · intro h
    refine riemannHypothesis_iff_noLowerSide.mpr (fun w hlt => ?_)
    have := ((meetingOnLine_iff_fiber_onLine _).mp (h _ (generatedFrequency_of_zero w))) w rfl
    linarith
  · intro hRH T _
    exact (meetingOnLine_iff_fiber_onLine T).mpr
      (fun z _ => thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1)

/-- Un seul signal à toute fréquence engendrée ⟺ RH. -/
theorem singleSignal_law_iff_riemannHypothesis :
    (∀ T : ℝ, GeneratedFrequency T → SingleSignal T) ↔ RiemannHypothesis := by
  rw [← noMeetingBelow_iff_riemannHypothesis]
  exact forall_congr' (fun T => imp_congr_right (fun _ => singleSignal_iff_meetingOnLine T))

/-- **Réduction** : la fréquence de `w` est prise dès que le point de rencontre du zéro `w` est à la position de la ligne
(c'est `β_w = 1/2` écrit sur la rencontre, `meeting_on_line_iff`). -/
theorem frequencyTaken_of_meeting_on_line (w : TrueZero)
    (h : contactMinusAt w 0 = lineContact (rZeroHeight w.1) 0) : FrequencyTaken w :=
  ⟨w, rfl, (meeting_on_line_iff w).mp h, rfl⟩

/-- La rencontre sur la ligne à la fréquence de `w` prend la fréquence de `w`. -/
theorem frequencyTaken_of_meetingOnLine (w : TrueZero) (h : MeetingOnLine (rZeroHeight w.1)) : FrequencyTaken w :=
  frequencyTaken_of_meeting_on_line w (h w rfl)

/-! ## 6. Correspondance démontrée : objets côté premiers ⟺ objets spectraux (unicité, aucun exposant fixé) -/

/-- Le point de rencontre d'indice `0` d'un zéro est le point de rencontre de son point. -/
theorem contactMinusAt_eq_meetingOf (z : TrueZero) : contactMinusAt z 0 = meetingOf (zeroPoint z) := by
  rw [contactMinusAt_eq_exp]
  unfold meetingOf
  rw [zeroPoint_re, zeroPoint_im]
  simp

/-- La position de la ligne à la fréquence `T` est le point de rencontre du point de la ligne `1/2 + iT`. -/
theorem lineContact_eq_meetingOf (T : ℝ) : lineContact T 0 = meetingOf ⟨1 / 2, T⟩ := by
  unfold lineContact linePhase meetingOf
  simp

/-- Le membre supérieur porté par un index explicite a pour rencontre le point de rencontre de l'index (point ou conjugué). -/
theorem contactMinusAt_indexUpper (σ : ExplicitIndex) :
    contactMinusAt (indexUpper σ) 0 = meetingOf (σ : ℂ) := by
  rw [contactMinusAt_eq_meetingOf, meetingOf_abs_im (σ : ℂ)]
  unfold meetingOf
  obtain ⟨hT, hβ⟩ := explicitIndex_upper_readings σ
  rw [zeroPoint_re, zeroPoint_im, hT, hβ]

/-- **Fréquence engendrée par les premiers ⟺ un zéro de cette hauteur.** Sens ⟹ : la représentation vraie porte un signal de
poids non nul à la fréquence `T`, son membre supérieur est un zéro de hauteur `T`. Sens ⟸ : dans toute représentation du reste
des premiers, le zéro figure avec sa multiplicité (`contains_member`). Aucun exposant n'est fixé. -/
theorem arithmeticFrequency_iff (T : ℝ) : ArithmeticFrequency T ↔ GeneratedFrequency T := by
  constructor
  · intro h
    obtain ⟨σ, -, hσ⟩ := h primeTrueRepresentation
    exact ⟨indexUpper σ, by rw [(explicitIndex_upper_readings σ).1]; exact hσ⟩
  · rintro ⟨z, rfl⟩ Rep
    obtain ⟨i, hi, hw⟩ := Rep.toSpectral.contains_member (memberIndex z)
    have hi' : Rep.point i = zeroPoint z := hi
    have hw' : Rep.weight i = -(zetaZeroMultiplicity (zeroPoint z) : ℂ) := hw
    refine ⟨i, ?_, ?_⟩
    · rw [hw', neg_ne_zero]
      exact_mod_cast (zetaZeroMultiplicity_pos (zeroPoint_isNontrivial z).1).ne'
    · rw [hi']
      exact abs_of_pos z.2

/-- La hauteur de tout zéro est une fréquence engendrée par les premiers. -/
theorem arithmeticFrequency_of_zero (z : TrueZero) : ArithmeticFrequency (rZeroHeight z.1) :=
  (arithmeticFrequency_iff _).mpr (generatedFrequency_of_zero z)

/-- **Rencontre arithmétique à la position de la ligne ⟺ rencontre sur la ligne (forme spectrale).** Sens ⟹ : la
représentation vraie porte chaque zéro. Sens ⟸ : un signal de poids non nul d'une représentation du reste des premiers est un
zéro non trivial (`no_intruder`), son membre supérieur a la fréquence `T`, sa rencontre est celle du zéro. -/
theorem arithmeticMeeting_iff_meetingOnLine (T : ℝ) :
    ArithmeticMeeting T (lineContact T 0) ↔ MeetingOnLine T := by
  constructor
  · intro h z hz
    have hw' : primeTrueRepresentation.weight (memberIndex z) ≠ 0 := by
      show -(zetaZeroMultiplicity (zeroPoint z) : ℂ) ≠ 0
      rw [neg_ne_zero]
      exact_mod_cast (zetaZeroMultiplicity_pos (zeroPoint_isNontrivial z).1).ne'
    have hT : |(primeTrueRepresentation.point (memberIndex z)).im| = T := by
      show |rZeroHeight z.1| = T
      have hpos : 0 < rZeroHeight z.1 := z.2
      rw [abs_of_pos hpos, hz]
    have := h primeTrueRepresentation (memberIndex z) hw' hT
    rw [contactMinusAt_eq_meetingOf]
    exact this
  · intro h Rep i hw hT
    have hz : IsNontrivialZetaZero (Rep.point i) := by
      by_contra hn
      exact hw (Rep.toSpectral.no_intruder i hn)
    let σ : ExplicitIndex := ⟨Rep.point i, hz⟩
    have hσ : rZeroHeight (indexUpper σ).1 = T := by
      rw [(explicitIndex_upper_readings σ).1]; exact hT
    have := h (indexUpper σ) hσ
    rw [contactMinusAt_indexUpper] at this
    exact this

/-- **Rencontre arithmétique au-delà de la position de la ligne ⟺ signal en dessous d'une demi**, lu sur l'index : la forme,
côté premiers, de « fréquence à rencontre sous une demi ». -/
theorem arithmetic_meeting_beyond_line_iff_low (σ : ExplicitIndex) :
    lineContact |(σ : ℂ).im| 0 < meetingOf (σ : ℂ) ↔ (σ : ℂ).re < 1 / 2 := by
  obtain ⟨hT, hβ⟩ := explicitIndex_upper_readings σ
  rw [← contactMinusAt_indexUpper, ← hT, ← hβ]
  exact meeting_below_iff_low (indexUpper σ)

/-- **La loi côté premiers ⟺ RH** : toute fréquence engendrée par les premiers a sa rencontre arithmétique à la position de la
ligne ⟺ RH. Quantifiée sur toutes les fréquences, la flèche manquante a la force de RH ; à une fréquence donnée elle est le but
de la chaîne. -/
theorem arithmeticMeeting_law_iff_riemannHypothesis :
    (∀ T : ℝ, ArithmeticFrequency T → ArithmeticMeeting T (lineContact T 0)) ↔ RiemannHypothesis := by
  rw [← noMeetingBelow_iff_riemannHypothesis]
  exact forall_congr' fun T =>
    imp_congr (arithmeticFrequency_iff T) (arithmeticMeeting_iff_meetingOnLine T)

/-- **Réduction de la chaîne, côté premiers** : la fréquence de `w` est prise dès que la rencontre arithmétique à cette
fréquence est à la position de la ligne. -/
theorem frequencyTaken_of_arithmeticMeeting (w : TrueZero)
    (h : ArithmeticMeeting (rZeroHeight w.1) (lineContact (rZeroHeight w.1) 0)) : FrequencyTaken w :=
  frequencyTaken_of_meetingOnLine w ((arithmeticMeeting_iff_meetingOnLine _).mp h)


/-! ## 7. Trois objets distincts : rencontre propre, rencontre collective, événement premier (audit du 2026-10-16)

Correction méthodologique (texte d'audit collé par l'auteur) : `ArithmeticMeeting` est écrit sur la rencontre PROPRE de chaque
composante (`meetingOf (Rep.point i)`), non sur la rencontre du signal collectif avec son fond ; les mesures de E321–E322
lisent les zéros d'une contribution filtrée du signal collectif, calibrés sur un contrôle ON, donc un objet de la seconde
espèce. Les trois objets sont séparés ici, chacun écrit sur les premiers seuls :

* `C_n` : rencontre propre de la composante `n`, `meetingOf (point n)` (fonction du seul point) ;
* `R` : rencontre collective, `CollectiveMeeting x` (le reste lissé des premiers s'annule en `x`) : une relation sur TOUTES
  les composantes à la fois (`collectiveMeeting_iff_sum_zero`), indépendante de la représentation ; à une telle rencontre
  chaque composante vaut l'opposé de la somme des autres (`collectiveMeeting_component_eq_neg_rest`) : rien n'y fixe la
  rencontre propre d'une composante ;
* `P` : événement premier, `PrimeEvent n` (`Λ(n) ≠ 0`) : la primitive arithmétique `x·S(x)` du reste des premiers avance de
  `h·ψ(N)` sur `[N, N + h]` (`arithmetic_primitive_step`), ses pentes à gauche et à droite d'un entier diffèrent de `Λ(N)`
  (`arithmetic_primitive_slope_jump`), non nul exactement aux événements premiers (`primeEvent_slope_jump_ne_zero`) ; toute
  somme FINIE de composantes est dérivable en tout `x > 0` (`finite_components_differentiableAt`) : l'événement n'appartient
  à aucune sous-somme finie, il est porté par la somme infinie seule (phénomène de la fonction de Weierstrass ; E323).

Ce que cette section ne fait pas : elle ne dit pas quelle contrainte les événements `P` imposent simultanément aux rencontres
propres `C_n` et à leur résultante `R` ; c'est la flèche manquante, écrite dans le but de la chaîne. -/

/-- **Forme individuelle** : `ArithmeticMeeting T c` demande la rencontre PROPRE de chaque composante de fréquence `T` ; il ne
mentionne pas la rencontre du signal collectif avec son fond. -/
theorem arithmeticMeeting_individual (T c : ℝ) :
    ArithmeticMeeting T c ↔ ∀ Rep : PrimeSignalRepresentation ExplicitIndex, ∀ i, Rep.weight i ≠ 0 →
      |(Rep.point i).im| = T → meetingOf (Rep.point i) = c := Iff.rfl

/-- **Rencontre collective** : le signal collectif des premiers rencontre son fond en `x` (le reste lissé des premiers s'annule).
Écrit sur `smoothedRemainder` seul. -/
def CollectiveMeeting (x : ℝ) : Prop := smoothedRemainder x = 0

/-- Une rencontre collective est une relation sur TOUTES les composantes à la fois : leur somme s'annule. -/
theorem collectiveMeeting_iff_sum_zero (Rep : PrimeSignalRepresentation ExplicitIndex) {x : ℝ} (hx : 1 < x) :
    CollectiveMeeting x ↔ ∑' i, Rep.weight i * Perron.f x (Rep.point i) = 0 := by
  unfold CollectiveMeeting
  rw [Rep.reproduces x hx]

/-- La rencontre collective est la même dans toute représentation du reste des premiers. -/
theorem collectiveMeeting_representation_free (R₁ R₂ : PrimeSignalRepresentation ExplicitIndex) {x : ℝ} (hx : 1 < x) :
    (∑' i, R₁.weight i * Perron.f x (R₁.point i) = 0) ↔ (∑' i, R₂.weight i * Perron.f x (R₂.point i) = 0) := by
  rw [R₁.reproduces x hx, R₂.reproduces x hx]

/-- Les composantes d'une représentation du reste des premiers sont sommables en tout `x > 1`. -/
theorem PrimeSignalRepresentation.summable_components {ι : Type*} (Rep : PrimeSignalRepresentation ι) {x : ℝ}
    (hx : 1 < x) : Summable fun i => Rep.weight i * Perron.f x (Rep.point i) := by
  refine (summable_profiles Rep.point (fun i => Rep.weight i / (Rep.point i * (Rep.point i + 1)))
    Rep.re_le_one Rep.summable hx).congr fun i => ?_
  change Rep.weight i / (Rep.point i * (Rep.point i + 1)) * (x : ℂ) ^ Rep.point i =
    Rep.weight i * ((x : ℂ) ^ Rep.point i / (Rep.point i * (Rep.point i + 1)))
  ring

/-- À une rencontre collective, chaque composante vaut l'opposé de la somme de toutes les autres : la relation porte sur la
somme, elle ne fixe la rencontre propre d'aucune composante. -/
theorem collectiveMeeting_component_eq_neg_rest (Rep : PrimeSignalRepresentation ExplicitIndex) {x : ℝ} (hx : 1 < x)
    (hR : CollectiveMeeting x) (i : ExplicitIndex) :
    Rep.weight i * Perron.f x (Rep.point i) =
      -∑' j, if j = i then 0 else Rep.weight j * Perron.f x (Rep.point j) := by
  have hs := Rep.summable_components hx
  have h0 := (collectiveMeeting_iff_sum_zero Rep hx).mp hR
  rw [hs.tsum_eq_add_tsum_ite i] at h0
  linear_combination h0

/-- **Événement premier** : `n` porte un poids `Λ(n) ≠ 0`, c'est-à-dire `n` est une puissance de premier. -/
def PrimeEvent (n : ℕ) : Prop := ArithmeticFunction.vonMangoldt n ≠ 0

theorem primeEvent_iff_isPrimePow (n : ℕ) : PrimeEvent n ↔ IsPrimePow n :=
  ArithmeticFunction.vonMangoldt_ne_zero_iff

/-- `ψ(N)` est la somme des poids `Λ(n)`, `n ≤ N`. -/
theorem psi_natCast_eq_sum_range (N : ℕ) :
    (Chebyshev.psi (N : ℝ) : ℂ) = ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℂ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  push_cast
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_Icc, Finset.mem_range]
  omega

/-- **Pas de la primitive arithmétique** : entre l'entier `N` et `N + h`, `0 < h ≤ 1`, la primitive `x·S(x)` du reste des
premiers avance exactement de `h·ψ(N)` : elle est affine par morceaux, de pente `ψ(N)` sur `]N, N + 1]`. -/
theorem arithmetic_primitive_step (N : ℕ) {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) :
    smoothedMangoldtPrimitive ((N : ℝ) + h) =
      smoothedMangoldtPrimitive N + (h : ℂ) * (Chebyshev.psi (N : ℝ) : ℂ) := by
  have hceil : ⌈(N : ℝ) + h⌉₊ = N + 1 := by
    rw [Nat.ceil_eq_iff (Nat.succ_ne_zero N)]
    constructor <;> push_cast <;> linarith
  have hceilN : ⌈(N : ℝ)⌉₊ = N := Nat.ceil_natCast N
  have hx : ((N : ℂ) + (h : ℂ)) ≠ 0 := by
    have : (N : ℝ) + h ≠ 0 := by positivity
    exact_mod_cast this
  unfold smoothedMangoldtPrimitive smoothedVonMangoldtSum
  rw [hceil, hceilN, psi_natCast_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ]
  push_cast
  have hlast : ((N : ℂ) + (h : ℂ)) *
      ((ArithmeticFunction.vonMangoldt N : ℂ) * (1 - (N : ℂ) / ((N : ℂ) + (h : ℂ)))) =
      (h : ℂ) * (ArithmeticFunction.vonMangoldt N : ℂ) := by
    field_simp
    ring
  have hterm : ∀ n ∈ Finset.range N,
      ((N : ℂ) + (h : ℂ)) * ((ArithmeticFunction.vonMangoldt n : ℂ) * (1 - (n : ℂ) / ((N : ℂ) + (h : ℂ)))) =
        (N : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℂ) * (1 - (n : ℂ) / (N : ℂ))) +
          (h : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) := by
    intro n hn
    have hN : (N : ℂ) ≠ 0 := by
      have := Finset.mem_range.mp hn
      exact_mod_cast (by omega : N ≠ 0)
    field_simp
    ring
  rw [mul_add, Finset.mul_sum, mul_add, Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    hlast, Finset.mul_sum]
  ac_rfl

/-- **Saut de pente aux événements premiers** : en tout entier `N ≥ 1`, pour `0 < h < 1`, la pente à droite moins la pente à
gauche de la primitive arithmétique vaut `Λ(N)`. -/
theorem arithmetic_primitive_slope_jump {N : ℕ} (hN : 1 ≤ N) {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    (smoothedMangoldtPrimitive ((N : ℝ) + h) - smoothedMangoldtPrimitive N) / (h : ℂ)
      - (smoothedMangoldtPrimitive N - smoothedMangoldtPrimitive ((N : ℝ) - h)) / (h : ℂ)
      = (ArithmeticFunction.vonMangoldt N : ℂ) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hA := arithmetic_primitive_step (M + 1) h0 h1.le
  have hB := arithmetic_primitive_step M (h := 1 - h) (by linarith) (by linarith)
  have hC := smoothedMangoldtPrimitive_nat_difference M
  have hcast1 : ((M : ℝ) + (1 - h)) = ((M + 1 : ℕ) : ℝ) - h := by push_cast; ring
  have hcast2 : ((M : ℝ) + 1) = ((M + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast1] at hB
  rw [hcast2] at hC
  have hψ : (Chebyshev.psi ((M + 1 : ℕ) : ℝ) : ℂ) - (Chebyshev.psi (M : ℝ) : ℂ) =
      (ArithmeticFunction.vonMangoldt (M + 1) : ℂ) := by
    rw [psi_natCast_eq_sum_range, psi_natCast_eq_sum_range, Finset.sum_range_succ (n := M + 1)]
    ring
  have hh : (h : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  push_cast at hA hB hC hψ ⊢
  rw [div_sub_div_same, div_eq_iff hh]
  linear_combination hA + hB - hC + (h : ℂ) * hψ

/-- Aux événements premiers, le saut de pente de la primitive arithmétique est non nul : l'événement est une propriété du reste
des premiers que ne porte aucune fonction dérivable. -/
theorem primeEvent_slope_jump_ne_zero {N : ℕ} (hN : 1 ≤ N) (hP : PrimeEvent N) {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    (smoothedMangoldtPrimitive ((N : ℝ) + h) - smoothedMangoldtPrimitive N) / (h : ℂ)
      - (smoothedMangoldtPrimitive N - smoothedMangoldtPrimitive ((N : ℝ) - h)) / (h : ℂ) ≠ 0 := by
  rw [arithmetic_primitive_slope_jump hN h0 h1]
  exact_mod_cast hP

/-- **Toute somme finie de composantes est dérivable** en tout `x > 0` : aucune sous-somme finie ne porte un saut de pente ;
l'événement premier appartient à la somme infinie seule. -/
theorem finite_components_differentiableAt {ι : Type*} (Rep : PrimeSignalRepresentation ι) (s : Finset ι) {x : ℝ}
    (hx : 0 < x) :
    DifferentiableAt ℝ (fun y : ℝ => ∑ i ∈ s, Rep.weight i * Perron.f y (Rep.point i)) x := by
  apply DifferentiableAt.fun_sum
  intro i _
  apply DifferentiableAt.const_mul
  show DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) ^ Rep.point i / (Rep.point i * (Rep.point i + 1))) x
  apply DifferentiableAt.div_const
  exact (hasDerivAt_ofReal_cpow_const hx.ne' (Rep.ne_zero i).1).differentiableAt


/-! ## 8. Les trois ingrédients de la loi de mouvement cherchée (texte collé par l'auteur, 2026-10-16)

Proposition recherchée par l'auteur dans les anciens théorèmes de mouvement : « passage vertical depuis ON + fréquence authentique
suivante + rigidité `M^Z = M` ⟹ impossibilité d'une arrivée sous `1/2` », prouvée sans `radial_conservation_anchored`, sans RH, sans le
théorème ouvert. Inventaire des théorèmes compilés dont la conclusion est la position radiale de l'arrivée d'un passage : chacun suppose
soit une propriété de l'arrivée elle-même (`AmplitudeStableSync`, `TowerSymmetric`, `hOnly`, `hSep`, pas de comptage `< 2`), soit RH ou
`PNoRegimeChange`, soit n'est qu'une caractérisation (`vertical_exhausts_iff_arrival_onLine`). Aucun ne conclut depuis les trois
ingrédients seuls. Le théorème ci-dessous dit pourquoi : sur tout passage vertical depuis ON, les trois ingrédients sont ACQUIS avec une
conclusion qui ne mentionne pas la position radiale de l'arrivée, et la liaison `M^Z = M` vaut sur TOUT passage
(`passage_prime_tower_bond`), même de même hauteur (`sameHeight_satisfies_both_rigidities`) ; les obligations de contact sont satisfaites
par toute position radiale dans `]0, 1/2]` (`parameter_grid_admissible`). L'exclusion n'est donc pas compilée indépendamment, et ces trois
ingrédients ne peuvent pas la porter seuls : la loi de mouvement cherchée doit lire autre chose que la succession, la fréquence et la
liaison du premier partagé. -/

/-- **Les trois ingrédients, acquis sur tout passage vertical depuis ON** : fréquence de l'arrivée engendrée par le reste des premiers,
liaison `M^Z = M` au premier partagé (occurrence de l'arrivée = minimum attendu du départ, premier, poids `Λ(M) = log M`, position de
Tour), hauteur qui monte, et `β_l ≤ 1/2`. Aucune de ces conclusions ne lit la position radiale de l'arrivée en dessous d'une demi. -/
theorem movement_law_three_ingredients (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hV : VerticalPassage p)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    ArithmeticFrequency (rZeroHeight p.zLaterMember) ∧
    occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
    Nat.Prime (occurrence ⟨p.zLaterMember, hL⟩) ∧
    ArithmeticFunction.vonMangoldt (occurrence ⟨p.zLaterMember, hL⟩) =
      Real.log (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) ∧
    rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
    rZeroRadialPosition p.zLaterMember ≤ 1 / 2 := by
  obtain ⟨h1, h2, _, h4, _⟩ := passage_prime_tower_bond p hE hL
  have hprof := engaged_passage_profile p hE hL hV hOn
  exact ⟨arithmeticFrequency_of_zero ⟨p.zLaterMember, hL⟩, h1, h2, h4, hV, hprof.2.2.1⟩


/-! ## 9. Loi de compensation entre déplacement vertical et déplacement radial (texte collé par l'auteur, 2026-10-16)

Programme de l'auteur : (1) la progression des premiers impose la fréquence suivante et son point de rencontre attendu ; (2) un
changement de hauteur modifie la géométrie de la Tour ; (3) un changement de position radiale déplace aussi ses contacts et modifie son
amplitude ; (4) la preuve cherchée : ces deux déplacements ne peuvent pas se compenser tout en conservant la rencontre arithmétique
attendue ; (5) si cette impossibilité est déjà compilée indépendamment dans les travaux sur les mouvements, elle ferme le but.

Ce que cette section compile, sans normalisation (les contacts et le point de rencontre sont des abscisses brutes ; aucune
amplitude divisée par `√x` n'entre ici) :
* le déplacement du point de rencontre d'un passage `e → w` depuis un départ sur la ligne se DÉCOMPOSE exactement en une part
  verticale (fonction des deux fréquences seules) et une part radiale (logarithme du facteur radial de `w`) ;
* la part verticale est strictement négative dès que la hauteur monte (la rencontre attendue se rapproche de `1`) : (2) ;
* la part radiale est nulle ⟺ ON, strictement positive ⟺ en dessous d'une demi : (3) ;
* COMPENSATION DE LA RENCONTRE DU DÉPART : `C_0(w) = C_0(e)` ⟺ la part radiale compense exactement la part verticale ; sur un
  passage qui monte, elle exige `β_w < 1/2` : la compensation est le cas bas lui-même, et elle est RÉALISABLE au niveau de la fonction
  de rencontre (pour toute fréquence de départ il existe une fréquence plus haute et une position radiale sous une demi qui rendent le
  même point de rencontre) ; l'impossibilité (4) est donc FAUSSE dans la forme « conserver la rencontre du départ » ;
* CONSERVATION DE LA RENCONTRE ATTENDUE À LA NOUVELLE FRÉQUENCE : `C_0(w) = C_0^ligne(T_w)` ⟺ part radiale nulle ⟺ ON ; c'est la
  forme (4) vraie, et elle est le but lui-même : la loi quantifiée ⟺ RH ;
* côté premiers : `ArithmeticMeeting T (ligne)` ⟺ le déplacement radial de tout signal des premiers de fréquence `T` est nul.
(5) : l'inventaire de la §8 reste valable, aucune impossibilité indépendante n'est compilée ; ce que le compilateur attend, écrit
dans le vocabulaire de la compensation, est : le déplacement radial du signal des premiers à la fréquence du zéro suivant vaut zéro. -/

/-- **Déplacement vertical de la rencontre attendue** : de la fréquence `T` à la fréquence `T'`, le point de rencontre de la ligne
se déplace de `log C_0^ligne(T') − log C_0^ligne(T)`. Fonction des deux fréquences seules. -/
noncomputable def verticalMeetingShift (T T' : ℝ) : ℝ :=
  Real.log (lineContact T' 0) - Real.log (lineContact T 0)

/-- **Déplacement radial de la rencontre d'un signal** : écart logarithmique entre sa rencontre et la position de la ligne à sa
fréquence. Abscisses brutes, aucune normalisation. -/
noncomputable def radialMeetingShift (z : TrueZero) : ℝ :=
  Real.log (contactMinusAt z 0) - Real.log (lineContact (rZeroHeight z.1) 0)

/-- **Déplacement radial d'un signal des premiers** : même écart, écrit sur un point `p` d'une représentation du reste des
premiers, désigné par sa fréquence `|Im p|` seule. -/
noncomputable def arithmeticRadialShift (p : ℂ) : ℝ :=
  Real.log (meetingOf p) - Real.log (lineContact |p.im| 0)

theorem verticalMeetingShift_eq (T T' : ℝ) :
    verticalMeetingShift T T' = Real.arctan (2 * T') / T' - Real.arctan (2 * T) / T := by
  have h2 : ∀ S : ℝ, S / (1 / 2) = 2 * S := fun S => by ring
  unfold verticalMeetingShift lineContact linePhase
  rw [Real.log_exp, Real.log_exp]
  simp only [Int.cast_zero, zero_mul, add_zero, h2]

/-- La part radiale est le logarithme du facteur radial. -/
theorem radialMeetingShift_eq_log_radialFactor (z : TrueZero) :
    radialMeetingShift z = Real.log (radialFactor z) := by
  unfold radialMeetingShift
  rw [contact_eq_line_mul_radial, Real.log_mul (lineContact_pos _ _).ne' (radialFactor_pos z).ne']
  ring

/-- (3) Un déplacement radial en dessous d'une demi translate la rencontre vers l'extérieur. -/
theorem radialMeetingShift_pos_iff (z : TrueZero) :
    0 < radialMeetingShift z ↔ rZeroRadialPosition z.1 < 1 / 2 := by
  rw [radialMeetingShift_eq_log_radialFactor, Real.log_pos_iff (radialFactor_pos z).le]
  exact radialFactor_gt_one_iff z

/-- (3) Aucun déplacement radial de la rencontre ⟺ signal sur la ligne. -/
theorem radialMeetingShift_eq_zero_iff (z : TrueZero) :
    radialMeetingShift z = 0 ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  rw [radialMeetingShift_eq_log_radialFactor, ← radialFactor_eq_one_iff]
  constructor
  · intro h
    have := Real.exp_log (radialFactor_pos z)
    rw [h, Real.exp_zero] at this
    exact this.symm
  · intro h
    rw [h, Real.log_one]

/-- **Décomposition exacte du déplacement de la rencontre sur un passage parti de la ligne** : part verticale (fréquences
seules) + part radiale de l'arrivée. -/
theorem meeting_shift_decomposed (e w : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2) :
    Real.log (contactMinusAt w 0) - Real.log (contactMinusAt e 0) =
      verticalMeetingShift (rZeroHeight e.1) (rZeroHeight w.1) + radialMeetingShift w := by
  rw [(meeting_on_line_iff e).mpr he]
  unfold verticalMeetingShift radialMeetingShift
  ring

/-- `arctan v / v < arctan u / u` pour `0 < u < v` (valeur moyenne appliquée deux fois). -/
theorem arctan_div_strictAnti {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    Real.arctan v / v < Real.arctan u / u := by
  have hv : 0 < v := hu.trans huv
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.arctan (fun x => 1 / (1 + x ^ 2)) hu
    Real.continuous_arctan.continuousOn (fun x _ => Real.hasDerivAt_arctan x)
  obtain ⟨d, hd, hdd⟩ := exists_hasDerivAt_eq_slope Real.arctan (fun x => 1 / (1 + x ^ 2)) huv
    Real.continuous_arctan.continuousOn (fun x _ => Real.hasDerivAt_arctan x)
  rw [Real.arctan_zero, sub_zero, sub_zero] at hcd
  have h1 : u / (1 + u ^ 2) < Real.arctan u := by
    have hcu : c < u := hc.2
    have hc0 : 0 < c := hc.1
    have hlt : u / (1 + u ^ 2) < u / (1 + c ^ 2) := by
      apply div_lt_div_of_pos_left hu (by positivity)
      nlinarith
    calc u / (1 + u ^ 2) < u / (1 + c ^ 2) := hlt
      _ = u * (1 / (1 + c ^ 2)) := by ring
      _ = Real.arctan u := by rw [hcd]; field_simp
  have h2 : Real.arctan v - Real.arctan u < (v - u) / (1 + u ^ 2) := by
    have hud : u < d := hd.1
    have hlt : (v - u) / (1 + d ^ 2) < (v - u) / (1 + u ^ 2) := by
      apply div_lt_div_of_pos_left (by linarith) (by positivity)
      nlinarith
    have hvu : v - u ≠ 0 := by linarith
    calc Real.arctan v - Real.arctan u = (v - u) * (1 / (1 + d ^ 2)) := by
          rw [hdd]; field_simp
      _ = (v - u) / (1 + d ^ 2) := by ring
      _ < (v - u) / (1 + u ^ 2) := hlt
  rw [div_lt_div_iff₀ hv hu]
  have h3 : u * (Real.arctan v - Real.arctan u) < (v - u) * Real.arctan u := by
    calc u * (Real.arctan v - Real.arctan u) < u * ((v - u) / (1 + u ^ 2)) :=
          mul_lt_mul_of_pos_left h2 hu
      _ = (v - u) * (u / (1 + u ^ 2)) := by ring
      _ < (v - u) * Real.arctan u := mul_lt_mul_of_pos_left h1 (by linarith)
  nlinarith

/-- (2) **Un changement de hauteur déplace la rencontre attendue** : la part verticale est strictement négative dès que la
hauteur monte. -/
theorem verticalMeetingShift_neg {T T' : ℝ} (hT : 0 < T) (hTT' : T < T') : verticalMeetingShift T T' < 0 := by
  rw [verticalMeetingShift_eq]
  have h := arctan_div_strictAnti (u := 2 * T) (v := 2 * T') (by linarith) (by linarith)
  have e1 : Real.arctan (2 * T') / T' = 2 * (Real.arctan (2 * T') / (2 * T')) := by
    field_simp
  have e2 : Real.arctan (2 * T) / T = 2 * (Real.arctan (2 * T) / (2 * T)) := by
    field_simp
  rw [e1, e2]
  linarith

/-- (2) La rencontre attendue à la nouvelle fréquence est strictement en deçà de la rencontre du départ. -/
theorem expected_meeting_moves_inward {T T' : ℝ} (hT : 0 < T) (hTT' : T < T') :
    lineContact T' 0 < lineContact T 0 := by
  have h := verticalMeetingShift_neg hT hTT'
  unfold verticalMeetingShift at h
  exact (Real.log_lt_log_iff (lineContact_pos _ _) (lineContact_pos _ _)).mp (by linarith)

/-- **Compensation de la rencontre du départ** : sur un passage parti de la ligne, la rencontre de l'arrivée coïncide avec celle
du départ ⟺ la part radiale compense exactement la part verticale. -/
theorem meeting_compensation_iff (e w : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2) :
    contactMinusAt w 0 = contactMinusAt e 0 ↔
      radialMeetingShift w = - verticalMeetingShift (rZeroHeight e.1) (rZeroHeight w.1) := by
  have hd := meeting_shift_decomposed e w he
  constructor
  · intro h
    rw [h, sub_self] at hd
    linarith
  · intro h
    have h0 : Real.log (contactMinusAt w 0) = Real.log (contactMinusAt e 0) := by linarith
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (contactMinusAt_positive w 0))
      (Set.mem_Ioi.mpr (contactMinusAt_positive e 0)) h0

/-- **La compensation est le cas bas** : sur un passage qui monte depuis la ligne, conserver la rencontre du départ exige une
arrivée en dessous d'une demi. -/
theorem meeting_compensation_requires_low (e w : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2)
    (hT : rZeroHeight e.1 < rZeroHeight w.1) (h : contactMinusAt w 0 = contactMinusAt e 0) :
    rZeroRadialPosition w.1 < 1 / 2 := by
  rw [← radialMeetingShift_pos_iff, (meeting_compensation_iff e w he).mp h]
  have hv := verticalMeetingShift_neg (T := rZeroHeight e.1) (T' := rZeroHeight w.1) e.2 hT
  linarith

/-- **Conservation de la rencontre attendue à la nouvelle fréquence ⟺ déplacement radial nul** (forme (4) vraie : c'est le but). -/
theorem expected_meeting_iff_radial_shift_zero (w : TrueZero) :
    contactMinusAt w 0 = lineContact (rZeroHeight w.1) 0 ↔ radialMeetingShift w = 0 := by
  unfold radialMeetingShift
  constructor
  · intro h; rw [h, sub_self]
  · intro h
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (contactMinusAt_positive w 0))
      (Set.mem_Ioi.mpr (lineContact_pos _ _)) (by linarith)

/-- **La compensation de la rencontre du départ est réalisable pour la fonction de rencontre** : pour toute fréquence `T` et toute
fréquence `T'` plus haute assez proche, il existe une position radiale strictement sous une demi dont le signal de fréquence `T'`
rencontre l'axe exactement au point de rencontre de la ligne à la fréquence `T`. Énoncé sur la fonction `meetingOf` d'un point du
plan, aucun zéro n'est fabriqué : il dit que l'impossibilité (4) est fausse sous la forme « conserver la rencontre du départ ». -/
theorem meeting_compensation_realizable {T T' : ℝ} (hT : 0 < T) (hTT' : T < T')
    (hsmall : T' * (Real.arctan (2 * T) / T) < Real.pi / 2) :
    ∃ β : ℝ, 0 < β ∧ β < 1 / 2 ∧ meetingOf ⟨β, T'⟩ = lineContact T 0 := by
  have hT' : 0 < T' := hT.trans hTT'
  set θ := T' * (Real.arctan (2 * T) / T) with hθ
  have ha : 0 < Real.arctan (2 * T) := Real.arctan_pos.mpr (by linarith)
  have hθpos : 0 < θ := by positivity
  have htan : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθpos hsmall
  refine ⟨T' / Real.tan θ, by positivity, ?_, ?_⟩
  · -- `β < 1/2 ⟺ 2T' < tan θ ⟺ arctan(2T') < θ`
    rw [div_lt_iff₀ htan]
    have hlt : Real.arctan (2 * T') < θ := by
      have h := arctan_div_strictAnti (u := 2 * T) (v := 2 * T') (by linarith) (by linarith)
      have e1 : Real.arctan (2 * T') = T' * (2 * (Real.arctan (2 * T') / (2 * T'))) := by
        field_simp
      have e2 : θ = T' * (2 * (Real.arctan (2 * T) / (2 * T))) := by
        rw [hθ]; field_simp
      rw [e1, e2]
      exact mul_lt_mul_of_pos_left (by linarith) hT'
    have := Real.tan_lt_tan_of_lt_of_lt_pi_div_two (Real.neg_pi_div_two_lt_arctan _) hsmall hlt
    rw [Real.tan_arctan] at this
    linarith
  · unfold meetingOf lineContact linePhase
    simp only [Int.cast_zero, zero_mul, add_zero]
    congr 1
    have hdiv : T' / (T' / Real.tan θ) = Real.tan θ := by
      field_simp
    rw [hdiv, Real.arctan_tan (by linarith) hsmall, hθ]
    field_simp

/-- **Pour toute fréquence de départ il existe une fréquence plus haute où la compensation est réalisable** : l'impossibilité (4)
n'est pas un théorème de la fonction de rencontre dans la forme « conserver la rencontre du départ ». -/
theorem exists_compensating_frequency {T : ℝ} (hT : 0 < T) :
    ∃ T' : ℝ, T < T' ∧ ∃ β : ℝ, 0 < β ∧ β < 1 / 2 ∧ meetingOf ⟨β, T'⟩ = lineContact T 0 := by
  set a := Real.arctan (2 * T) with ha
  have ha0 : 0 < a := Real.arctan_pos.mpr (by linarith)
  have ha1 : a < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hr : 1 < (Real.pi / 2 + a) / (2 * a) := by
    rw [one_lt_div (by positivity)]; linarith
  refine ⟨T * ((Real.pi / 2 + a) / (2 * a)), lt_mul_of_one_lt_right hT hr, ?_⟩
  apply meeting_compensation_realizable hT (lt_mul_of_one_lt_right hT hr)
  have : T * ((Real.pi / 2 + a) / (2 * a)) * (a / T) = (Real.pi / 2 + a) / 2 := by
    field_simp
  rw [← ha, this]
  linarith

/-- Le déplacement radial du point d'un zéro est son déplacement radial de rencontre. -/
theorem arithmeticRadialShift_zeroPoint (z : TrueZero) :
    arithmeticRadialShift (zeroPoint z) = radialMeetingShift z := by
  have hpos : 0 < (zeroPoint z).im := by rw [zeroPoint_im]; exact z.2
  unfold arithmeticRadialShift radialMeetingShift
  rw [contactMinusAt_eq_meetingOf, abs_of_pos hpos, zeroPoint_im]

/-- **Côté premiers : la rencontre arithmétique à la position de la ligne ⟺ déplacement radial nul de tout signal des premiers de
fréquence `T`.** C'est ce que le compilateur attend, écrit dans le vocabulaire de la compensation. -/
theorem arithmeticMeeting_iff_radial_shift_zero (T : ℝ) :
    ArithmeticMeeting T (lineContact T 0) ↔
      ∀ Rep : PrimeSignalRepresentation ExplicitIndex, ∀ i, Rep.weight i ≠ 0 → |(Rep.point i).im| = T →
        arithmeticRadialShift (Rep.point i) = 0 := by
  refine forall_congr' fun Rep => forall_congr' fun i => imp_congr_right fun _ => imp_congr_right fun hT => ?_
  unfold arithmeticRadialShift
  rw [hT]
  constructor
  · intro h; rw [h, sub_self]
  · intro h
    have hm : 0 < meetingOf (Rep.point i) := Real.exp_pos _
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr hm)
      (Set.mem_Ioi.mpr (lineContact_pos _ _)) (by linarith)

/-- **Fermeture par la loi de compensation** : un signal d'amplitude strictement décroissante le long des premiers dont le
déplacement radial de rencontre est nul est exclu. -/
theorem compensation_law_closes (w : TrueZero)
    (hDecr : ∀ x y : ℝ, 1 ≤ x → x < y → pairAmplitude w y < pairAmplitude w x)
    (h : radialMeetingShift w = 0) : False :=
  frequencyTaken_closes w hDecr
    (frequencyTaken_of_meeting_on_line w ((expected_meeting_iff_radial_shift_zero w).mpr h))

/-- **La loi « aucun déplacement radial de rencontre » quantifiée sur tous les signaux ⟺ RH.** -/
theorem no_radial_shift_law_iff_riemannHypothesis :
    (∀ z : TrueZero, radialMeetingShift z = 0) ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_noLowerSide]
  constructor
  · intro h z hlt
    have := (radialMeetingShift_eq_zero_iff z).mp (h z)
    linarith
  · intro h z
    exact (radialMeetingShift_eq_zero_iff z).mpr (only_low_candidate h z)

#print axioms radial_from_meeting
#print axioms radial_from_need_ratio
#print axioms meeting_below_iff_low
#print axioms singleSignal_iff_meetingOnLine
#print axioms meeting_shift_detects
#print axioms meeting_shift_blind
#print axioms noMeetingBelow_iff_riemannHypothesis
#print axioms frequencyTaken_of_meeting_on_line
#print axioms primeTrueRepresentation
#print axioms contactMinusAt_eq_meetingOf
#print axioms lineContact_eq_meetingOf
#print axioms arithmeticFrequency_iff
#print axioms arithmeticMeeting_iff_meetingOnLine
#print axioms arithmetic_meeting_beyond_line_iff_low
#print axioms arithmeticMeeting_law_iff_riemannHypothesis
#print axioms frequencyTaken_of_arithmeticMeeting
#print axioms collectiveMeeting_component_eq_neg_rest
#print axioms arithmetic_primitive_slope_jump
#print axioms primeEvent_slope_jump_ne_zero
#print axioms finite_components_differentiableAt
#print axioms movement_law_three_ingredients
#print axioms arctan_div_strictAnti
#print axioms verticalMeetingShift_neg
#print axioms meeting_shift_decomposed
#print axioms meeting_compensation_iff
#print axioms meeting_compensation_requires_low
#print axioms expected_meeting_iff_radial_shift_zero
#print axioms meeting_compensation_realizable
#print axioms exists_compensating_frequency
#print axioms arithmeticMeeting_iff_radial_shift_zero
#print axioms compensation_law_closes
#print axioms no_radial_shift_law_iff_riemannHypothesis

/-! ## 10. Non-compensation et amplitude imposée (2026-10-16)

Pivot : le reste des autres vrais zéros n'est pas un degré de liberté. La courbe des premiers (`smoothedRemainder`) est la
somme exacte de TOUS les vrais zéros (sommabilité absolue démontrée) ; la contribution d'un vrai zéro `z` est donc la courbe
moins la somme FIXE des contributions de tous les autres (`imposed_contribution_eq`). Aucun remplacement ne reconstruit
(`imposed_contribution_unique`). Sur un écart premier, l'amplitude de la contribution imposée à `z` varie de `e^{β_z L_r}`,
identité vraie pour tout `β_z` (`imposed_contribution_drift`) : la présence et l'unicité sont imposées, la VALEUR de `β_z`
n'est pas lue par ces identités. Aucun point synthétique : tout porte sur `z : TrueZero`. -/

/-- Somme des contributions lissées de tous les AUTRES vrais zéros que `z`, à l'abscisse `x`. -/
noncomputable def othersSum (z : TrueZero) (x : ℝ) : ℂ :=
  ∑' σ : ExplicitIndex, if σ = memberIndex z then 0 else nontrivialZeroResidueTerm x σ

/-- **La contribution d'un vrai zéro est imposée** : terme lissé de `z` = reste des premiers − somme des autres vrais zéros. -/
theorem imposed_contribution_eq (z : TrueZero) {x : ℝ} (hx : 1 < x) :
    nontrivialZeroResidueTerm x (memberIndex z) = smoothedRemainder x - othersSum z x := by
  rw [smoothedRemainder_eq_tsum_residueTerm hx,
    (nontrivial_zero_residue_series_summable hx).tsum_eq_add_tsum_ite (memberIndex z)]
  unfold othersSum
  ring

/-- **Forme incrémentale sur un écart** `1 < a < b` : l'incrément de la contribution de `z` est l'incrément du reste moins
celui des autres vrais zéros. -/
theorem imposed_contribution_increment (z : TrueZero) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    nontrivialZeroResidueTerm b (memberIndex z) - nontrivialZeroResidueTerm a (memberIndex z) =
      (smoothedRemainder b - smoothedRemainder a) - (othersSum z b - othersSum z a) := by
  rw [imposed_contribution_eq z ha, imposed_contribution_eq z hb]
  ring

/-- **Unicité de la contribution imposée** : aucun remplacement du point de `z` (point `ρ' ≠ ρ`, partie réelle `≤ 1`, hauteur
positive), en particulier aucun changement d'amplitude à fréquence fixée, ne reconstruit le reste des premiers. Instance de
`replacement_not_reconstruct` sur le vrai zéro (multiplicité `> 0` démontrée). -/
theorem imposed_contribution_unique (z : TrueZero) {ρ' : ℂ} (hne : ρ' ≠ zeroPoint z) (hre' : ρ'.re ≤ 1)
    (him' : 0 < ρ'.im) {p : ℕ} (hp : 1 ≤ p) :
    ∃ x : ℝ, 1 < x ∧
      ¬ Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo (smoothedCanonicalAt x) p
        (-pointSmoothedPairContribution (zetaZeroMultiplicity (zeroPoint z)) (zeroPoint z) x)
        (pointSmoothedPairContribution (zetaZeroMultiplicity (zeroPoint z)) ρ' x) (j + 1))
        Filter.atTop (nhds (normalizedSmoothedRemainder x)) :=
  replacement_not_reconstruct hne (explicitIndex_re_le_one (memberIndex z)) hre' (by rw [zeroPoint_im]; exact z.2) him'
    (zetaZeroMultiplicity_pos (zeroPoint_isNontrivial z).1) hp

/-- Cas du changement d'amplitude à fréquence fixée, pour le vrai zéro `z` (`δ` réel non nul). -/
theorem imposed_amplitude_change_unique (z : TrueZero) {δ : ℝ} (hδ : δ ≠ 0)
    (hre' : (zeroPoint z).re + δ ≤ 1) {p : ℕ} (hp : 1 ≤ p) :
    ∃ x : ℝ, 1 < x ∧
      ¬ Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo (smoothedCanonicalAt x) p
        (-pointSmoothedPairContribution (zetaZeroMultiplicity (zeroPoint z)) (zeroPoint z) x)
        (pointSmoothedPairContribution (zetaZeroMultiplicity (zeroPoint z)) (zeroPoint z + δ) x) (j + 1))
        Filter.atTop (nhds (normalizedSmoothedRemainder x)) :=
  amplitude_change_not_reconstruct (ρ := zeroPoint z) hδ (explicitIndex_re_le_one (memberIndex z)) hre' (by rw [zeroPoint_im]; exact z.2)
    (zetaZeroMultiplicity_pos (zeroPoint_isNontrivial z).1) hp

/-- Module de la contribution lissée de `z` sur deux abscisses `0 < p`, `0 < q` : rapport = rapport des modules bruts. -/
theorem residueTerm_norm_ratio (z : TrueZero) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ‖nontrivialZeroResidueTerm q (memberIndex z)‖ / ‖nontrivialZeroResidueTerm p (memberIndex z)‖ =
      ‖zeroTerm z q‖ / ‖zeroTerm z p‖ := by
  rw [residueTerm_norm, residueTerm_norm]
  have hm : (0 : ℝ) < zetaZeroMultiplicity (zeroPoint z) := by
    exact_mod_cast zetaZeroMultiplicity_pos (zeroPoint_isNontrivial z).1
  have hN : 0 < ‖zeroPoint z + 1‖ := by
    rw [norm_pos_iff]; intro h
    have := congrArg Complex.re h
    simp at this
    have := zeroPoint_re_pos z
    linarith
  have hzp : 0 < ‖zeroTerm z p‖ := by
    rw [norm_zeroTerm_eq z hp]
    have := norm_zeroPoint_pos z
    positivity
  field_simp

/-- **Dérive de la contribution imposée sur un écart premier** : le module de la contribution imposée à `z` (reste des
premiers moins somme des autres vrais zéros) varie de `e^{β_z L_r}` de `p_r` à son successeur ; la version normalisée de
`z` varie de `e^{(β_z − 1/2) L_r}`. Identité vraie pour toute position radiale de `z` : elle compose l'imposition (a), le
pas d'amplitude par écart et le rapport de besoin ; elle ne fixe pas `β_z`. -/
theorem imposed_contribution_drift (z : TrueZero) (r : ℕ) :
    ‖smoothedRemainder (fnPrimeSuccessor r : ℝ) - othersSum z (fnPrimeSuccessor r : ℝ)‖ /
        ‖smoothedRemainder (fnPrimeAtRank r : ℝ) - othersSum z (fnPrimeAtRank r : ℝ)‖ =
      Real.exp (rZeroRadialPosition z.1 * rPrimeGapLogRatio r) ∧
    pairAmplitude z (fnPrimeSuccessor r : ℝ) / pairAmplitude z (fnPrimeAtRank r : ℝ) =
      Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * rPrimeGapLogRatio r) := by
  have h0 : (0 : ℝ) < (fnPrimeAtRank r : ℝ) := by exact_mod_cast thm_primeAtRank_pos r
  have h1 : (0 : ℝ) < (fnPrimeSuccessor r : ℝ) := by
    unfold fnPrimeSuccessor; exact_mod_cast thm_primeAtRank_pos _
  have h01 : (1 : ℝ) < (fnPrimeAtRank r : ℝ) := by
    exact_mod_cast (thm_primeAtRank_isPrime r).one_lt
  have h11 : (1 : ℝ) < (fnPrimeSuccessor r : ℝ) := by
    unfold fnPrimeSuccessor; exact_mod_cast (thm_primeAtRank_isPrime _).one_lt
  refine ⟨?_, pairAmplitude_prime_step z r⟩
  rw [← imposed_contribution_eq z h01, ← imposed_contribution_eq z h11,
    residueTerm_norm_ratio z h0 h1, rawAmplitude_prime_step]

#print axioms imposed_contribution_eq
#print axioms imposed_contribution_increment
#print axioms imposed_contribution_unique
#print axioms imposed_amplitude_change_unique
#print axioms imposed_contribution_drift


/-! ## 11. La fréquence lue sur la rencontre d'un signal sous un demi (auteur, 2026-10-16)

Demande de l'auteur : « démontrer que les zéros hors de la ligne doivent nécessairement avoir une hauteur au-dessus de la hauteur
attendue si `β < 1/2`, donc grandissent forcément trop vite par rapport à la fréquence attendue ; zêta est une somme, y revenir et
compiler cela ». Chaque terme de la somme (formule explicite : la courbe des premiers est la somme des signaux des vrais zéros) a deux
lectures de sa fréquence : la fréquence propre (vitesse de rotation, espacement des rencontres) et la fréquence que la ligne
attribue à sa première rencontre (la hauteur d'un signal de la ligne qui rencontrerait l'axe au même point). Abscisses brutes, aucune
normalisation. Ce que la section établit, pour tout point du plan (aucun zéro fabriqué) :
* sous un demi, la fréquence attendue lue sur la rencontre est STRICTEMENT PLUS BASSE que la fréquence propre : le signal est
  au-dessus de la hauteur attendue (`low_meeting_reads_lower_frequency`) ;
* sur la ligne, les deux lectures coïncident (`line_meeting_reads_own_frequency`) ;
* l'écart de phase entre le signal et le signal attendu croît sans borne le long de l'axe : le signal tourne trop vite
  (`phase_gap_unbounded`) ;
* instance sur un vrai zéro (`zero_low_meeting_reads_lower_frequency`).
Portée : caractérisation (sous un demi ⟹ désaccord des deux lectures ; sur la ligne ⟹ accord) ; elle ne dit pas lequel des deux cas
la courbe des premiers impose. -/

/-- Sous un demi, la rencontre propre est au-delà de celle de la ligne à la même fréquence. -/
theorem arctan_low_gt_line {β T : ℝ} (hβ0 : 0 < β) (hβ : β < 1 / 2) (hT : 0 < T) :
    Real.arctan (2 * T) / T < Real.arctan (T / β) / T := by
  apply div_lt_div_of_pos_right _ hT
  apply Real.arctan_strictMono
  rw [lt_div_iff₀ hβ0]
  nlinarith

/-- **Sous un demi, la fréquence attendue lue sur la rencontre est plus basse que la fréquence propre** : si un signal de point
`p` (`0 < Re p < 1/2`, `Im p > 0`) rencontre l'axe exactement là où le signal de la ligne de fréquence `T'` le rencontre, alors
`T' < Im p` : le signal est AU-DESSUS de la hauteur que sa rencontre attend. -/
theorem low_meeting_reads_lower_frequency {p : ℂ} {T' : ℝ} (hβ0 : 0 < p.re) (hβ : p.re < 1 / 2) (hT : 0 < p.im)
    (hT' : 0 < T') (h : meetingOf p = lineContact T' 0) : T' < p.im := by
  rw [lineContact_eq_meetingOf] at h
  unfold meetingOf at h
  have h' := Real.exp_injective h
  simp only at h'
  have hl : Real.arctan (T' / (1 / 2)) = Real.arctan (2 * T') := by congr 1; field_simp
  rw [hl] at h'
  by_contra hle
  push Not at hle
  have hlow := arctan_low_gt_line hβ0 hβ hT
  rcases hle.lt_or_eq with hlt | heq
  · have hanti := arctan_div_strictAnti (u := 2 * p.im) (v := 2 * T') (by linarith) (by linarith)
    have e1 : Real.arctan (2 * T') / T' = 2 * (Real.arctan (2 * T') / (2 * T')) := by field_simp
    have e2 : Real.arctan (2 * p.im) / p.im = 2 * (Real.arctan (2 * p.im) / (2 * p.im)) := by field_simp
    linarith
  · rw [← heq] at h'
    linarith

/-- **Sur la ligne, la fréquence attendue lue sur la rencontre est la fréquence propre.** -/
theorem line_meeting_reads_own_frequency {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (h : lineContact T 0 = lineContact T' 0) : T' = T := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := expected_meeting_moves_inward hT' hlt
    linarith
  · have := expected_meeting_moves_inward hT hgt
    linarith

/-- **Le signal tourne trop vite** : dès que la fréquence propre dépasse la fréquence attendue, l'écart de phase entre le signal et
le signal attendu dépasse toute borne le long de l'axe. -/
theorem phase_gap_unbounded {T T' : ℝ} (h : T' < T) (M : ℝ) : ∃ x : ℝ, 1 < x ∧ M < (T - T') * Real.log x := by
  have hd : 0 < T - T' := by linarith
  refine ⟨Real.exp (max (M / (T - T')) 0 + 1), ?_, ?_⟩
  · have := le_max_right (M / (T - T')) 0
    exact Real.one_lt_exp_iff.mpr (by linarith)
  · rw [Real.log_exp]
    have h1 := le_max_left (M / (T - T')) 0
    have h2 : M / (T - T') * (T - T') = M := by field_simp
    nlinarith

/-- **Instance sur un vrai zéro** : un vrai zéro sous un demi est au-dessus de toute fréquence de la ligne qui partage sa
rencontre, et son écart de phase avec le signal de cette fréquence croît sans borne. -/
theorem zero_low_meeting_reads_lower_frequency (z : TrueZero) (hβ : rZeroRadialPosition z.1 < 1 / 2) {T' : ℝ}
    (hT' : 0 < T') (h : lineContact T' 0 = contactMinusAt z 0) :
    T' < rZeroHeight z.1 ∧ ∀ M : ℝ, ∃ x : ℝ, 1 < x ∧ M < (rZeroHeight z.1 - T') * Real.log x := by
  have hlt : T' < rZeroHeight z.1 := by
    have := low_meeting_reads_lower_frequency (p := zeroPoint z) (zeroPoint_re_pos z)
      (by rw [zeroPoint_re]; exact hβ) (by rw [zeroPoint_im]; exact z.2) hT'
      (by rw [← contactMinusAt_eq_meetingOf]; exact h.symm)
    rwa [zeroPoint_im] at this
  exact ⟨hlt, phase_gap_unbounded hlt⟩

#print axioms low_meeting_reads_lower_frequency
#print axioms line_meeting_reads_own_frequency
#print axioms phase_gap_unbounded
#print axioms zero_low_meeting_reads_lower_frequency


/-! ## 12. Synchronisation conjointe sur chaque écart premier : fréquence, rencontres, amplitude (auteur, 2026-10-17)

Demande de l'auteur : « la synchronisation doit porter sur trois éléments indissociables : la fréquence, les points de rencontre
et l'amplitude, pour chaque Tour et chaque écart premier ; aucun des trois ne doit être oublié ni remplacé par un autre » ;
« composer les résultats existants, identifier la seule implication réellement manquante, la minimiser et tenter de la
démontrer ». Canal LISSÉ (celui où la loi par écart est démontrée), abscisses brutes, aucune normalisation, aucun zéro fabriqué.

* **Objet conjoint** (`jointTerm`, `memberJoint`) : la contribution lissée exacte d'un vrai zéro est, sans perte,
  `−m · (x^β / (‖ρ‖‖ρ + 1‖)) · e^{i(T log x − θ_s)}` (`residueTerm_joint`, forme polaire `point_polar`, `cpow_polar`) : amplitude
  `x^β`, fréquence `T`, calage `θ_s = arg ρ + arg(ρ + 1)` (`smoothingPhase`) ; ce sont ses seuls paramètres.
* **Loi conjointe sur un écart** (`memberJoint_gap_step`) : de `p_n` à `p_{n+1}`, la contribution est multipliée par `e^{β L_n}`
  et tourne de `T L_n` ; amplitude et fréquence dans un seul facteur, calage conservé.
* **Rencontres du terme lissé** (`smoothedMeeting`) : la contribution y est réelle (`residueTerm_real_at_smoothedMeeting`) ;
  elles sont les rencontres brutes multipliées par `exp(arctan(T/(β + 1))/T)` (`smoothedMeeting_eq_contact`), espacées de `π/T`
  (`smoothedMeeting_spacing`) ; elles sont celles de la ligne ⟺ `β = 1/2` (`smoothedMeeting_line_iff`).
* **Synchronisation conjointe** (`prime_gap_joint_synchronization`) : sur chaque écart, l'incrément de la courbe des premiers est
  la somme des contributions conjointes de TOUS les vrais zéros ; celle d'un vrai zéro est imposée (`imposed_joint_gap`).
* **Désaccord conjoint, écart par écart** (`low_joint_deviation_every_gap`, `mirror_joint_deviation_every_gap`) : sous un demi,
  par rapport au signal de la ligne qui partage sa première rencontre, excès de phase positif sur chaque écart et cumul non borné
  (`primeGap_log_telescope`, `primeGap_log_unbounded`), rencontres brutes et lissées décalées, enveloppe décroissante ; le miroir :
  même fréquence, rencontres en deçà, enveloppe croissante `e^{(1/2 − β) L_n} > 1` sur chaque écart. Caractérisations.
* **Forme de fermeture à un seul écart** (`ImposedNotFasterAtGap`, `ImposedOnScaleAtGap`) : sur UN écart, la contribution
  imposée au miroir ne grandit pas plus vite que l'échelle commune ⟹ contradiction (`mirror_not_faster_closes`). STATUT EXACT
  (revue du 2026-10-17) : ce n'est PAS une réduction. Le rapport imposé sur un écart vaut l'identité `e^{β L_n}`
  (`imposedNotFasterAtGap_iff`) : la forme équivaut à `β_{w*} ≤ 1/2`, c'est-à-dire à `β_w ≥ 1/2`, la conclusion elle-même réécrite ;
  elle n'est pas « plus arithmétique » : elle contient la somme de tous les autres vrais zéros (`othersSum`). Énoncée pour tous les
  vrais zéros, elle est équivalente à RH (`notFaster_law_iff_riemannHypothesis`). La seule forme écrite avec les premiers seuls
  reste la borne d'exposant `< 1 − β_w` du reste lissé (`hAbsurdCloses` dans la chaîne), de la nature d'une bande sans zéro. Ce qui
  manque : une information sur la taille de la contribution imposée sur un écart qui ne passe pas par `β`.
* **Entrée de la matrice** (`gapPhase`, `gapEnvelope`, `gap_entry_joint`, `gapEnvelope_eq_raw`,
  `at_most_one_meeting_in_short_gap`) : contribution exacte d'un indice à un écart = phase et enveloppe aux deux bornes ; enveloppe
  lissée = module exact du terme lissé (conversion de canal vers `x^β/‖ρ‖` par `residueTerm_norm`) ; un écart plus court qu'un
  demi-tour contient au plus une rencontre lissée. -/

section JointGap
open Complex

theorem point_polar (p : ℂ) (h : 0 < p.re) :
    p = (‖p‖ : ℂ) * Complex.exp ((Real.arctan (p.im / p.re) : ℂ) * I) := by
  set t := p.im / p.re with ht
  set c := Real.cos (Real.arctan t) with hcdef
  set s := Real.sin (Real.arctan t) with hsdef
  have hc : 0 < c := Real.cos_arctan_pos t
  have hs : s = c * t := by
    have h1 := Real.tan_arctan t
    rw [Real.tan_eq_sin_div_cos] at h1
    have h1' : s / c = t := h1
    rw [div_eq_iff hc.ne'] at h1'
    linarith
  have hcs : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hn2 : ‖p‖ ^ 2 = p.re ^ 2 + p.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 : c ^ 2 * (p.re ^ 2 + p.im ^ 2) = p.re ^ 2 := by
    rw [hs, ht] at hcs
    field_simp at hcs
    nlinarith [hcs]
  have hnc : ‖p‖ * c = p.re := by
    have hsq : (‖p‖ * c) ^ 2 = p.re ^ 2 := by rw [mul_pow, hn2]; linarith [h1]
    have hpos : 0 ≤ ‖p‖ * c := by positivity
    nlinarith [sq_nonneg (‖p‖ * c - p.re), sq_nonneg (‖p‖ * c + p.re)]
  have hns : ‖p‖ * s = p.im := by
    rw [hs, ← mul_assoc, hnc, ht]; field_simp
  apply Complex.ext
  · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]; exact hnc.symm
  · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]; exact hns.symm

theorem cpow_polar (p : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ p = ((x ^ p.re : ℝ) : ℂ) * Complex.exp (((p.im * Real.log x : ℝ) : ℂ) * I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le,
    Real.rpow_def_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  conv_lhs => rw [← Complex.re_add_im p]
  push_cast; ring

/-- Phase de calage du terme lissé : `arg ρ + arg(ρ + 1)`. -/
noncomputable def smoothingPhase (p : ℂ) : ℝ :=
  Real.arctan (p.im / p.re) + Real.arctan (p.im / (p.re + 1))

/-- Contribution conjointe : amplitude `x^β/N`, fréquence `T`, calage `θ`, multiplicité `m`. -/
noncomputable def jointTerm (m β T θ N x : ℝ) : ℂ :=
  -(m : ℂ) * ((x ^ β / N : ℝ) : ℂ) * Complex.exp (((T * Real.log x - θ : ℝ) : ℂ) * I)

theorem residueTerm_joint (σ : ExplicitIndex) {x : ℝ} (hx : 0 < x) :
    nontrivialZeroResidueTerm x σ =
      jointTerm (zetaZeroMultiplicity (σ : ℂ)) (σ : ℂ).re (σ : ℂ).im (smoothingPhase σ)
        (‖(σ : ℂ)‖ * ‖(σ : ℂ) + 1‖) x := by
  obtain ⟨h0, h1⟩ := explicitIndex_ne_zero σ
  have hre := (isNontrivialZetaZero_re_mem_Ioo σ.property).1
  have hP1 := point_polar (σ : ℂ) hre
  have hP2 := point_polar ((σ : ℂ) + 1) (by simp; linarith)
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, add_zero] at hP2
  have hden : (σ : ℂ) * ((σ : ℂ) + 1) =
      ((‖(σ : ℂ)‖ * ‖(σ : ℂ) + 1‖ : ℝ) : ℂ) * Complex.exp (((smoothingPhase σ : ℝ) : ℂ) * I) := by
    have hA : (σ : ℂ) * ((σ : ℂ) + 1) =
        ((‖(σ : ℂ)‖ : ℂ) * Complex.exp ((Real.arctan ((σ : ℂ).im / (σ : ℂ).re) : ℂ) * I)) *
          ((‖(σ : ℂ) + 1‖ : ℂ) * Complex.exp ((Real.arctan ((σ : ℂ).im / ((σ : ℂ).re + 1)) : ℂ) * I)) := by
      rw [← hP1, ← hP2]
    rw [hA]
    unfold smoothingPhase
    push_cast
    rw [show ((Real.arctan ((σ : ℂ).im / (σ : ℂ).re) : ℂ) + (Real.arctan ((σ : ℂ).im / ((σ : ℂ).re + 1)) : ℂ)) * I
        = (Real.arctan ((σ : ℂ).im / (σ : ℂ).re) : ℂ) * I + (Real.arctan ((σ : ℂ).im / ((σ : ℂ).re + 1)) : ℂ) * I by ring,
      Complex.exp_add]
    ring
  have hN : (‖(σ : ℂ)‖ * ‖(σ : ℂ) + 1‖ : ℝ) ≠ 0 := by
    have := norm_pos_iff.mpr h0; have := norm_pos_iff.mpr h1; positivity
  have hE := Complex.exp_ne_zero (((smoothingPhase σ : ℝ) : ℂ) * I)
  have hform : nontrivialZeroResidueTerm x σ =
      -(zetaZeroMultiplicity (σ : ℂ) : ℂ) * ((x : ℂ) ^ (σ : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1))) := by
    unfold nontrivialZeroResidueTerm Perron.f; rfl
  rw [hform, hden, cpow_polar _ hx]
  unfold jointTerm
  have hsub : Complex.exp ((((σ : ℂ).im * Real.log x - smoothingPhase σ : ℝ) : ℂ) * I) =
      Complex.exp ((((σ : ℂ).im * Real.log x : ℝ) : ℂ) * I) / Complex.exp (((smoothingPhase σ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_sub]; congr 1; push_cast; ring
  rw [hsub]
  have hNc : ((‖(σ : ℂ)‖ * ‖(σ : ℂ) + 1‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN
  push_cast at hNc ⊢
  field_simp

theorem jointTerm_step (m β T θ N : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    jointTerm m β T θ N b =
      (((b / a) ^ β : ℝ) : ℂ) * Complex.exp (((T * Real.log (b / a) : ℝ) : ℂ) * I) * jointTerm m β T θ N a := by
  unfold jointTerm
  rw [Real.div_rpow hb.le ha.le, Real.log_div hb.ne' ha.ne']
  have hab : a ^ β ≠ 0 := (Real.rpow_pos_of_pos ha β).ne'
  have he : Complex.exp (((T * Real.log b - θ : ℝ) : ℂ) * I) =
      Complex.exp (((T * (Real.log b - Real.log a) : ℝ) : ℂ) * I) *
        Complex.exp (((T * Real.log a - θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [he]
  rcases eq_or_ne N 0 with hN | hN
  · simp [hN]
  have habc : ((a ^ β : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hab
  push_cast
  field_simp

theorem jointTerm_real_at_meeting (m β T θ N : ℝ) (hT : T ≠ 0) (k : ℤ) :
    (jointTerm m β T θ N (Real.exp ((θ + k * Real.pi) / T))).im = 0 := by
  unfold jointTerm
  rw [Real.log_exp]
  have : T * ((θ + k * Real.pi) / T) - θ = k * Real.pi := by field_simp; ring
  rw [this]
  have hs : Real.sin (k * Real.pi) = 0 := Real.sin_int_mul_pi k
  rw [Complex.mul_im, Complex.exp_ofReal_mul_I_im, hs, Complex.exp_ofReal_mul_I_re]
  simp

/-- Contribution conjointe d'un indice de la formule explicite (ses trois paramètres propres). -/
noncomputable def memberJoint (σ : ExplicitIndex) (x : ℝ) : ℂ :=
  jointTerm (zetaZeroMultiplicity (σ : ℂ)) (σ : ℂ).re (σ : ℂ).im (smoothingPhase σ) (‖(σ : ℂ)‖ * ‖(σ : ℂ) + 1‖) x

theorem residueTerm_eq_memberJoint (σ : ExplicitIndex) {x : ℝ} (hx : 0 < x) :
    nontrivialZeroResidueTerm x σ = memberJoint σ x := residueTerm_joint σ hx

theorem primeAtRank_one_lt_real (n : ℕ) : (1 : ℝ) < (fnPrimeAtRank n : ℝ) := by
  exact_mod_cast (thm_primeAtRank_isPrime n).one_lt

theorem primeGap_log_eq (n : ℕ) :
    Real.log ((fnPrimeSuccessor n : ℝ) / (fnPrimeAtRank n : ℝ)) = rPrimeGapLogRatio n := rfl

/-- **Loi conjointe sur un écart premier** : de `p_n` à `p_{n+1}`, la contribution conjointe d'un indice est multipliée par
`e^{β L_n}` (amplitude) et tourne de `T L_n` (fréquence), son calage (rencontres) restant celui de `p_n`. -/
theorem memberJoint_gap_step (σ : ExplicitIndex) (n : ℕ) :
    memberJoint σ (fnPrimeSuccessor n : ℝ) =
      ((Real.exp ((σ : ℂ).re * rPrimeGapLogRatio n) : ℝ) : ℂ) *
        Complex.exp ((((σ : ℂ).im * rPrimeGapLogRatio n : ℝ) : ℂ) * I) * memberJoint σ (fnPrimeAtRank n : ℝ) := by
  have h0 : (0 : ℝ) < (fnPrimeAtRank n : ℝ) := by linarith [primeAtRank_one_lt_real n]
  have h1 : (0 : ℝ) < (fnPrimeSuccessor n : ℝ) := by
    unfold fnPrimeSuccessor; linarith [primeAtRank_one_lt_real (n + 1)]
  unfold memberJoint
  rw [jointTerm_step _ _ _ _ _ h0 h1, primeGap_log_eq, Real.rpow_def_of_pos (div_pos h1 h0), primeGap_log_eq, mul_comm (rPrimeGapLogRatio n)]

/-- **Synchronisation conjointe sur chaque écart premier** : l'incrément de la courbe des premiers sur `[p_n, p_{n+1}]` est la
somme, sur TOUS les vrais zéros, de leurs contributions conjointes (amplitude, fréquence, calage). -/
theorem prime_gap_joint_synchronization (n : ℕ) :
    smoothedRemainder (fnPrimeSuccessor n : ℝ) - smoothedRemainder (fnPrimeAtRank n : ℝ) =
      ∑' σ : ExplicitIndex, (memberJoint σ (fnPrimeSuccessor n : ℝ) - memberJoint σ (fnPrimeAtRank n : ℝ)) := by
  have ha := primeAtRank_one_lt_real n
  have hb : (1 : ℝ) < (fnPrimeSuccessor n : ℝ) := by unfold fnPrimeSuccessor; exact primeAtRank_one_lt_real (n + 1)
  rw [smoothedRemainder_eq_tsum_residueTerm hb, smoothedRemainder_eq_tsum_residueTerm ha,
    ← (nontrivial_zero_residue_series_summable hb).tsum_sub (nontrivial_zero_residue_series_summable ha)]
  exact tsum_congr fun σ => by
    rw [residueTerm_eq_memberJoint σ (by linarith), residueTerm_eq_memberJoint σ (by linarith)]

/-- **Contribution conjointe imposée sur chaque écart** : celle d'un vrai zéro est l'incrément de la courbe des premiers moins
celui de la part fixe des autres vrais zéros. -/
theorem imposed_joint_gap (w : TrueZero) (n : ℕ) :
    memberJoint (memberIndex w) (fnPrimeSuccessor n : ℝ) - memberJoint (memberIndex w) (fnPrimeAtRank n : ℝ) =
      (smoothedRemainder (fnPrimeSuccessor n : ℝ) - smoothedRemainder (fnPrimeAtRank n : ℝ)) -
        (othersSum w (fnPrimeSuccessor n : ℝ) - othersSum w (fnPrimeAtRank n : ℝ)) := by
  have ha := primeAtRank_one_lt_real n
  have hb : (1 : ℝ) < (fnPrimeSuccessor n : ℝ) := by unfold fnPrimeSuccessor; exact primeAtRank_one_lt_real (n + 1)
  rw [← residueTerm_eq_memberJoint _ (by linarith), ← residueTerm_eq_memberJoint _ (by linarith)]
  exact imposed_contribution_increment w ha hb

/-- Rencontres du terme lissé : là où sa contribution est réelle. -/
noncomputable def smoothedMeeting (p : ℂ) (k : ℤ) : ℝ := Real.exp ((smoothingPhase p + k * Real.pi) / p.im)

theorem smoothingPhase_zeroPoint (z : TrueZero) :
    smoothingPhase (zeroPoint z) = smoothingPhase ⟨rZeroRadialPosition z.1, rZeroHeight z.1⟩ := by
  unfold smoothingPhase; rw [zeroPoint_re, zeroPoint_im]

/-- **La contribution lissée d'un vrai zéro est réelle à chacune de ses rencontres lissées.** -/
theorem residueTerm_real_at_smoothedMeeting (z : TrueZero) (k : ℤ) :
    (nontrivialZeroResidueTerm (smoothedMeeting (zeroPoint z) k) (memberIndex z)).im = 0 := by
  have hpos : 0 < smoothedMeeting (zeroPoint z) k := Real.exp_pos _
  rw [residueTerm_eq_memberJoint (memberIndex z) hpos]
  unfold memberJoint smoothedMeeting
  exact jointTerm_real_at_meeting _ _ _ _ _ (by rw [show ((memberIndex z : ExplicitIndex) : ℂ) = zeroPoint z from rfl, zeroPoint_im]; exact z.2.ne') k

/-- **Raccord des deux familles de rencontres** : rencontre lissée = rencontre brute × `exp(arctan(T/(β + 1))/T)`. -/
theorem smoothedMeeting_eq_contact (z : TrueZero) (k : ℤ) :
    smoothedMeeting (zeroPoint z) k =
      contactMinusAt z k * Real.exp (Real.arctan (rZeroHeight z.1 / (rZeroRadialPosition z.1 + 1)) / rZeroHeight z.1) := by
  rw [contactMinusAt_eq_exp, ← Real.exp_add]
  unfold smoothedMeeting smoothingPhase
  rw [zeroPoint_re, zeroPoint_im]
  congr 1; ring

theorem smoothedMeeting_spacing (p : ℂ) (k : ℤ) :
    Real.log (smoothedMeeting p (k + 1)) - Real.log (smoothedMeeting p k) = Real.pi / p.im := by
  unfold smoothedMeeting; rw [Real.log_exp, Real.log_exp]; push_cast; ring

/-- Sous un demi, le calage lissé est au-delà de celui de la ligne à la même fréquence. -/
theorem smoothingPhase_low_gt_line {β T : ℝ} (hβ0 : 0 < β) (hβ : β < 1 / 2) (hT : 0 < T) :
    smoothingPhase ⟨1 / 2, T⟩ < smoothingPhase ⟨β, T⟩ := by
  unfold smoothingPhase
  apply add_lt_add <;> apply Real.arctan_strictMono <;> apply div_lt_div_of_pos_left hT <;> simp <;> linarith

/-- Au-dessus d'un demi, le calage lissé est en deçà de celui de la ligne. -/
theorem smoothingPhase_high_lt_line {β T : ℝ} (hβ : 1 / 2 < β) (hT : 0 < T) :
    smoothingPhase ⟨β, T⟩ < smoothingPhase ⟨1 / 2, T⟩ := by
  unfold smoothingPhase
  apply add_lt_add <;> apply Real.arctan_strictMono <;> apply div_lt_div_of_pos_left hT <;> simp <;> linarith

/-- **Les rencontres lissées sont celles de la ligne ⟺ sur la ligne.** -/
theorem smoothedMeeting_line_iff (z : TrueZero) :
    smoothedMeeting (zeroPoint z) 0 = smoothedMeeting ⟨1 / 2, rZeroHeight z.1⟩ 0 ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  have hT : (0 : ℝ) < rZeroHeight z.1 := z.2
  unfold smoothedMeeting
  rw [smoothingPhase_zeroPoint, zeroPoint_im]
  simp only [Int.cast_zero, zero_mul, add_zero]
  constructor
  · intro h
    have h' := Real.exp_injective h
    rw [div_left_inj' hT.ne'] at h'
    rcases lt_trichotomy (rZeroRadialPosition z.1) (1 / 2) with hlt | heq | hgt
    · linarith [smoothingPhase_low_gt_line (zeroPoint_re_pos z |>.trans_eq (zeroPoint_re z)) hlt hT]
    · exact heq
    · linarith [smoothingPhase_high_lt_line hgt hT]
  · intro h; rw [h]

/-- Télescopage des pas logarithmiques : `Σ_{r<N} L_r = log(p_N/p_0)`. -/
theorem primeGap_log_telescope (N : ℕ) :
    ∑ r ∈ Finset.range N, rPrimeGapLogRatio r = Real.log ((fnPrimeAtRank N : ℝ) / (fnPrimeAtRank 0 : ℝ)) := by
  have hpos : ∀ k, (0 : ℝ) < (fnPrimeAtRank k : ℝ) := fun k => by linarith [primeAtRank_one_lt_real k]
  have hstep : ∀ r, rPrimeGapLogRatio r = Real.log (fnPrimeAtRank (r + 1) : ℝ) - Real.log (fnPrimeAtRank r : ℝ) := by
    intro r
    rw [← primeGap_log_eq, Real.log_div (by unfold fnPrimeSuccessor; exact (hpos _).ne') (hpos r).ne']
    rfl
  rw [Finset.sum_congr rfl (fun r _ => hstep r), Finset.sum_range_sub (fun k => Real.log (fnPrimeAtRank k : ℝ)),
    Real.log_div (hpos N).ne' (hpos 0).ne']

/-- Les pas logarithmiques cumulés dépassent toute borne. -/
theorem primeGap_log_unbounded (M : ℝ) : ∃ N : ℕ, M < ∑ r ∈ Finset.range N, rPrimeGapLogRatio r := by
  have h0 : (0 : ℝ) < (fnPrimeAtRank 0 : ℝ) := by linarith [primeAtRank_one_lt_real 0]
  set K := Real.exp (M + Real.log (fnPrimeAtRank 0 : ℝ))
  refine ⟨⌈K⌉₊ + 1, ?_⟩
  rw [primeGap_log_telescope, Real.log_div (by linarith [primeAtRank_one_lt_real (⌈K⌉₊ + 1)]) h0.ne']
  have hid : ⌈K⌉₊ + 1 ≤ fnPrimeAtRank (⌈K⌉₊ + 1) := thm_primeAtRank_strictMono.id_le _
  have hK : K < (fnPrimeAtRank (⌈K⌉₊ + 1) : ℝ) := by
    calc K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
      _ < (⌈K⌉₊ : ℝ) + 1 := by linarith
      _ ≤ (fnPrimeAtRank (⌈K⌉₊ + 1) : ℝ) := by exact_mod_cast hid
  have := Real.log_lt_log (Real.exp_pos _) hK
  rw [Real.log_exp] at this
  linarith

/-- **Désaccord conjoint sur chaque écart premier (zéro sous un demi)**, contre DEUX RÉFÉRENCES DISTINCTES, aucune n'étant un vrai
zéro : (R1) le signal de la ligne qui partage la première rencontre brute de `w` (fréquence `T'`, paramètre de l'énoncé) ;
(R2) le signal de la ligne à la fréquence propre `T_w`. Un vrai zéro sous un demi présente ENSEMBLE, sur chaque écart premier :
contre (R1), une avance de phase en excès `(T_w − T') L_n > 0` qui s'additionne d'un écart à l'autre et dépasse toute borne ;
contre (R2), des rencontres brutes (`radialFactor > 1`) et lissées (calage plus grand) décalées au-delà ; et une enveloppe qui
décroît par rapport à l'échelle commune, d'un facteur `e^{(β − 1/2) L_n} < 1`. Caractérisation : aucun de ces faits n'est une
contradiction. -/
theorem low_joint_deviation_every_gap (w : TrueZero) (hβ : rZeroRadialPosition w.1 < 1 / 2) {T' : ℝ} (hT' : 0 < T')
    (h : lineContact T' 0 = contactMinusAt w 0) :
    T' < rZeroHeight w.1 ∧
    1 < radialFactor w ∧
    smoothingPhase ⟨1 / 2, rZeroHeight w.1⟩ < smoothingPhase (zeroPoint w) ∧
    (∀ n : ℕ, 0 < (rZeroHeight w.1 - T') * rPrimeGapLogRatio n ∧
      pairAmplitude w (fnPrimeSuccessor n : ℝ) / pairAmplitude w (fnPrimeAtRank n : ℝ) < 1) ∧
    (∀ M : ℝ, ∃ N : ℕ, M < ∑ r ∈ Finset.range N, (rZeroHeight w.1 - T') * rPrimeGapLogRatio r) := by
  have hlt := (zero_low_meeting_reads_lower_frequency w hβ hT' h).1
  have hd : 0 < rZeroHeight w.1 - T' := by linarith
  refine ⟨hlt, (radialFactor_gt_one_iff w).mpr hβ, ?_, fun n => ⟨mul_pos hd (thm_primeGapLogRatio_pos n), ?_⟩, fun M => ?_⟩
  · rw [smoothingPhase_zeroPoint]
    have h0 : 0 < rZeroRadialPosition w.1 := by rw [← zeroPoint_re]; exact zeroPoint_re_pos w
    exact smoothingPhase_low_gt_line h0 hβ w.2
  · rw [pairAmplitude_prime_step]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith) (thm_primeGapLogRatio_pos n))
  · obtain ⟨N, hN⟩ := primeGap_log_unbounded (M / (rZeroHeight w.1 - T'))
    refine ⟨N, ?_⟩
    rw [← Finset.mul_sum]
    have := (div_lt_iff₀ hd).mp hN
    linarith

/-- **Désaccord conjoint du miroir sur chaque écart premier** : même fréquence, rencontres brutes et lissées en deçà de celles de la
ligne, enveloppe qui CROÎT par rapport à l'échelle commune d'un facteur `e^{(1/2 − β) L_n} > 1` sur chaque écart. -/
theorem mirror_joint_deviation_every_gap (w : TrueZero) (hβ : rZeroRadialPosition w.1 < 1 / 2) :
    rZeroHeight (mirrorMember w).1 = rZeroHeight w.1 ∧
    radialFactor (mirrorMember w) < 1 ∧
    smoothingPhase (zeroPoint (mirrorMember w)) < smoothingPhase ⟨1 / 2, rZeroHeight w.1⟩ ∧
    ∀ n : ℕ, pairAmplitude (mirrorMember w) (fnPrimeSuccessor n : ℝ) / pairAmplitude (mirrorMember w) (fnPrimeAtRank n : ℝ) =
        Real.exp ((1 / 2 - rZeroRadialPosition w.1) * rPrimeGapLogRatio n) ∧
      1 < pairAmplitude (mirrorMember w) (fnPrimeSuccessor n : ℝ) / pairAmplitude (mirrorMember w) (fnPrimeAtRank n : ℝ) := by
  have hhigh : 1 / 2 < rZeroRadialPosition (mirrorMember w).1 := by rw [mirrorMember_radial]; linarith
  refine ⟨mirrorMember_ordinate w, (radialFactor_lt_one_iff _).mpr hhigh, ?_, fun n => ?_⟩
  · rw [smoothingPhase_zeroPoint, mirrorMember_ordinate]
    exact smoothingPhase_high_lt_line (by rw [mirrorMember_radial] at hhigh ⊢; exact hhigh) w.2
  · have he : pairAmplitude (mirrorMember w) (fnPrimeSuccessor n : ℝ) / pairAmplitude (mirrorMember w) (fnPrimeAtRank n : ℝ) =
        Real.exp ((1 / 2 - rZeroRadialPosition w.1) * rPrimeGapLogRatio n) := by
      rw [pairAmplitude_prime_step, mirrorMember_radial]; congr 1; ring
    refine ⟨he, ?_⟩
    rw [he]
    exact Real.one_lt_exp_iff.mpr (mul_pos (by linarith) (thm_primeGapLogRatio_pos n))

/-! ### Forme minimale de l'implication manquante -/

/-- Sur l'écart `n`, la contribution imposée à `z` (courbe des premiers moins part fixe des autres vrais zéros) ne grandit pas plus
vite que l'échelle commune. -/
def ImposedNotFasterAtGap (z : TrueZero) (n : ℕ) : Prop :=
  ‖smoothedRemainder (fnPrimeSuccessor n : ℝ) - othersSum z (fnPrimeSuccessor n : ℝ)‖ /
      ‖smoothedRemainder (fnPrimeAtRank n : ℝ) - othersSum z (fnPrimeAtRank n : ℝ)‖ ≤
    Real.exp (rPrimeGapLogRatio n / 2)

/-- Sur l'écart `n`, la contribution imposée à `z` grandit exactement à l'échelle commune. -/
def ImposedOnScaleAtGap (z : TrueZero) (n : ℕ) : Prop :=
  ‖smoothedRemainder (fnPrimeSuccessor n : ℝ) - othersSum z (fnPrimeSuccessor n : ℝ)‖ /
      ‖smoothedRemainder (fnPrimeAtRank n : ℝ) - othersSum z (fnPrimeAtRank n : ℝ)‖ =
    Real.exp (rPrimeGapLogRatio n / 2)

theorem imposedNotFasterAtGap_iff (z : TrueZero) (n : ℕ) :
    ImposedNotFasterAtGap z n ↔ rZeroRadialPosition z.1 ≤ 1 / 2 := by
  unfold ImposedNotFasterAtGap
  rw [(imposed_contribution_drift z n).1, Real.exp_le_exp]
  have hL := thm_primeGapLogRatio_pos n
  constructor <;> intro h <;> nlinarith

theorem imposedOnScaleAtGap_iff (z : TrueZero) (n : ℕ) :
    ImposedOnScaleAtGap z n ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  unfold ImposedOnScaleAtGap
  rw [(imposed_contribution_drift z n).1, Real.exp_eq_exp]
  have hL := thm_primeGapLogRatio_pos n
  constructor
  · intro h; nlinarith
  · intro h; rw [h]; ring

/-- **Forme minimale (un seul écart, une seule inégalité, côté miroir)** : si, sur UN écart premier, la contribution imposée au
miroir d'un zéro sous un demi ne grandit pas plus vite que l'échelle commune, contradiction. -/
theorem mirror_not_faster_closes (w : TrueZero) (hβ : rZeroRadialPosition w.1 < 1 / 2) (n : ℕ)
    (h : ImposedNotFasterAtGap (mirrorMember w) n) : False := by
  rw [imposedNotFasterAtGap_iff, mirrorMember_radial] at h
  linarith

/-- Les deux formes sont la même obligation dans le cas bas : forme (a) sur `w` ⟺ forme (b) sur le miroir de `w`. -/
theorem onScale_iff_mirror_not_faster (w : TrueZero) (hle : rZeroRadialPosition w.1 ≤ 1 / 2) (n : ℕ) :
    ImposedOnScaleAtGap w n ↔ ImposedNotFasterAtGap (mirrorMember w) n := by
  rw [imposedOnScaleAtGap_iff, imposedNotFasterAtGap_iff, mirrorMember_radial]
  constructor <;> intro h <;> linarith

/-- **Portée** : la forme minimale, énoncée pour tous les vrais zéros (sur un seul écart), est équivalente à RH. -/
theorem notFaster_law_iff_riemannHypothesis (n : ℕ) :
    (∀ z : TrueZero, ImposedNotFasterAtGap z n) ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_noLowerSide]
  constructor
  · intro h z hlt
    exact mirror_not_faster_closes z hlt n (h _)
  · intro h z
    rw [imposedNotFasterAtGap_iff, only_low_candidate h z]

/-! ### Entrée de la matrice de synchronisation (correction 1 de la revue du 2026-10-17)

Chaque entrée (écart × indice) porte ensemble fréquence, phase et enveloppe aux deux bornes, et les rencontres lissées
situées dans l'écart. La cellule de `Terminal/SynchronizationMatrix.lean` (`matrixCell`, différence des termes lissés) est
exactement cette entrée (`matrixCell_eq_gap_entry`, dans ce module-là, qui importe celui-ci). La fréquence de référence
(signal de la ligne qui partage la première rencontre brute) n'est pas un champ de l'entrée : c'est un paramètre des énoncés de
désaccord, dont l'existence n'est pas démontrée ici ; elle n'est jamais la hauteur d'un vrai zéro. -/

/-- Phase d'un indice à l'abscisse `x` (fréquence × log x − calage des rencontres lissées). -/
noncomputable def gapPhase (σ : ExplicitIndex) (x : ℝ) : ℝ := (σ : ℂ).im * Real.log x - smoothingPhase σ

/-- Enveloppe exacte d'un indice dans le canal lissé : `m · x^β / (‖ρ‖‖ρ + 1‖)`. -/
noncomputable def gapEnvelope (σ : ExplicitIndex) (x : ℝ) : ℝ :=
  (zetaZeroMultiplicity (σ : ℂ) : ℝ) * (x ^ (σ : ℂ).re / (‖(σ : ℂ)‖ * ‖(σ : ℂ) + 1‖))

/-- **Entrée de la matrice de synchronisation** (cellule `[a, b]` × indice `σ`, canal lissé) : la contribution exacte de
l'indice à l'écart, écrite par sa phase et son enveloppe aux deux bornes. -/
theorem gap_entry_joint (σ : ExplicitIndex) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    nontrivialZeroResidueTerm b σ - nontrivialZeroResidueTerm a σ =
      -((gapEnvelope σ b : ℂ) * Complex.exp ((gapPhase σ b : ℂ) * I)) +
        (gapEnvelope σ a : ℂ) * Complex.exp ((gapPhase σ a : ℂ) * I) := by
  rw [residueTerm_joint σ ha, residueTerm_joint σ hb]
  unfold jointTerm gapEnvelope gapPhase
  push_cast
  ring

/-- Module de l'enveloppe lissée = multiplicité × module du terme brut `x^β/‖ρ‖` / `‖ρ + 1‖` (conversion de canal). -/
theorem gapEnvelope_eq_raw (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    gapEnvelope (memberIndex z) x = ‖nontrivialZeroResidueTerm x (memberIndex z)‖ := by
  rw [residueTerm_joint _ hx]
  unfold jointTerm gapEnvelope
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_exp_ofReal_mul_I, mul_one]
  have h1 := norm_nonneg ((memberIndex z : ExplicitIndex) : ℂ)
  have h2 := norm_nonneg (((memberIndex z : ExplicitIndex) : ℂ) + 1)
  simp [Complex.norm_real]
  left; rw [abs_of_nonneg (Real.rpow_nonneg hx.le _)]

/-- **Rencontres dans un écart** : si l'écart est plus court qu'un demi-tour (`T·L < π`), il contient au plus UNE rencontre
lissée. -/
theorem at_most_one_meeting_in_short_gap (p : ℂ) (hT : 0 < p.im) {a b : ℝ} (hshort : p.im * (b - a) < Real.pi)
    {k j : ℤ} (hk : a ≤ Real.log (smoothedMeeting p k) ∧ Real.log (smoothedMeeting p k) ≤ b)
    (hj : a ≤ Real.log (smoothedMeeting p j) ∧ Real.log (smoothedMeeting p j) ≤ b) : k = j := by
  unfold smoothedMeeting at hk hj
  rw [Real.log_exp] at hk hj
  have hk' : ((k : ℝ) - j) * Real.pi / p.im ≤ b - a := by
    have : ((k : ℝ) - j) * Real.pi / p.im = (smoothingPhase p + k * Real.pi) / p.im - (smoothingPhase p + j * Real.pi) / p.im := by
      field_simp; ring
    rw [this]; linarith [hk.2, hj.1]
  have hj' : ((j : ℝ) - k) * Real.pi / p.im ≤ b - a := by
    have : ((j : ℝ) - k) * Real.pi / p.im = (smoothingPhase p + j * Real.pi) / p.im - (smoothingPhase p + k * Real.pi) / p.im := by
      field_simp; ring
    rw [this]; linarith [hj.2, hk.1]
  have h1 : ((k : ℝ) - j) * Real.pi < Real.pi := by
    have := (div_le_iff₀ hT).mp hk'; nlinarith
  have h2 : ((j : ℝ) - k) * Real.pi < Real.pi := by
    have := (div_le_iff₀ hT).mp hj'; nlinarith
  have hpi := Real.pi_pos
  have e1 : (k : ℝ) - j < 1 := by nlinarith
  have e2 : (j : ℝ) - k < 1 := by nlinarith
  have : k - j < 1 := by exact_mod_cast e1
  have : j - k < 1 := by exact_mod_cast e2
  omega

end JointGap

#print axioms point_polar
#print axioms cpow_polar
#print axioms residueTerm_joint
#print axioms jointTerm_step
#print axioms jointTerm_real_at_meeting
#print axioms residueTerm_eq_memberJoint
#print axioms primeAtRank_one_lt_real
#print axioms primeGap_log_eq
#print axioms memberJoint_gap_step
#print axioms prime_gap_joint_synchronization
#print axioms imposed_joint_gap
#print axioms smoothingPhase_zeroPoint
#print axioms residueTerm_real_at_smoothedMeeting
#print axioms smoothedMeeting_eq_contact
#print axioms smoothedMeeting_spacing
#print axioms smoothingPhase_low_gt_line
#print axioms smoothingPhase_high_lt_line
#print axioms smoothedMeeting_line_iff
#print axioms primeGap_log_telescope
#print axioms primeGap_log_unbounded
#print axioms low_joint_deviation_every_gap
#print axioms mirror_joint_deviation_every_gap
#print axioms imposedNotFasterAtGap_iff
#print axioms imposedOnScaleAtGap_iff
#print axioms mirror_not_faster_closes
#print axioms onScale_iff_mirror_not_faster
#print axioms notFaster_law_iff_riemannHypothesis
#print axioms gap_entry_joint
#print axioms gapEnvelope_eq_raw
#print axioms at_most_one_meeting_in_short_gap

end RHV6Fresh
