/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.OnCrossReadings
import RHV6Fresh.Terminal.TangentialInversion
import RHV6Fresh.Terminal.WindowProgression
import RHV6Fresh.Terminal.RemainderRepresentation
import RHV6Fresh.Terminal.WholeWindingObligation
import RHV6Fresh.Terminal.RegimeTrigger
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.PrimeCounting

/-!
# RHV6Fresh — lecture conjointe des paramètres : amplitude, résolution, arithmétique (auteur,
2026-10-06)

Orientation de l'auteur : la recherche porte sur les obligations CONJOINTES de reproduction
arithmétique, de fréquence et d'amplitude ; l'enroulement doit en être une conséquence. Ce module
relie explicitement, pour un vrai zéro `ρ = β + iT` (`T > 0`), les objets déjà compilés :

* paramètres indépendants : la partie réelle `β = rZeroRadialPosition` et la hauteur `T =
rZeroHeight` ;
* quantités dérivées (fonctions de `(β, T)`, jamais données indépendantes) : la phase
  `φ = arctan(T/β)` (`towerMotion_phase`), les contacts `C_k = exp((φ + kπ)/T)` (`contactMinusAt`),
  l'intervalle logarithmique `ℓ = π/T` (`towerPitch`), la fréquence de phase `T` dans la coordonnée
  `u = log x` (`pointCurve_hasDerivAt`), l'amplitude brute `x^β/√(β² + T²)` (`zeroTerm_norm`),
  l'amplitude normalisée `A(x) = x^{β − 1/2}/√(β² + T²)` (`normalizedRadius_eq`).

Aucun premier n'entre dans le producteur de contacts ; aucun indice de contact n'est un paramètre
indépendant du zéro (le contact d'indice `k` est une fonction de `(β, T, k)`).

Statuts (quatre) : DÉMONTRÉ = théorème de ce module ou des bases ; CONDITIONNEL = sous l'unique
prémisse d'enroulement entier (`riemannHypothesis_of_whole_winding_all_passages`, signature
inchangée)
ou sous une hypothèse écrite ; OBSERVATION NUMÉRIQUE = expériences citées dans les maîtres ; OUVERT
=
le premier raccord non démontré, énoncé dans la section 7.

Ce que ce module NE fait pas : il n'ajoute aucune prémisse (ni budget, ni appartenance ON, ni
progression de hauteur, ni symétrie, ni amorce) ; il ne présente pas l'équivalence « prémisse ⟺ RH »
comme une dérivation de la prémisse ; il n'identifie pas le reste lissé au déficit de comptage
`π − li` (aucun théorème de liaison : manque exposé, section 5).
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Les quantités dérivées et leurs relations exactes (DÉMONTRÉ, toute position radiale) -/

/-- **Contacts et hauteur** : `log C_{k+1} − log C_k = π/T = ℓ`. L'intervalle logarithmique entre
deux
contacts consécutifs est la seule donnée du pas ; il ne dépend que de la hauteur. -/
theorem contact_log_step (z : TrueZero) (k : ℤ) :
    Real.log (contactMinusAt z (k + 1)) - Real.log (contactMinusAt z k) = towerPitch z := by
  rw [log_contact_eq, log_contact_eq]
  unfold towerPitch
  push_cast
  field_simp
  ring

/-- Le rapport de deux contacts consécutifs est `e^ℓ`. -/
theorem contact_ratio_eq_exp_pitch (z : TrueZero) (k : ℤ) :
    contactMinusAt z (k + 1) / contactMinusAt z k = Real.exp (towerPitch z) := by
  have h0 := contactMinusAt_positive z k
  have h1 := contactMinusAt_positive z (k + 1)
  rw [← contact_log_step, Real.exp_sub, Real.exp_log h1, Real.exp_log h0]

/-- **Distances ordinaires le long d'une Tour** : `C_{k+1} − C_k = C_k·(e^ℓ − 1)`. Le pas
LOGARITHMIQUE
est constant le long d'une Tour ; la distance ordinaire entre contacts croît strictement avec `k`.
Ne pas
confondre la diminution du pas logarithmique ENTRE Tours (hauteur qui monte) avec les distances
ordinaires
LE LONG d'une Tour. -/
theorem contact_ordinary_gap_eq (z : TrueZero) (k : ℤ) :
    contactMinusAt z (k + 1) - contactMinusAt z k =
      contactMinusAt z k * (Real.exp (towerPitch z) - 1) := by
  have h0 := contactMinusAt_positive z k
  have h := contact_ratio_eq_exp_pitch z k
  rw [div_eq_iff h0.ne'] at h
  rw [h]
  ring

theorem contact_ordinary_gap_strictMono (z : TrueZero) (k : ℤ) :
    contactMinusAt z (k + 1) - contactMinusAt z k <
      contactMinusAt z (k + 1 + 1) - contactMinusAt z (k + 1) := by
  rw [contact_ordinary_gap_eq, contact_ordinary_gap_eq]
  have hℓ : 0 < towerPitch z := div_pos Real.pi_pos z.2
  have hexp : 0 < Real.exp (towerPitch z) - 1 := by
    have := Real.add_one_lt_exp (ne_of_gt hℓ)
    linarith
  have hlt : contactMinusAt z k < contactMinusAt z (k + 1) := contactAt_ordered z k
  exact mul_lt_mul_of_pos_right hlt hexp

/-- Le support `‖ρ‖ = √(β² + T²)`. -/
theorem zeroPoint_norm_eq_sqrt (z : TrueZero) :
    ‖zeroPoint z‖ = Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (zeroPoint z)), zeroPoint_norm_sq]

/-- **Amplitude et résolution, sans supposer ON** : `A(x) = x^{β − 1/2} · ℓ / √(π² + β² ℓ²)`, `ℓ =
π/T`.
L'amplitude normalisée est écrite avec l'intervalle logarithmique à la place de la hauteur :
amplitude et
résolution sont deux lectures des mêmes paramètres. -/
theorem normalizedRadius_eq_pitch (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    normalizedRadius z x =
      x ^ (rZeroRadialPosition z.1 - 1 / 2) * towerPitch z /
        Real.sqrt (Real.pi ^ 2 + rZeroRadialPosition z.1 ^ 2 * towerPitch z ^ 2) := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hℓ : 0 < towerPitch z := div_pos Real.pi_pos hT
  have hTℓ : rZeroHeight z.1 * towerPitch z = Real.pi := by
    unfold towerPitch; field_simp
  have hkey : Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) * towerPitch z =
      Real.sqrt (Real.pi ^ 2 + rZeroRadialPosition z.1 ^ 2 * towerPitch z ^ 2) := by
    have h1 : Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) * towerPitch z =
        Real.sqrt ((rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) * towerPitch z ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hℓ.le]
    rw [h1]
    congr 1
    linear_combination (rZeroHeight z.1 * towerPitch z + Real.pi) * hTℓ
  rw [normalizedRadius_eq z hx, zeroPoint_norm_eq_sqrt, ← hkey]
  have hs : 0 < Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) :=
    Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hT 2))
  field_simp

/-- **Amplitude entre deux abscisses positives** : `A(y)/A(x) = (y/x)^{β − 1/2}`. -/
theorem normalizedRadius_ratio (z : TrueZero) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    normalizedRadius z y / normalizedRadius z x = (y / x) ^ (rZeroRadialPosition z.1 - 1 / 2) := by
  rw [normalizedRadius_eq z hx, normalizedRadius_eq z hy, Real.div_rpow hy.le hx.le]
  have hN := norm_zeroPoint_pos z
  have hxr : 0 < x ^ (rZeroRadialPosition z.1 - 1 / 2) := Real.rpow_pos_of_pos hx _
  field_simp

/-- **Amplitude entre deux contacts propres** : `A(C_{k+1})/A(C_k) = e^{(β − 1/2) ℓ}`. Vrai pour
toute
position radiale : c'est une fonction de `(β, ℓ)`. -/
theorem normalizedRadius_own_contact_step (z : TrueZero) (k : ℤ) :
    normalizedRadius z (contactMinusAt z (k + 1)) / normalizedRadius z (contactMinusAt z k) =
      Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * towerPitch z) := by
  have hpos := normalizedRadius_pos z (contactMinusAt_positive z k)
  rw [div_eq_iff hpos.ne', radius_step_between_contacts z z k]
  congr 2
  unfold towerPitch
  ring

/-- **Dans le régime ON seulement** : `A(x) = ℓ/√(π² + ℓ²/4)`, constante le long de l'axe.
Conséquence de
ON (`β = 1/2`), jamais supposée pour prouver ON. -/
theorem normalizedRadius_onLine_pitch (z : TrueZero) (hz : rZeroRadialPosition z.1 = 1 / 2) {x : ℝ}
    (hx : 0 < x) :
    normalizedRadius z x = towerPitch z / Real.sqrt (Real.pi ^ 2 + towerPitch z ^ 2 / 4) := by
  rw [normalizedRadius_eq_pitch z hx, hz]
  simp only [sub_self, Real.rpow_zero, one_mul]
  congr 2
  ring

/-- **Caractérisation (pas obligation acquise)** : l'amplitude normalisée est la même à deux
contacts
propres consécutifs ⟺ le zéro est en ligne. Le sens direct lit la partie réelle ; il ne la fixe pas.
-/
theorem own_contact_amplitude_flat_iff (z : TrueZero) (k : ℤ) :
    normalizedRadius z (contactMinusAt z (k + 1)) = normalizedRadius z (contactMinusAt z k) ↔
      rZeroRadialPosition z.1 = 1 / 2 := by
  have hpos := normalizedRadius_pos z (contactMinusAt_positive z k)
  rw [← div_eq_one_iff_eq hpos.ne', normalizedRadius_own_contact_step]
  unfold towerPitch
  rw [← mul_div_assoc]
  exact radius_step_eq_one_iff z z

/-- **Lecture croisée réunie (DÉMONTRÉ, toute position radiale)** : aux contacts du membre `e`, la
position du membre `l` avance de `T_l/T_e` demi-tours et son rayon normalisé est multiplié par
`e^{(β_l − 1/2) π/T_e}`. Les deux lectures portent sur les mêmes contacts ; la première ne lit que
les
hauteurs, la seconde lit la partie réelle de `l`. -/
theorem joint_cross_reading (e l : TrueZero) (k : ℤ) :
    towerPosition l (contactMinusAt e (k + 1)) - towerPosition l (contactMinusAt e k) =
        rZeroHeight l.1 / rZeroHeight e.1 ∧
      normalizedRadius l (contactMinusAt e (k + 1)) =
        Real.exp ((rZeroRadialPosition l.1 - 1 / 2) * Real.pi / rZeroHeight e.1) *
          normalizedRadius l (contactMinusAt e k) :=
  ⟨cross_advance_between_contacts e l k, radius_step_between_contacts e l k⟩

/-! ## 2. Inversion : restitution depuis des contacts authentiques et consécutifs (DÉMONTRÉ) -/

/-- La tangente au contact ne s'annule jamais (`T > 0`) : la branche de l'inversion radiale est
définie. -/
theorem inversion_tan_ne_zero (z : TrueZero) (k : ℤ) :
    Real.tan (rZeroHeight z.1 * Real.log (contactMinusAt z k)) ≠ 0 := by
  rw [contactAt_tangent_minus]
  exact div_ne_zero z.2.ne' (thm_zeroRadialPosition_positive z.1).ne'

/-- **Restitution** : deux contacts AUTHENTIQUES et CONSÉCUTIFS du même zéro rendent `T` puis `β` :
`T = π/log(C_{k+1}/C_k)`, `β = T/tan(T log C_k)`. C'est la lecture de contacts CONNUS ; elle ne
prédit pas un contact inconnu et n'utilise que les contacts du membre lui-même. -/
theorem inversion_from_consecutive_contacts (z : TrueZero) (k : ℤ) :
    Real.pi / Real.log (contactMinusAt z (k + 1) / contactMinusAt z k) = rZeroHeight z.1 ∧
      rZeroHeight z.1 / Real.tan (rZeroHeight z.1 * Real.log (contactMinusAt z k)) =
        rZeroRadialPosition z.1 := by
  refine ⟨inversion_height z k, ?_⟩
  rw [contactAt_tangent_minus]
  have hβ := thm_zeroRadialPosition_positive z.1
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  rw [div_div_eq_mul_div, mul_div_assoc]
  field_simp

/-- **Encadrement d'un contact INCONNU** depuis l'état engagé : sur un passage où la hauteur avance
et dont le
départ est en ligne, tout contact du membre atteint est le contact de ligne à sa hauteur multiplié
par un
facteur `λ ∈ [1, e^{1/(2 T_l²)}[` (`engaged_event_restriction`). C'est un encadrement, pas une
prédiction :
le facteur n'est pas fixé, et `λ = 1 ⟺` arrivée en ligne. -/
theorem unknown_contact_bracket (p : TZeroPassage) (hL : 0 < rZeroHeight p.zLaterMember)
    (hβ : rZeroRadialPosition p.zLaterMember ≤ 1 / 2) (k : ℤ) :
    contactMinusAt ⟨p.zLaterMember, hL⟩ k =
        lineContact (rZeroHeight p.zLaterMember) k * radialFactor ⟨p.zLaterMember, hL⟩ ∧
      1 ≤ radialFactor ⟨p.zLaterMember, hL⟩ ∧
      (radialFactor ⟨p.zLaterMember, hL⟩ = 1 ↔ rZeroRadialPosition p.zLaterMember = 1 / 2) := by
  refine ⟨contact_eq_line_mul_radial _ k, ?_, radialFactor_eq_one_iff _⟩
  rcases lt_or_eq_of_le hβ with hlt | heq
  · exact le_of_lt ((radialFactor_gt_one_iff ⟨p.zLaterMember, hL⟩).mpr hlt)
  · exact le_of_eq ((radialFactor_eq_one_iff ⟨p.zLaterMember, hL⟩).mpr heq).symm

/-! ## 3. Le facteur de lissage `−m/(ρ + 1)` : effet exact sur l'amplitude et la phase (DÉMONTRÉ) -/

/-- Le facteur qui transporte la Tour brute `x^ρ/ρ` vers la contribution lissée `−m x^ρ/(ρ(ρ+1))`.
-/
noncomputable def smoothingFactor (z : TrueZero) : ℂ :=
  -(zetaZeroMultiplicity (zeroPoint z) : ℂ) / (zeroPoint z + 1)

/-- **Transport membre par membre** : contribution lissée `=` facteur `×` Tour brute. -/
theorem residueTerm_eq_smoothingFactor_mul (z : TrueZero) (x : ℝ) :
    nontrivialZeroResidueTerm x (memberIndex z) = smoothingFactor z * zeroTerm z x := by
  rw [residueTerm_eq_zeroTerm]
  unfold smoothingFactor
  ring

/-- Partie réelle du facteur : `−m(β + 1)/((β + 1)² + T²)`. -/
theorem smoothingFactor_re (z : TrueZero) :
    (smoothingFactor z).re =
      -(zetaZeroMultiplicity (zeroPoint z) : ℝ) * (rZeroRadialPosition z.1 + 1) /
        ((rZeroRadialPosition z.1 + 1) ^ 2 + rZeroHeight z.1 ^ 2) := by
  unfold smoothingFactor
  rw [Complex.div_re]
  simp only [Complex.neg_re, Complex.natCast_re, Complex.neg_im, Complex.natCast_im, Complex.add_re,
    Complex.one_re, Complex.add_im, Complex.one_im, zeroPoint_re, zeroPoint_im, neg_zero, zero_mul,
    add_zero, Complex.normSq_apply]
  ring

/-- Partie imaginaire du facteur : `m T/((β + 1)² + T²)`, strictement positive. Le facteur de
lissage
TOURNE la contribution : la phase du terme lissé n'est pas celle de la Tour brute. -/
theorem smoothingFactor_im (z : TrueZero) :
    (smoothingFactor z).im =
      (zetaZeroMultiplicity (zeroPoint z) : ℝ) * rZeroHeight z.1 /
        ((rZeroRadialPosition z.1 + 1) ^ 2 + rZeroHeight z.1 ^ 2) := by
  unfold smoothingFactor
  rw [Complex.div_im]
  simp only [Complex.neg_re, Complex.natCast_re, Complex.neg_im, Complex.natCast_im, Complex.add_re,
    Complex.one_re, Complex.add_im, Complex.one_im, zeroPoint_re, zeroPoint_im, neg_zero, zero_mul,
    Complex.normSq_apply]
  ring

/-- Module du facteur : `m/√((β + 1)² + T²)`. Il MODIFIE l'amplitude d'un rapport constant le long
de
l'axe (fonction de `(β, T, m)`). -/
theorem smoothingFactor_norm (z : TrueZero) :
    ‖smoothingFactor z‖ =
      (zetaZeroMultiplicity (zeroPoint z) : ℝ) /
        Real.sqrt ((rZeroRadialPosition z.1 + 1) ^ 2 + rZeroHeight z.1 ^ 2) := by
  unfold smoothingFactor
  rw [norm_div, norm_neg, Complex.norm_natCast, Complex.norm_def, Complex.normSq_apply]
  congr 2
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zeroPoint_re,
    zeroPoint_im, add_zero]
  ring

/-- **Amplitude de la contribution lissée** : `m · x^β/(√(β² + T²) · √((β + 1)² + T²))`. -/
theorem residueTerm_norm_joint (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    ‖nontrivialZeroResidueTerm x (memberIndex z)‖ =
      (zetaZeroMultiplicity (zeroPoint z) : ℝ) * x ^ rZeroRadialPosition z.1 /
        (Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) *
          Real.sqrt ((rZeroRadialPosition z.1 + 1) ^ 2 + rZeroHeight z.1 ^ 2)) := by
  rw [residueTerm_eq_smoothingFactor_mul, norm_mul, smoothingFactor_norm, zeroTerm_norm hx,
    zeroPoint_norm_eq_sqrt]
  have hT := z.2
  have h1 : 0 < Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) :=
    Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hT 2))
  have h2 : 0 < Real.sqrt ((rZeroRadialPosition z.1 + 1) ^ 2 + rZeroHeight z.1 ^ 2) :=
    Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hT 2))
  field_simp

/-- **Au contact propre de la Tour brute** : la contribution lissée exacte vaut le facteur de
lissage fois
la valeur réelle signée `(−1)^k ‖terme brut‖` du terme brut. -/
theorem residueTerm_at_own_contact (z : TrueZero) (k : ℤ) :
    nontrivialZeroResidueTerm (contactMinusAt z k) (memberIndex z) =
      smoothingFactor z * (((-1 : ℝ) ^ k * ‖zeroTerm z (contactMinusAt z k)‖ : ℝ) : ℂ) := by
  rw [residueTerm_eq_smoothingFactor_mul]
  congr 1
  exact zeroTerm_at_own_contact z k

/-- **Projection réelle de la contribution lissée au contact brut** :
`(−1)^k ‖terme brut‖ · (−m(β + 1))/((β + 1)² + T²)`. -/
theorem residueTerm_re_at_own_contact (z : TrueZero) (k : ℤ) :
    (nontrivialZeroResidueTerm (contactMinusAt z k) (memberIndex z)).re =
      (-1 : ℝ) ^ k * ‖zeroTerm z (contactMinusAt z k)‖ *
        (-(zetaZeroMultiplicity (zeroPoint z) : ℝ) * (rZeroRadialPosition z.1 + 1) /
          ((rZeroRadialPosition z.1 + 1) ^ 2 + rZeroHeight z.1 ^ 2)) := by
  rw [residueTerm_at_own_contact, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, smoothingFactor_re]
  ring

/-- **Les contacts bruts ne sont pas des contacts du terme lissé** : au contact propre de la Tour
brute, la
contribution lissée a une partie imaginaire NON NULLE (le facteur tourne d'un angle de tangente
`−T/(β + 1)`). Aucun transport automatique des contacts bruts au terme lissé. -/
theorem residueTerm_im_at_own_contact_ne_zero (z : TrueZero) (k : ℤ) :
    (nontrivialZeroResidueTerm (contactMinusAt z k) (memberIndex z)).im ≠ 0 := by
  rw [residueTerm_at_own_contact, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_add, smoothingFactor_im]
  have hm : (0 : ℝ) < zetaZeroMultiplicity (zeroPoint z) := by
    exact_mod_cast zetaZeroMultiplicity_pos (zeroPoint_isNontrivial z).1
  have hT := z.2
  have hden : 0 < (rZeroRadialPosition z.1 + 1) ^ 2 + rZeroHeight z.1 ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hT 2)
  have hnorm : 0 < ‖zeroTerm z (contactMinusAt z k)‖ := by
    rw [zeroTerm_norm (contactMinusAt_positive z k)]
    exact div_pos (Real.rpow_pos_of_pos (contactMinusAt_positive z k) _) (norm_zeroPoint_pos z)
  have hk : (-1 : ℝ) ^ k ≠ 0 := zpow_ne_zero _ (by norm_num)
  exact mul_ne_zero (div_pos (mul_pos hm hT) hden).ne' (mul_ne_zero hk hnorm.ne')

/-- **La contribution d'un membre dans la somme collective, sans l'isoler** : pour `x > 1` et toute
hauteur
`H ≥ T_z`, le reste lissé des premiers est la contribution lissée de `z` plus la somme finie des
autres
contributions de hauteur `≤ H` plus la somme à l'infini des suivants. Identité entre objets ; elle
ne
borne rien. -/
theorem remainder_eq_member_add_others (z : TrueZero) {H x : ℝ} (hz : rZeroHeight z.1 ≤ H)
    (hx : 1 < x) :
    smoothedRemainder x = smoothingFactor z * zeroTerm z x +
      (∑ σ ∈ (precedingIndices_finite H).toFinset.erase (memberIndex z),
        nontrivialZeroResidueTerm x σ) + followingSum H x := by
  rw [remainder_eq_preceding_add_following H hx, precedingSum_split_member H x z hz,
    residueTerm_eq_smoothingFactor_mul]

/-! ## 4. Dérivée de la contribution de comptage : la Tour brute comme variation (DÉMONTRÉ, pour
toute
primitive locale de `e^w/w`) -/

/-- **Identité différentielle** : pour toute fonction `F` dont la dérivée au point `ρ log x` est
`e^{ρ log x}/(ρ log x)` (toute primitive locale de `e^w/w`, quelle que soit la branche choisie), la
composée `y ↦ F(ρ log y)` a pour dérivée en `x > 1` la valeur `ρ · zeroTerm_ρ(x)/(x log x)`. Elle
relie la
Tour brute à la variation de la contribution de comptage ; elle n'identifie ni leurs contacts ni
leurs
extrema. Mathlib ne définit pas `Ei` : la primitive est une hypothèse explicite, pas un objet du
dépôt. -/
theorem counting_contribution_hasDerivAt (z : TrueZero) {F : ℂ → ℂ} {x : ℝ} (hx : 1 < x)
    (hF : HasDerivAt F
      (Complex.exp (zeroPoint z * (Real.log x : ℂ)) / (zeroPoint z * (Real.log x : ℂ)))
      (zeroPoint z * (Real.log x : ℂ))) :
    HasDerivAt (fun y : ℝ => F (zeroPoint z * (Real.log y : ℂ)))
      (zeroPoint z * zeroTerm z x / ((x : ℂ) * (Real.log x : ℂ))) x := by
  have hx0 : 0 < x := lt_trans one_pos hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hinner : HasDerivAt (fun y : ℝ => zeroPoint z * (Real.log y : ℂ))
      (zeroPoint z * ((x⁻¹ : ℝ) : ℂ)) x :=
    (Real.hasDerivAt_log hx0.ne').ofReal_comp.const_mul (zeroPoint z)
  have hρ := zeroPoint_ne_zero z
  have hcpow : (x : ℂ) ^ zeroPoint z = Complex.exp (zeroPoint z * (Real.log x : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx0.ne'), Complex.ofReal_log hx0.le,
      mul_comm]
  have hlog' : (Real.log x : ℂ) ≠ 0 := by exact_mod_cast hlog.ne'
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have heq : zeroPoint z * zeroTerm z x / ((x : ℂ) * (Real.log x : ℂ)) =
      Complex.exp (zeroPoint z * (Real.log x : ℂ)) / (zeroPoint z * (Real.log x : ℂ)) *
        (zeroPoint z * ((x⁻¹ : ℝ) : ℂ)) := by
    unfold zeroTerm
    rw [hcpow]
    push_cast
    field_simp
  rw [heq]
  exact HasDerivAt.comp x hF hinner

/-! ## 5. Les canaux arithmétiques et leurs incréments exacts (DÉMONTRÉ) ; le déficit de comptage et
son
absence de liaison avec le reste lissé (MANQUE EXPOSÉ) -/

/-- Le `n`-ième premier a exactement `n + 1` premiers jusqu'à lui compris : `π(p_n) = n + 1`. -/
theorem primeCounting_primeAtRank (n : ℕ) : Nat.primeCounting (fnPrimeAtRank n) = n + 1 := by
  unfold fnPrimeAtRank
  rw [Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting', Nat.count_succ,
    ← Nat.primeCounting', Nat.primeCounting'_nth_eq, if_pos (Nat.prime_nth_prime n)]

/-- **Saut du canal `π`** : entre deux premiers consécutifs, le comptage des premiers avance de `1`.
-/
theorem primeCounting_step (n : ℕ) :
    Nat.primeCounting (fnPrimeAtRank (n + 1)) = Nat.primeCounting (fnPrimeAtRank n) + 1 := by
  rw [primeCounting_primeAtRank, primeCounting_primeAtRank]

/-- **Saut du canal `ψ` en un premier** : `Λ(p) = log p`, le poids de l'événement premier. -/
theorem psi_jump_at_prime (n : ℕ) :
    ArithmeticFunction.vonMangoldt (fnPrimeAtRank n) = Real.log (fnPrimeAtRank n) :=
  ArithmeticFunction.vonMangoldt_apply_prime (thm_primeAtRank_isPrime n)

/-- **Le canal `ψ` compte aussi les puissances de premiers** : `Λ(p^{k+1}) = log p ≠ 0`. Les sauts
de `π` et
ceux de `ψ` ne sont pas les mêmes événements. -/
theorem psi_jump_at_prime_power (n k : ℕ) :
    ArithmeticFunction.vonMangoldt (fnPrimeAtRank n ^ (k + 1)) = Real.log (fnPrimeAtRank n) :=
  ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k) |>.trans
    (ArithmeticFunction.vonMangoldt_apply_prime (thm_primeAtRank_isPrime n))

/-- L'intégrale logarithmique décalée `li₂(x) = ∫_2^x dt/log t` (convention : borne inférieure `2`,
aucune
valeur principale). Objet nouveau de ce module ; aucun théorème du dépôt ne le relie au reste lissé.
-/
noncomputable def offsetLogIntegral (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-- `1/log t` est continue sur tout intervalle fermé contenu dans `[2, ∞)`. -/
theorem inv_log_continuousOn {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc a b) := by
  apply ContinuousOn.div continuousOn_const
  · apply Real.continuousOn_log.mono
    intro t ht
    rw [Set.mem_uIcc] at ht
    have : 2 ≤ t := by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    exact ne_of_gt (by linarith)
  · intro t ht
    rw [Set.mem_uIcc] at ht
    have : 2 ≤ t := by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    exact ne_of_gt (Real.log_pos (by linarith))

theorem inv_log_intervalIntegrable {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b :=
  (inv_log_continuousOn ha hb).intervalIntegrable

/-- **Incrément de `li₂` entre deux abscisses `≥ 2`** : `li₂(b) − li₂(a) = ∫_a^b dt/log t`. -/
theorem offsetLogIntegral_sub {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    offsetLogIntegral b - offsetLogIntegral a = ∫ t in a..b, 1 / Real.log t := by
  unfold offsetLogIntegral
  rw [intervalIntegral.integral_interval_sub_left (inv_log_intervalIntegrable le_rfl hb)
    (inv_log_intervalIntegrable le_rfl ha)]

/-- Le déficit de comptage `R(x) = π(x) − li₂(x)` aux entiers. Objet nouveau ; non relié au reste
lissé. -/
noncomputable def countingDeficit (n : ℕ) : ℝ := (Nat.primeCounting n : ℝ) - offsetLogIntegral n

/-- **Incrément exact du déficit entre deux premiers consécutifs** :
`R(p_{n+1}) − R(p_n) = 1 − ∫_{p_n}^{p_{n+1}} dt/log t`. Démontré avec les conventions de ce module
(borne
`2`, premiers `≥ 2`). C'est l'incrément du canal `π − li`, pas celui du reste lissé `ψ`-pondéré :
aucun
théorème ne lie `countingDeficit` à `smoothedRemainder`. -/
theorem countingDeficit_step (n : ℕ) :
    countingDeficit (fnPrimeAtRank (n + 1)) - countingDeficit (fnPrimeAtRank n) =
      1 - ∫ t in (fnPrimeAtRank n : ℝ)..(fnPrimeAtRank (n + 1) : ℝ), 1 / Real.log t := by
  unfold countingDeficit
  have h2 : (2 : ℝ) ≤ fnPrimeAtRank n := by exact_mod_cast (thm_primeAtRank_isPrime n).two_le
  have h2' : (2 : ℝ) ≤ fnPrimeAtRank (n + 1) := by
    exact_mod_cast (thm_primeAtRank_isPrime (n + 1)).two_le
  rw [primeCounting_step, ← offsetLogIntegral_sub h2 h2']
  push_cast
  ring

/-! ## 6. Obligations exactes sur une fenêtre : amplitude d'une Tour contre progression première
(DÉMONTRÉ ; aucune borne de fenêtre ne devient une borne par passage) -/

/-- **Amplitude d'une Tour lue aux deux bouts d'une fenêtre de `m` transitions premières** :
`A(p_{n+m})/A(p_n) = (p_{n+m}/p_n)^{β − 1/2}`. -/
theorem window_amplitude_ratio (z : TrueZero) (n m : ℕ) :
    normalizedRadius z (fnPrimeAtRank (n + m)) / normalizedRadius z (fnPrimeAtRank n) =
      ((fnPrimeAtRank (n + m) : ℝ) / (fnPrimeAtRank n : ℝ)) ^
        (rZeroRadialPosition z.1 - 1 / 2) := by
  have h0 : (0 : ℝ) < fnPrimeAtRank n := by exact_mod_cast thm_primeAtRank_pos n
  have h1 : (0 : ℝ) < fnPrimeAtRank (n + m) := by exact_mod_cast thm_primeAtRank_pos _
  exact normalizedRadius_ratio z h0 h1

/-- **Sous la ligne, l'amplitude normalisée décroît sur toute fenêtre paire, d'au moins le plancher
premier** :
`A(p_{n+m})/A(p_n) ≤ (1 + 3m/p_n)^{β − 1/2} < 1` (`β < 1/2`, `m` pair non nul, `p_n > 3`). La
progression
première (fonction du rang seul) fixe le plancher du rapport des abscisses ; la partie réelle fixe
le
sens. La borne porte sur UNE Tour entre deux premiers ; elle ne dit rien d'un passage entre deux
Tours. -/
theorem window_amplitude_decay_of_low (z : TrueZero) (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (n m : ℕ) (hm : Even m) (hm0 : m ≠ 0) (h3 : 3 < fnPrimeAtRank n) :
    normalizedRadius z (fnPrimeAtRank (n + m)) / normalizedRadius z (fnPrimeAtRank n) ≤
        (1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ)) ^ (rZeroRadialPosition z.1 - 1 / 2) ∧
      (1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ)) ^ (rZeroRadialPosition z.1 - 1 / 2) < 1 := by
  have h0 : (0 : ℝ) < fnPrimeAtRank n := by exact_mod_cast thm_primeAtRank_pos n
  have hw : (fnPrimeAtRank n : ℝ) + 3 * (m : ℝ) ≤ (fnPrimeAtRank (n + m) : ℝ) := by
    exact_mod_cast primeAtRank_window_ge_three_mul n m hm h3
  have hbase : 1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ) ≤
      (fnPrimeAtRank (n + m) : ℝ) / (fnPrimeAtRank n : ℝ) := by
    have hrew : (1 : ℝ) + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ) =
        ((fnPrimeAtRank n : ℝ) + 3 * (m : ℝ)) / (fnPrimeAtRank n : ℝ) := by field_simp
    rw [hrew]
    exact div_le_div_of_nonneg_right hw h0.le
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hgt1 : 1 < 1 + 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ) := by
    have : 0 < 3 * (m : ℝ) / (fnPrimeAtRank n : ℝ) := by positivity
    linarith
  have hneg : rZeroRadialPosition z.1 - 1 / 2 < 0 := by linarith
  refine ⟨?_, ?_⟩
  · rw [window_amplitude_ratio]
    exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hneg.le (Set.mem_Ioi.mpr (by linarith))
      (Set.mem_Ioi.mpr (lt_of_lt_of_le (by linarith) hbase)) hbase
  · exact Real.rpow_lt_one_of_one_lt_of_neg hgt1 hneg

/-! ## 7. La flèche réelle, composée sous l'obligation d'enroulement entier (ancienne prémisse,
désormais hypothèse ⟺ RH ; CONDITIONNEL) ; le premier raccord non
démontré (OUVERT) -/

/-- **Lecture conjointe sous l'obligation d'enroulement entier (ancienne prémisse), sur un passage
parti du zéro ON engagé** : si la
Tour du
membre atteint reste sous celle du membre précédent en tout point de l'axe positif, alors (1) la
partie
réelle est conservée, `β_l = 1/2` ; (2) l'amplitude normalisée de `l` est plate à ses contacts
propres ;
(3) le pas logarithmique de `l` est strictement contracté par rapport à celui de `e` ; (4) aux
contacts de
`e`, le rayon normalisé de `l` est conservé. Chaque conséquence est une lecture de `(β_l, T_l)` ; la
prémisse n'est pas dérivée ici. -/
theorem joint_reading_of_whole_winding (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) (hV : VerticalPassage p)
    (hWind : ∀ x : ℝ, 0 < x →
      ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ∧
      (∀ k : ℤ, normalizedRadius ⟨p.zLaterMember, hL⟩
          (contactMinusAt ⟨p.zLaterMember, hL⟩ (k + 1)) =
        normalizedRadius ⟨p.zLaterMember, hL⟩ (contactMinusAt ⟨p.zLaterMember, hL⟩ k)) ∧
      towerPitch ⟨p.zLaterMember, hL⟩ < towerPitch ⟨p.zEarlierMember, hE⟩ ∧
      (∀ k : ℤ, normalizedRadius ⟨p.zLaterMember, hL⟩
          (contactMinusAt ⟨p.zEarlierMember, hE⟩ (k + 1)) =
        normalizedRadius ⟨p.zLaterMember, hL⟩ (contactMinusAt ⟨p.zEarlierMember, hE⟩ k)) := by
  have hβ : rZeroRadialPosition p.zLaterMember = 1 / 2 :=
    (whole_winding_conserves_radial p hE hL hWind).1.trans hOn
  refine ⟨hβ, fun k => (own_contact_amplitude_flat_iff _ k).mpr hβ,
    (vertical_iff_pitch_contracts p hE hL).mp hV, fun k => ?_⟩
  have h1 := (radius_step_eq_one_iff ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩).mpr hβ
  rw [(joint_cross_reading ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ k).2, h1, one_mul]

/-- **Renouvellement de la progression de hauteur sous l'obligation d'enroulement entier (ancienne
prémisse)** : depuis le zéro ON
engagé `e`,
`p : e → l` monte (acquis) ; si la Tour de `l` reste sous celle de `e` en tout point de l'axe
positif
(prémisse, lue sur CE passage seulement), alors `q : l → s` monte. Composition : conservation de la
partie réelle (`whole_winding_conserves_radial`) puis régime gardé (`engaged_regime_kept`).
Fermeture
ensuite par `junction_vertical_vertical`. -/
theorem renewed_height_advance_of_whole_winding {o p q : TZeroPassage}
    (hJ : o.zLaterMember = p.zEarlierMember) (hJq : p.zLaterMember = q.zEarlierMember)
    (hE : 0 < rZeroHeight o.zLaterMember) (ho : VerticalPassage o)
    (hOn : rZeroRadialPosition o.zLaterMember = 1 / 2)
    (hWind : ∀ (hE' : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember),
      ∀ x : ℝ, 0 < x →
        ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE'⟩ x‖) :
    VerticalPassage q := by
  have hV : VerticalPassage p := (engaged_regime_kept hJ ho hOn).1
  have hOnE : rZeroRadialPosition p.zEarlierMember = 1 / 2 := by rw [← hJ]; exact hOn
  have hPE : 0 < rZeroHeight p.zEarlierMember := by rw [← hJ]; exact hE
  have hPL : 0 < rZeroHeight p.zLaterMember := lt_of_lt_of_le hPE (passage_height_le p)
  have hOnL := (joint_reading_of_whole_winding p hPE hPL hOnE hV (hWind hPE hPL)).1
  exact (engaged_regime_kept hJq hV hOnL).1

/-- **Nécessité** : sous RH, la prémisse tient sur tout passage (sens acquis de
`riemannHypothesis_iff_passage_whole_winding`). Avec
`riemannHypothesis_of_whole_winding_all_passages`,
l'équivalence est complète ; elle n'est PAS une dérivation de la prémisse. -/
theorem whole_winding_all_passages_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ p : TZeroPassage, ∀ (hE : 0 < rZeroHeight p.zEarlierMember)
      (hL : 0 < rZeroHeight p.zLaterMember), ∀ x : ℝ, 0 < x →
      ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖ :=
  riemannHypothesis_iff_passage_whole_winding.mpr hRH

/-- **Premier raccord non démontré, énoncé exactement (OUVERT)** : la représentation exacte du reste
lissé
par les contributions des vrais zéros est acquise pour tout `x > 1`
(`smoothedRemainder_eq_tsum_residueTerm`) ;
ce qui n'est pas dérivé est que cette identité impose, à chaque zéro, la non-croissance de son
amplitude
normalisée entre deux contacts propres consécutifs, c'est-à-dire `β ≤ 1/2`. Ce théorème dit
seulement que
cette non-croissance pour TOUS les zéros donne la prémisse sur tout passage (par réflexion : un zéro
et son
miroir sont tous deux au plus à un demi, donc en ligne), donc RH : c'est une CARACTÉRISATION de
plus, pas la
flèche ; elle sert à nommer exactement le raccord manquant, sans le poser en hypothèse d'un théorème
de
fermeture. -/
theorem whole_winding_of_own_contact_amplitude_nonincreasing
    (h : ∀ z : TrueZero, ∀ k : ℤ,
      normalizedRadius z (contactMinusAt z (k + 1)) ≤ normalizedRadius z (contactMinusAt z k)) :
    ∀ p : TZeroPassage, ∀ (hE : 0 < rZeroHeight p.zEarlierMember)
      (hL : 0 < rZeroHeight p.zLaterMember), ∀ x : ℝ, 0 < x →
      ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖ := by
  have hle : ∀ z : TrueZero, rZeroRadialPosition z.1 ≤ 1 / 2 := by
    intro z
    have hk := h z 0
    have hpos := normalizedRadius_pos z (contactMinusAt_positive z 0)
    rw [radius_step_between_contacts z z 0] at hk
    have hexp : Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * Real.pi / rZeroHeight z.1) ≤ 1 := by
      by_contra hgt
      push Not at hgt
      have := mul_lt_mul_of_pos_right hgt hpos
      rw [one_mul] at this
      exact absurd hk (not_le.mpr this)
    rw [Real.exp_le_one_iff] at hexp
    have hT := z.2
    have hnum : (rZeroRadialPosition z.1 - 1 / 2) * Real.pi ≤ 0 := by
      by_contra hc
      push Not at hc
      exact absurd hexp (not_le.mpr (div_pos hc hT))
    by_contra hc
    push Not at hc
    have := mul_pos (sub_pos.mpr hc) Real.pi_pos
    linarith
  have hOn : ∀ z : TrueZero, rZeroRadialPosition z.1 = 1 / 2 := by
    intro z
    have h1 := hle z
    have h2 := hle (mirrorMember z)
    rw [mirrorMember_radial] at h2
    linarith
  intro p hE hL
  exact (whole_winding_iff_onLine p hE hL (hOn ⟨p.zEarlierMember, hE⟩)).mpr
    (hOn ⟨p.zLaterMember, hL⟩)

#print axioms contact_log_step
#print axioms normalizedRadius_eq_pitch
#print axioms normalizedRadius_ratio
#print axioms normalizedRadius_own_contact_step
#print axioms normalizedRadius_onLine_pitch
#print axioms own_contact_amplitude_flat_iff
#print axioms joint_cross_reading
#print axioms inversion_from_consecutive_contacts
#print axioms unknown_contact_bracket
#print axioms residueTerm_eq_smoothingFactor_mul
#print axioms smoothingFactor_norm
#print axioms residueTerm_re_at_own_contact
#print axioms residueTerm_im_at_own_contact_ne_zero
#print axioms remainder_eq_member_add_others
#print axioms counting_contribution_hasDerivAt
#print axioms primeCounting_step
#print axioms psi_jump_at_prime_power
#print axioms countingDeficit_step
#print axioms window_amplitude_decay_of_low
#print axioms joint_reading_of_whole_winding
#print axioms renewed_height_advance_of_whole_winding
#print axioms whole_winding_all_passages_of_riemannHypothesis
#print axioms whole_winding_of_own_contact_amplitude_nonincreasing

end RHV6Fresh
