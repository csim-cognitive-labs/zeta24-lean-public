/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PairWordInversion
import RHV6Fresh.Terminal.PairBreakOfZero
import RHV6Fresh.Terminal.Universalization
import RHV6Fresh.Terminal.FixedGapRaccords
import RHV6Fresh.Terminal.MeetingPriceTheorem

/-!
# RHV6Fresh — Terminal/CarrierSelection : nommer l'arête manquante et isoler la sélection des porteurs
(E457, plan Φ étapes Φ0 + Φ1, §19.80 et §19.82, 2026-11-08 ; module isolé, NON importé par `RHV6Fresh.lean` ;
aucune hypothèse, aucun axiome, aucun `sorry`)

Point de départ (validé par l'auteur, §19.80) : la causalité compilée premiers + (β, T) → mot → Tour et miroir est complète
en aval de la Tour et muette sur la SÉLECTION des porteurs : le seul nœud non lu par le canal des contacts est le poids
`zeroMult` (E451). Ce module (i) NOMME ce que l'arête doit livrer par trois reformulations exactes de RH, qui ne sont jamais
des prémisses, et (ii) prouve que la sélection n'est dans aucun préfixe fini du mot.

## 1. Mots et porteurs
* `towerWord β T n` : mot de la Tour `(β, T)` au premier de rang `n` (dernier contact avant ce premier, E449/E453) ;
  `zeroWord z` : mot d'un zéro vrai ; `towerPoint β T = β + iT` ; `IsCarrier β T` : poids non nul.
* `isCarrier_zero` : un zéro vrai est porteur ; `not_isCarrier_iff` : hors du pôle, non porteur ⟺ zêta ne s'annule pas.
## 2. R1 — `carrierWordsSelfMirror_iff_riemannHypothesis` : « tout mot porteur égale le mot de son miroir » ⟺ RH.
## 3. R2 — `heightInjectiveOnCarriers_iff_riemannHypothesis` : « deux zéros vrais supérieurs de même hauteur sont le même » ⟺ RH ;
  `noMixedHeight_of_heightInjective` : R2 ⟹ `NoMixedHeight` (la réciproque n'a pas été obtenue par sonde, voir E457).
## 4. R3 — `priceRadiallyBlindOnCarriers_iff_riemannHypothesis` : « le prix d'E445 (`offPrice`, normalisé par
  `pair_amplitude_eq_price` : `x^β + x^{1−β} = 2√x · offPrice β x`) vaut celui de la ligne (`offPrice_line` : 1) en tout premier,
  pour tout zéro vrai » ⟺ RH ; variante R3' `termModulusMirrorBlind_iff_riemannHypothesis` : « le terme du zéro et celui de son
  miroir ont même module en tout premier » ⟺ RH ; `radial_half_of_term_modulus_eq_two_primes` : DEUX premiers distincts suffisent
  (le rapport `x^{2β−1}·‖ρ*‖/‖ρ‖` de `zero_pair_term_ratio` porte un facteur de normalisation constant, d'où deux points).
## 5. Φ1 — stabilité du mot vers la droite en β
* `continuousAt_stagePosition_radial`, `floor_stable_right_of_continuous_mono` : la position d'étage est continue et strictement
  croissante en `β` ; la partie entière étant continue à droite, un premier EXACTEMENT sur un contact (fraction de cellule nulle)
  reste dans sa cellule quand `β` croît — c'est la direction de perturbation qui préserve toutes les lectures, convention de bord
  comprise ; `towerWord_stable_right`, `towerWord_stable_right_finset` : le mot est conservé sur tout ensemble fini de rangs.
## 6. Φ1 — `exists_nonCarrier_same_word_on_finset` : pour tout zéro vrai `z`, tout ensemble fini de rangs `S` et tout `ε > 0`, il
  existe `β'` avec `β < β' < min(β + ε, 1)` tel que la Tour `(β', T)` — MÊME hauteur, même fréquence — n'est pas porteuse et a le
  même mot que `z` sur `S` (zéros isolés : `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, ordre d'annulation fini).
## 7. `finite_window_predicate_not_carrier_selective` : tout prédicat sur les mots qui ne dépend que d'un nombre fini de rangs, vrai
  sur le mot d'un zéro, est vrai sur le mot d'une Tour non porteuse de même hauteur. K0 (E450) et A4 (E429) sont des théorèmes ;
  la route des fenêtres finies (grammaire modulo 6 comprise) est fermée ; portée exacte (rectification 2026-11-09, §19.85) : la sélection des
  porteurs ne peut pas être caractérisée par un prédicat portant EXCLUSIVEMENT sur une fenêtre finie du mot ; il n'est PAS démontré
  qu'elle ne dépende que de la queue du mot, et une condition locale enrichie d'une information indépendante du mot n'est pas exclue.

Portée : aucune contradiction n'est tirée ; aucune des trois reformulations n'est posée ; aucune théorie spectrale.
-/

namespace RHV6Fresh

open Real Filter Topology RHV3Lean
open Complex (I)

/-! ## 1. Mots et porteurs -/

noncomputable def towerWord (β T : ℝ) (n : ℕ) : ℤ := lastContactBefore β T (fnPrimeAtRank n : ℝ)

noncomputable def zeroWord (z : TrueZero) : ℕ → ℤ := towerWord (rZeroRadialPosition z.1) (rZeroHeight z.1)

noncomputable def towerPoint (β T : ℝ) : ℂ := (β : ℂ) + (T : ℂ) * I

def IsCarrier (β T : ℝ) : Prop := zeroMult (towerPoint β T) ≠ 0

theorem towerPoint_re (β T : ℝ) : (towerPoint β T).re = β := by simp [towerPoint]

theorem towerPoint_im (β T : ℝ) : (towerPoint β T).im = T := by simp [towerPoint]

theorem towerPoint_zeroPoint (z : TrueZero) :
    towerPoint (rZeroRadialPosition z.1) (rZeroHeight z.1) = zeroPoint z := by
  apply Complex.ext
  · rw [towerPoint_re, zeroPoint_re]
  · rw [towerPoint_im, zeroPoint_im]

theorem towerPoint_ne_one {β T : ℝ} (hT : 0 < T) : towerPoint β T ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  rw [towerPoint_im] at this
  simp at this
  linarith

theorem zeroPoint_ne_one (z : TrueZero) : zeroPoint z ≠ 1 := by
  rw [← towerPoint_zeroPoint]
  exact towerPoint_ne_one (zero_height_pos z)

theorem isCarrier_zero (z : TrueZero) : IsCarrier (rZeroRadialPosition z.1) (rZeroHeight z.1) := by
  unfold IsCarrier
  rw [towerPoint_zeroPoint]
  exact Nat.one_le_iff_ne_zero.mp (one_le_zeroMult_zeroPoint z)

theorem not_isCarrier_iff {β T : ℝ} (hT : 0 < T) :
    ¬ IsCarrier β T ↔ riemannZeta (towerPoint β T) ≠ 0 := by
  unfold IsCarrier
  rw [not_not]
  exact zeroMult_eq_zero_iff (towerPoint_ne_one hT)

/-! ## 2. R1 : les mots porteurs sont égaux à leur miroir -/

def CarrierWordsSelfMirror : Prop := ∀ z : TrueZero, zeroWord (mirrorMember z) = zeroWord z

theorem carrierWordsSelfMirror_iff_riemannHypothesis : CarrierWordsSelfMirror ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply thm_riemannHypothesis_of_allUpperOnCriticalLine
    intro z
    exact (zero_pair_words_eq_iff z).mp (fun n => congrFun (h z) n)
  · intro hRH z
    rw [mirrorMember_eq_self_of_onLine (thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1)]

/-! ## 3. R2 : la hauteur est injective sur les porteurs -/

def HeightInjectiveOnCarriers : Prop := ∀ z w : TrueZero, rZeroHeight z.1 = rZeroHeight w.1 → z = w

theorem heightInjectiveOnCarriers_iff_riemannHypothesis : HeightInjectiveOnCarriers ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply thm_riemannHypothesis_of_allUpperOnCriticalLine
    intro z
    have hm := h (mirrorMember z) z (mirrorMember_ordinate z)
    have hr := mirrorMember_radial z
    rw [hm] at hr
    linarith
  · intro hRH z w hzw
    have hz := thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1
    have hw := thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1
    apply Subtype.ext
    apply Subtype.ext
    apply Complex.ext
    · change rZeroRadialPosition z.1 = rZeroRadialPosition w.1
      rw [hz, hw]
    · exact hzw

theorem noMixedHeight_of_heightInjective (h : HeightInjectiveOnCarriers) : NoMixedHeight :=
  noMixedHeight_of_riemannHypothesis (heightInjectiveOnCarriers_iff_riemannHypothesis.mp h)

/-! ## 4. R3 : le prix est radialement aveugle sur les porteurs -/

theorem offPrice_line (x : ℝ) : offPrice (1 / 2) x = 1 := by
  unfold offPrice
  simp

theorem offPrice_eq_one_iff {β x : ℝ} (hx : 1 < x) : offPrice β x = 1 ↔ β = 1 / 2 := by
  constructor
  · intro h
    by_contra hne
    have hz : (β - 1 / 2) * Real.log x ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hne) (Real.log_pos hx).ne'
    exact absurd h (ne_of_gt (Real.one_lt_cosh.mpr hz))
  · intro h
    subst h
    exact offPrice_line x

def PriceRadiallyBlindOnCarriers : Prop :=
  ∀ (z : TrueZero) (n : ℕ), offPrice (rZeroRadialPosition z.1) (fnPrimeAtRank n : ℝ) = 1

theorem one_lt_primeAtRank_real (n : ℕ) : (1 : ℝ) < (fnPrimeAtRank n : ℝ) := by
  exact_mod_cast (thm_primeAtRank_isPrime n).one_lt

theorem priceRadiallyBlindOnCarriers_iff_riemannHypothesis :
    PriceRadiallyBlindOnCarriers ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply thm_riemannHypothesis_of_allUpperOnCriticalLine
    intro z
    exact (offPrice_eq_one_iff (one_lt_primeAtRank_real 0)).mp (h z 0)
  · intro hRH z n
    rw [thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1]
    exact offPrice_line _

def TermModulusMirrorBlind : Prop :=
  ∀ (z : TrueZero) (n : ℕ),
    ‖zeroTerm z (fnPrimeAtRank n : ℝ)‖ = ‖zeroTerm (mirrorMember z) (fnPrimeAtRank n : ℝ)‖

theorem rpow_mul_const_eq_one_at_two_points {a c x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ y) (h1 : x ^ a * c = 1) (h2 : y ^ a * c = 1) : a = 0 := by
  have hxy' : x ^ a = y ^ a := mul_right_cancel₀ hc.ne' (h1.trans h2.symm)
  have hl := congrArg Real.log hxy'
  rw [Real.log_rpow hx, Real.log_rpow hy] at hl
  have hne : Real.log x ≠ Real.log y :=
    fun h => hxy (Real.log_injOn_pos (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy) h)
  by_contra ha
  exact hne (mul_left_cancel₀ ha hl)

theorem radial_half_of_term_modulus_eq_two_primes (z : TrueZero) {m n : ℕ} (hmn : m ≠ n)
    (hm : ‖zeroTerm z (fnPrimeAtRank m : ℝ)‖ = ‖zeroTerm (mirrorMember z) (fnPrimeAtRank m : ℝ)‖)
    (hn : ‖zeroTerm z (fnPrimeAtRank n : ℝ)‖ = ‖zeroTerm (mirrorMember z) (fnPrimeAtRank n : ℝ)‖) :
    rZeroRadialPosition z.1 = 1 / 2 := by
  have hpm : (0 : ℝ) < fnPrimeAtRank m := by exact_mod_cast thm_primeAtRank_pos m
  have hpn : (0 : ℝ) < fnPrimeAtRank n := by exact_mod_cast thm_primeAtRank_pos n
  have hne : (fnPrimeAtRank m : ℝ) ≠ fnPrimeAtRank n := by
    exact_mod_cast thm_primeAtRank_strictMono.injective.ne hmn
  have hmir : 0 < ‖zeroPoint (mirrorMember z)‖ := norm_pos_iff.mpr (zeroPoint_ne_zero _)
  have hself : 0 < ‖zeroPoint z‖ := norm_pos_iff.mpr (zeroPoint_ne_zero _)
  have hzm : 0 < ‖zeroTerm (mirrorMember z) (fnPrimeAtRank m : ℝ)‖ := by
    rw [mirror_zeroTerm_norm hpm]; exact div_pos (Real.rpow_pos_of_pos hpm _) hmir
  have hzn : 0 < ‖zeroTerm (mirrorMember z) (fnPrimeAtRank n : ℝ)‖ := by
    rw [mirror_zeroTerm_norm hpn]; exact div_pos (Real.rpow_pos_of_pos hpn _) hmir
  have r1 : ‖zeroTerm z (fnPrimeAtRank m : ℝ)‖ / ‖zeroTerm (mirrorMember z) (fnPrimeAtRank m : ℝ)‖ = 1 := by
    rw [hm, div_self hzm.ne']
  have r2 : ‖zeroTerm z (fnPrimeAtRank n : ℝ)‖ / ‖zeroTerm (mirrorMember z) (fnPrimeAtRank n : ℝ)‖ = 1 := by
    rw [hn, div_self hzn.ne']
  rw [zero_pair_term_ratio z hpm] at r1
  rw [zero_pair_term_ratio z hpn] at r2
  have := rpow_mul_const_eq_one_at_two_points (div_pos hmir hself) hpm hpn hne r1 r2
  linarith

theorem termModulusMirrorBlind_iff_riemannHypothesis : TermModulusMirrorBlind ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply thm_riemannHypothesis_of_allUpperOnCriticalLine
    intro z
    exact radial_half_of_term_modulus_eq_two_primes z (by norm_num : (0 : ℕ) ≠ 1) (h z 0) (h z 1)
  · intro hRH z n
    rw [mirrorMember_eq_self_of_onLine (thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1)]

/-! ## 5. Φ1 : stabilité du mot vers la droite en β -/

theorem continuousAt_stagePosition_radial {β : ℝ} (hβ : 0 < β) (T q : ℝ) :
    ContinuousAt (fun b : ℝ => stagePosition b T q) β := by
  simp only [stagePosition]
  apply ContinuousAt.div_const
  apply ContinuousAt.sub continuousAt_const
  have h1 : ContinuousAt (fun b : ℝ => T / b) β := continuousAt_const.div continuousAt_id hβ.ne'
  exact Real.continuous_arctan.continuousAt.comp h1

theorem floor_stable_right_of_continuous_mono {f : ℝ → ℝ} {β : ℝ} (hc : ContinuousAt f β)
    (hmono : ∀ b, β < b → f β < f b) :
    ∃ δ > 0, ∀ b, β < b → b < β + δ → ⌊f b⌋ = ⌊f β⌋ := by
  have h1 : f β < ⌊f β⌋ + 1 := Int.lt_floor_add_one _
  have hev : ∀ᶠ b in 𝓝 β, f b < ⌊f β⌋ + 1 := hc.eventually (gt_mem_nhds h1)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun b hb1 hb2 => ?_⟩
  rw [Int.floor_eq_iff]
  constructor
  · exact le_trans (Int.floor_le _) (le_of_lt (hmono b hb1))
  · apply hball
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

theorem towerWord_stable_right {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (n : ℕ) :
    ∃ δ > 0, ∀ b, β < b → b < β + δ → towerWord b T n = towerWord β T n :=
  floor_stable_right_of_continuous_mono (continuousAt_stagePosition_radial hβ T _)
    (fun _b hb => stagePosition_lt_of_radial_lt hT hβ hb _)

theorem towerWord_stable_right_finset {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (S : Finset ℕ) :
    ∃ δ > 0, ∀ b, β < b → b < β + δ → ∀ n ∈ S, towerWord b T n = towerWord β T n := by
  have hev : ∀ n ∈ S, ∀ᶠ b in 𝓝[>] β, towerWord b T n = towerWord β T n := by
    intro n _
    obtain ⟨δ, hδ, h⟩ := towerWord_stable_right hβ hT n
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨δ, hδ, fun b hd hb => h b hb ?_⟩
    rw [Real.dist_eq, abs_lt] at hd
    linarith [hd.2]
  rw [← Filter.eventually_all_finset, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, h⟩ := hev
  refine ⟨δ, hδ, fun b hb1 hb2 => h ?_ hb1⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ## 6. Φ1 : théorème d'isolement -/

theorem exists_nonCarrier_same_word_on_finset (z : TrueZero) (S : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ β' : ℝ, rZeroRadialPosition z.1 < β' ∧ β' < rZeroRadialPosition z.1 + ε ∧ β' < 1 ∧
      ¬ IsCarrier β' (rZeroHeight z.1) ∧ ∀ n ∈ S, towerWord β' (rZeroHeight z.1) n = zeroWord z n := by
  have hβ : 0 < rZeroRadialPosition z.1 := zero_radial_pos z
  have hβ1 : rZeroRadialPosition z.1 < 1 := zero_radial_lt_one z
  have hT : 0 < rZeroHeight z.1 := zero_height_pos z
  have han : AnalyticAt ℂ riemannZeta (zeroPoint z) :=
    riemannZeta_analyticOnNhd_compl_one _ (zeroPoint_ne_one z)
  have hne : ∀ᶠ w in 𝓝[≠] zeroPoint z, riemannZeta w ≠ 0 := by
    rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.mpr h) (analyticOrderAt_riemannZeta_ne_top (zeroPoint_ne_one z))
    · exact h
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne
  obtain ⟨δ₀, hδ₀, hiso⟩ := hne
  obtain ⟨δ₁, hδ₁, hword⟩ := towerWord_stable_right_finset hβ hT S
  set η := min (min δ₀ δ₁) (min ε (1 - rZeroRadialPosition z.1)) with hη
  have hηpos : 0 < η := lt_min (lt_min hδ₀ hδ₁) (lt_min hε (by linarith))
  have hη0 : η ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hη1 : η ≤ δ₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hηε : η ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hηβ : η ≤ 1 - rZeroRadialPosition z.1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨rZeroRadialPosition z.1 + η / 2, by linarith, by linarith, by linarith, ?_, ?_⟩
  · rw [not_isCarrier_iff hT]
    apply hiso
    · rw [Complex.dist_eq, ← towerPoint_zeroPoint]
      have hd : towerPoint (rZeroRadialPosition z.1 + η / 2) (rZeroHeight z.1) -
          towerPoint (rZeroRadialPosition z.1) (rZeroHeight z.1) = ((η / 2 : ℝ) : ℂ) := by
        simp only [towerPoint]
        push_cast
        ring
      rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    · rw [Set.mem_compl_singleton_iff]
      intro h
      have := congrArg Complex.re h
      rw [towerPoint_re, zeroPoint_re] at this
      linarith
  · intro n hn
    exact hword _ (by linarith) (by linarith) n hn

/-! ## 7. Corollaire : aucun prédicat à fenêtre finie ne sépare les porteurs -/

theorem finite_window_predicate_not_carrier_selective (P : (ℕ → ℤ) → Prop) (S : Finset ℕ)
    (hP : ∀ w w' : ℕ → ℤ, (∀ n ∈ S, w n = w' n) → (P w ↔ P w')) (z : TrueZero) (hz : P (zeroWord z)) :
    ∃ β' : ℝ, 0 < β' ∧ β' < 1 ∧ ¬ IsCarrier β' (rZeroHeight z.1) ∧ P (towerWord β' (rZeroHeight z.1)) := by
  obtain ⟨β', h1, -, h3, h4, h5⟩ := exists_nonCarrier_same_word_on_finset z S one_pos
  exact ⟨β', (zero_radial_pos z).trans h1, h3, h4, (hP _ _ h5).mpr hz⟩

#print axioms carrierWordsSelfMirror_iff_riemannHypothesis
#print axioms heightInjectiveOnCarriers_iff_riemannHypothesis
#print axioms noMixedHeight_of_heightInjective
#print axioms priceRadiallyBlindOnCarriers_iff_riemannHypothesis
#print axioms radial_half_of_term_modulus_eq_two_primes
#print axioms termModulusMirrorBlind_iff_riemannHypothesis
#print axioms towerWord_stable_right_finset
#print axioms exists_nonCarrier_same_word_on_finset
#print axioms finite_window_predicate_not_carrier_selective

end RHV6Fresh
