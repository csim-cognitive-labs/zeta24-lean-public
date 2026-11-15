/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.BackgroundModulation
import RHV6Fresh.Terminal.ZetaRealSegment
import RHV6Fresh.Terminal.OnRadialRing
import RHV6Fresh.Terminal.RemainderExponent
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Étages `k = n`, progression du fond par cellule, attendu de la fibre suivante (auteur, 2026-10-10)

Pour le membre canonique de rang `n`, l'étage lu est l'indice de contact `k = n` (aucun paramètre ajouté à la Tour) :
`φ = arctan(T/β)`, `u = (φ + nπ)/T`, `W = π/T`, `C⁻ = e^u`, `C⁺ = e^{u+W}` (contacts authentiques `C_n`, `C_{n+1}`).

Contenu (tout est DÉMONTRÉ, axiomes standard) :
* §1 objets d'étage et contacts : `C_k = e^{u_k}`, `C_{k+1} = e^{u_k + W}`, `u_k > 0` pour `k ≥ 0` ;
* §2 progression du fond `L = ∫_u^{u+W} e^v/v dv = li(C⁺) − li(C⁻)` (changement de variable `t = e^v`) ; bornes par le
  minimum et le maximum de `e^v/v` sur la cellule, séparément AVANT (`u + W ≤ 1`), APRÈS (`1 ≤ u`) et TRAVERSANT
  (`u < 1 < u + W`) le point `v = 1`, et borne universelle `L ≥ e·W`. Aucune décroissance de `L` n'est supposée : sur
  les cellules après `1`, `L/W ≥ e^u/u` croît avec `u` ;
* §3 contacts, extrema et modulation : l'extremum `D_k` de la contribution de comptage est STRICTEMENT dans la cellule
  `]C_k, C_{k+1}[` ; `|Δb_{ρ,k}| ≤ 2 e^{(β−1)u_k}·L_k` ; rapports `L/W ≥ e`, `L/a = L·√(T²+1/4)`, `L/a² = L·(T²+1/4)` avec
  `a = 1/√(T²+1/4)` (`onRadius`, amplitude ON) : objets d'étude, non obligations ;
* §4 partie finie du reste sous une hauteur, bornée par `√x` dès que ses membres sont ON (déplacé depuis la chaîne) ;
* §5 attendu de la fibre suivante, canal LISSÉ (seule représentation démontrée) : la contribution des membres de
  hauteur dans `]H, H']` vaut `R − P_H − Q_{H'}` en tout `x > 1` et sur toute fenêtre ; la queue est bornée par
  `budget(H')·x` (`β ≤ 1`) avec `budget(H') → 0` ; sous un historique ON jusqu'à `H`, l'attendu de la fibre suivante
  est enfermé dans `C·x + B_H √x + budget(H')·x` ; lecture locale : si l'attendu est borné par `C·x^θ`, tout membre
  de la fibre a une partie réelle `≤ θ`, et à `θ = 1/2` toute la fibre est ON.

Canal `J` : aucune formule explicite de `J` (Riemann, `Σ_ρ li(x^ρ)`) n'est dans le dépôt ni dans Mathlib ; ce module
n'importe PAS la représentation lissée dans le canal `J`. L'obligation de transport vers `J` reste explicite.
-/

namespace RHV6Fresh

open RHV3Lean Filter Topology

/-! ## 1. Étages : contacts authentiques à l'indice `k` -/

/-- Début logarithmique de l'étage `k` : `u_k = (arctan(T/β) + kπ)/T = log C_k`. -/
noncomputable def stageLogStart (z : TrueZero) (k : ℤ) : ℝ :=
  (Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) + (k : ℝ) * Real.pi) / rZeroHeight z.1

/-- Largeur logarithmique d'une cellule : `W = π/T`. -/
noncomputable def stagePitch (z : TrueZero) : ℝ := Real.pi / rZeroHeight z.1

/-- Progression du fond sur l'étage `k` : `L_k = ∫_{u_k}^{u_k + W} e^v/v dv`. -/
noncomputable def stageBackground (z : TrueZero) (k : ℤ) : ℝ :=
  ∫ v in stageLogStart z k..stageLogStart z k + stagePitch z, Real.exp v / v

/-- Étage canonique : le membre de rang `n` lu à l'indice `k = n`. -/
noncomputable def canonicalStageBackground (n : ℕ) : ℝ := stageBackground (canonicalZero n) n

theorem stagePitch_pos (z : TrueZero) : 0 < stagePitch z := div_pos Real.pi_pos z.2

theorem stageLogStart_pos (z : TrueZero) {k : ℤ} (hk : 0 ≤ k) : 0 < stageLogStart z k := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have ha : 0 < Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) :=
    Real.arctan_pos.mpr (div_pos hT hβ)
  have hk' : (0 : ℝ) ≤ (k : ℝ) * Real.pi := mul_nonneg (by exact_mod_cast hk) Real.pi_pos.le
  unfold stageLogStart
  exact div_pos (by linarith) hT

theorem contactMinusAt_eq_exp_stage (z : TrueZero) (k : ℤ) :
    contactMinusAt z k = Real.exp (stageLogStart z k) := by
  rw [contactMinusAt_eq_exp]; rfl

theorem contactMinusAt_succ_eq_exp_stage (z : TrueZero) (k : ℤ) :
    contactMinusAt z (k + 1) = Real.exp (stageLogStart z k + stagePitch z) := by
  have hT : rZeroHeight z.1 ≠ 0 := z.2.ne'
  rw [contactMinusAt_eq_exp]
  congr 1
  unfold stageLogStart stagePitch
  push_cast
  field_simp
  ring

/-! ## 2. Progression du fond sur une cellule : `L = li(C⁺) − li(C⁻)` et ses bornes -/

theorem expDiv_continuousOn {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun v : ℝ => Real.exp v / v) (Set.uIcc a b) := by
  refine Real.continuous_exp.continuousOn.div continuousOn_id fun v hv => ?_
  rw [Set.uIcc_of_le hab] at hv
  exact (lt_of_lt_of_le ha hv.1).ne'

/-- **Changement de variable** `t = e^v` : `∫_a^b e^v/v dv = ∫_{e^a}^{e^b} dt/log t`. -/
theorem integral_expDiv_eq_cellBackground {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ v in a..b, Real.exp v / v = cellBackground (Real.exp a) (Real.exp b) := by
  have hg : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Real.exp '' Set.uIcc a b) := by
    refine ContinuousOn.div continuousOn_const (Real.continuousOn_log.mono ?_) ?_
    · rintro t ⟨v, _, rfl⟩; exact (Real.exp_pos v).ne'
    · rintro t ⟨v, hv, rfl⟩
      rw [Set.uIcc_of_le hab] at hv
      rw [Real.log_exp]; exact (lt_of_lt_of_le ha hv.1).ne'
  have h := intervalIntegral.integral_comp_mul_deriv' (a := a) (b := b) (f := Real.exp)
    (f' := Real.exp) (g := fun t : ℝ => 1 / Real.log t)
    (fun v _ => Real.hasDerivAt_exp v) Real.continuous_exp.continuousOn hg
  unfold cellBackground
  rw [← h]
  refine intervalIntegral.integral_congr fun v _ => ?_
  simp only [Function.comp, Real.log_exp]
  ring

/-- `L_k = li(C_{k+1}) − li(C_k)` : la progression du fond sur l'étage est celle de la cellule de contacts. -/
theorem stageBackground_eq_cellBackground (z : TrueZero) {k : ℤ} (hk : 0 ≤ k) :
    stageBackground z k = cellBackground (contactMinusAt z k) (contactMinusAt z (k + 1)) := by
  rw [contactMinusAt_eq_exp_stage, contactMinusAt_succ_eq_exp_stage]
  exact integral_expDiv_eq_cellBackground (stageLogStart_pos z hk)
    (le_add_of_nonneg_right (stagePitch_pos z).le)

/-- Après `1`, `e^v/v` croît : `1 ≤ u ≤ v ⟹ e^u/u ≤ e^v/v`. -/
theorem expDiv_le_of_one_le {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    Real.exp u / u ≤ Real.exp v / v := by
  have he : Real.exp v = Real.exp u * Real.exp (v - u) := by rw [← Real.exp_add]; congr 1; ring
  have h1 := Real.add_one_le_exp (v - u)
  have hkey : v ≤ Real.exp (v - u) * u := by nlinarith
  rw [div_le_div_iff₀ (by linarith) (by linarith), he]
  have := mul_le_mul_of_nonneg_left hkey (Real.exp_pos u).le
  linarith [this]

/-- Avant `1`, `e^v/v` décroît : `0 < u ≤ v ≤ 1 ⟹ e^v/v ≤ e^u/u`. -/
theorem expDiv_le_of_le_one {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1) :
    Real.exp v / v ≤ Real.exp u / u := by
  have he : Real.exp u = Real.exp v * Real.exp (u - v) := by rw [← Real.exp_add]; congr 1; ring
  have h1 := Real.add_one_le_exp (u - v)
  have hkey : u ≤ v * Real.exp (u - v) := by nlinarith
  rw [div_le_div_iff₀ (by linarith) hu, he]
  have := mul_le_mul_of_nonneg_left hkey (Real.exp_pos v).le
  linarith [this]

/-- Minimum global : `e ≤ e^v/v` pour `v > 0` (atteint en `v = 1`). -/
theorem exp_one_le_expDiv {v : ℝ} (hv : 0 < v) : Real.exp 1 ≤ Real.exp v / v := by
  rw [le_div_iff₀ hv]
  have he : Real.exp v = Real.exp 1 * Real.exp (v - 1) := by rw [← Real.exp_add]; congr 1; ring
  have h1 := Real.add_one_le_exp (v - 1)
  rw [he]
  have := mul_le_mul_of_nonneg_left (show v ≤ Real.exp (v - 1) by linarith) (Real.exp_pos 1).le
  linarith [this]

/-- Bornes d'une intégrale de `e^v/v` par un minorant et un majorant ponctuels. -/
theorem integral_expDiv_bounds {a b m M : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hm : ∀ v ∈ Set.Icc a b, m ≤ Real.exp v / v) (hM : ∀ v ∈ Set.Icc a b, Real.exp v / v ≤ M) :
    (b - a) * m ≤ ∫ v in a..b, Real.exp v / v ∧ ∫ v in a..b, Real.exp v / v ≤ (b - a) * M := by
  have hi : IntervalIntegrable (fun v : ℝ => Real.exp v / v) MeasureTheory.volume a b :=
    (expDiv_continuousOn ha hab).intervalIntegrable
  constructor
  · have h := intervalIntegral.integral_mono_on hab intervalIntegrable_const hi hm
    rwa [intervalIntegral.integral_const, smul_eq_mul] at h
  · have h := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const hM
    rwa [intervalIntegral.integral_const, smul_eq_mul] at h

/-- Cellule APRÈS `1` (`1 ≤ a ≤ b`) : `(b − a) e^a/a ≤ ∫ ≤ (b − a) e^b/b`. -/
theorem integral_expDiv_after {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (b - a) * (Real.exp a / a) ≤ ∫ v in a..b, Real.exp v / v ∧
      ∫ v in a..b, Real.exp v / v ≤ (b - a) * (Real.exp b / b) :=
  integral_expDiv_bounds (by linarith) hab (fun v hv => expDiv_le_of_one_le ha hv.1)
    (fun v hv => expDiv_le_of_one_le (le_trans ha hv.1) hv.2)

/-- Cellule AVANT `1` (`0 < a ≤ b ≤ 1`) : `(b − a) e^b/b ≤ ∫ ≤ (b − a) e^a/a`. -/
theorem integral_expDiv_before {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b - a) * (Real.exp b / b) ≤ ∫ v in a..b, Real.exp v / v ∧
      ∫ v in a..b, Real.exp v / v ≤ (b - a) * (Real.exp a / a) :=
  integral_expDiv_bounds ha hab
    (fun v hv => expDiv_le_of_le_one (lt_of_lt_of_le ha hv.1) hv.2 hb)
    (fun v hv => expDiv_le_of_le_one ha hv.1 (le_trans hv.2 hb))

/-- Cellule TRAVERSANT `1` (`0 < a ≤ 1 ≤ b`) : `(b − a)·e ≤ ∫ ≤ (b − a)·max(e^a/a, e^b/b)`. -/
theorem integral_expDiv_crossing {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b) :
    (b - a) * Real.exp 1 ≤ ∫ v in a..b, Real.exp v / v ∧
      ∫ v in a..b, Real.exp v / v ≤ (b - a) * max (Real.exp a / a) (Real.exp b / b) :=
  integral_expDiv_bounds ha (le_trans ha1 hb1)
    (fun v hv => exp_one_le_expDiv (lt_of_lt_of_le ha hv.1))
    (fun v hv => by
      rcases le_total v 1 with h | h
      · exact le_trans (expDiv_le_of_le_one ha hv.1 h) (le_max_left _ _)
      · exact le_trans (expDiv_le_of_one_le h hv.2) (le_max_right _ _))

/-- Borne universelle : `(b − a)·e ≤ ∫_a^b e^v/v` pour `0 < a ≤ b`. -/
theorem integral_expDiv_ge {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * Real.exp 1 ≤ ∫ v in a..b, Real.exp v / v :=
  (integral_expDiv_bounds (M := Real.exp a / a + Real.exp b / b + 0) ha hab
    (fun v hv => exp_one_le_expDiv (lt_of_lt_of_le ha hv.1)) (fun v hv => by
      rcases le_total v 1 with h | h
      · have := expDiv_le_of_le_one ha hv.1 h
        have : 0 ≤ Real.exp b / b := (div_pos (Real.exp_pos _) (by linarith [hv.2, hv.1])).le
        linarith
      · have := expDiv_le_of_one_le h hv.2
        have : 0 ≤ Real.exp a / a := (div_pos (Real.exp_pos _) ha).le
        linarith)).1

theorem stage_width (z : TrueZero) (k : ℤ) :
    stageLogStart z k + stagePitch z - stageLogStart z k = stagePitch z := by ring

/-- **Étage, borne universelle** : `L_k ≥ e·W`. -/
theorem stageBackground_ge (z : TrueZero) {k : ℤ} (hk : 0 ≤ k) :
    Real.exp 1 * stagePitch z ≤ stageBackground z k := by
  have h := integral_expDiv_ge (stageLogStart_pos z hk) (le_add_of_nonneg_right (stagePitch_pos z).le)
  rw [stage_width] at h
  unfold stageBackground; linarith

/-- **Étage APRÈS `1`** (`1 ≤ u_k`) : `W e^{u}/u ≤ L_k ≤ W e^{u+W}/(u+W)`. -/
theorem stageBackground_after (z : TrueZero) {k : ℤ} (h1 : 1 ≤ stageLogStart z k) :
    stagePitch z * (Real.exp (stageLogStart z k) / stageLogStart z k) ≤ stageBackground z k ∧
      stageBackground z k ≤ stagePitch z *
        (Real.exp (stageLogStart z k + stagePitch z) / (stageLogStart z k + stagePitch z)) := by
  have h := integral_expDiv_after h1 (le_add_of_nonneg_right (stagePitch_pos z).le)
  rw [stage_width] at h
  exact h

/-- **Étage AVANT `1`** (`u_k + W ≤ 1`) : `W e^{u+W}/(u+W) ≤ L_k ≤ W e^{u}/u`. -/
theorem stageBackground_before (z : TrueZero) {k : ℤ} (hk : 0 ≤ k)
    (h1 : stageLogStart z k + stagePitch z ≤ 1) :
    stagePitch z * (Real.exp (stageLogStart z k + stagePitch z) / (stageLogStart z k + stagePitch z)) ≤
        stageBackground z k ∧
      stageBackground z k ≤ stagePitch z * (Real.exp (stageLogStart z k) / stageLogStart z k) := by
  have h := integral_expDiv_before (stageLogStart_pos z hk) (le_add_of_nonneg_right (stagePitch_pos z).le) h1
  rw [stage_width] at h
  exact h

/-- **Étage TRAVERSANT `1`** (`u_k ≤ 1 ≤ u_k + W`) : `e·W ≤ L_k ≤ W·max(e^u/u, e^{u+W}/(u+W))`. -/
theorem stageBackground_crossing (z : TrueZero) {k : ℤ} (hk : 0 ≤ k) (h1 : stageLogStart z k ≤ 1)
    (h2 : 1 ≤ stageLogStart z k + stagePitch z) :
    stagePitch z * Real.exp 1 ≤ stageBackground z k ∧
      stageBackground z k ≤ stagePitch z * max (Real.exp (stageLogStart z k) / stageLogStart z k)
        (Real.exp (stageLogStart z k + stagePitch z) / (stageLogStart z k + stagePitch z)) := by
  have h := integral_expDiv_crossing (stageLogStart_pos z hk) h1 h2
  rw [stage_width] at h
  exact h

/-- Les trois cas couvrent tout étage `k ≥ 0` (aucune hypothèse sur la décroissance de `L`). -/
theorem stage_cases (z : TrueZero) (k : ℤ) :
    stageLogStart z k + stagePitch z ≤ 1 ∨
      (stageLogStart z k ≤ 1 ∧ 1 ≤ stageLogStart z k + stagePitch z) ∨ 1 ≤ stageLogStart z k := by
  by_cases h : stageLogStart z k + stagePitch z ≤ 1
  · exact Or.inl h
  · by_cases h' : stageLogStart z k ≤ 1
    · exact Or.inr (Or.inl ⟨h', by linarith⟩)
    · exact Or.inr (Or.inr (by linarith))

/-! ## 3. Contacts, extrema, modulation et rapports sur l'étage -/

/-- **L'extremum de la modulation est strictement à l'intérieur de la cellule de contacts** :
`C_k < D_k < C_{k+1}` (décalage `arctan(β/T)/T ∈ ]0, W/2[`). -/
theorem modulationExtremum_mem_cell (z : TrueZero) (k : ℤ) :
    contactMinusAt z k < modulationExtremum z k ∧ modulationExtremum z k < contactMinusAt z (k + 1) := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have h1 := Real.arctan_lt_pi_div_two (rZeroHeight z.1 / rZeroRadialPosition z.1)
  have h2 := Real.neg_pi_div_two_lt_arctan (rZeroHeight z.1 / rZeroRadialPosition z.1)
  rw [contactMinusAt_eq_exp, contactMinusAt_eq_exp]
  unfold modulationExtremum
  constructor
  · exact Real.exp_lt_exp.mpr (div_lt_div_of_pos_right (by linarith) hT)
  · refine Real.exp_lt_exp.mpr (div_lt_div_of_pos_right ?_ hT)
    push_cast; linarith

/-- **Modulation sur l'étage** : `|Δb_{ρ,k}| ≤ 2 e^{(β−1)u_k} L_k`, toute position radiale. -/
theorem stageModulation_abs_le (z : TrueZero) {k : ℤ} (hk : 0 ≤ k) :
    |cellModulation z (contactMinusAt z k) (contactMinusAt z (k + 1))| ≤
      2 * Real.exp ((rZeroRadialPosition z.1 - 1) * stageLogStart z k) * stageBackground z k := by
  have h := cellModulation_abs_le_at_contacts z hk
  rw [stageBackground_eq_cellBackground z hk]
  have hc : contactMinusAt z k ^ (rZeroRadialPosition z.1 - 1) =
      Real.exp ((rZeroRadialPosition z.1 - 1) * stageLogStart z k) := by
    rw [contactMinusAt_eq_exp_stage, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]
  rwa [hc] at h

/-- Rapport fond / largeur : `L/W ≥ e`. -/
theorem stageBackground_div_pitch_ge (z : TrueZero) {k : ℤ} (hk : 0 ≤ k) :
    Real.exp 1 ≤ stageBackground z k / stagePitch z := by
  rw [le_div_iff₀ (stagePitch_pos z)]; exact stageBackground_ge z hk

/-- Rapport fond / largeur après `1` : `L/W ≥ e^{u}/u`, croissant avec `u` (la charge ne décroît pas avec la cellule). -/
theorem stageBackground_div_pitch_ge_after (z : TrueZero) {k : ℤ} (h1 : 1 ≤ stageLogStart z k) :
    Real.exp (stageLogStart z k) / stageLogStart z k ≤ stageBackground z k / stagePitch z := by
  rw [le_div_iff₀ (stagePitch_pos z)]
  linarith [(stageBackground_after z h1).1]

/-- Rapport fond / amplitude ON `a = 1/√(T²+1/4)` : `L/a = L·√(T²+1/4)`. -/
theorem stageBackground_div_onRadius (z : TrueZero) (k : ℤ) :
    stageBackground z k / onRadius (rZeroHeight z.1) =
      stageBackground z k * Real.sqrt (rZeroHeight z.1 ^ 2 + 1 / 4) := by
  unfold onRadius; rw [div_div_eq_mul_div, div_one]

/-- Rapport fond / amplitude ON au carré : `L/a² = L·(T²+1/4)`. -/
theorem stageBackground_div_onRadius_sq (z : TrueZero) (k : ℤ) :
    stageBackground z k / onRadius (rZeroHeight z.1) ^ 2 =
      stageBackground z k * (rZeroHeight z.1 ^ 2 + 1 / 4) := by
  unfold onRadius
  rw [div_pow, one_pow, Real.sq_sqrt (by positivity), div_div_eq_mul_div, div_one]

/-- Minorations des rapports : `L/a ≥ eπ√(T²+1/4)/T`, `L/a² ≥ eπ(T²+1/4)/T`. -/
theorem stage_ratios_ge (z : TrueZero) {k : ℤ} (hk : 0 ≤ k) :
    Real.exp 1 * stagePitch z * Real.sqrt (rZeroHeight z.1 ^ 2 + 1 / 4) ≤
        stageBackground z k / onRadius (rZeroHeight z.1) ∧
      Real.exp 1 * stagePitch z * (rZeroHeight z.1 ^ 2 + 1 / 4) ≤
        stageBackground z k / onRadius (rZeroHeight z.1) ^ 2 := by
  rw [stageBackground_div_onRadius, stageBackground_div_onRadius_sq]
  have h := stageBackground_ge z hk
  exact ⟨mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _),
    mul_le_mul_of_nonneg_right h (by positivity)⟩

/-- Étage canonique (rang `n`, indice `k = n`) : `L_n = li(C_{n+1}) − li(C_n)`, `L_n ≥ eπ/T_n`, extremum intérieur. -/
theorem canonical_stage (n : ℕ) :
    canonicalStageBackground n = cellBackground (contactMinusAt (canonicalZero n) n)
        (contactMinusAt (canonicalZero n) ((n : ℤ) + 1)) ∧
      Real.exp 1 * stagePitch (canonicalZero n) ≤ canonicalStageBackground n ∧
      contactMinusAt (canonicalZero n) n < modulationExtremum (canonicalZero n) n ∧
      modulationExtremum (canonicalZero n) n < contactMinusAt (canonicalZero n) ((n : ℤ) + 1) := by
  have hk : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  exact ⟨stageBackground_eq_cellBackground _ hk, stageBackground_ge _ hk,
    modulationExtremum_mem_cell _ n⟩


/-! ## Partie finie du reste sous une hauteur : bornée par `√x` dès que ses membres sont ON (fermé) -/

/-- Coefficient d'un zéro dans la partie FINIE du reste (hauteur absolue `≤ H`) : son coefficient lissé, ou zéro. -/
noncomputable def precedingWeight (H : ℝ) (σ : ExplicitIndex) : ℂ :=
  if H < |(σ : ℂ).im| then 0 else -(zetaZeroMultiplicity (σ : ℂ) : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1))

theorem precedingWeight_norm_summable (H : ℝ) :
    Summable fun σ : ExplicitIndex => ‖precedingWeight H σ‖ := by
  have hsum0 : Summable fun σ : ExplicitIndex =>
      ‖-(zetaZeroMultiplicity (σ : ℂ) : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1))‖ :=
    multiplicity_weight_summable.congr fun σ => by rw [neg_div, norm_neg]
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun σ => ?_) hsum0
  unfold precedingWeight
  split_ifs
  · rw [norm_zero]; exact norm_nonneg _
  · exact le_rfl

/-- Budget de la partie finie : somme des modules des coefficients de hauteur `≤ H`. -/
noncomputable def precedingBudget (H : ℝ) : ℝ := ∑' σ : ExplicitIndex, ‖precedingWeight H σ‖

theorem precedingSum_term_eq (H x : ℝ) (σ : ExplicitIndex) :
    (if H < |(σ : ℂ).im| then (0 : ℂ) else nontrivialZeroResidueTerm x σ) =
      precedingWeight H σ * (x : ℂ) ^ (σ : ℂ) := by
  unfold precedingWeight nontrivialZeroResidueTerm Perron.f
  split_ifs
  · simp
  · ring

/-- Un index explicite n'est jamais réel : son membre supérieur a sa hauteur en valeur absolue et sa partie réelle. -/
theorem explicitIndex_upper_readings (σ : ExplicitIndex) :
    rZeroHeight (indexUpper σ).1 = |(σ : ℂ).im| ∧ rZeroRadialPosition (indexUpper σ).1 = (σ : ℂ).re := by
  rcases lt_trichotomy (0 : ℝ) (σ : ℂ).im with h | h | h
  · rw [indexUpper_of_pos h]
    exact ⟨by rw [abs_of_pos h]; rfl, rfl⟩
  · exfalso
    have hre := isNontrivialZetaZero_re_mem_Ioo σ.property
    apply riemannZeta_real_ne_zero_of_mem_Ioo (σ : ℂ).re hre.1 hre.2
    have hσ : ((σ : ℂ).re : ℂ) = (σ : ℂ) := by apply Complex.ext <;> simp [← h]
    rw [hσ]; exact σ.property.1
  · rw [indexUpper_of_neg h]
    refine ⟨?_, thm_conjugateZero_radialPosition _⟩
    rw [thm_conjugateZero_height, abs_of_neg h]; rfl

/-- **La partie finie est bornée par `√x` dès que tous ses membres sont ON.** -/
theorem precedingSum_le_budget_of_onLine {H : ℝ}
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ H → rZeroRadialPosition w.1 = 1 / 2) {x : ℝ} (hx : 1 < x) :
    ‖precedingSum H x‖ ≤ precedingBudget H * x ^ (1 / 2 : ℝ) := by
  have hx0 : 0 < x := lt_trans one_pos hx
  have hre : ∀ σ : ExplicitIndex, ¬ H < |(σ : ℂ).im| → (σ : ℂ).re ≤ 1 / 2 := fun σ hσ => by
    obtain ⟨hh, hr⟩ := explicitIndex_upper_readings σ
    rw [← hr]; exact (hOn _ (by rw [hh]; exact not_lt.mp hσ)).le
  have hterm : ∀ σ : ExplicitIndex,
      ‖(if H < |(σ : ℂ).im| then (0 : ℂ) else nontrivialZeroResidueTerm x σ)‖ ≤
        ‖precedingWeight H σ‖ * x ^ (1 / 2 : ℝ) := by
    intro σ
    rw [precedingSum_term_eq, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    by_cases h : H < |(σ : ℂ).im|
    · have h0 : precedingWeight H σ = 0 := by unfold precedingWeight; rw [if_pos h]
      rw [h0, norm_zero, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx.le (hre σ h)) (norm_nonneg _)
  have hdom : Summable fun σ : ExplicitIndex => ‖precedingWeight H σ‖ * x ^ (1 / 2 : ℝ) :=
    (precedingWeight_norm_summable H).mul_right _
  have hs : Summable fun σ : ExplicitIndex =>
      ‖(if H < |(σ : ℂ).im| then (0 : ℂ) else nontrivialZeroResidueTerm x σ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hdom
  unfold precedingSum precedingBudget
  calc ‖∑' σ : ExplicitIndex, (if H < |(σ : ℂ).im| then (0 : ℂ) else nontrivialZeroResidueTerm x σ)‖
      ≤ ∑' σ : ExplicitIndex, ‖(if H < |(σ : ℂ).im| then (0 : ℂ) else nontrivialZeroResidueTerm x σ)‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' σ : ExplicitIndex, ‖precedingWeight H σ‖ * x ^ (1 / 2 : ℝ) :=
        Summable.tsum_le_tsum hterm hs hdom
    _ = (∑' σ : ExplicitIndex, ‖precedingWeight H σ‖) * x ^ (1 / 2 : ℝ) := tsum_mul_right

/-- **Sous un historique ON jusqu'à `H`, la borne `√x` de la somme des suivants équivaut à celle du reste lissé.** -/
theorem followingSum_sqrt_of_remainder_sqrt {H : ℝ}
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ H → rZeroRadialPosition w.1 = 1 / 2)
    (hR : ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 : ℝ)) :
    ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖followingSum H x‖ ≤ C * x ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := hR
  refine ⟨C + precedingBudget H, fun x hx => ?_⟩
  have hsplit := remainder_eq_preceding_add_following H hx
  have hF : followingSum H x = smoothedRemainder x - precedingSum H x := by rw [hsplit]; ring
  rw [hF, add_mul]
  exact (norm_sub_le _ _).trans (add_le_add (hC x hx) (precedingSum_le_budget_of_onLine hOn hx))

#print axioms precedingSum_le_budget_of_onLine
#print axioms followingSum_sqrt_of_remainder_sqrt

/-! ## 5. Attendu de la fibre suivante (canal lissé, représentation démontrée) -/

/-- Contribution des membres de hauteur absolue dans `]H, H']` : `P_{H'} − P_H`. Pour deux hauteurs consécutives, c'est
la fibre du membre suivant (lui, son miroir et les autres points de même hauteur, avec multiplicités). -/
noncomputable def nextFiberSum (H H' x : ℝ) : ℂ := precedingSum H' x - precedingSum H x

/-- Coefficient d'un zéro dans la fibre `]H, H']`. -/
noncomputable def fiberWeight (H H' : ℝ) (σ : ExplicitIndex) : ℂ := precedingWeight H' σ - precedingWeight H σ

/-- **Attendu de la fibre suivante** : `fibre = R − P_H − Q_{H'}` en tout `x > 1` (identité ; aucune borne). -/
theorem expected_next_fiber (H H' : ℝ) {x : ℝ} (hx : 1 < x) :
    nextFiberSum H H' x = smoothedRemainder x - precedingSum H x - followingSum H' x := by
  rw [remainder_eq_preceding_add_following H' hx]; unfold nextFiberSum; ring

/-- **Attendu en incrément** sur une fenêtre `[a, b]` : `Δfibre = ΔR − ΔP_H − ΔQ_{H'}` (queue conservée entière). -/
theorem expected_next_fiber_increment (H H' : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    nextFiberSum H H' b - nextFiberSum H H' a =
      (smoothedRemainder b - smoothedRemainder a) - (precedingSum H b - precedingSum H a)
        - (followingSum H' b - followingSum H' a) := by
  rw [expected_next_fiber H H' ha, expected_next_fiber H H' hb]; ring

/-- **Queue, borne démontrée** : `‖Q_H(x)‖ ≤ budget(H)·x` pour `x > 1` (toute position radiale, par `Re ρ ≤ 1`). -/
theorem followingSum_norm_le_budget_linear (H : ℝ) {x : ℝ} (hx : 1 < x) :
    ‖followingSum H x‖ ≤ followingBudget H * x := by
  have hx0 : 0 < x := lt_trans one_pos hx
  have hterm : ∀ σ : ExplicitIndex, ‖followingWeight H σ * (x : ℂ) ^ (σ : ℂ)‖ ≤ ‖followingWeight H σ‖ * x := by
    intro σ
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc x ^ (σ : ℂ).re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (explicitIndex_re_le_one σ)
      _ = x := Real.rpow_one x
  have hdom : Summable fun σ : ExplicitIndex => ‖followingWeight H σ‖ * x :=
    (followingWeight_norm_summable H).mul_right _
  have hs : Summable fun σ : ExplicitIndex => ‖followingWeight H σ * (x : ℂ) ^ (σ : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hdom
  unfold followingSum followingBudget
  calc ‖∑' σ : ExplicitIndex, followingWeight H σ * (x : ℂ) ^ (σ : ℂ)‖
      ≤ ∑' σ : ExplicitIndex, ‖followingWeight H σ * (x : ℂ) ^ (σ : ℂ)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' σ : ExplicitIndex, ‖followingWeight H σ‖ * x := Summable.tsum_le_tsum hterm hs hdom
    _ = (∑' σ : ExplicitIndex, ‖followingWeight H σ‖) * x := tsum_mul_right

/-- **Le budget de la queue tend vers zéro** quand la hauteur de coupure monte (convergence dominée). -/
theorem followingBudget_tendsto_zero : Tendsto followingBudget atTop (𝓝 0) := by
  have hsum0 : Summable fun σ : ExplicitIndex =>
      ‖-(zetaZeroMultiplicity (σ : ℂ) : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1))‖ :=
    multiplicity_weight_summable.congr fun σ => by rw [neg_div, norm_neg]
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun H σ => ‖followingWeight H σ‖) (g := fun _ => (0 : ℝ)) hsum0 (fun σ => ?_) ?_
  · simp only [tsum_zero] at h
    exact h
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop |(σ : ℂ).im|] with H hH
    unfold followingWeight; rw [if_neg (not_lt.mpr hH), norm_zero]
  · refine Eventually.of_forall fun H σ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    unfold followingWeight; split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _

/-- **Enveloppe admissible de l'attendu, depuis l'historique seul** : sous un historique ON jusqu'à `H`, la fibre
`]H, H']` est enfermée dans `C·x + B_H·√x + budget(H')·x`, avec `C` la constante démontrée du reste (exposant `1`). -/
theorem expected_next_fiber_bound {H H' : ℝ}
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ H → rZeroRadialPosition w.1 = 1 / 2) :
    ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖nextFiberSum H H' x‖ ≤
      C * x + precedingBudget H * x ^ (1 / 2 : ℝ) + followingBudget H' * x := by
  obtain ⟨C, hC⟩ := smoothedRemainder_linear_growth
  refine ⟨C, fun x hx => ?_⟩
  rw [expected_next_fiber H H' hx]
  have hR := hC x hx
  rw [Real.rpow_one] at hR
  calc ‖smoothedRemainder x - precedingSum H x - followingSum H' x‖
      ≤ ‖smoothedRemainder x‖ + ‖precedingSum H x‖ + ‖followingSum H' x‖ := by
        refine (norm_sub_le _ _).trans ?_
        linarith [norm_sub_le (smoothedRemainder x) (precedingSum H x)]
    _ ≤ _ := by
        linarith [precedingSum_le_budget_of_onLine hOn hx, followingSum_norm_le_budget_linear H' hx]

theorem fiberWeight_norm_summable (H H' : ℝ) : Summable fun σ : ExplicitIndex => ‖fiberWeight H H' σ‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun σ => norm_sub_le _ _)
    ((precedingWeight_norm_summable H').add (precedingWeight_norm_summable H))

/-- La fibre est une série de profils `x^σ` à coefficients `fiberWeight`. -/
theorem nextFiberSum_eq_tsum (H H' : ℝ) {x : ℝ} (hx : 1 < x) :
    nextFiberSum H H' x = ∑' σ : ExplicitIndex, fiberWeight H H' σ * (x : ℂ) ^ (σ : ℂ) := by
  have hx0 : 0 < x := lt_trans one_pos hx
  have hsP : ∀ K : ℝ, Summable fun σ : ExplicitIndex => precedingWeight K σ * (x : ℂ) ^ (σ : ℂ) := fun K =>
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun σ => by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      exact mul_le_mul_of_nonneg_left (by
        calc x ^ (σ : ℂ).re ≤ x ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hx.le (explicitIndex_re_le_one σ)
          _ = x := Real.rpow_one x) (norm_nonneg _))
      ((precedingWeight_norm_summable K).mul_right x))
  have hP : ∀ K : ℝ, precedingSum K x = ∑' σ : ExplicitIndex, precedingWeight K σ * (x : ℂ) ^ (σ : ℂ) :=
    fun K => by unfold precedingSum; exact tsum_congr fun σ => precedingSum_term_eq K x σ
  unfold nextFiberSum
  rw [hP, hP, ← (hsP H').tsum_sub (hsP H)]
  refine tsum_congr fun σ => ?_
  unfold fiberWeight; ring

/-- **Lecture locale de l'attendu** : si la fibre `]H, H']` est bornée par `C·x^θ`, tout zéro de la fibre a une partie
réelle `≤ θ`. -/
theorem nextFiber_growth_bounds_each {H H' θ C : ℝ}
    (h : ∀ x : ℝ, 1 < x → ‖nextFiberSum H H' x‖ ≤ C * x ^ θ) (ρ : ExplicitIndex)
    (hρ : H < |(ρ : ℂ).im|) (hρ' : |(ρ : ℂ).im| ≤ H') : (ρ : ℂ).re ≤ θ := by
  classical
  by_contra hlt
  push Not at hlt
  have key := cpow_series_growth_fibre_zero (fun σ : ExplicitIndex => (σ : ℂ))
    (fiberWeight H H') explicitIndex_re_le_one explicitIndex_locallyFinite (fiberWeight_norm_summable H H')
    (θ := θ) (C := C) (fun x hx => by rw [← nextFiberSum_eq_tsum H H' hx]; exact h x hx) (ρ : ℂ) hlt
  rw [tsum_eq_single ρ (fun σ hσ => if_neg (fun h => hσ (Subtype.ext h))), if_pos rfl] at key
  unfold fiberWeight precedingWeight at key
  rw [if_neg (not_lt.mpr hρ'), if_pos hρ, sub_zero] at key
  obtain ⟨h0, h1⟩ := explicitIndex_ne_zero ρ
  have hm : (zetaZeroMultiplicity (ρ : ℂ) : ℂ) = 0 := by
    have := (div_eq_zero_iff.mp key).resolve_right (mul_ne_zero h0 h1)
    exact neg_eq_zero.mp this
  exact (zetaZeroMultiplicity_pos ρ.property.1).ne' (by exact_mod_cast hm)

/-- **Fibre suivante ON sous l'attendu à l'échelle `√x`** : si la fibre `]H, H']` est bornée par `C·√x`, tout membre
de hauteur dans `]H, H']` est ON (le membre et son miroir, de même hauteur, sont tous deux dans la fibre). -/
theorem nextFiber_onLine_of_sqrt {H H' : ℝ}
    (h : ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖nextFiberSum H H' x‖ ≤ C * x ^ (1 / 2 : ℝ))
    (w : TrueZero) (hw : H < rZeroHeight w.1) (hw' : rZeroHeight w.1 ≤ H') :
    rZeroRadialPosition w.1 = 1 / 2 := by
  obtain ⟨C, hC⟩ := h
  have hT : 0 < rZeroHeight w.1 := w.2
  have h1 := nextFiber_growth_bounds_each hC (memberIndex w)
    (by change H < |rZeroHeight w.1|; rw [abs_of_pos hT]; exact hw)
    (by change |rZeroHeight w.1| ≤ H'; rw [abs_of_pos hT]; exact hw')
  have hTm : rZeroHeight (mirrorMember w).1 = rZeroHeight w.1 := mirrorMember_ordinate w
  have h2 := nextFiber_growth_bounds_each hC (memberIndex (mirrorMember w))
    (by change H < |rZeroHeight (mirrorMember w).1|; rw [hTm, abs_of_pos hT]; exact hw)
    (by change |rZeroHeight (mirrorMember w).1| ≤ H'; rw [hTm, abs_of_pos hT]; exact hw')
  rw [show ((memberIndex w : ExplicitIndex) : ℂ) = zeroPoint w from rfl, zeroPoint_re] at h1
  rw [show ((memberIndex (mirrorMember w) : ExplicitIndex) : ℂ) = zeroPoint (mirrorMember w) from rfl,
    zeroPoint_re, mirrorMember_radial] at h2
  linarith

/-- **L'inégalité manquante, sous sa forme exacte** : sous un historique ON jusqu'à `H`, l'attendu de la fibre `]H, H']`
est borné par `√x` ⟺ `R − Q_{H'}` l'est (la partie finie `P_H` est déjà bornée). Aucun des deux côtés n'est démontré. -/
theorem expected_sqrt_iff_remainder_sub_tail_sqrt {H H' : ℝ}
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ H → rZeroRadialPosition w.1 = 1 / 2) :
    (∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖nextFiberSum H H' x‖ ≤ C * x ^ (1 / 2 : ℝ)) ↔
      ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x - followingSum H' x‖ ≤ C * x ^ (1 / 2 : ℝ) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + precedingBudget H, fun x hx => ?_⟩
    have he := expected_next_fiber H H' hx
    have : smoothedRemainder x - followingSum H' x = nextFiberSum H H' x + precedingSum H x := by
      rw [he]; ring
    rw [this, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC x hx) (precedingSum_le_budget_of_onLine hOn hx))
  · rintro ⟨C, hC⟩
    refine ⟨C + precedingBudget H, fun x hx => ?_⟩
    rw [expected_next_fiber H H' hx, sub_right_comm, add_mul]
    exact (norm_sub_le _ _).trans (add_le_add (hC x hx) (precedingSum_le_budget_of_onLine hOn hx))

/-! ## 6. Fenêtres communes : bornes de queue composées, contrainte conjointe, portée de la coupure fixée

Prédicteur (auteur, 2026-10-10, relecture d'E189) : sur des fenêtres communes tirées de l'historique, l'attendu
`Y = R − P_H` doit valoir `F + Q_{H'}` (fibre entière, miroirs et multiplicités compris, PLUS la queue encadrée). Les
énoncés ci-dessous composent uniquement des bornes démontrées ; ils gardent la queue entière et ses signes : la queue est
UNE série, la même pondération `w_σ` sert à toutes les fenêtres (`tail_joint_functional_bound`). Portée exacte de
`followingBudget_tendsto_zero` : la limite est en la hauteur de coupure ; pour une coupure FIXÉE (au prochain zéro),
`budget·x` reste d'exposant `1` en `x` et n'est jamais une borne en `√x` (`fixed_cut_budget_not_sqrt`). -/

/-- Le terme général de la queue est sommable pour `x > 1` (par `Re σ ≤ 1`). -/
theorem followingSum_term_summable (H : ℝ) {x : ℝ} (hx : 1 < x) :
    Summable fun σ : ExplicitIndex => followingWeight H σ * (x : ℂ) ^ (σ : ℂ) := by
  have hx0 : 0 < x := lt_trans one_pos hx
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun σ => ?_)
    ((followingWeight_norm_summable H).mul_right x))
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc x ^ (σ : ℂ).re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (explicitIndex_re_le_one σ)
    _ = x := Real.rpow_one x

/-- **Queue sur une fenêtre** `[a, b]` : `‖Q_H(b) − Q_H(a)‖ ≤ budget(H)·(a + b)`. Composition de bornes démontrées ;
l'exposant reste `1`. -/
theorem tail_window_increment_bound (H : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    ‖followingSum H b - followingSum H a‖ ≤ followingBudget H * (a + b) := by
  rw [mul_add, add_comm (followingBudget H * a)]
  exact (norm_sub_le _ _).trans (add_le_add (followingSum_norm_le_budget_linear H hb)
    (followingSum_norm_le_budget_linear H ha))

/-- **Coupure à la hauteur de l'historique** : pour `H ≤ H'`, `‖Q_{H'}(x)‖ ≤ budget(H)·x`. La queue au-dessus de
l'arrivée se borne par le budget de la hauteur de départ (le budget de l'arrivée n'est pas lisible avant elle). -/
theorem tail_history_cut_bound {H H' : ℝ} (hHH : H ≤ H') {x : ℝ} (hx : 1 < x) :
    ‖followingSum H' x‖ ≤ followingBudget H * x :=
  (followingSum_norm_le_budget_linear H' hx).trans
    (mul_le_mul_of_nonneg_right (followingBudget_antitone hHH) (le_of_lt (lt_trans one_pos hx)))

/-- **Contrainte conjointe sur plusieurs fenêtres, signes et corrélations conservés** : pour une famille finie de points
`x_r > 1` et de coefficients `λ_r`, si chaque profil `σ` de la queue vérifie `‖Σ_r λ_r x_r^σ‖ ≤ M`, alors
`‖Σ_r λ_r Q_H(x_r)‖ ≤ budget(H)·M`. Avec `M = Σ_r |λ_r| x_r` on retrouve la borne point par point ; tout gain de `M`
passe par la répartition des hauteurs `Im σ` de la queue (comptage), non par cette borne. -/
theorem tail_joint_functional_bound (H : ℝ) {ι : Type*} (s : Finset ι) (x : ι → ℝ) (lam : ι → ℂ)
    (hx : ∀ r ∈ s, 1 < x r) {M : ℝ}
    (hM : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → ‖∑ r ∈ s, lam r * (x r : ℂ) ^ (σ : ℂ)‖ ≤ M) :
    ‖∑ r ∈ s, lam r * followingSum H (x r)‖ ≤ followingBudget H * M := by
  classical
  have hterm : ∀ r ∈ s, Summable fun σ : ExplicitIndex => lam r * (followingWeight H σ * (x r : ℂ) ^ (σ : ℂ)) :=
    fun r hr => (followingSum_term_summable H (hx r hr)).mul_left (lam r)
  have hswap : ∑ r ∈ s, lam r * followingSum H (x r) =
      ∑' σ : ExplicitIndex, followingWeight H σ * ∑ r ∈ s, lam r * (x r : ℂ) ^ (σ : ℂ) := by
    unfold followingSum
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum hterm]
    refine tsum_congr fun σ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hbound : ∀ σ : ExplicitIndex,
      ‖followingWeight H σ * ∑ r ∈ s, lam r * (x r : ℂ) ^ (σ : ℂ)‖ ≤ ‖followingWeight H σ‖ * M := by
    intro σ
    by_cases hσ : H < |(σ : ℂ).im|
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM σ hσ) (norm_nonneg _)
    · have h0 : followingWeight H σ = 0 := by unfold followingWeight; rw [if_neg hσ]
      rw [h0]; simp
  have hdom : Summable fun σ : ExplicitIndex => ‖followingWeight H σ‖ * M :=
    (followingWeight_norm_summable H).mul_right M
  have hs : Summable fun σ : ExplicitIndex =>
      ‖followingWeight H σ * ∑ r ∈ s, lam r * (x r : ℂ) ^ (σ : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hdom
  rw [hswap]
  calc ‖∑' σ : ExplicitIndex, followingWeight H σ * ∑ r ∈ s, lam r * (x r : ℂ) ^ (σ : ℂ)‖
      ≤ ∑' σ : ExplicitIndex, ‖followingWeight H σ * ∑ r ∈ s, lam r * (x r : ℂ) ^ (σ : ℂ)‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' σ : ExplicitIndex, ‖followingWeight H σ‖ * M := Summable.tsum_le_tsum hbound hs hdom
    _ = followingBudget H * M := by unfold followingBudget; exact tsum_mul_right

/-- **Attendu conjoint de la fibre suivante** : `Σ_r λ_r (R − P_H)(x_r) − Σ_r λ_r F(x_r)` est la lecture conjointe de la
queue `Q_{H'}`, bornée par `budget(H')·M`. C'est l'identité obligatoire de l'attendu, lue sur plusieurs fenêtres à la fois,
avec la queue entière. -/
theorem expected_next_fiber_joint (H H' : ℝ) {ι : Type*} (s : Finset ι) (x : ι → ℝ) (lam : ι → ℂ)
    (hx : ∀ r ∈ s, 1 < x r) {M : ℝ}
    (hM : ∀ σ : ExplicitIndex, H' < |(σ : ℂ).im| → ‖∑ r ∈ s, lam r * (x r : ℂ) ^ (σ : ℂ)‖ ≤ M) :
    ‖∑ r ∈ s, lam r * (smoothedRemainder (x r) - precedingSum H (x r))
        - ∑ r ∈ s, lam r * nextFiberSum H H' (x r)‖ ≤ followingBudget H' * M := by
  have hid : ∑ r ∈ s, lam r * (smoothedRemainder (x r) - precedingSum H (x r))
      - ∑ r ∈ s, lam r * nextFiberSum H H' (x r) = ∑ r ∈ s, lam r * followingSum H' (x r) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [expected_next_fiber H H' (hx r hr)]; ring
  rw [hid]
  exact tail_joint_functional_bound H' s x lam hx hM

/-- **Attendu sur une fenêtre** `[a, b]`, sous un historique ON jusqu'à `H` : `‖ΔF‖ ≤ ‖ΔR‖ + B_H(√a + √b) +
budget(H')(a + b)`. Composition de bornes démontrées, exposant `1` pour la queue. -/
theorem expected_next_fiber_window_bound {H H' : ℝ}
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ H → rZeroRadialPosition w.1 = 1 / 2)
    {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    ‖nextFiberSum H H' b - nextFiberSum H H' a‖ ≤ ‖smoothedRemainder b - smoothedRemainder a‖
      + precedingBudget H * (a ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ)) + followingBudget H' * (a + b) := by
  rw [expected_next_fiber_increment H H' ha hb]
  have hP : ‖precedingSum H b - precedingSum H a‖ ≤ precedingBudget H * (a ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ)) := by
    rw [mul_add, add_comm (precedingBudget H * a ^ (1 / 2 : ℝ))]
    exact (norm_sub_le _ _).trans
      (add_le_add (precedingSum_le_budget_of_onLine hOn hb) (precedingSum_le_budget_of_onLine hOn ha))
  have hQ := tail_window_increment_bound H' ha hb
  have h1 := norm_sub_le (smoothedRemainder b - smoothedRemainder a - (precedingSum H b - precedingSum H a))
    (followingSum H' b - followingSum H' a)
  have h2 := norm_sub_le (smoothedRemainder b - smoothedRemainder a) (precedingSum H b - precedingSum H a)
  linarith

/-- Le budget de la queue au-dessus de `H` est strictement positif dès qu'un index explicite est au-dessus de `H`. -/
theorem followingBudget_pos_of_above {H : ℝ} (σ : ExplicitIndex) (hσ : H < |(σ : ℂ).im|) :
    0 < followingBudget H := by
  have hpos : 0 < ‖followingWeight H σ‖ := by
    rw [norm_pos_iff]
    unfold followingWeight
    rw [if_pos hσ]
    obtain ⟨h0, h1⟩ := explicitIndex_ne_zero σ
    refine div_ne_zero ?_ (mul_ne_zero h0 h1)
    rw [neg_ne_zero]
    exact_mod_cast (zetaZeroMultiplicity_pos σ.property.1).ne'
  unfold followingBudget
  exact lt_of_lt_of_le hpos
    ((followingWeight_norm_summable H).le_tsum σ fun _ _ => norm_nonneg _)

/-- **Portée de la coupure fixée** : si `budget(H) > 0`, aucune constante ne fait de `budget(H)·x` une borne en `√x` sur
`x > 1`. La limite `budget → 0` est en la hauteur de coupure, pas en `x`. -/
theorem fixed_cut_budget_not_sqrt {H : ℝ} (hpos : 0 < followingBudget H) :
    ¬ ∃ C : ℝ, ∀ x : ℝ, 1 < x → followingBudget H * x ≤ C * x ^ (1 / 2 : ℝ) := by
  rintro ⟨C, hC⟩
  set b := followingBudget H with hb
  set s : ℝ := |C| / b + 1 with hs
  have hs1 : 1 ≤ s := by
    have : 0 ≤ |C| / b := div_nonneg (abs_nonneg C) hpos.le
    linarith
  have hx : 1 < s * s + 1 := by nlinarith
  have hsq : (s * s + 1) ^ (1 / 2 : ℝ) = Real.sqrt (s * s + 1) := (Real.sqrt_eq_rpow _).symm
  have h := hC (s * s + 1) hx
  rw [hsq] at h
  have hsqrt_pos : 0 < Real.sqrt (s * s + 1) := Real.sqrt_pos.mpr (by positivity)
  have hgt : s < Real.sqrt (s * s + 1) := by
    rw [Real.lt_sqrt (by linarith)]; linarith
  -- b·(s² + 1) = b·√(s²+1)·√(s²+1) ≤ C·√(s²+1), donc b·√(s²+1) ≤ C ≤ |C|
  have hmul : Real.sqrt (s * s + 1) * Real.sqrt (s * s + 1) = s * s + 1 :=
    Real.mul_self_sqrt (by positivity)
  have h2 : b * Real.sqrt (s * s + 1) ≤ C := by
    have : b * Real.sqrt (s * s + 1) * Real.sqrt (s * s + 1) ≤ C * Real.sqrt (s * s + 1) := by
      rw [mul_assoc, hmul]; exact h
    exact le_of_mul_le_mul_right this hsqrt_pos
  have h3 : b * s < |C| := by
    calc b * s < b * Real.sqrt (s * s + 1) := mul_lt_mul_of_pos_left hgt hpos
      _ ≤ C := h2
      _ ≤ |C| := le_abs_self C
  have h4 : b * s = |C| + b := by rw [hs, mul_add, mul_one, mul_div_cancel₀ _ hpos.ne']
  linarith

#print axioms integral_expDiv_eq_cellBackground
#print axioms stageBackground_crossing
#print axioms modulationExtremum_mem_cell
#print axioms followingBudget_tendsto_zero
#print axioms expected_next_fiber_bound
#print axioms nextFiber_onLine_of_sqrt
#print axioms tail_joint_functional_bound
#print axioms expected_next_fiber_joint
#print axioms fixed_cut_budget_not_sqrt

end RHV6Fresh
