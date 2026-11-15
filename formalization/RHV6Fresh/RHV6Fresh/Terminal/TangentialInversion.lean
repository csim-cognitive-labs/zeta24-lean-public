/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Tower.Incidences
import RHV6Fresh.Terminal.TowerWinding

/-!
# Inversion tangentielle : deux contacts successifs rendent `(β, T)` ; un premier encadré ne rend qu'une région (E176, 2026-10-05)

Conventions du dépôt : phase `φ = arctan(T/β)`, contact `C_k = exp((φ + kπ)/T)` (`contactMinusAt z k = C_k`,
`contactPlusAt z k = C_{k+1}`, `windingContact β T k`), cellule d'un réel `q > 0` : `(C_k, C_{k+1}]` (règle du pivot).

1. **Inversion exacte sur un zéro** : `T = π / log(C_{k+1}/C_k)` et `β = T · cot(T · log C_k)`, pour tout zéro supérieur et tout `k`
   (`inversion_height`, `inversion_radial`) ; deux zéros qui ont la même paire de contacts indexée ont mêmes `T` et `β`
   (`inversion_reads_own_contacts`) : l'inversion d'un membre ne lit que SES contacts.
2. **Reconstruction avec branche** : si `0 < T · log a − kπ < π/2`, alors `β := T · cot(T · log a) > 0` et `a = C_k` pour `(β, T)`
   (`branch_inversion_reconstructs`) ; l'invariance de la cotangente par `kπ` ne suffit pas, c'est l'égalité indexée qui fixe `k`.
3. **Premier dans une cellule** : pour TOUTE `(β, T)`, `T > 0`, tout réel `q > 0` est dans une cellule et une seule
   (`every_real_in_unique_cell`) : l'encadrement d'un premier ne sélectionne aucune `(β, T)`.
4. **Premier égal à un contact** : `C_k = q` ⟺ `arctan(T/β) = T log q − kπ` (`contact_eq_iff_phase`), et alors
   `β = T · cot(T log q)` (`contact_radial_formula`) ; `β < 1` ⟺ `arctan T < arctan(T/β)` (`radial_lt_one_iff_branch`) ; deux premiers
   tous deux contacts d'une même Tour quantifient la hauteur : `T · (log q₂ − log q₁) = (k − j)π` (`two_contacts_height_quantized`).

Portée : identités et caractérisations vraies pour toute `(β, T)` ; aucune ne sélectionne un zéro ni ne transporte une partie réelle
d'un membre au suivant. Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Inversion exacte sur un zéro -/

theorem cot_eq_inv_tan (x : ℝ) : Real.cot x = (Real.tan x)⁻¹ := by
  rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, inv_div]

/-- `T = π / log(C_{k+1}/C_k)`. -/
theorem inversion_height (z : TrueZero) (k : ℤ) :
    Real.pi / Real.log (contactPlusAt z k / contactMinusAt z k) = rZeroHeight z.1 := by
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  rw [Real.log_div (ne_of_gt (contactPlusAt_positive z k)) (ne_of_gt (contactMinusAt_positive z k)),
    contactAt_consecutive_logWidth]
  field_simp [Real.pi_ne_zero]

/-- `β = T · cot(T · log C_k)`. -/
theorem inversion_radial (z : TrueZero) (k : ℤ) :
    rZeroHeight z.1 * Real.cot (rZeroHeight z.1 * Real.log (contactMinusAt z k)) =
      rZeroRadialPosition z.1 := by
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  rw [cot_eq_inv_tan, contactAt_tangent_minus, inv_div]
  field_simp

/-- **Singularité de l'inversion** (relecture de l'auteur, 2026-10-10) : au contact, `tan θ = T/β ≠ 0`, donc `sin θ ≠ 0` ET
`cos θ ≠ 0`. L'expression `β = T·cot θ = T·cos θ / sin θ` est singulière aux ZÉROS de la tangente (`sin θ = 0`, où
`cot` n'est pas définie) ; aux PÔLES de la tangente (`cos θ = 0`) elle vaut `0`, exclu par `β > 0`. -/
theorem inversion_sin_cos_ne_zero (z : TrueZero) (k : ℤ) :
    Real.sin (rZeroHeight z.1 * Real.log (contactMinusAt z k)) ≠ 0 ∧
      Real.cos (rZeroHeight z.1 * Real.log (contactMinusAt z k)) ≠ 0 := by
  have hne : Real.tan (rZeroHeight z.1 * Real.log (contactMinusAt z k)) ≠ 0 := by
    rw [contactAt_tangent_minus z k]
    exact div_ne_zero (ne_of_gt z.2) (ne_of_gt (thm_zeroRadialPosition_positive z.1))
  rw [Real.tan_eq_sin_div_cos] at hne
  constructor
  · intro h; exact hne (by rw [h, zero_div])
  · intro h; exact hne (by rw [h, div_zero])

/-- `β = T·cos θ / sin θ` au contact, avec `sin θ ≠ 0` : la seule forme singulière possible est `sin θ = 0`. -/
theorem inversion_radial_cos_div_sin (z : TrueZero) (k : ℤ) :
    rZeroHeight z.1 * Real.cos (rZeroHeight z.1 * Real.log (contactMinusAt z k)) /
        Real.sin (rZeroHeight z.1 * Real.log (contactMinusAt z k)) = rZeroRadialPosition z.1 := by
  rw [← inversion_radial z k, Real.cot_eq_cos_div_sin, mul_div_assoc]

/-- L'inversion d'un membre ne lit que ses propres contacts : même paire indexée ⟹ même hauteur et même partie réelle. -/
theorem inversion_reads_own_contacts (z w : TrueZero) (k j : ℤ)
    (hMinus : contactMinusAt z k = contactMinusAt w j) (hPlus : contactPlusAt z k = contactPlusAt w j) :
    rZeroHeight z.1 = rZeroHeight w.1 ∧ rZeroRadialPosition z.1 = rZeroRadialPosition w.1 := by
  have hT : rZeroHeight z.1 = rZeroHeight w.1 := by
    rw [← inversion_height z k, ← inversion_height w j, hMinus, hPlus]
  refine ⟨hT, ?_⟩
  rw [← inversion_radial z k, ← inversion_radial w j, hMinus, hT]

/-! ## 2. Reconstruction avec branche -/

/-- Si `0 < T log a − kπ < π/2`, la partie réelle lue `β := T cot(T log a)` est positive et `a` est le contact d'indice `k` de la
Tour de paramètres `(β, T)`. -/
theorem branch_inversion_reconstructs {T a : ℝ} (hT : 0 < T) (ha : 0 < a) (k : ℤ)
    (hLow : 0 < T * Real.log a - k * Real.pi) (hHigh : T * Real.log a - k * Real.pi < Real.pi / 2) :
    0 < T * Real.cot (T * Real.log a) ∧
      windingContact (T * Real.cot (T * Real.log a)) T k = a := by
  set y := T * Real.log a - k * Real.pi with hy
  have hx : T * Real.log a = y + k * Real.pi := by rw [hy]; ring
  have htan : Real.tan (T * Real.log a) = Real.tan y := by
    rw [hx, (Real.tan_periodic.int_mul k) y]
  have hcos : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hHigh⟩
  have hsin : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hLow (by linarith [Real.pi_pos])
  have htpos : 0 < Real.tan y := by rw [Real.tan_eq_sin_div_cos]; exact div_pos hsin hcos
  have hcot : Real.cot (T * Real.log a) = (Real.tan y)⁻¹ := by rw [cot_eq_inv_tan, htan]
  have hβ : 0 < T * Real.cot (T * Real.log a) := by rw [hcot]; exact mul_pos hT (inv_pos.mpr htpos)
  refine ⟨hβ, ?_⟩
  have hratio : T / (T * Real.cot (T * Real.log a)) = Real.tan y := by
    rw [hcot]; field_simp
  unfold windingContact
  rw [hratio, Real.arctan_tan (by linarith [Real.pi_pos]) hHigh]
  have : (y + k * Real.pi) / T = Real.log a := by
    rw [← hx]; field_simp
  rw [this, Real.exp_log ha]

/-! ## 3. Premier dans une cellule : toute `(β, T)` convient -/

theorem windingContact_lt_iff {β T q x : ℝ} (hT : 0 < T) (hq : 0 < q) :
    windingContact β T x < q ↔ x < (T * Real.log q - Real.arctan (T / β)) / Real.pi := by
  unfold windingContact
  rw [← Real.exp_log hq, Real.exp_lt_exp, Real.exp_log hq, div_lt_iff₀ hT, lt_div_iff₀ Real.pi_pos]
  constructor <;> intro h <;> linarith

theorem le_windingContact_iff {β T q x : ℝ} (hT : 0 < T) (hq : 0 < q) :
    q ≤ windingContact β T x ↔ (T * Real.log q - Real.arctan (T / β)) / Real.pi ≤ x := by
  unfold windingContact
  rw [← Real.exp_log hq, Real.exp_le_exp, Real.exp_log hq, le_div_iff₀ hT, div_le_iff₀ Real.pi_pos]
  constructor <;> intro h <;> linarith

/-- Pour toute `(β, T)` avec `T > 0`, tout réel `q > 0` est dans exactement une cellule `(C_k, C_{k+1}]`. -/
theorem every_real_in_unique_cell (β : ℝ) {T q : ℝ} (hT : 0 < T) (hq : 0 < q) :
    ∃! k : ℤ, windingContact β T k < q ∧ q ≤ windingContact β T ((k : ℝ) + 1) := by
  set s := (T * Real.log q - Real.arctan (T / β)) / Real.pi with hs
  refine ⟨⌈s⌉ - 1, ?_, ?_⟩
  · refine ⟨(windingContact_lt_iff hT hq).mpr ?_, (le_windingContact_iff hT hq).mpr ?_⟩
    · push_cast; linarith [Int.ceil_lt_add_one s]
    · push_cast; linarith [Int.le_ceil s]
  · rintro k ⟨h1, h2⟩
    have a := (windingContact_lt_iff hT hq).mp h1
    have b := (le_windingContact_iff hT hq).mp h2
    have hc : ⌈s⌉ = k + 1 := by
      rw [Int.ceil_eq_iff]; push_cast; exact ⟨by linarith, b⟩
    omega

/-! ## 4. Premier égal à un contact -/

theorem contact_eq_iff_phase {β T q : ℝ} (hT : 0 < T) (hq : 0 < q) (k : ℤ) :
    windingContact β T k = q ↔ Real.arctan (T / β) = T * Real.log q - k * Real.pi := by
  unfold windingContact
  constructor
  · intro h
    have := congrArg Real.log h
    rw [Real.log_exp] at this
    field_simp at this
    linarith
  · intro h
    rw [h]
    have : (T * Real.log q - k * Real.pi + k * Real.pi) / T = Real.log q := by
      rw [sub_add_cancel]; field_simp
    rw [this, Real.exp_log hq]

/-- Un premier égal au contact d'indice `k` fixe la partie réelle en fonction de la hauteur : `β = T cot(T log q)`. -/
theorem contact_radial_formula {β T q : ℝ} (hT : 0 < T) (hβ : 0 < β) (hq : 0 < q) (k : ℤ)
    (h : windingContact β T k = q) : β = T * Real.cot (T * Real.log q) := by
  have hφ := (contact_eq_iff_phase hT hq k).mp h
  have hx : T * Real.log q = Real.arctan (T / β) + k * Real.pi := by linarith
  rw [hx, cot_eq_inv_tan, (Real.tan_periodic.int_mul k) _, Real.tan_arctan, inv_div]
  field_simp

/-- `β < 1` ⟺ la phase dépasse `arctan T` : la branche des parties réelles de la bande est la fenêtre `]arctan T, π/2[`. -/
theorem radial_lt_one_iff_branch {β T : ℝ} (hT : 0 < T) (hβ : 0 < β) :
    β < 1 ↔ Real.arctan T < Real.arctan (T / β) := by
  rw [Real.arctan_lt_arctan_iff]
  constructor
  · intro h; rw [lt_div_iff₀ hβ]; nlinarith
  · intro h; rw [lt_div_iff₀ hβ] at h; nlinarith

/-- Deux premiers tous deux contacts d'une même Tour : la hauteur est quantifiée, `T (log q₂ − log q₁) = (k − j)π`. -/
theorem two_contacts_height_quantized {β T q₁ q₂ : ℝ} (hT : 0 < T) (h₁ : 0 < q₁) (h₂ : 0 < q₂) (j k : ℤ)
    (hj : windingContact β T j = q₁) (hk : windingContact β T k = q₂) :
    T * (Real.log q₂ - Real.log q₁) = ((k : ℝ) - j) * Real.pi := by
  have a := (contact_eq_iff_phase hT h₁ j).mp hj
  have b := (contact_eq_iff_phase hT h₂ k).mp hk
  linarith

end RHV6Fresh
