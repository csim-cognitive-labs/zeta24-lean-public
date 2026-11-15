/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CollectiveContactAccumulation
import RHV6Fresh.Terminal.RawSpectralChannel

/-!
# RHV6Fresh — troncature par hauteur et passage à la somme infinie (mission, 2026-11-03, module C)

Le passage de l'accumulation finie à la somme sur tous les zéros est un problème analytique
distinct du télescopage. Ce module le traite canal par canal.

**Canal intégré** (`integratedTowerTerm`, poids `−m·x^ρ/(ρ(ρ+1))`) : série absolument convergente
(`nontrivial_zero_residue_series_summable`, corpus). Résultats inconditionnels :
`height_truncation_finite`, `contact_accumulation_height_split`,
`integrated_contact_accumulation_converges`, `tendsto_lowFrequencies_atTop`,
`integrated_contact_limit_eq_spectral`, `integrated_accumulation_limit`.

**Canal brut** (`rawTowerTerm`, poids `−m·x^ρ/ρ`) : la série n'est pas absolument convergente ;
la formule explicite brute `ψ(x) = x − Σ_ρ x^ρ/ρ − log 2π − ½ log(1 − x⁻²)` (sommation symétrique
par hauteur, `x` non entier) n'est NI dans Mathlib NI dans le corpus. Elle est isolée ici comme
prémisse NOMMÉE et EXPLICITE `RawExplicitFormulaAt x` (une définition `Prop`, jamais un axiome,
jamais posée vraie). Les théorèmes `raw_contact_limit_at_continuity`, `raw_contact_limit_at_jump`
et `contact_limit_preserves_arithmetic_jump` la prennent en HYPOTHÈSE affichée : ils montrent que,
SI la formule brute converge aux deux demi-entiers encadrant `n`, alors l'accumulation par contacts
du canal brut reconstruit exactement `Λ(n)`. Ce sont des résultats CONDITIONNELS.

`psi_half_difference` (inconditionnel) : `ψ(n + ½) − ψ(n − ½) = Λ(n)`.
-/

namespace RHV6Fresh

open RHV3Lean ArithmeticFunction Filter Topology

/-! ## 1. Canal intégré : troncature, découpage, convergence -/

theorem height_truncation_finite (H : ℝ) : (lowFrequencySet H).Finite := lowFrequencySet_finite H

/-- L'accumulation collective tronquée à la hauteur `H`. -/
noncomputable def truncatedAccumulation (H : ℝ) (F : ExplicitIndex → ℝ → ℂ)
    (k₀ : ExplicitIndex → ℤ) (n : ExplicitIndex → ℕ) (a x : ℝ) : ℂ :=
  collectiveAccumulation (lowFrequencies H) F k₀ n a x

theorem truncatedAccumulation_eq (H : ℝ) (F : ExplicitIndex → ℝ → ℂ) (k₀ : ExplicitIndex → ℤ)
    (n : ExplicitIndex → ℕ) (a x : ℝ) :
    truncatedAccumulation H F k₀ n a x = ∑ ρ ∈ lowFrequencies H, (F ρ x - F ρ a) :=
  finite_contact_accumulation_eq_spectral_difference _ _ _ _ _ _

/-- La contribution tronquée du canal intégré, comme somme finie. -/
theorem channelOn_lowFrequencies (H : ℝ) (x : ℝ) :
    channelOn (↑(lowFrequencies H)) x = ∑ ρ ∈ lowFrequencies H, integratedTowerTerm ρ x := by
  unfold channelOn
  rw [Finset.tsum_subtype']
  rfl

/-- **Découpage par hauteur** : canal entier = accumulation tronquée + complément (`a, x > 1`). -/
theorem contact_accumulation_height_split (H : ℝ) (k₀ : ExplicitIndex → ℤ)
    (n : ExplicitIndex → ℕ) {a x : ℝ} (ha : 1 < a) (hx : 1 < x) :
    (∑' ρ : ExplicitIndex, integratedTowerTerm ρ x) -
        (∑' ρ : ExplicitIndex, integratedTowerTerm ρ a) =
      truncatedAccumulation H integratedTowerTerm k₀ n a x +
        (channelOn (↑(lowFrequencies H))ᶜ x - channelOn (↑(lowFrequencies H))ᶜ a) := by
  rw [truncatedAccumulation_eq, Finset.sum_sub_distrib, ← channelOn_lowFrequencies,
    ← channelOn_lowFrequencies]
  change (∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm x ρ) -
      (∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm a ρ) = _
  rw [channel_eq_packet_add_complement (↑(lowFrequencies H)) hx,
    channel_eq_packet_add_complement (↑(lowFrequencies H)) ha]
  ring

/-- **Convergence absolue du canal intégré** (corpus). -/
theorem integrated_contact_accumulation_converges {x : ℝ} (hx : 1 < x) :
    Summable (fun ρ : ExplicitIndex => integratedTowerTerm ρ x) :=
  nontrivial_zero_residue_series_summable hx

/-- Les troncatures par hauteur épuisent les indices : pour toute famille finie `t`, `t ⊆ Z_H` dès
que `H` dépasse la somme des hauteurs absolues de `t`. -/
theorem tendsto_lowFrequencies_atTop : Tendsto lowFrequencies atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro t
  refine ⟨∑ ρ ∈ t, |(ρ : ℂ).im|, fun H hH => ?_⟩
  intro ρ hρ
  rw [mem_lowFrequencies]
  calc |(ρ : ℂ).im| ≤ ∑ ρ ∈ t, |(ρ : ℂ).im| :=
        Finset.single_le_sum (f := fun ρ : ExplicitIndex => |(ρ : ℂ).im|)
          (fun ρ _ => abs_nonneg ((ρ : ℂ).im)) hρ
    _ ≤ H := hH

/-- **Limite du canal intégré** : les sommes tronquées par hauteur convergent vers la série. -/
theorem integrated_contact_limit_eq_spectral {x : ℝ} (hx : 1 < x) :
    Tendsto (fun H : ℝ => ∑ ρ ∈ lowFrequencies H, integratedTowerTerm ρ x) atTop
      (𝓝 (∑' ρ : ExplicitIndex, integratedTowerTerm ρ x)) :=
  (integrated_contact_accumulation_converges hx).hasSum.comp tendsto_lowFrequencies_atTop

/-- **Limite de l'accumulation tronquée** : `A_H(a, x) → Σ_ρ F_ρ(x) − Σ_ρ F_ρ(a)`
(canal intégré). -/
theorem integrated_accumulation_limit (k₀ : ExplicitIndex → ℤ) (n : ExplicitIndex → ℕ)
    {a x : ℝ} (ha : 1 < a) (hx : 1 < x) :
    Tendsto (fun H : ℝ => truncatedAccumulation H integratedTowerTerm k₀ n a x) atTop
      (𝓝 ((∑' ρ : ExplicitIndex, integratedTowerTerm ρ x) -
        (∑' ρ : ExplicitIndex, integratedTowerTerm ρ a))) := by
  have h := (integrated_contact_limit_eq_spectral hx).sub (integrated_contact_limit_eq_spectral ha)
  refine h.congr (fun H => ?_)
  rw [truncatedAccumulation_eq, Finset.sum_sub_distrib]

/-! ## 2. Canal brut : la prémisse isolée et ses conséquences conditionnelles -/

/-- La somme partielle symétrique du canal brut, tronquée à la hauteur `H`. -/
noncomputable def rawPartialSum (H : ℝ) (x : ℝ) : ℂ := ∑ ρ ∈ lowFrequencies H, rawTowerTerm ρ x

/-- Le fond brut est réutilisé du corpus : `rawBackground x = x − log 2π − ½ log(1 − x⁻²)`
(`Terminal/FirstGainPremise.lean`), de même que `chebyshevMidpoint x = (ψ(x) + ψ(x⁻))/2`. -/
theorem rawBackground_eq (x : ℝ) :
    rawBackground x = x - Real.log (2 * Real.pi) - (1 / 2) * Real.log (1 - x⁻¹ ^ 2) := rfl

/-- **LA PRÉMISSE ISOLÉE (ouverte dans le corpus)** : la formule explicite brute converge en `x`
(sommation symétrique par hauteur) vers `ψ₀(x) = (ψ(x) + ψ(x⁻))/2`. Vraie classiquement pour
`x > 1` ; elle n'est démontrée ni dans Mathlib ni dans le corpus. C'est une définition `Prop`,
jamais un axiome, jamais posée vraie. -/
def RawExplicitFormulaAt (x : ℝ) : Prop :=
  Tendsto (fun H : ℝ => (rawBackground x : ℂ) + rawPartialSum H x) atTop
    (𝓝 (chebyshevMidpoint x : ℂ))

/-- `ψ` est localement constante à gauche d'un non-entier : `ψ₀(x) = ψ(x)` dès que `⌊x⌋ < x`. -/
theorem chebyshevMidpoint_eq_psi {x : ℝ} (hx : ((⌊x⌋₊ : ℕ) : ℝ) < x) :
    chebyshevMidpoint x = Chebyshev.psi x := by
  unfold chebyshevMidpoint
  have hlim : Filter.limUnder (nhdsWithin x (Set.Iio x)) Chebyshev.psi = Chebyshev.psi x := by
    apply Filter.Tendsto.limUnder_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT hx] with y hy
    rw [← psi_floor y, ← psi_floor x]
    congr 2
    have h0 : 0 ≤ y := le_trans (Nat.cast_nonneg _) hy.1.le
    symm
    rw [Nat.floor_eq_iff h0]
    exact ⟨hy.1.le, hy.2.trans (Nat.lt_floor_add_one x)⟩
  rw [hlim]
  ring

theorem floor_lt_add_half (n : ℕ) : ((⌊(n : ℝ) + 1 / 2⌋₊ : ℕ) : ℝ) < (n : ℝ) + 1 / 2 := by
  have : ⌊(n : ℝ) + 1 / 2⌋₊ = n := by
    rw [Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
  rw [this]; linarith

theorem floor_lt_sub_half {n : ℕ} (hn : 1 ≤ n) :
    ((⌊(n : ℝ) - 1 / 2⌋₊ : ℕ) : ℝ) < (n : ℝ) - 1 / 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : ⌊(n : ℝ) - 1 / 2⌋₊ = n - 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    push_cast [Nat.cast_sub hn]
    constructor <;> linarith
  rw [this]
  push_cast [Nat.cast_sub hn]
  linarith

/-- Conditionnel : hors des événements, l'accumulation brute par contacts, plus le fond, tend vers
`ψ(x) − ψ(a)` dès que la formule brute converge en `a` et en `x`. -/
theorem raw_contact_limit_at_continuity {a x : ℝ} (ha' : ((⌊a⌋₊ : ℕ) : ℝ) < a)
    (hx' : ((⌊x⌋₊ : ℕ) : ℝ) < x)
    (ha : RawExplicitFormulaAt a) (hx : RawExplicitFormulaAt x) (k₀ : ExplicitIndex → ℤ)
    (n : ExplicitIndex → ℕ) :
    Tendsto (fun H : ℝ => ((rawBackground x : ℂ) - rawBackground a) +
        truncatedAccumulation H rawTowerTerm k₀ n a x) atTop
      (𝓝 ((Chebyshev.psi x : ℂ) - Chebyshev.psi a)) := by
  have h := hx.sub ha
  rw [chebyshevMidpoint_eq_psi hx', chebyshevMidpoint_eq_psi ha'] at h
  refine h.congr (fun H => ?_)
  rw [truncatedAccumulation_eq, Finset.sum_sub_distrib]
  unfold rawPartialSum
  ring

/-- `ψ` aux demi-entiers : `ψ(n + ½) = ψ(n)`. -/
theorem psi_add_half (n : ℕ) : Chebyshev.psi ((n : ℝ) + 1 / 2) = Chebyshev.psi n := by
  rw [← psi_floor ((n : ℝ) + 1 / 2)]
  congr 2
  rw [Nat.floor_eq_iff (by positivity)]
  constructor <;> linarith

/-- `ψ(n − ½) = ψ(n − 1)` pour `n ≥ 1`. -/
theorem psi_sub_half {n : ℕ} (hn : 1 ≤ n) :
    Chebyshev.psi ((n : ℝ) - 1 / 2) = Chebyshev.psi ((n : ℝ) - 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← psi_floor ((n : ℝ) - 1 / 2)]
  have hfloor : ⌊(n : ℝ) - 1 / 2⌋₊ = n - 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    push_cast [Nat.cast_sub hn]
    constructor <;> linarith
  rw [hfloor]
  push_cast [Nat.cast_sub hn]
  rfl

/-- **Le saut entre deux demi-entiers est le poids de von Mangoldt** : `ψ(n+½) − ψ(n−½) = Λ(n)`. -/
theorem psi_half_difference {n : ℕ} (hn : 1 ≤ n) :
    Chebyshev.psi ((n : ℝ) + 1 / 2) - Chebyshev.psi ((n : ℝ) - 1 / 2) = Λ n := by
  rw [psi_add_half, psi_sub_half hn, ← thm_weightFromPsi_chebyshev hn]
  rfl

/-- **Conditionnel, à la cassure** : si la formule brute converge aux deux demi-entiers encadrant
`n`, la différence des sommes partielles brutes, plus celle du fond, tend vers `Λ(n)`. -/
theorem raw_contact_limit_at_jump {n : ℕ} (hn : 1 ≤ n)
    (hplus : RawExplicitFormulaAt ((n : ℝ) + 1 / 2))
    (hminus : RawExplicitFormulaAt ((n : ℝ) - 1 / 2)) :
    Tendsto (fun H : ℝ => ((rawBackground ((n : ℝ) + 1 / 2) : ℂ) -
          rawBackground ((n : ℝ) - 1 / 2)) +
        (rawPartialSum H ((n : ℝ) + 1 / 2) - rawPartialSum H ((n : ℝ) - 1 / 2))) atTop
      (𝓝 ((Λ n : ℝ) : ℂ)) := by
  have h := hplus.sub hminus
  rw [chebyshevMidpoint_eq_psi (floor_lt_add_half n),
    chebyshevMidpoint_eq_psi (floor_lt_sub_half hn),
    ← Complex.ofReal_sub, psi_half_difference hn] at h
  refine h.congr (fun H => ?_)
  ring

/-- **Conditionnel : l'accumulation par contacts du canal brut conserve le saut arithmétique.**
Sous la prémisse isolée aux deux demi-entiers, l'accumulation collective tronquée (chaque Tour sur
ses propres contacts, bords compris) plus le fond tend vers `Λ(n)`. -/
theorem contact_limit_preserves_arithmetic_jump {n : ℕ} (hn : 1 ≤ n)
    (hplus : RawExplicitFormulaAt ((n : ℝ) + 1 / 2))
    (hminus : RawExplicitFormulaAt ((n : ℝ) - 1 / 2))
    (k₀ : ExplicitIndex → ℤ) (m : ExplicitIndex → ℕ) :
    Tendsto (fun H : ℝ => ((rawBackground ((n : ℝ) + 1 / 2) : ℂ) -
          rawBackground ((n : ℝ) - 1 / 2)) +
        truncatedAccumulation H rawTowerTerm k₀ m ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2)) atTop
      (𝓝 ((Λ n : ℝ) : ℂ)) := by
  refine (raw_contact_limit_at_jump hn hplus hminus).congr (fun H => ?_)
  rw [truncatedAccumulation_eq, Finset.sum_sub_distrib]
  rfl

#print axioms integrated_accumulation_limit
#print axioms psi_half_difference
#print axioms contact_limit_preserves_arithmetic_jump

end RHV6Fresh
