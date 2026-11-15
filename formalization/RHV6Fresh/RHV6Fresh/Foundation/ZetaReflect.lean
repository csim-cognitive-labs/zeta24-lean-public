/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
Fichier contenant des adaptations de code tiers sous Apache 2.0 : la provenance est indiquée ci-dessous et ses notices sont conservées.
-/

import RHV3Lean.Objects.FunctionalMirror
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# RHV6Fresh — L4, représentation des zéros hors ligne : port de zeta23

**Source portée** : `anthropics/formal-math`, sous-projet `zeta23`
(<https://github.com/anthropics/formal-math/tree/main/zeta23>, Apache-2.0),
formalisation Lean 4 validée par les auteurs du théorème « plus des deux tiers
des zéros de zêta sont simples et sur la droite critique » (Alpöge–Furman,
arXiv:2608.13637). Même toolchain (`leanprover/lean4:v4.33.0-rc2`) et même
révision de Mathlib (`51e6992efd06126df61a496bebf8f49482a4e129`) que ce dépôt.

Fichiers retranscrits (PORT, jamais import) :
* `Zeta23/Statement.lean` — `IsNontrivialZero`, `zeroMult` ;
* `Zeta23/Defs.lean` — `reflect`, `ZeroConfig` ;
* `Zeta23/ZetaReflect.lean` — `analyticOrderAt_conj_conj`,
  `analyticOrderAt_zeta_conj`, `analyticOrderAt_zeta_one_sub`,
  `zeta_reflect_zero`, `zeta_mult_reflect` ;
* `Zeta23/Statement/Seam.lean`, `SeamClosed.lean` — finitude des fenêtres,
  `one_le_mult`, `zetaZeroConfig`.

Écarts de port, tous documentés sur place : la réflexion de Schwarz
`riemannZeta_conj` est prise dans Mathlib (sans hypothèse `s ≠ 1`) là où zeta23
la redémontre ; les énoncés sont posés sur `PIsNonTrivialZetaZero` (RHV3Lean O1),
définitionnellement identique à `IsNontrivialZero` de zeta23 ; la multiplicité
est conservée au niveau `ℕ∞` (`nZeroMultiplicity`, RHV3Lean) puis projetée en
`ℕ` (`zeroMult`, zeta23).

**Sens (maîtres §8)** : personne ne sait calculer un zéro hors de la droite
critique. Le miroir n'est donc jamais calculé ni approché ; il est représenté
par cette méthode compilée : point d'annulation de zêta dans la bande ouverte,
multiplicité analytique, image réfléchie `ρ ↦ 1 − ρ̄` de même multiplicité,
finitude de toute fenêtre d'ordonnées. Le miroir de RHV3Lean (`cMirrorSupport`)
est littéralement `reflect` de zeta23 (`zetaReflect_eq_mirrorSupport`, `rfl`).

Aucun sorry, aucun admit, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean Complex Set Filter Topology
open scoped ComplexConjugate

/-! ## 1. Zéro non trivial, multiplicité, réflexion — identité avec RHV3Lean O1 -/

/-- zeta23 `IsNontrivialZero ρ := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1` est,
mot pour mot, `PIsNonTrivialZetaZero` de RHV3Lean. -/
theorem isNontrivialZero_iff (ρ : ℂ) :
    PIsNonTrivialZetaZero ρ ↔ (riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) := Iff.rfl

/-- zeta23 `zeroMult` : multiplicité en `ℕ` (`toNat` envoie `⊤` sur `0`). -/
noncomputable def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

theorem zeroMult_eq_toNat_multiplicity (z : TNonTrivialZetaZero) :
    zeroMult (cZeroSupport z) = (nZeroMultiplicity z).toNat := rfl

/-- zeta23 `reflect` : `ρ ↦ 1 − ρ̄` (même ordonnée, partie réelle réfléchie). -/
def zetaReflect (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

/-- Le support du miroir de RHV3Lean est exactement `reflect` de zeta23. -/
theorem zetaReflect_eq_mirrorSupport (z : TNonTrivialZetaZero) :
    zetaReflect (cZeroSupport z) = cMirrorSupport z := rfl

@[simp] theorem zetaReflect_re (ρ : ℂ) : (zetaReflect ρ).re = 1 - ρ.re := by
  simp [zetaReflect]

@[simp] theorem zetaReflect_im (ρ : ℂ) : (zetaReflect ρ).im = ρ.im := by
  simp [zetaReflect]

/-! ## 2. Ordre d'annulation sous conjugaison (port de `Zeta23/ZetaReflect.lean` §2) -/

private lemma tendsto_conj_nhds (w : ℂ) :
    Tendsto (fun z => conj z) (𝓝 (conj w)) (𝓝 w) := by
  have h := (Complex.continuous_conj).tendsto (conj w)
  rwa [Complex.conj_conj] at h

private lemma analyticAt_conj_conj {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f w) :
    AnalyticAt ℂ (fun z => conj (f (conj z))) (conj w) := by
  rw [analyticAt_iff_eventually_differentiableAt] at hf ⊢
  filter_upwards [(tendsto_conj_nhds w).eventually hf] with z hz
  have h2 := hz.conj_conj
  rw [Complex.conj_conj] at h2
  exact h2

/-- L'ordre d'annulation de `z ↦ conj (f (conj z))` en `conj w` est celui de `f` en `w`. -/
theorem analyticOrderAt_conj_conj (f : ℂ → ℂ) (w : ℂ) :
    analyticOrderAt (fun z => conj (f (conj z))) (conj w) = analyticOrderAt f w := by
  by_cases hf : AnalyticAt ℂ f w
  · by_cases htop : analyticOrderAt f w = ⊤
    · rw [htop, analyticOrderAt_eq_top]
      filter_upwards [(tendsto_conj_nhds w).eventually (analyticOrderAt_eq_top.mp htop)] with z hz
      simp [hz]
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← hn]
      rw [Eq.comm, hf.analyticOrderAt_eq_natCast] at hn
      obtain ⟨g, hg, hgne, hfg⟩ := hn
      rw [(analyticAt_conj_conj hf).analyticOrderAt_eq_natCast]
      refine ⟨fun z => conj (g (conj z)), analyticAt_conj_conj hg, by simpa using hgne, ?_⟩
      filter_upwards [(tendsto_conj_nhds w).eventually hfg] with z hz
      have : conj (f (conj z)) = conj ((conj z - w) ^ n * g (conj z)) := by rw [hz]; rfl
      rw [this]
      simp only [map_mul, map_pow, map_sub, Complex.conj_conj]
      rfl
  · have hf' : ¬ AnalyticAt ℂ (fun z => conj (f (conj z))) (conj w) := by
      intro hcon
      apply hf
      have h2 := analyticAt_conj_conj hcon
      rw [Complex.conj_conj] at h2
      exact h2.congr (Filter.Eventually.of_forall fun u => by
        simp only [Complex.conj_conj])
    rw [analyticOrderAt_of_not_analyticAt hf, analyticOrderAt_of_not_analyticAt hf']

/-- L'ordre d'annulation de zêta est symétrique par conjugaison.
Écart de port : zeta23 suppose `w ≠ 1` parce qu'il redémontre la réflexion de
Schwarz hors du pôle ; Mathlib la fournit partout (`riemannZeta_conj`), donc
l'hypothèse tombe. -/
theorem analyticOrderAt_zeta_conj (w : ℂ) :
    analyticOrderAt riemannZeta (conj w) = analyticOrderAt riemannZeta w := by
  have hcong : (fun z => conj (riemannZeta (conj z))) =ᶠ[𝓝 (conj w)] riemannZeta := by
    filter_upwards with z
    rw [riemannZeta_conj, Complex.conj_conj]
  calc analyticOrderAt riemannZeta (conj w)
      = analyticOrderAt (fun z => conj (riemannZeta (conj z))) (conj w) :=
        (analyticOrderAt_congr hcong).symm
    _ = analyticOrderAt riemannZeta w := analyticOrderAt_conj_conj _ _

/-! ## 3. Transport de l'ordre par l'équation fonctionnelle (port §3) -/

/-- Le préfacteur de `riemannZeta_one_sub` : `E(s) = 2(2π)^{−s} Γ(s) cos(πs/2)`. -/
private noncomputable def Efac (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)

private lemma two_pi_ne_zero' : (2 * (Real.pi : ℂ)) ≠ 0 := by
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨two_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero⟩

private lemma Efac_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : Efac s ≠ 0 := by
  have hsne : ∀ m : ℕ, s ≠ -m := by
    intro m h
    rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) h0
  have hcpow : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero two_pi_ne_zero']
    exact Complex.exp_ne_zero _
  have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have hπ : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h2 : (Real.pi : ℂ) * s = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
      linear_combination (2 : ℂ) * hk
    have hs_eq : s = ((2 * k + 1 : ℤ) : ℂ) := by
      have h3 := mul_left_cancel₀ hπ h2
      rw [h3]
      push_cast
      ring
    rw [hs_eq, Complex.intCast_re] at h0 h1
    have h0' : (0 : ℤ) < 2 * k + 1 := by exact_mod_cast h0
    have h1' : (2 * k + 1 : ℤ) < 1 := by exact_mod_cast h1
    omega
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hsne
  unfold Efac
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hcpow) hΓ) hcos

private lemma analyticAt_Efac {s : ℂ} (h0 : 0 < s.re) : AnalyticAt ℂ Efac s := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-z)) s := by
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards with z
    exact (differentiableAt_id.neg).const_cpow (Or.inl two_pi_ne_zero')
  have h2 : AnalyticAt ℂ Complex.Gamma s := by
    rw [analyticAt_iff_eventually_differentiableAt]
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds h0] with z hz
    refine Complex.differentiableAt_Gamma z fun m => ?_
    intro h
    rw [h] at hz
    simp only [Complex.neg_re, Complex.natCast_re] at hz
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) hz
  have h3 : AnalyticAt ℂ (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z / 2)) s := by
    have hlin : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) * z / 2) s := by
      apply AnalyticAt.div_const
      exact analyticAt_const.mul analyticAt_id
    exact Complex.analyticAt_cos.comp hlin
  have h4 : AnalyticAt ℂ (fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-z)) s :=
    analyticAt_const.mul h1
  exact (h4.mul h2).mul h3

/-- Transport de l'ordre par l'équation fonctionnelle : dans la bande ouverte,
`ord_{1−w} ζ = ord_w ζ`. -/
theorem analyticOrderAt_zeta_one_sub {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    analyticOrderAt riemannZeta (1 - w) = analyticOrderAt riemannZeta w := by
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hev : (riemannZeta ∘ (fun z : ℂ => 1 - z)) =ᶠ[𝓝 w]
      (Efac * riemannZeta) := by
    filter_upwards [hopen.mem_nhds ⟨h0, h1⟩] with z hz
    have hzne : ∀ n : ℕ, z ≠ -n := by
      intro n h
      rw [h] at hz
      simp only [Complex.neg_re, Complex.natCast_re] at hz
      exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) hz.1
    have hzne1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      simp only [Complex.one_re] at hz
      exact lt_irrefl 1 hz.2
    change riemannZeta (1 - z) = Efac z * riemannZeta z
    rw [riemannZeta_one_sub hzne hzne1]
    unfold Efac
    ring
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) w := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun z : ℂ => 1 - z) w ≠ 0 := by
    have : deriv (fun z : ℂ => 1 - z) w = -1 := by
      rw [deriv_const_sub]
      simp
    rw [this]
    simp
  have hEfac := analyticAt_Efac h0
  have hEord : analyticOrderAt Efac w = 0 :=
    hEfac.analyticOrderAt_eq_zero.mpr (Efac_ne_zero h0 h1)
  calc analyticOrderAt riemannZeta (1 - w)
      = analyticOrderAt (riemannZeta ∘ (fun z : ℂ => 1 - z)) w := by
        rw [analyticOrderAt_comp_of_deriv_ne_zero hg hg']
    _ = analyticOrderAt (Efac * riemannZeta) w := analyticOrderAt_congr hev
    _ = analyticOrderAt Efac w + analyticOrderAt riemannZeta w := by
        by_cases hζw : AnalyticAt ℂ riemannZeta w
        · exact analyticOrderAt_mul hEfac hζw
        · exfalso
          exact hζw (by
            rw [analyticAt_iff_eventually_differentiableAt]
            have hne1 : w ≠ 1 := by
              intro h
              rw [h] at h1
              simp at h1
            filter_upwards [isOpen_compl_singleton.mem_nhds
              (by simpa using hne1 : w ∈ ({(1 : ℂ)}ᶜ))] with z hz
            exact differentiableAt_riemannZeta (by simpa using hz))
    _ = analyticOrderAt riemannZeta w := by rw [hEord, zero_add]

/-! ## 4. Les deux champs de réflexion (port §4) -/

/-- H-symm (ensemble) : `ρ ↦ 1 − ρ̄` envoie les zéros non triviaux sur les zéros
non triviaux. -/
theorem zeta_reflect_zero (ρ : ℂ) (h : PIsNonTrivialZetaZero ρ) :
    PIsNonTrivialZetaZero (zetaReflect ρ) := by
  obtain ⟨hzero, h0, h1⟩ := h
  have hρne : ∀ n : ℕ, ρ ≠ -n := by
    intro n h
    rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) h0
  have hρne1 : ρ ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have hrefl_eq : zetaReflect ρ = conj (1 - ρ) := by
    unfold zetaReflect
    rw [map_sub, map_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [hrefl_eq, riemannZeta_conj, riemannZeta_one_sub hρne hρne1, hzero]
    simp
  · rw [zetaReflect_re]
    linarith
  · rw [zetaReflect_re]
    linarith

/-- H-symm (multiplicité), niveau `ℕ∞` : `ord_{1−ρ̄} ζ = ord_ρ ζ`. -/
theorem analyticOrderAt_zeta_reflect {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt riemannZeta (zetaReflect ρ) = analyticOrderAt riemannZeta ρ := by
  have hrefl_eq : zetaReflect ρ = conj (1 - ρ) := by
    unfold zetaReflect
    rw [map_sub, map_one]
  rw [hrefl_eq, analyticOrderAt_zeta_conj, analyticOrderAt_zeta_one_sub h0 h1]

/-- H-symm (multiplicité), forme zeta23 : `m_{1−ρ̄} = m_ρ`. -/
theorem zeta_mult_reflect (ρ : ℂ) (h : PIsNonTrivialZetaZero ρ) :
    zeroMult (zetaReflect ρ) = zeroMult ρ := by
  unfold zeroMult
  rw [analyticOrderAt_zeta_reflect h.2.1 h.2.2]

/-! ## 5. Raccord avec le miroir de RHV3Lean (S1) -/

/-- Le miroir de RHV3Lean conserve la multiplicité analytique (niveau `ℕ∞`). -/
theorem mirror_multiplicity (z : TNonTrivialZetaZero) :
    nZeroMultiplicity (zMirrorZero z) = nZeroMultiplicity z :=
  analyticOrderAt_zeta_reflect (thm_zeroRadialPosition_positive z)
    (thm_zeroRadialPosition_lt_one z)

/-- Idem sur la branche supérieure. -/
theorem upperMirror_multiplicity (z : TUpperNonTrivialZetaZero) :
    nZeroMultiplicity (zUpperMirrorZero z).1 = nZeroMultiplicity z.1 :=
  mirror_multiplicity z.1

/-- Le support du miroir supérieur est `reflect` du support. -/
theorem upperMirror_support_eq_reflect (z : TUpperNonTrivialZetaZero) :
    cZeroSupport (zUpperMirrorZero z).1 = zetaReflect (cZeroSupport z.1) := rfl

/-! ## 6. Finitude et multiplicité ≥ 1 (port de `Zeta23/Statement/Seam.lean`) -/

/-- ζ est analytique sur `ℂ ∖ {1}`. -/
theorem riemannZeta_analyticOnNhd_compl_one : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro s hs
  exact (differentiableAt_riemannZeta hs).differentiableWithinAt

/-- `ℂ ∖ {1}` est connexe. -/
theorem isConnected_compl_one : IsConnected ({1}ᶜ : Set ℂ) :=
  isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 1

/-- ζ n'est identiquement nulle au voisinage d'aucun point de `ℂ ∖ {1}`. -/
theorem analyticOrderAt_riemannZeta_ne_top {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine riemannZeta_analyticOnNhd_compl_one.analyticOrderAt_ne_top_of_isPreconnected
    isConnected_compl_one.isPreconnected h2 hs ?_
  rw [(riemannZeta_analyticOnNhd_compl_one 2 h2).analyticOrderAt_eq_zero.mpr
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
  exact ENat.zero_ne_top

/-- La multiplicité d'un vrai zéro est finie. -/
theorem multiplicity_ne_top (z : TNonTrivialZetaZero) : nZeroMultiplicity z ≠ ⊤ :=
  analyticOrderAt_riemannZeta_ne_top (thm_zeroSupport_ne_pole z)

/-- H-fin : en un zéro non trivial, `1 ≤ m_ρ`. -/
theorem one_le_zeroMult (ρ : ℂ) (h : PIsNonTrivialZetaZero ρ) : 1 ≤ zeroMult ρ := by
  have hρ1 : ρ ≠ 1 := by
    intro h1
    have := h.2.2
    rw [h1] at this
    simp at this
  have han : AnalyticAt ℂ riemannZeta ρ := riemannZeta_analyticOnNhd_compl_one ρ hρ1
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 := han.analyticOrderAt_ne_zero.mpr h.1
  have hnetop := analyticOrderAt_riemannZeta_ne_top hρ1
  unfold zeroMult
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_natCast, ne_eq, Nat.cast_eq_zero] at hne0 ⊢
  omega

/-- Les zéros de ζ (hors du pôle) sont localement finis sur tout ℂ. -/
theorem riemannZeta_zeros_locallyFinite (z : ℂ) :
    ∃ t ∈ 𝓝 z, (t ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0}).Finite := by
  by_cases hz : z = 1
  · subst hz
    have hres := riemannZeta_residue_one
    have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), riemannZeta s ≠ 0 := by
      have : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) * riemannZeta s ≠ 0 :=
        hres.eventually_ne one_ne_zero
      exact this.mono fun s hs h => hs (by simp [h])
    rw [eventually_nhdsWithin_iff] at hev
    refine ⟨{s | s ∈ ({1}ᶜ : Set ℂ) → riemannZeta s ≠ 0}, hev, ?_⟩
    refine (Set.finite_empty).subset ?_
    rintro s ⟨hs, hs1, hz⟩
    exact hs hs1 hz
  · have hcod :=
      riemannZeta_analyticOnNhd_compl_one.eqOn_zero_or_eventually_ne_zero_of_preconnected
        isConnected_compl_one.isPreconnected
    rcases hcod with hzero | hcod
    · exfalso
      have : riemannZeta 2 = 0 := hzero (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
      exact riemannZeta_ne_zero_of_one_lt_re (by norm_num) this
    · rw [Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin] at hcod
      obtain ⟨t, ht, hfin⟩ := hcod z hz
      refine ⟨t, ht, hfin.subset ?_⟩
      rintro s ⟨hst, hs1, hs0⟩
      exact ⟨hst, hs1, by simpa using hs0⟩

/-- Finitude locale : il n'y a qu'un nombre fini de zéros non triviaux d'ordonnée
dans `(T₁, T₂]`. -/
theorem zeta_window_finite (T₁ T₂ : ℝ) :
    ({ρ | PIsNonTrivialZetaZero ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite := by
  set K : Set ℂ := (Icc 0 1) ×ℂ (Icc T₁ T₂) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  choose t ht hfin using riemannZeta_zeros_locallyFinite
  obtain ⟨I, -, hcover⟩ := hKc.elim_nhds_subcover t (fun z _ => ht z)
  have hfinU : (⋃ z ∈ I, (t z ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0})).Finite :=
    I.finite_toSet.biUnion fun z _ => hfin z
  refine hfinU.subset ?_
  rintro ρ ⟨hρ, hT₁, hT₂⟩
  have hρ1 : ρ ≠ 1 := by
    intro h1
    have := hρ.2.2
    rw [h1] at this
    simp at this
  have hρK : ρ ∈ K := ⟨⟨hρ.2.1.le, hρ.2.2.le⟩, ⟨hT₁.le, hT₂⟩⟩
  obtain ⟨z, hzI, hρz⟩ := mem_iUnion₂.mp (hcover hρK)
  exact mem_iUnion₂.mpr ⟨z, hzI, hρz, hρ1, hρ.1⟩

/-! ## 7. La configuration abstraite de zéros (port de `Zeta23/Defs.lean` §3) -/

/-- zeta23 `ZeroConfig` : un ensemble de points distincts de la bande fermée, avec
multiplicités `≥ 1`, localement fini en ordonnée, invariant par `ρ ↦ 1 − ρ̄` à
multiplicité égale. « Toute multi-partie localement finie de points de la bande,
invariante par `ρ ↦ 1 − ρ̄` ; elle ne contient aucune arithmétique. » -/
structure ZeroConfig where
  carrier : Set ℂ
  mult : ℂ → ℕ
  one_le_mult : ∀ ρ ∈ carrier, 1 ≤ mult ρ
  strip : ∀ ρ ∈ carrier, 0 ≤ ρ.re ∧ ρ.re ≤ 1
  reflect_mem : ∀ ρ ∈ carrier, zetaReflect ρ ∈ carrier
  mult_reflect : ∀ ρ ∈ carrier, mult (zetaReflect ρ) = mult ρ
  finite_window : ∀ T₁ T₂ : ℝ, (carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite

/-- Les zéros non triviaux de ζ avec leurs multiplicités, comme configuration
abstraite — sans hypothèse (zeta23 `zetaZeroConfig`, couture fermée). -/
noncomputable def zetaZeroConfig : ZeroConfig where
  carrier := {ρ | PIsNonTrivialZetaZero ρ}
  mult := zeroMult
  one_le_mult := fun ρ h => one_le_zeroMult ρ h
  strip := fun _ h => ⟨h.2.1.le, h.2.2.le⟩
  reflect_mem := fun ρ h => zeta_reflect_zero ρ h
  mult_reflect := fun ρ h => zeta_mult_reflect ρ h
  finite_window := zeta_window_finite

@[simp] theorem zetaZeroConfig_carrier :
    zetaZeroConfig.carrier = {ρ | PIsNonTrivialZetaZero ρ} := rfl

@[simp] theorem zetaZeroConfig_mult : zetaZeroConfig.mult = zeroMult := rfl

/-- Tout vrai zéro de RHV3Lean est un point de la configuration portée. -/
theorem zeroSupport_mem_zetaZeroConfig (z : TNonTrivialZetaZero) :
    cZeroSupport z ∈ zetaZeroConfig.carrier := z.2

/-! ## 7. La réflexion de l'équation fonctionnelle elle-même : `ρ ↦ 1 − ρ`

`riemannZeta_one_sub` (Mathlib) relie `ζ(1 − s)` à `ζ(s)` : le zéro réfléchi par l'équation
fonctionnelle est `1 − ρ = (1 − β, −T)`, dans le demi-plan inférieur.  Il est le conjugué du miroir
supérieur `1 − ρ̄` (zeta23 `reflect`), à un pas de conjugaison près (`riemannZeta_conj`).  C'est ce
zéro, et lui seul, qui porte le renversement du sens de parcours de la seconde Tour
(`Tower/ReflectedMotion.lean`) : sa vitesse angulaire est `−T`. -/

/-- `ρ ↦ 1 − ρ` : la réflexion de l'équation fonctionnelle. -/
def zetaFunctionalReflect (ρ : ℂ) : ℂ := 1 - ρ

/-- Le zéro réfléchi est le conjugué du miroir supérieur. -/
theorem zetaFunctionalReflect_eq_conj_reflect (ρ : ℂ) :
    zetaFunctionalReflect ρ = conj (zetaReflect ρ) := by
  unfold zetaFunctionalReflect zetaReflect
  rw [map_sub, map_one, Complex.conj_conj]

@[simp] theorem zetaFunctionalReflect_re (ρ : ℂ) : (zetaFunctionalReflect ρ).re = 1 - ρ.re := by
  simp [zetaFunctionalReflect]

@[simp] theorem zetaFunctionalReflect_im (ρ : ℂ) : (zetaFunctionalReflect ρ).im = -ρ.im := by
  simp [zetaFunctionalReflect]

/-- `ρ ↦ 1 − ρ` envoie les zéros non triviaux sur les zéros non triviaux (équation fonctionnelle
et conjugaison, port zeta23 + Mathlib). -/
theorem zeta_functionalReflect_zero (ρ : ℂ) (h : PIsNonTrivialZetaZero ρ) :
    PIsNonTrivialZetaZero (zetaFunctionalReflect ρ) := by
  obtain ⟨hzero, _, _⟩ := zeta_reflect_zero ρ h
  refine ⟨?_, ?_, ?_⟩
  · rw [zetaFunctionalReflect_eq_conj_reflect, riemannZeta_conj, hzero]
    simp
  · rw [zetaFunctionalReflect_re]
    linarith [h.2.2]
  · rw [zetaFunctionalReflect_re]
    linarith [h.2.1]

/-- Conservation de la multiplicité sous `ρ ↦ 1 − ρ`. -/
theorem zeta_mult_functionalReflect (ρ : ℂ) (h : PIsNonTrivialZetaZero ρ) :
    zeroMult (zetaFunctionalReflect ρ) = zeroMult ρ := by
  unfold zeroMult
  rw [zetaFunctionalReflect_eq_conj_reflect, analyticOrderAt_zeta_conj,
    analyticOrderAt_zeta_reflect h.2.1 h.2.2]

/-- Le zéro réfléchi de `z` est le conjugué du support du miroir supérieur de `z`. -/
theorem functionalReflect_support_eq_conj_mirror (z : TUpperNonTrivialZetaZero) :
    zetaFunctionalReflect (cZeroSupport z.1) = conj (cZeroSupport (zUpperMirrorZero z).1) := by
  rw [zetaFunctionalReflect_eq_conj_reflect]
  rfl

/-- Coordonnées du zéro réfléchi : partie réelle `1 − β` (celle du miroir supérieur). -/
theorem functionalReflect_re_eq_mirror (z : TUpperNonTrivialZetaZero) :
    (zetaFunctionalReflect (cZeroSupport z.1)).re = rZeroRadialPosition (zUpperMirrorZero z).1 := by
  rw [functionalReflect_support_eq_conj_mirror]
  simp [rZeroRadialPosition]

/-- Coordonnées du zéro réfléchi : partie imaginaire `−T` (l'opposé de celle du miroir supérieur). -/
theorem functionalReflect_im_eq_neg_mirror (z : TUpperNonTrivialZetaZero) :
    (zetaFunctionalReflect (cZeroSupport z.1)).im = -(rZeroHeight (zUpperMirrorZero z).1) := by
  rw [functionalReflect_support_eq_conj_mirror]
  simp [rZeroHeight]

end RHV6Fresh
