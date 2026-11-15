/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.OffCarrier
import RHV6Fresh.Terminal.MeetingExactness
import RHV6Fresh.Terminal.RegimeCell
import RHV6Fresh.Terminal.RayCapture

/-!
# Mêmes écarts, Tour géométrique et contacts (module isolé, non importé par la chaîne, 2026-11-01)

Étape F du plan pré-enregistré au maître §19.24.8, consolidée par le texte de l'auteur « Démonstration mathématique
de la Tour issue du zéro authentique » (2026-11-01). Feu vert de l'auteur le 2026-11-01. Tous les énoncés sont des
instances, des compositions ou des réécritures de théorèmes existants ; **aucune hypothèse nouvelle**, une seule
définition nouvelle (`geometricTower`, la construction `Z_ρ(s) = ρ·exp((β + iT)s/T)` du texte, §3).

## F — les mêmes écarts

* **F1** `primeGapContribution_eq_interval` : la contribution brute d'un point au rang `n` est `gapTerm` sur les bornes
  logarithmiques de l'écart `⟨n⟩ : PrimeGapInterval` (égalité par définition).
* **F2** `lower_eq_exp_a`, `meetingPoint_eq_exp_b` : les bornes de l'écart sont les exponentielles des bornes de la
  contribution ; la rencontre est `exp b = p_{n+1}`.
* **F3** `primeGapContribution_eq_cpow`, `primeGapContribution_eq_zeroTerm_sub` : contribution brute
  `= (p_{n+1}^ρ − p_n^ρ)/ρ` (la quantité `Δ_{ρ,n}` du texte) `= 𝒯_ρ(p_{n+1}) − 𝒯_ρ(p_n)` sur la Tour du zéro.
* **F4** `smoothedLocalContribution_eq_scaled_raw` : contribution lissée `= (−m/(ρ + 1))` × contribution brute,
  sur le même écart.
* **F5** `tsum_smoothed_eq_remainder_at_meeting` : la somme sur tous les vrais zéros des contributions lissées de `⟨n⟩`
  est l'incrément du reste lissé entre `p_n` et la rencontre.
* **F6** `OffCarrier.same_gap_bounds`, `OffCarrier.pair_signature_on_gap`, `OffCarrier.break_at_meetingPoint` : pour
  un porteur OFF, l'écart de la paire, l'écart de la liaison et l'écart de la cassure ont les bornes de `⟨C.n⟩`.
* **F7** `contact_ne_densitySignChange` : aucun contact `C_k` d'un vrai zéro n'est un changement de signe `x_{k'}` de
  sa densité de comptage, pour tous `k, k'`.
* **F8** `no_finite_family_at_any_meeting` : à aucune rencontre, aucune famille finie (en particulier les trois
  premiers zéros) n'accomplit la demande sur un voisinage.

## T — la Tour géométrique du texte (§2–§7 du texte)

* **T1** `contact_ratio` : `C_{k+1}/C_k = exp(π/T)`.
* **T2** `height_from_contacts` : `T = π / log(C_{k+1}/C_k)` (reconstruction de la fréquence).
* **T3** `radial_from_contact` : `β = T / tan(T·log C_k)` (inversion tangentielle, tout `k`).
* **T4** `radius_at_contact`, `radius_ratio`, `radius_ratio_gt_one` : rayon `R_k = C_k^β/‖ρ‖`, `R_{k+1}/R_k = exp(βπ/T) > 1`
  (descente spiralée vers l'origine quand `k` décroît).
* **T5** `geometricTower_zero`, `geometricTower_norm`, `geometricTower_similar_zeroTerm` : la construction
  `Z_ρ(s) = ρ·exp(ρ s/T)` part exactement de `ρ` (`Z_ρ(0) = ρ`), a pour rayon `‖ρ‖·exp(βs/T)`, et est l'image de la
  fonction de Tour `𝒯_ρ(x) = x^ρ/ρ` par l'**homothétie** de rapport réel `‖ρ‖²·exp(−2βφ/T)` sous le changement de
  paramètre `s = T·log x − 2φ` : les deux représentations du texte sont reliées par une similitude du plan (ici une
  homothétie), et les contacts `C_k` de `𝒯_ρ` correspondent aux passages `s_k = kπ − φ` de `Z_ρ` sur l'axe réel.

## E — signature de la paire sur trois écarts consécutifs

* **E1** `OffCarrier.pair_signature_three_gaps` : la signature hyperbolique de la paire sur `⟨n⟩, ⟨n+1⟩, ⟨n+2⟩`
  télescope en une seule intégrale sur `[log p_n, log p_{n+3}]`. Identité ; la question « signature ⟹ ⊥ ? » de
  §19.12 reste ouverte, rien n'est conclu sur `β`.

Aucun énoncé ne conclut sur `β` ; aucun n'identifie un contact à un premier ; aucun ne pose d'hypothèse.
Aucun `sorry`, aucun `admit`, aucun axiome. Ce module n'est pas importé par `RHV6Fresh.lean`.
-/

namespace RHV6Fresh

open RHV3Lean Filter Topology

/-! ## F1–F2. Une seule notion d'écart -/

/-- **F1.** La contribution brute au rang `n` est `gapTerm` sur les bornes logarithmiques de l'écart `⟨n⟩`. -/
theorem primeGapContribution_eq_interval (ρ : ℂ) (n : ℕ) :
    primeGapContribution ρ n = gapTerm ρ (⟨n⟩ : PrimeGapInterval).a (⟨n⟩ : PrimeGapInterval).b := rfl

/-- **F2.** La borne inférieure de l'écart est l'exponentielle de la borne inférieure de la contribution. -/
theorem lower_eq_exp_a (I : PrimeGapInterval) : Real.exp I.a = I.lower :=
  Real.exp_log (lt_trans one_pos I.one_lt_lower)

/-- **F2.** La rencontre est l'exponentielle de la borne supérieure de la contribution : `exp b = p_{n+1}`. -/
theorem meetingPoint_eq_exp_b (I : PrimeGapInterval) : Real.exp I.b = meetingPoint I :=
  Real.exp_log (lt_trans one_pos I.one_lt_upper)

/-! ## F3. La contribution brute est `Δ_{ρ,n}` du texte, lue sur la Tour -/

/-- **F3.** `Δ_{ρ,n} = (p_{n+1}^ρ − p_n^ρ)/ρ`. -/
theorem primeGapContribution_eq_cpow (z : TrueZero) (n : ℕ) :
    primeGapContribution (zeroPoint z) n =
      (((fnPrimeAtRank (n + 1) : ℝ) : ℂ) ^ zeroPoint z - ((fnPrimeAtRank n : ℝ) : ℂ) ^ zeroPoint z) /
        zeroPoint z := by
  have h : ∀ k, (0 : ℝ) < fnPrimeAtRank k := fun k => by
    exact_mod_cast (thm_primeAtRank_isPrime k).pos
  exact gapTerm_eq_cpow (zeroPoint_ne_zero z) (h n) (h (n + 1))

/-- **F3 bis.** La contribution brute est l'incrément de la fonction de Tour `𝒯_ρ(x) = x^ρ/ρ` entre `p_n` et la
rencontre `p_{n+1}`. -/
theorem primeGapContribution_eq_zeroTerm_sub (z : TrueZero) (n : ℕ) :
    primeGapContribution (zeroPoint z) n =
      zeroTerm z (meetingPoint ⟨n⟩) - zeroTerm z (⟨n⟩ : PrimeGapInterval).lower := by
  rw [primeGapContribution_eq_cpow, sub_div]
  rfl

/-! ## F4–F5. Canal lissé : même écart, même rencontre -/

/-- **F4.** Contribution lissée `= (−m/(ρ + 1))` × contribution brute, sur le même écart. -/
theorem smoothedLocalContribution_eq_scaled_raw (ρ : ExplicitIndex) (n : ℕ) :
    smoothedLocalContribution ρ ⟨n⟩ =
      (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) + 1)) * primeGapContribution ρ n := rfl

/-- **F5.** La somme sur tous les vrais zéros des contributions lissées de `⟨n⟩` est l'incrément du reste lissé entre
`p_n` et la rencontre `p_{n+1}`. -/
theorem tsum_smoothed_eq_remainder_at_meeting (n : ℕ) :
    ∑' ρ : ExplicitIndex, smoothedLocalContribution ρ ⟨n⟩ =
      smoothedRemainder (meetingPoint ⟨n⟩) - smoothedRemainder (⟨n⟩ : PrimeGapInterval).lower :=
  (all_signals_meet ⟨n⟩).symm

/-! ## F6. Porteur OFF : paire, liaison, cassure sur le même écart -/

namespace OffCarrier

variable (C : OffCarrier)

/-- **F6.** L'écart du porteur a pour bornes `p_n` (occurrence du zéro OFF) et la rencontre `p_{n+1}`, premier partagé
du raccord sortant. -/
theorem same_gap_bounds :
    C.gap.lower = (fnPrimeAtRank C.n : ℝ) ∧
    meetingPoint C.gap = (fnPrimeAtRank (C.n + 1) : ℝ) ∧
    meetingPoint C.gap = (C.outgoingRaccord.M : ℝ) :=
  ⟨rfl, rfl, C.liaison.1⟩

/-- **F6 bis.** La signature de la paire est écrite sur les bornes logarithmiques de ce même écart. -/
theorem pair_signature_on_gap :
    C.gap.a = Real.log (fnPrimeAtRank C.n) ∧ C.gap.b = Real.log (meetingPoint C.gap) ∧
    gapTerm (zeroPoint C.zero) C.gap.a C.gap.b + gapTerm (zeroPoint (mirrorMember C.zero)) C.gap.a C.gap.b -
        2 * gapTerm C.linePoint C.gap.a C.gap.b =
      ∫ t in C.gap.a..C.gap.b,
        2 * (Complex.cosh ((C.radialShift : ℂ) * t) - 1) * Complex.exp (C.linePoint * t) :=
  ⟨rfl, rfl, C.pair_gapTerm_signature C.gap⟩

/-- **F6 ter.** Le pas de la cassure atteint exactement la rencontre de ce même écart. -/
theorem break_at_meetingPoint :
    ((C.meetingPred + 1 : ℕ) : ℝ) = meetingPoint C.gap ∧
    remainderIncrement C.meetingPred =
      ((Real.log (fnPrimeAtRank (C.n + 1)) : ℝ) : ℂ) -
        (stepAt backgroundPrimitive (fnPrimeAtRank (C.n + 1)) - stepAt backgroundPrimitive C.meetingPred) :=
  ⟨by rw [C.meetingPred_succ]; rfl, C.break_at_meeting⟩

end OffCarrier

/-! ## F7. Aucun contact n'est un changement de signe de la densité -/

/-- **F7.** Pour tous `k, k'`, le contact `C_k` d'un vrai zéro n'est pas le changement de signe `x_{k'}` de sa densité de
comptage : `arctan(T/β) ∈ (0, π/2)` ne vaut jamais `π/2 + mπ`. -/
theorem contact_ne_densitySignChange (z : TrueZero) (k k' : ℤ) :
    contactMinusAt z k ≠ Real.exp (densitySignChangeLog (rZeroHeight z.1) k') := by
  intro h
  have hT : 0 < rZeroHeight z.1 := z.2
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hlog := congrArg Real.log h
  rw [contactMinusAt_eq_exp, Real.log_exp, Real.log_exp] at hlog
  unfold densitySignChangeLog at hlog
  have heq : Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) =
      Real.pi / 2 + ((k' - k : ℤ) : ℝ) * Real.pi := by
    have := (div_left_inj' hT.ne').mp hlog
    push_cast
    linarith
  have h0 : 0 < Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) :=
    Real.arctan_pos.mpr (div_pos hT hβ)
  have h1 := Real.arctan_lt_pi_div_two (rZeroHeight z.1 / rZeroRadialPosition z.1)
  have hpi := Real.pi_pos
  rcases le_or_gt 0 (k' - k) with hm | hm
  · have : (0 : ℝ) ≤ ((k' - k : ℤ) : ℝ) := by exact_mod_cast hm
    nlinarith
  · have : ((k' - k : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : k' - k ≤ -1)
    nlinarith

/-! ## F8. Aucune famille finie n'accomplit la demande à une rencontre -/

/-- **F8.** À la rencontre de tout écart `⟨n⟩`, aucune famille finie de parts (en particulier les trois premiers zéros)
n'égale le reste lissé sur un voisinage. -/
theorem no_finite_family_at_any_meeting (n : ℕ) (s : Finset ExplicitIndex) :
    ¬ (∀ᶠ x in 𝓝 (meetingPoint ⟨n⟩), smoothedRemainder x = ∑ ρ ∈ s, nontrivialZeroResidueTerm x ρ) :=
  no_finite_family_accomplishes_demand ⟨n⟩ s

/-! ## T1–T4. Contacts et rayons de la fonction de Tour -/

/-- **T1.** `C_{k+1}/C_k = exp(π/T)`. -/
theorem contact_ratio (z : TrueZero) (k : ℤ) :
    contactMinusAt z (k + 1) / contactMinusAt z k = Real.exp (Real.pi / rZeroHeight z.1) := by
  rw [← contactAt_consecutive_logWidth z k, ← Real.log_div (contactPlusAt_positive z k).ne'
    (contactMinusAt_positive z k).ne', Real.exp_log (div_pos (contactPlusAt_positive z k) (contactMinusAt_positive z k))]
  rfl

/-- **T2.** Reconstruction de la fréquence : `T = π / log(C_{k+1}/C_k)`. -/
theorem height_from_contacts (z : TrueZero) (k : ℤ) :
    rZeroHeight z.1 = Real.pi / Real.log (contactMinusAt z (k + 1) / contactMinusAt z k) := by
  rw [contact_ratio, Real.log_exp]
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  field_simp

/-- **T3.** Inversion tangentielle : `β = T / tan(T·log C_k)`, pour tout `k`. -/
theorem radial_from_contact (z : TrueZero) (k : ℤ) :
    rZeroRadialPosition z.1 = rZeroHeight z.1 / Real.tan (rZeroHeight z.1 * Real.log (contactMinusAt z k)) := by
  rw [contactAt_tangent_minus]
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  have hβ : rZeroRadialPosition z.1 ≠ 0 := ne_of_gt (thm_zeroRadialPosition_positive z.1)
  field_simp

/-- **T4.** Rayon de la Tour au contact : `R_k = C_k^β/‖ρ‖`. -/
theorem radius_at_contact (z : TrueZero) (k : ℤ) :
    ‖zeroTerm z (contactMinusAt z k)‖ = contactMinusAt z k ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖ :=
  zeroTerm_norm (contactMinusAt_positive z k)

/-- **T4 bis.** `R_{k+1} = R_k · exp(βπ/T)`. -/
theorem radius_ratio (z : TrueZero) (k : ℤ) :
    ‖zeroTerm z (contactMinusAt z (k + 1))‖ =
      ‖zeroTerm z (contactMinusAt z k)‖ * Real.exp (rZeroRadialPosition z.1 * Real.pi / rZeroHeight z.1) := by
  rw [zeroTerm_norm_transport z (contactMinusAt_positive z k) (contactMinusAt_positive z (k + 1)),
    contact_ratio, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 2
  ring

/-- **T4 ter.** Le rapport des rayons consécutifs dépasse `1` : la Tour descend vers l'origine quand `k` décroît. -/
theorem radius_ratio_gt_one (z : TrueZero) :
    1 < Real.exp (rZeroRadialPosition z.1 * Real.pi / rZeroHeight z.1) :=
  Real.one_lt_exp_iff.mpr (div_pos (mul_pos (thm_zeroRadialPosition_positive z.1) Real.pi_pos) z.2)

/-! ## T5. La construction géométrique `Z_ρ(s)` du texte et sa similitude avec la fonction de Tour -/

/-- La Tour géométrique du texte : `Z_ρ(s) = ρ·exp((β + iT)s/T)`, `s ≤ 0` pour la descente. -/
noncomputable def geometricTower (z : TrueZero) (s : ℝ) : ℂ :=
  zeroPoint z * Complex.exp (zeroPoint z / (rZeroHeight z.1 : ℂ) * (s : ℂ))

/-- **T5.** Départ exact au zéro authentique : `Z_ρ(0) = ρ`. -/
theorem geometricTower_zero (z : TrueZero) : geometricTower z 0 = zeroPoint z := by
  unfold geometricTower; simp

/-- L'exposant de `Z_ρ` : `ρ s/T = (βs/T) + i s`. -/
theorem geometricTower_exponent (z : TrueZero) (s : ℝ) :
    zeroPoint z / (rZeroHeight z.1 : ℂ) * (s : ℂ) =
      ((rZeroRadialPosition z.1 * s / rZeroHeight z.1 : ℝ) : ℂ) + (s : ℂ) * Complex.I := by
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  have hρ : zeroPoint z = (rZeroRadialPosition z.1 : ℂ) + (rZeroHeight z.1 : ℂ) * Complex.I :=
    Complex.ext (by simp [zeroPoint_re]) (by simp [zeroPoint_im])
  have hTc : (rZeroHeight z.1 : ℂ) ≠ 0 := by exact_mod_cast hT
  have hinv : (rZeroHeight z.1 : ℂ) * (rZeroHeight z.1 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hTc
  rw [hρ]
  push_cast
  linear_combination ((s : ℂ) * Complex.I) * hinv

/-- **T5 bis.** Rayon de la Tour géométrique : `‖Z_ρ(s)‖ = ‖ρ‖·exp(βs/T)` (strictement décroissant quand `s` décroît). -/
theorem geometricTower_norm (z : TrueZero) (s : ℝ) :
    ‖geometricTower z s‖ = ‖zeroPoint z‖ * Real.exp (rZeroRadialPosition z.1 * s / rZeroHeight z.1) := by
  unfold geometricTower
  rw [norm_mul, Complex.norm_exp, geometricTower_exponent]
  simp

/-- **T5 ter, la similitude.** Sous le changement de paramètre `s = T·log x − 2φ`, la Tour géométrique est l'image de
la fonction de Tour par l'homothétie réelle de rapport `‖ρ‖²·exp(−2βφ/T)` :
`Z_ρ(T·log x − 2φ) = ‖ρ‖²·exp(−2βφ/T) · 𝒯_ρ(x)`. Les contacts `C_k` (où `T·log C_k = φ + kπ`) correspondent
exactement aux passages `s_k = kπ − φ` de `Z_ρ` sur l'axe réel. -/
theorem geometricTower_similar_zeroTerm (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    geometricTower z (rZeroHeight z.1 * Real.log x - 2 * (towerMotionOf z).phase) =
      ((‖zeroPoint z‖ ^ 2 *
        Real.exp (-2 * rZeroRadialPosition z.1 * (towerMotionOf z).phase / rZeroHeight z.1) : ℝ) : ℂ) *
        zeroTerm z x := by
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  have hTc : (rZeroHeight z.1 : ℂ) ≠ 0 := by exact_mod_cast hT
  have hρ0 : zeroPoint z ≠ 0 := zeroPoint_ne_zero z
  have hρ : zeroPoint z = (rZeroRadialPosition z.1 : ℂ) + (rZeroHeight z.1 : ℂ) * Complex.I :=
    Complex.ext (by simp [zeroPoint_re]) (by simp [zeroPoint_im])
  have hpolar : zeroPoint z =
      (‖zeroPoint z‖ : ℂ) * Complex.exp (((towerMotionOf z).phase : ℂ) * Complex.I) := zeroPoint_polar z
  -- Identité centrale : `ρ²·exp(ρ s/T) = K·exp(ρ·log x)` avec `s = T·log x − 2φ`.
  have key : zeroPoint z ^ 2 *
      Complex.exp (zeroPoint z / (rZeroHeight z.1 : ℂ) *
        ((rZeroHeight z.1 * Real.log x - 2 * (towerMotionOf z).phase : ℝ) : ℂ)) =
      ((‖zeroPoint z‖ ^ 2 *
        Real.exp (-2 * rZeroRadialPosition z.1 * (towerMotionOf z).phase / rZeroHeight z.1) : ℝ) : ℂ) *
        Complex.exp ((Real.log x : ℂ) * zeroPoint z) := by
    rw [geometricTower_exponent]
    conv_lhs => rw [hpolar]
    rw [mul_pow, sq (Complex.exp _), ← Complex.exp_add, mul_assoc, ← Complex.exp_add]
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    have hinv : (rZeroHeight z.1 : ℂ) * (rZeroHeight z.1 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hTc
    rw [hρ]
    linear_combination ((rZeroRadialPosition z.1 : ℂ) * (Real.log x : ℂ)) * hinv
  unfold geometricTower zeroTerm
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
  apply mul_left_cancel₀ hρ0
  rw [← mul_assoc, ← sq, key]
  field_simp

/-! ## E1. Signature de la paire sur trois écarts consécutifs -/

/-- Concaténation des contributions brutes : télescopage de `gapTerm` sur deux écarts adjacents. -/
theorem gapTerm_add (ρ : ℂ) (a b c : ℝ) : gapTerm ρ a b + gapTerm ρ b c = gapTerm ρ a c := by
  unfold gapTerm
  exact intervalIntegral.integral_add_adjacent_intervals
    (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)

namespace OffCarrier

variable (C : OffCarrier)

/-- **E1.** La signature hyperbolique de la paire (zéro OFF, miroir, moins deux fois le point de ligne) sur trois
écarts consécutifs `[p_n, p_{n+1}]`, `[p_{n+1}, p_{n+2}]`, `[p_{n+2}, p_{n+3}]` télescope en une seule intégrale sur
`[log p_n, log p_{n+3}]`. Identité pour toute position radiale ; rien n'est conclu sur `β`. -/
theorem pair_signature_three_gaps (n : ℕ) :
    (∑ j ∈ Finset.range 3,
      (gapTerm (zeroPoint C.zero) (Real.log (fnPrimeAtRank (n + j))) (Real.log (fnPrimeAtRank (n + j + 1))) +
        gapTerm (zeroPoint (mirrorMember C.zero)) (Real.log (fnPrimeAtRank (n + j)))
          (Real.log (fnPrimeAtRank (n + j + 1))) -
        2 * gapTerm C.linePoint (Real.log (fnPrimeAtRank (n + j))) (Real.log (fnPrimeAtRank (n + j + 1))))) =
      ∫ t in Real.log (fnPrimeAtRank n)..Real.log (fnPrimeAtRank (n + 3)),
        2 * (Complex.cosh ((C.radialShift : ℂ) * t) - 1) * Complex.exp (C.linePoint * t) := by
  rw [← gapTerm_mirror_pair C.linePoint C.radialShift, ← C.zeroPoint_eq_line_sub_shift,
    ← C.mirrorPoint_eq_line_add_shift]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h : ∀ σ : ℂ,
      gapTerm σ (Real.log (fnPrimeAtRank n)) (Real.log (fnPrimeAtRank (n + 1))) +
        gapTerm σ (Real.log (fnPrimeAtRank (n + 1))) (Real.log (fnPrimeAtRank (n + 2))) +
        gapTerm σ (Real.log (fnPrimeAtRank (n + 2))) (Real.log (fnPrimeAtRank (n + 3))) =
      gapTerm σ (Real.log (fnPrimeAtRank n)) (Real.log (fnPrimeAtRank (n + 3))) := by
    intro σ; rw [gapTerm_add, gapTerm_add]
  have h1 := h (zeroPoint C.zero)
  have h2 := h (zeroPoint (mirrorMember C.zero))
  have h3 := h C.linePoint
  simp only [show n + 0 = n from rfl, show n + 0 + 1 = n + 1 from rfl, show n + 1 + 1 = n + 2 from rfl,
    show n + 2 + 1 = n + 3 from rfl] at *
  linear_combination h1 + h2 - 2 * h3

end OffCarrier

end RHV6Fresh
