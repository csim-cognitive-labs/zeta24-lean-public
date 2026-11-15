/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ExactSignalArchitecture
import RHV6Fresh.Terminal.RayCapture
import RHV6Fresh.Terminal.JointParameterReading

/-!
# Signaux de Tour stables : mode normalisé, Tour de contacts, conversions (reconstruction E345/E346, 2026-10-20)

Trois objets distincts par zéro `ρ = β + iT`, `u = log x` :

* `ExactZeroSignal` (déjà compilé) : `E_ρ(u) = e^{ρu}/ρ` = terme `x^ρ/ρ` ; enveloppe `e^{βu}/‖ρ‖` VARIABLE ;
* `NormalizedZeroMode` (ce module) : `Q_ρ(u) = e^{i(Tu − θ)}`, `θ = arctan(T/β)` ; module `1`, phase de dérivée `T` ;
* `ContactTower` (ce module) : les contacts `C_k = exp((θ + kπ)/T)` et leur pas logarithmique `π/T`.

Conversions démontrées : `E_ρ(u) = (e^{βu}/‖ρ‖)·Q_ρ(u)` (`exact_eq_envelope_mul_normalized`) ; les contacts sont les
abscisses où `Q_ρ` est réel (`normalizedMode_im_at_contact`) ; `Q_ρ(u + π/T) = −Q_ρ(u)` (`normalizedMode_half_turn`) ;
un déplacement radial ne change `Q_ρ` que par une phase constante (`normalizedMode_radial_shift_is_constant_phase`) ;
deux membres miroirs ont le même mode à une phase constante près (`mirror_modes_same_frequency`).

Portée : identités vraies pour toute position radiale `β > 0` ; aucune ne fixe `β`. La contribution exacte au comptage
`−2 Re Ei(ρ log x)` n'a pas d'objet dans Mathlib (`Ei` absent) : aucun théorème sur elle n'est transféré ici ; sa densité
`−2 Re(e^{ρu})/u` est `counting_modulation_eq_raw_derivative` (BackgroundModulation), dont la phase est NULLE (cos(Tu)), distincte
de la phase `−θ` du mode : `density_phase_ne_mode_phase`.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **Mode normalisé** `Q_ρ(u) = exp(i(T u − arctan(T/β)))` : module `1`, fréquence angulaire `T`, phase constante. -/
structure NormalizedZeroMode where
  β : ℝ
  T : ℝ

/-- Phase constante du mode : `θ = arctan(T/β)` (phase de `ρ` pour `β > 0`). -/
noncomputable def NormalizedZeroMode.θ (m : NormalizedZeroMode) : ℝ := Real.arctan (m.T / m.β)

/-- Phase instantanée `T u − θ`. -/
noncomputable def NormalizedZeroMode.phase (m : NormalizedZeroMode) (u : ℝ) : ℝ := m.T * u - m.θ

noncomputable def NormalizedZeroMode.eval (m : NormalizedZeroMode) (u : ℝ) : ℂ :=
  Complex.exp ((m.phase u : ℂ) * Complex.I)

def ExactZeroSignal.toNormalized (s : ExactZeroSignal) : NormalizedZeroMode := ⟨s.β, s.T⟩

noncomputable def normalizedModeOf (z : TrueZero) : NormalizedZeroMode :=
  ⟨rZeroRadialPosition z.1, rZeroHeight z.1⟩

/-- **Tour de contacts** : les abscisses `C_k` d'un vrai zéro et leur pas logarithmique. -/
structure ContactTower where
  z : TrueZero

noncomputable def ContactTower.contact (c : ContactTower) (k : ℤ) : ℝ := contactMinusAt c.z k

noncomputable def ContactTower.pitch (c : ContactTower) : ℝ := Real.pi / rZeroHeight c.z.1

/-! ## 1. Invariants du mode normalisé -/

/-- `|Q_ρ(u)| = 1` pour tout `u`, toute position radiale. -/
theorem normalizedMode_norm (m : NormalizedZeroMode) (u : ℝ) : ‖m.eval u‖ = 1 := by
  unfold NormalizedZeroMode.eval; exact Complex.norm_exp_ofReal_mul_I _

/-- La phase a pour dérivée la fréquence `T`, constante. -/
theorem normalizedMode_phase_hasDerivAt (m : NormalizedZeroMode) (u : ℝ) :
    HasDerivAt m.phase m.T u := by
  unfold NormalizedZeroMode.phase
  simpa using ((hasDerivAt_id u).const_mul m.T).sub_const m.θ

/-- Demi-tour : `Q_ρ(u + π/T) = −Q_ρ(u)` (`T ≠ 0`). -/
theorem normalizedMode_half_turn (m : NormalizedZeroMode) (hT : m.T ≠ 0) (u : ℝ) :
    m.eval (u + Real.pi / m.T) = -m.eval u := by
  unfold NormalizedZeroMode.eval NormalizedZeroMode.phase
  have h : ((m.T * (u + Real.pi / m.T) - m.θ : ℝ) : ℂ) * Complex.I =
      ((m.T * u - m.θ : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
    push_cast
    have : (m.T : ℂ) ≠ 0 := by exact_mod_cast hT
    field_simp
    ring
  rw [h, Complex.exp_add, Complex.exp_pi_mul_I]; ring

/-- Parties réelle et imaginaire : `cos`, `sin` de la phase. -/
theorem normalizedMode_re (m : NormalizedZeroMode) (u : ℝ) : (m.eval u).re = Real.cos (m.phase u) := by
  unfold NormalizedZeroMode.eval; exact Complex.exp_ofReal_mul_I_re _

theorem normalizedMode_im (m : NormalizedZeroMode) (u : ℝ) : (m.eval u).im = Real.sin (m.phase u) := by
  unfold NormalizedZeroMode.eval; exact Complex.exp_ofReal_mul_I_im _

/-! ## 2. Conversion signal exact ↔ mode normalisé -/

/-- **Conversion** : `E_ρ(u) = (e^{βu}/‖ρ‖) · Q_ρ(u)` pour `β > 0`. L'enveloppe porte toute la variation de module. -/
theorem exact_eq_envelope_mul_normalized (s : ExactZeroSignal) (hβ : 0 < s.β) (u : ℝ) :
    s.eval u = ((Real.exp (s.β * u) / Real.sqrt (s.β ^ 2 + s.T ^ 2) : ℝ) : ℂ) * s.toNormalized.eval u := by
  rw [exactSignal_polar s hβ]; rfl

/-- Le mode normalisé d'un signal exact a module `1` : le module du signal exact est son enveloppe seule. -/
theorem exact_norm_eq_envelope (s : ExactZeroSignal) (hβ : 0 < s.β) (u : ℝ) :
    ‖s.eval u‖ = Real.exp (s.β * u) / Real.sqrt (s.β ^ 2 + s.T ^ 2) := exactSignal_norm s hβ u

/-- Le terme `x^ρ/ρ` d'un vrai zéro est enveloppe × mode normalisé en `u = log x`. -/
theorem zeroTerm_eq_envelope_mul_normalized (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    zeroTerm z x = ((Real.exp (rZeroRadialPosition z.1 * Real.log x) /
        Real.sqrt (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) : ℝ) : ℂ) *
      (normalizedModeOf z).eval (Real.log x) := by
  rw [zeroTerm_eq_exactSignal z hx, exact_eq_envelope_mul_normalized _ (thm_zeroRadialPosition_positive z.1)]
  rfl

/-! ## 3. Contacts : abscisses où le mode est réel, pas `π/T` -/

/-- La phase du mode d'un vrai zéro au contact `C_k` vaut `kπ`. -/
theorem normalizedMode_phase_at_contact (z : TrueZero) (k : ℤ) :
    (normalizedModeOf z).phase (Real.log (contactMinusAt z k)) = k * Real.pi := by
  unfold NormalizedZeroMode.phase NormalizedZeroMode.θ normalizedModeOf
  rw [contactMinusAt_eq_exp z k, Real.log_exp]
  have hT : rZeroHeight z.1 ≠ 0 := z.2.ne'
  field_simp
  ring

/-- **Les contacts sont les abscisses où le mode normalisé est réel** : `Im Q(log C_k) = 0`. -/
theorem normalizedMode_im_at_contact (z : TrueZero) (k : ℤ) :
    ((normalizedModeOf z).eval (Real.log (contactMinusAt z k))).im = 0 := by
  rw [normalizedMode_im, normalizedMode_phase_at_contact]
  exact Real.sin_int_mul_pi k

/-- Au contact `C_k`, le mode vaut `(−1)^k`. -/
theorem normalizedMode_re_at_contact (z : TrueZero) (k : ℤ) :
    ((normalizedModeOf z).eval (Real.log (contactMinusAt z k))).re = (-1 : ℝ) ^ k := by
  rw [normalizedMode_re, normalizedMode_phase_at_contact]
  exact Real.cos_int_mul_pi k

/-- Pas logarithmique de la Tour de contacts : `log C_{k+1} − log C_k = π/T` (réutilisation). -/
theorem contactTower_pitch (c : ContactTower) (k : ℤ) :
    Real.log (c.contact (k + 1)) - Real.log (c.contact k) = c.pitch :=
  contact_log_step c.z k

/-- Le pas des contacts est le demi-tour du mode normalisé : avancer de `pitch` change le signe de `Q`. -/
theorem contactTower_pitch_is_half_turn (c : ContactTower) (u : ℝ) :
    (normalizedModeOf c.z).eval (u + c.pitch) = -(normalizedModeOf c.z).eval u :=
  normalizedMode_half_turn _ c.z.2.ne' u

/-! ## 4. Déplacement radial : phase constante seulement -/

/-- **Un déplacement radial ne change le mode normalisé que par une phase constante** `e^{i(θ' − θ)}` :
fréquence et module sont invariants. -/
theorem normalizedMode_radial_shift_is_constant_phase (β β' T : ℝ) (u : ℝ) :
    (⟨β, T⟩ : NormalizedZeroMode).eval u =
      Complex.exp (((Real.arctan (T / β') - Real.arctan (T / β) : ℝ) : ℂ) * Complex.I) *
        (⟨β', T⟩ : NormalizedZeroMode).eval u := by
  unfold NormalizedZeroMode.eval NormalizedZeroMode.phase NormalizedZeroMode.θ
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- Deux membres miroirs `β + iT`, `(1 − β) + iT` ont le même mode normalisé à une phase constante près
(même fréquence intrinsèque). -/
theorem mirror_modes_same_frequency (β T : ℝ) (u : ℝ) :
    (⟨β, T⟩ : NormalizedZeroMode).eval u =
      Complex.exp (((Real.arctan (T / (1 - β)) - Real.arctan (T / β) : ℝ) : ℂ) * Complex.I) *
        (⟨1 - β, T⟩ : NormalizedZeroMode).eval u :=
  normalizedMode_radial_shift_is_constant_phase β (1 - β) T u

/-! ## 5. Densité de comptage et mode : deux phases distinctes -/

/-- La densité de comptage `−2 Re(e^{ρu})/u` a la phase `cos(T u)` (nulle), distincte de la phase `T u − θ` du mode :
`Re(e^{ρu}) = e^{βu} cos(T u)`. -/
theorem density_phase_ne_mode_phase (β T u : ℝ) :
    (Complex.exp ((zeroCoeff β T) * u)).re = Real.exp (β * u) * Real.cos (T * u) := by
  have h : (zeroCoeff β T) * u = ((β * u : ℝ) : ℂ) + ((T * u : ℝ) : ℂ) * Complex.I := by
    unfold zeroCoeff; push_cast; ring
  rw [h, Complex.exp_add, ← Complex.ofReal_exp, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

#print axioms exact_eq_envelope_mul_normalized
#print axioms normalizedMode_im_at_contact
#print axioms normalizedMode_radial_shift_is_constant_phase

end RHV6Fresh
