/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RaccordTransportObligation

/-!
# Rigidité arithmétique de la phase aux cassures (E431, §19.46)

Module isolé (non ajouté à `RHV6Fresh.lean`). Suite de `RaccordTransportObligation` (E430, §19.45) : la plus faible
hypothèse compilée qui survivait, `PairDepositOnLine` (la paire dépose à la cassure comme la paire en ligne), équivaut à
« le premier partagé tombe sur un changement de signe de la densité de ligne ». Ici elle est portée sur la SÉRIE des
premiers.

* §1 La fraction de cellule d'une Tour `(β, T)` en un changement de signe de la densité lit la position radiale :
  `arctan(β/T)/π` ; sous `PairDepositOnLine`, fractions de la Tour et du miroir au premier partagé.
* §2 Rigidité arithmétique (factorisation unique) : deux premiers distincts ne tombent jamais tous deux sur un
  changement de signe d'une même fréquence ; trois premiers ne partagent jamais la même fraction de cellule d'une Tour
  (une Tour ne touche au plus que deux premiers).
* §3 L'hypothèse « dépôt en ligne » en tout rang `m` (`PairDepositOnLineAt`), le surplus de la paire (`pairSurplus`),
  et : pour tout porteur, l'hypothèse est vraie en AU PLUS UN rang ; sur deux rangs distincts, un surplus au moins est
  non nul.

Aucune hypothèse posée, aucun `sorry`. Rien ici ne contredit l'existence d'un porteur : le complément absorbe le
surplus (identité de cassure pour tout paquet) et aucun pont compilé ne relie la densité réelle (dérivée de la
contribution de comptage) au pas du canal lissé des paquets (sonde S2 de E431).
-/

open Real RHV3Lean

namespace RHV6Fresh

/-! ## §1 Phase d'un changement de signe lue dans la cellule d'une Tour -/

theorem arctan_div_compl {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) :
    Real.arctan (T / β) = Real.pi / 2 - Real.arctan (β / T) := by
  rw [← Real.arctan_inv_of_pos (div_pos hβ hT), inv_div]

/-- Position d'étage d'un changement de signe de la densité de fréquence `T` dans la Tour `(β, T)` :
`k + arctan(β/T)/π`. -/
theorem stagePosition_at_signChange {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (k : ℤ) :
    stagePosition β T (Real.exp (densitySignChangeLog T k)) = k + Real.arctan (β / T) / Real.pi := by
  unfold stagePosition densitySignChangeLog
  rw [Real.log_exp, arctan_div_compl hβ hT]
  field_simp
  ring

theorem arctan_div_pi_mem {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) :
    0 ≤ Real.arctan (β / T) / Real.pi ∧ Real.arctan (β / T) / Real.pi < 1 := by
  have hπ := Real.pi_pos
  have h0 : 0 < Real.arctan (β / T) := Real.arctan_pos.mpr (div_pos hβ hT)
  have h1 : Real.arctan (β / T) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  exact ⟨div_nonneg h0.le hπ.le, by rw [div_lt_one hπ]; linarith⟩

/-- **La fraction de cellule en un changement de signe lit `β`** : `arctan(β/T)/π`, indépendante de `k`. -/
theorem cellFraction_at_signChange {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (k : ℤ) :
    cellFraction β T (Real.exp (densitySignChangeLog T k)) = Real.arctan (β / T) / Real.pi := by
  unfold cellFraction
  rw [stagePosition_at_signChange hβ hT k, Int.fract_intCast_add]
  exact Int.fract_eq_self.mpr (arctan_div_pi_mem hβ hT)

/-! ## §2 Rigidité arithmétique (factorisation unique) -/

/-- **Deux premiers distincts ne tombent jamais tous deux sur un changement de signe de la densité d'une même
fréquence** : `T log p = π(2k+1)/2` et `T log q = π(2j+1)/2` donneraient `p^(2j+1) = q^(2k+1)`. -/
theorem signChange_two_primes_false {T : ℝ} (hT : 0 < T) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {k j : ℤ} (hk : Real.log p = densitySignChangeLog T k)
    (hj : Real.log q = densitySignChangeLog T j) : False := by
  have hπ := Real.pi_pos
  have hlp : 0 < Real.log p := hp.log_pos
  have hlq : 0 < Real.log q := hq.log_pos
  unfold densitySignChangeLog at hk hj
  have hk' : T * Real.log p = Real.pi / 2 + k * Real.pi := by rw [hk]; field_simp
  have hj' : T * Real.log q = Real.pi / 2 + j * Real.pi := by rw [hj]; field_simp
  have hk0 : 0 ≤ k := by
    by_contra hneg
    have : k ≤ -1 := by omega
    have : (k : ℝ) ≤ -1 := by exact_mod_cast this
    nlinarith [mul_pos hT hlp]
  have hj0 : 0 ≤ j := by
    by_contra hneg
    have : j ≤ -1 := by omega
    have : (j : ℝ) ≤ -1 := by exact_mod_cast this
    nlinarith [mul_pos hT hlq]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (k : ℝ) = a := ⟨k.toNat, by exact_mod_cast (Int.toNat_of_nonneg hk0).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (j : ℝ) = b := ⟨j.toNat, by exact_mod_cast (Int.toNat_of_nonneg hj0).symm⟩
  rw [ha] at hk'; rw [hb] at hj'
  have e : T * ((2 * b + 1 : ℕ) * Real.log p) = T * ((2 * a + 1 : ℕ) * Real.log q) := by
    push_cast
    linear_combination (2 * (b : ℝ) + 1) * hk' - (2 * (a : ℝ) + 1) * hj'
  have e2 : Real.log ((p : ℝ) ^ (2 * b + 1)) = Real.log ((q : ℝ) ^ (2 * a + 1)) := by
    rw [Real.log_pow, Real.log_pow]
    exact mul_left_cancel₀ hT.ne' e
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have e3 : (p : ℝ) ^ (2 * b + 1) = (q : ℝ) ^ (2 * a + 1) :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (pow_pos hp0 _)) (Set.mem_Ioi.mpr (pow_pos hq0 _)) e2
  have e4 : p ^ (2 * b + 1) = q ^ (2 * a + 1) := by exact_mod_cast e3
  have hdvd : p ∣ q ^ (2 * a + 1) := e4 ▸ dvd_pow_self p (by omega)
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))

/-- **Une Tour ne touche au plus que deux premiers** : trois premiers ordonnés ne partagent jamais la même fraction
de cellule dans une Tour `(β, T)` (toute phase commune, contacts compris : `q^n p^m = r^m p^n`). -/
theorem same_cellFraction_three_primes_false {β T : ℝ} (hT : 0 < T) {p q r : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpq : p < q) (hqr : q < r)
    (h1 : cellFraction β T q = cellFraction β T p) (h2 : cellFraction β T r = cellFraction β T p) : False := by
  have hπ := Real.pi_pos
  unfold cellFraction at h1 h2
  obtain ⟨m, hm⟩ := Int.fract_eq_fract.mp h1
  obtain ⟨n, hn⟩ := Int.fract_eq_fract.mp h2
  unfold stagePosition at hm hn
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hpq' : Real.log p < Real.log q := Real.log_lt_log hp0 (by exact_mod_cast hpq)
  have hpr' : Real.log p < Real.log r := Real.log_lt_log hp0 (by exact_mod_cast (hpq.trans hqr))
  have hm' : T * (Real.log q - Real.log p) = m * Real.pi := by
    field_simp at hm; linarith
  have hn' : T * (Real.log r - Real.log p) = n * Real.pi := by
    field_simp at hn; linarith
  have hm0 : 0 < m := by
    by_contra hneg
    have : m ≤ 0 := by omega
    have : (m : ℝ) ≤ 0 := by exact_mod_cast this
    nlinarith [mul_pos hT (sub_pos.mpr hpq')]
  have hn0 : 0 < n := by
    by_contra hneg
    have : n ≤ 0 := by omega
    have : (n : ℝ) ≤ 0 := by exact_mod_cast this
    nlinarith [mul_pos hT (sub_pos.mpr hpr')]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (m : ℝ) = a := ⟨m.toNat, by exact_mod_cast (Int.toNat_of_nonneg hm0.le).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (n : ℝ) = b := ⟨n.toNat, by exact_mod_cast (Int.toNat_of_nonneg hn0.le).symm⟩
  rw [ha] at hm'; rw [hb] at hn'
  have e : T * (((b : ℕ) : ℝ) * Real.log q + ((a : ℕ) : ℝ) * Real.log p) =
      T * (((a : ℕ) : ℝ) * Real.log r + ((b : ℕ) : ℝ) * Real.log p) := by
    linear_combination (b : ℝ) * hm' - (a : ℝ) * hn'
  have e2 : Real.log ((q : ℝ) ^ b * (p : ℝ) ^ a) = Real.log ((r : ℝ) ^ a * (p : ℝ) ^ b) := by
    rw [Real.log_mul (pow_pos hq0 _).ne' (pow_pos hp0 _).ne',
      Real.log_mul (pow_pos hr0 _).ne' (pow_pos hp0 _).ne', Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow]
    exact mul_left_cancel₀ hT.ne' e
  have e3 : (q : ℝ) ^ b * (p : ℝ) ^ a = (r : ℝ) ^ a * (p : ℝ) ^ b :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) e2
  have e4 : q ^ b * p ^ a = r ^ a * p ^ b := by exact_mod_cast e3
  have hb0 : 0 < b := by
    have : (0 : ℝ) < b := by rw [← hb]; exact_mod_cast hn0
    exact_mod_cast this
  have hdvd : q ∣ r ^ a * p ^ b := e4 ▸ dvd_mul_of_dvd_left (dvd_pow_self q hb0.ne') _
  rcases (hq.dvd_mul).mp hdvd with h | h
  · exact (ne_of_lt hqr) ((Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow h))
  · exact (ne_of_lt hpq).symm ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h))

/-! ## §3 Le dépôt en ligne sur la série des premiers, pour tout porteur -/

namespace OffCarrier
variable (C : OffCarrier)

/-- Logarithme du premier de rang `m`. -/
noncomputable def primeLog (m : ℕ) : ℝ := Real.log (fnPrimeAtRank m)

theorem primeLog_pos (m : ℕ) : 0 < primeLog m := (thm_primeAtRank_isPrime m).log_pos

theorem breakLog_eq_primeLog : C.breakLog = primeLog (C.n + 1) := rfl

/-- **Hypothèse nommée, jamais posée**, au premier de rang `m` : la densité réelle de la paire y est celle de la
paire en ligne. -/
def PairDepositOnLineAt (m : ℕ) : Prop :=
  realCountingDensity (zeroPoint C.zero) (primeLog m) +
      realCountingDensity (zeroPoint (mirrorMember C.zero)) (primeLog m) =
    2 * realCountingDensity C.linePoint (primeLog m)

theorem pairDepositOnLine_iff_at : C.PairDepositOnLine ↔ C.PairDepositOnLineAt (C.n + 1) := Iff.rfl

/-- Surplus de la paire au premier de rang `m` : densité de la paire moins densité de la paire en ligne. -/
noncomputable def pairSurplus (m : ℕ) : ℝ :=
  realCountingDensity (zeroPoint C.zero) (primeLog m) +
      realCountingDensity (zeroPoint (mirrorMember C.zero)) (primeLog m) -
    2 * realCountingDensity C.linePoint (primeLog m)

/-- Le surplus est `2(cosh(δ log p_m) − 1)` fois la densité de ligne. -/
theorem pairSurplus_eq (m : ℕ) :
    C.pairSurplus m =
      2 * (Real.cosh (C.radialShift * primeLog m) - 1) * realCountingDensity C.linePoint (primeLog m) := by
  unfold pairSurplus
  rw [C.pair_real_density_eq_cosh_line]
  ring

theorem pairSurplus_eq_zero_iff (m : ℕ) : C.pairSurplus m = 0 ↔ C.PairDepositOnLineAt m := by
  unfold pairSurplus PairDepositOnLineAt
  exact sub_eq_zero

/-- Au rang `m`, le dépôt en ligne équivaut à « `log p_m` est un changement de signe de la densité de fréquence `T` ». -/
theorem pairDepositOnLineAt_iff_sign_change (m : ℕ) :
    C.PairDepositOnLineAt m ↔ ∃ k : ℤ, primeLog m = densitySignChangeLog (rZeroHeight C.zero.1) k := by
  have hT : C.linePoint.im ≠ 0 := by rw [C.linePoint_im]; exact C.zero.2.ne'
  have hcosh : 1 < Real.cosh (C.radialShift * primeLog m) :=
    Real.one_lt_cosh.mpr (mul_pos C.radialShift_pos (primeLog_pos m)).ne'
  rw [← C.pairSurplus_eq_zero_iff, C.pairSurplus_eq, ← C.linePoint_im,
    ← realCountingDensity_eq_zero_iff C.linePoint hT (primeLog_pos m)]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h0
    · exfalso
      rcases mul_eq_zero.mp h0 with h1 | h1
      · norm_num at h1
      · linarith
    · exact h0
  · intro h; rw [h]; ring

/-- **Sur toute la série des premiers, la paire ne dépose comme la ligne qu'en au plus un rang.** -/
theorem pairDepositOnLineAt_unique {m m' : ℕ} (h : C.PairDepositOnLineAt m) (h' : C.PairDepositOnLineAt m') :
    m = m' := by
  by_contra hne
  obtain ⟨k, hk⟩ := (C.pairDepositOnLineAt_iff_sign_change m).mp h
  obtain ⟨j, hj⟩ := (C.pairDepositOnLineAt_iff_sign_change m').mp h'
  exact signChange_two_primes_false C.zero.2 (thm_primeAtRank_isPrime m) (thm_primeAtRank_isPrime m')
    (fun e => hne (thm_primeAtRank_injective e)) hk hj

/-- Sur deux rangs distincts, l'un au moins des surplus de la paire est non nul. -/
theorem pairSurplus_ne_zero_of_ne {m m' : ℕ} (hne : m ≠ m') :
    C.pairSurplus m ≠ 0 ∨ C.pairSurplus m' ≠ 0 := by
  by_contra h
  obtain ⟨h1, h2⟩ := not_or.mp h
  exact hne (C.pairDepositOnLineAt_unique ((C.pairSurplus_eq_zero_iff m).mp (not_not.mp h1))
    ((C.pairSurplus_eq_zero_iff m').mp (not_not.mp h2)))

/-- Sous `PairDepositOnLine`, les fractions de cellule de la Tour et du miroir au premier partagé lisent leurs
positions radiales : `arctan(β/T)/π` et `arctan((1−β)/T)/π`. -/
theorem pairDepositOnLine_cellFraction (h : C.PairDepositOnLine) :
    cellFraction (rZeroRadialPosition C.zero.1) (rZeroHeight C.zero.1) (fnPrimeAtRank (C.n + 1)) =
      Real.arctan (rZeroRadialPosition C.zero.1 / rZeroHeight C.zero.1) / Real.pi ∧
    cellFraction (rZeroRadialPosition (mirrorMember C.zero).1) (rZeroHeight C.zero.1) (fnPrimeAtRank (C.n + 1)) =
      Real.arctan (rZeroRadialPosition (mirrorMember C.zero).1 / rZeroHeight C.zero.1) / Real.pi := by
  obtain ⟨k, hk⟩ := C.pairDepositOnLine_forces_sign_change h
  have hp : (0 : ℝ) < fnPrimeAtRank (C.n + 1) := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  have hβ := thm_zeroRadialPosition_positive C.zero.1
  have hβ' := thm_zeroRadialPosition_positive (mirrorMember C.zero).1
  have e : (fnPrimeAtRank (C.n + 1) : ℝ) = Real.exp (densitySignChangeLog (rZeroHeight C.zero.1) k) := by
    rw [← hk]; unfold OffCarrier.breakLog; rw [Real.exp_log hp]
  rw [e]
  exact ⟨cellFraction_at_signChange hβ C.zero.2 k, cellFraction_at_signChange hβ' C.zero.2 k⟩

end OffCarrier

end RHV6Fresh

#print axioms RHV6Fresh.cellFraction_at_signChange
#print axioms RHV6Fresh.signChange_two_primes_false
#print axioms RHV6Fresh.same_cellFraction_three_primes_false
#print axioms RHV6Fresh.OffCarrier.pairDepositOnLineAt_iff_sign_change
#print axioms RHV6Fresh.OffCarrier.pairDepositOnLineAt_unique
#print axioms RHV6Fresh.OffCarrier.pairSurplus_ne_zero_of_ne
#print axioms RHV6Fresh.OffCarrier.pairDepositOnLine_cellFraction
