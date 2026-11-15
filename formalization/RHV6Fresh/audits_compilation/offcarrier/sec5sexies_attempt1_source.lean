/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-! ## 5sexies. La cassure : où se trouve la demande de l'écart, et ce que la paire peut y faire (§19.13, 2026-10-30)

Demande de l'auteur : tirer parti du fait que **la demande de l'écart se trouve presque entièrement dans la cassure**
(le saut exact de l'escalier des premiers au bout de l'écart), et établir rigoureusement, sur les seuls éléments
collectés, ce que l'amplitude cumulée du zéro OFF et de son miroir peut ou ne peut pas réaliser à cette cassure.

Compilé ici, exact, local, sans moyenne :
* **C1. Localisation arithmétique de la cassure.** Au pas qui atteint `p_{n+1}`, l'incrément du reste exact est
  `log p_{n+1}` moins la variation du fond (`break_at_meeting`) ; à tout pas dont l'arrivée n'est pas une puissance de
  premier, l'incrément est la seule variation du fond (`no_break_off_prime_powers`) ; la demande de l'écart entier est
  la somme des pas intermédiaires plus la cassure terminale (`gap_demand_eq_break_add_rest`). Consigné : les puissances
  de premiers intérieures à l'écart portent elles aussi une cassure (`Λ ≠ 0`) ; « entre deux premiers l'escalier
  n'avance pas » vaut hors de ces points.
* **C2. Le calage de la paire est celui de la ligne.** Point par point, la densité de la paire est `2cosh(dt)` fois la
  densité de ligne de même fréquence (`pair_density_eq_cosh_line`, forme réelle `pair_real_density_eq_cosh_line`) ; la
  paire s'annule exactement où s'annule la ligne, aux points `(π/2 + kπ)/T` qui ne dépendent que de la fréquence
  (`pair_density_zero_iff`). **La paire n'est ni en avance ni en retard sur la ligne : « à temps » n'est pas un levier ;
  seule l'amplitude, `cosh(dt) > 1` strictement croissante le long du logarithme, la distingue.**
* **C3. Le pas de la paire avant la cassure est borné** par une enveloppe explicite (`pair_step_norm_le`), et cette
  enveloppe **dépasse strictement** celle de la paire de ligne (`pair_step_bound_gt_line_bound`) : l'amplitude cumulée
  rapproche la paire OFF de la cassure, elle ne l'en éloigne pas.
* **C4. La cassure est réalisée par la totalité.** Au pas de la cassure, ce que le paquet de la fréquence `T` ne
  fournit pas est fourni exactement par les autres fréquences (`break_compensated_by_other_frequencies`) — pour la paire
  OFF comme pour toute famille : aucun signal isolé, ON ou OFF, ne réalise une cassure.

Conclusion consignée (§19.13) : « le zéro OFF ne peut pas réaliser la cassure à temps du fait de son amplitude cumulée
avec son miroir » n'est pas dérivable des éléments collectés ; ils établissent le contraire sur le calage (identique à la
ligne) et sur l'amplitude (strictement supérieure). Ce qui distingue la paire OFF est son amplitude relative non bornée
aux rencontres (`pairRelativeAmplitude_unbounded`), et sa confrontation à la demande exige un fait sur le niveau de la
demande ou sur les autres fréquences qui n'est pas dans le corpus. -/

/-! ### C1. Localisation arithmétique de la cassure -/

/-- L'entier qui précède l'événement `p_{n+1}` : le pas `meetingPred → meetingPred + 1` est la cassure. -/
def meetingPred : ℕ := fnPrimeAtRank (C.n + 1) - 1

theorem meetingPred_succ : C.meetingPred + 1 = fnPrimeAtRank (C.n + 1) := by
  unfold meetingPred
  have := (thm_primeAtRank_isPrime (C.n + 1)).two_le
  omega

theorem two_le_meetingPred : 2 ≤ C.meetingPred := by
  have h0 : fnPrimeAtRank 0 < fnPrimeAtRank (C.n + 1) := thm_primeAtRank_strictMono (by omega)
  rw [thm_primeAtRank_zero_eq_two] at h0
  unfold meetingPred
  omega

/-- **La cassure au point de rencontre** : l'incrément du reste exact au pas qui atteint `p_{n+1}` est `log p_{n+1}`
moins la variation du fond. -/
theorem break_at_meeting :
    remainderIncrement C.meetingPred =
      ((Real.log (fnPrimeAtRank (C.n + 1)) : ℝ) : ℂ) -
        (stepAt backgroundPrimitive (fnPrimeAtRank (C.n + 1)) - stepAt backgroundPrimitive C.meetingPred) := by
  rw [remainderIncrement_arithmetic, C.meetingPred_succ,
    ArithmeticFunction.vonMangoldt_apply_prime (thm_primeAtRank_isPrime (C.n + 1))]

/-- **Hors des puissances de premiers, aucune cassure** : l'incrément du reste exact est la seule variation du fond. -/
theorem no_break_off_prime_powers (N : ℕ) (hN : ¬ IsPrimePow (N + 1)) :
    remainderIncrement N = -(stepAt backgroundPrimitive (N + 1) - stepAt backgroundPrimitive N) := by
  rw [remainderIncrement_arithmetic, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hN]
  simp

/-- Télescopage des pas du reste exact. -/
theorem gap_demand_sum_increments (a m : ℕ) :
    ∑ k ∈ Finset.range m, remainderIncrement (a + k) = exactRemainder (a + m) - exactRemainder a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    unfold remainderIncrement
    rw [← add_assoc]
    ring

/-- **La demande de l'écart est ses pas intermédiaires plus la cassure terminale** : l'incrément du reste exact sur
`[p_n, p_{n+1}]` est la somme des pas de `p_n` à `p_{n+1} − 1`, puis la cassure `log p_{n+1}` moins le fond. -/
theorem gap_demand_eq_break_add_rest :
    exactRemainder (fnPrimeAtRank (C.n + 1)) - exactRemainder (fnPrimeAtRank C.n) =
      (∑ k ∈ Finset.range (C.meetingPred - fnPrimeAtRank C.n),
        remainderIncrement (fnPrimeAtRank C.n + k)) +
        (((Real.log (fnPrimeAtRank (C.n + 1)) : ℝ) : ℂ) -
          (stepAt backgroundPrimitive (fnPrimeAtRank (C.n + 1)) -
            stepAt backgroundPrimitive C.meetingPred)) := by
  have hlt := thm_primeAtRank_strictMono (Nat.lt_succ_self C.n)
  have hsucc := C.meetingPred_succ
  have hw : fnPrimeAtRank C.n + (C.meetingPred - fnPrimeAtRank C.n) = C.meetingPred := by omega
  have hsum := gap_demand_sum_increments (fnPrimeAtRank C.n) (C.meetingPred - fnPrimeAtRank C.n + 1)
  rw [Finset.sum_range_succ, hw, ← add_assoc, hw, hsucc, C.break_at_meeting] at hsum
  exact hsum.symm

/-! ### C2. Le calage de la paire est celui de la ligne -/

/-- **Densité de la paire = `2cosh(dt)` × densité de ligne** (canal de comptage), point par point. -/
theorem pair_density_eq_cosh_line (t : ℝ) :
    countingDensity (zeroPoint C.zero) t + countingDensity (zeroPoint (mirrorMember C.zero)) t =
      2 * Complex.cosh ((C.radialShift : ℂ) * t) * countingDensity C.linePoint t := by
  rw [C.zeroPoint_eq_line_sub_shift, C.mirrorPoint_eq_line_add_shift]
  unfold countingDensity
  have h := mirror_pair_density C.linePoint C.radialShift t
  have h' : Complex.exp ((C.linePoint - C.radialShift) * t) + Complex.exp ((C.linePoint + C.radialShift) * t) =
      2 * Complex.cosh ((C.radialShift : ℂ) * t) * Complex.exp (C.linePoint * t) := by
    linear_combination h
  rw [← add_div, h']
  ring

/-- Forme réelle : `D_ρ(t) + D_{ρ*}(t) = 2cosh(dt) · D_{1/2+iT}(t)`. -/
theorem pair_real_density_eq_cosh_line (t : ℝ) :
    realCountingDensity (zeroPoint C.zero) t + realCountingDensity (zeroPoint (mirrorMember C.zero)) t =
      2 * Real.cosh (C.radialShift * t) * realCountingDensity C.linePoint t := by
  rw [C.zeroPoint_eq_line_sub_shift, C.mirrorPoint_eq_line_add_shift]
  have hre1 : (C.linePoint - (C.radialShift : ℂ)).re = 1 / 2 - C.radialShift := by
    rw [Complex.sub_re, Complex.ofReal_re, C.linePoint_re]
  have hre2 : (C.linePoint + (C.radialShift : ℂ)).re = 1 / 2 + C.radialShift := by
    rw [Complex.add_re, Complex.ofReal_re, C.linePoint_re]
  have him1 : (C.linePoint - (C.radialShift : ℂ)).im = rZeroHeight C.zero.1 := by
    rw [Complex.sub_im, Complex.ofReal_im, C.linePoint_im, sub_zero]
  have him2 : (C.linePoint + (C.radialShift : ℂ)).im = rZeroHeight C.zero.1 := by
    rw [Complex.add_im, Complex.ofReal_im, C.linePoint_im, add_zero]
  simp only [realCountingDensity, hre1, hre2, him1, him2, C.linePoint_re, C.linePoint_im]
  have e1 : Real.exp ((1 / 2 - C.radialShift) * t) = Real.exp (t / 2) * Real.exp (-(C.radialShift * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp ((1 / 2 + C.radialShift) * t) = Real.exp (t / 2) * Real.exp (C.radialShift * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (1 / 2 * t) = Real.exp (t / 2) := by congr 1; ring
  rw [e1, e2, e3, Real.cosh_eq]
  ring

/-- **Le calage de la paire est celui de la ligne** : la densité réelle de la paire s'annule exactement aux points
`(π/2 + kπ)/T` de la ligne, qui ne dépendent que de la fréquence. La paire n'est ni en avance ni en retard. -/
theorem pair_density_zero_iff {t : ℝ} (ht : 0 < t) :
    realCountingDensity (zeroPoint C.zero) t + realCountingDensity (zeroPoint (mirrorMember C.zero)) t = 0 ↔
      ∃ k : ℤ, t = densitySignChangeLog (rZeroHeight C.zero.1) k := by
  rw [C.pair_real_density_eq_cosh_line, mul_eq_zero, mul_eq_zero]
  have hcosh : Real.cosh (C.radialShift * t) ≠ 0 := (Real.cosh_pos _).ne'
  have hT : C.linePoint.im ≠ 0 := by rw [C.linePoint_im]; exact C.zero.2.ne'
  rw [realCountingDensity_eq_zero_iff C.linePoint hT ht, C.linePoint_im]
  constructor
  · rintro ((h2 | h) | h)
    · norm_num at h2
    · exact absurd h hcosh
    · exact h
  · intro h
    exact Or.inr h

/-! ### C3. Le pas de la paire avant la cassure : enveloppe explicite, strictement au-dessus de la ligne -/

/-- **Enveloppe du pas de la paire** sur `[log N, log(N + 1)]` (canal de comptage) :
`(e^{β log(N+1)} + e^{(1−β) log(N+1)}) / log N · (log(N+1) − log N)`. -/
theorem pair_step_norm_le (N : ℕ) (hN : 2 ≤ N) :
    ‖countingGapTerm (zeroPoint C.zero) (Real.log N) (Real.log (N + 1)) +
        countingGapTerm (zeroPoint (mirrorMember C.zero)) (Real.log N) (Real.log (N + 1))‖ ≤
      (Real.exp (rZeroRadialPosition C.zero.1 * Real.log (N + 1)) / Real.log N +
          Real.exp ((1 - rZeroRadialPosition C.zero.1) * Real.log (N + 1)) / Real.log N) *
        (Real.log (N + 1) - Real.log N) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 < Real.log N := Real.log_pos hN1
  have hab : Real.log N ≤ Real.log (N + 1) := Real.log_le_log (by linarith) (by linarith)
  have h1 := countingGapTerm_norm_le (zeroPoint C.zero) (zeroPoint_re_pos C.zero).le ha hab
  have h2 := countingGapTerm_norm_le (zeroPoint (mirrorMember C.zero)) (zeroPoint_re_pos _).le ha hab
  rw [zeroPoint_re] at h1
  rw [zeroPoint_re, mirrorMember_radial] at h2
  refine le_trans (norm_add_le _ _) ?_
  rw [add_mul]
  exact add_le_add h1 h2

/-- **L'enveloppe de la paire OFF dépasse strictement celle de la paire de ligne** : pour tout `b > 0`,
`2 e^{b/2} < e^{βb} + e^{(1−β)b}` (facteur `cosh(db) > 1`). L'amplitude cumulée rapproche la paire de la cassure. -/
theorem pair_step_bound_gt_line_bound {b : ℝ} (hb : 0 < b) :
    2 * Real.exp (1 / 2 * b) <
      Real.exp (rZeroRadialPosition C.zero.1 * b) + Real.exp ((1 - rZeroRadialPosition C.zero.1) * b) := by
  rw [C.zero_radial_eq]
  have e1 : Real.exp ((1 / 2 - C.radialShift) * b) = Real.exp (1 / 2 * b) * Real.exp (-(C.radialShift * b)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp ((1 - (1 / 2 - C.radialShift)) * b) =
      Real.exp (1 / 2 * b) * Real.exp (C.radialShift * b) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, e2]
  have hc : 1 < Real.cosh (C.radialShift * b) :=
    Real.one_lt_cosh.mpr (mul_pos C.radialShift_pos hb).ne'
  rw [Real.cosh_eq] at hc
  have hp : 0 < Real.exp (1 / 2 * b) := Real.exp_pos _
  nlinarith

/-! ### C4. La cassure est réalisée par la totalité -/

/-- **La cassure est réalisée par la totalité** : au pas de la cassure, ce que le paquet de la fréquence `T` ne fournit
pas est fourni exactement par les autres fréquences — pour la paire OFF comme pour toute famille. Aucun signal isolé ne
réalise une cassure ; aucune lecture « la paire doit réaliser la cassure à temps » n'est compilable. -/
theorem break_compensated_by_other_frequencies :
    eventCompensation C.packet C.meetingPred = packetIncrement C.packetᶜ C.meetingPred :=
  eventCompensation_eq_complement C.packet C.two_le_meetingPred

