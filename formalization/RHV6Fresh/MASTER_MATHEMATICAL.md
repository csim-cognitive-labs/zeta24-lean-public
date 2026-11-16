# RHV6Fresh: Mathematical master document

> Condensed English master document (current state and latest attempt only). The complete French master with the full research history is `RHV6final_STRATEGIE_MATHEMATIQUE.md`.

Conventions. Statement tags: `[C]` compiled in Lean (no `sorry`, no added axiom); `[N]` measured on a deterministic twin only (numerical observation, never a proof); `[def]` definition; `[<=>RH]` proved equivalent to RH (a characterisation, never a proof of RH); `[ND]` not derived. Lean files are under `formalization/RHV6Fresh/RHV6Fresh/Terminal/` unless stated otherwise. Twins use the Odlyzko zeros (up to 2,001,052) and the primes up to 3·10^7. Where a text and a compiled theorem disagree, the theorem prevails.

---

## 1. Status

- The Riemann Hypothesis is NOT proved. No Lean term of type `RiemannHypothesis` free of assumed premises exists.
- The terminal theorem `riemannHypothesis_terminal` (`DemonstrationChain.lean`) is conditional on one hypothesis, `ExpectedFrequencyRises` ("on every passage, the height, i.e. the frequency, of the later member is strictly larger than that of the earlier member"). That hypothesis is proved equivalent to RH (`expectedFrequencyRises_iff_riemannHypothesis`), so the terminal theorem is a conditional reduction, not a proof.
- The prime number theorem (Chebyshev form) is ported (`RHV6Fresh/PNTPort`, third-party code). Consequences compiled from it: logarithmic gaps of primes tend to 0, and meetings sample the frequencies (`LogGapsTheorem.lean`).
- The latest attempt (tent and break weight; shifted-prime band) ended with no theorem to write on the restriction studied (section 5).

---

## 2. Definitions and notation

### 2.1 Zeros, order, mirror

```text
zero z = rho = beta + iT,  0 < beta < 1,  zeta(rho) = 0,  member: T > 0
order key kappa(z) = (T(z), beta(z)), lexicographic order  z < w
fibre F(T0) = { z : T(z) = T0 } (finite);  rank n(z) = #{ w : w < z }
passage e -> l: consecutive members (no member strictly between)
mirror z* = 1 - conj(rho) = (1-beta) + iT   (T* = T, beta* = 1 - beta)
four zeros: rho, conj(rho), 1 - conj(rho), 1 - rho (same multiplicity)
mirror pair centre m(z) = (rho + rho*)/2 = 1/2 + iT
primes: p_0 = 2, p_n the n-th prime, g_n = p_{n+1} - p_n, pi(x) = #{p <= x}
Occ(z) = p_{n(z)},  p_min(z) = p_{n(z)+1}
```

On a passage `e -> l`: `n_l = n_e + 1`, `Occ(l) = p_min(e) =: M`; `M` is the shared prime (premier partagé). `p_min(e) < p_min(l)`.

### 2.2 Tower

```text
zeroTerm(q) = q^rho / rho,  q > 0        (the Tower of z is the curve q -> q^rho/rho)
phi(beta,T) = arctan(T/beta) in (0, pi/2),   cos(phi) = beta/|rho|
|q^rho/rho| = q^beta / |rho|;   arg(q^rho/rho) = T log q - phi  (mod 2 pi)
Re(q^rho/rho) = q^beta cos(theta - phi)/|rho|,  theta = T log q
Im(q^rho/rho) = q^beta (beta sin(theta) - T cos(theta))/|rho|^2
normalised Tower (scale sqrt(x)):  Gamma(u) = e^{u(rho - 1/2)}/rho,  x = e^u
   radial rate d = beta - 1/2 per unit of log x; angular speed T per unit of log x
   beta = 1/2: circle of centre 0; beta != 1/2: spiral
half turn:  Gamma(u + pi/T) = - e^{(beta - 1/2) pi/T} Gamma(u)
```

### 2.3 Contacts, cells, positions

```text
contact C_k = exp((phi + k pi)/T), k in Z;   T log C_k = phi + k pi;  tan(T log C_k) = T/beta
Im(q^rho/rho) = 0  <=>  q = C_k for some k
C_k^rho / rho = (-1)^k C_k^beta / |rho|    (real, alternating sign)
step: log C_{k+1} - log C_k = pi/T     (function of T alone)
cell length: l_k = C_{k+1} - C_k = C_k (e^{pi/T} - 1);   C_{k+1} = e^{pi/T} C_k
position: theta_z(q) = (T log q - phi)/pi;  cell of q: (C_k, C_{k+1}] with k = ceil(theta_z(q)) - 1
cell fraction f(x) = fract((T log x - phi)/pi) in [0,1)   (`cellFraction`);  last contact before x: `lastContactBefore`
line Tower: phi_0(T) = arctan(2T), c_0(T,k) = exp((phi_0 + k pi)/T)
radial factor r(z) = exp((phi - phi_0)/T);  C_k(z) = c_0(T,k) r(z);  r = 1 <=> beta = 1/2
```

A contact is the point where the Tower crosses the real axis. A Tower contact is never claimed to coincide with a prime (section 6).

### 2.4 Explicit formula and remainder

```text
smoothed remainder   A(x) = sum_{n<x} Lambda(n)(1 - n/x) - background(x) = sum_rho -m(rho) x^rho/(rho(rho+1))   (x > 1)
raw channel          c_rho(n) = -2 Re[(x_{n+1}^rho - x_n^rho)/rho],  x_n = p_n + 1/2
raw demand           rawDemand: the demand function of the cell-area modules (compiled: demandArea = integral of rawDemand)
```

### 2.5 Mod 6 grammar

```text
GoodMod6(n): n mod 6 in {1,5};   state(n) = B if n = 1, A if n = 5 (mod 6)
gapClass6(m,n) = (n - m) mod 6 in {0,2,4};   0: same state, 2: A -> B, 4: B -> A
gap g = 6a + r:  a = floor(g/6) (magnitude), r = g mod 6 (class)
```

### 2.6 Break, word, mirror word

The break (cassure) is the jump of the demand at a prime `x` (weight `Lambda(x) = log x`). The word of gaps is read from the primes through the contacts (it determines the Tower, section 3.1). The mirror `(1-beta, T)` has a word that is a function of the Tower's word. Phase shift `delta = phi_beta - phi_{1-beta}`; on a fraction `|delta|/pi` of the reals the mirror word is shifted by one unit (`mirrorWordShift`).

---

## 3. Established and measured statements

### 3.1 Compiled [C]

**Zeros, mirror, Tower geometry**
- Mirror: `T* = T`, `beta* = 1-beta`; mirror annulled iff `beta = 1/2`; centre `1/2 + iT` for every beta; zero at the centre of its pair iff `beta = 1/2`. (`mirrorMember_ordinate` in `Direct/MirrorCount.lean`; `mirror_annulled_iff_onLine` in `EngagedClosureVerdict.lean`; `mirror_pair_center`, `zero_at_center_iff_onLine` in `EngagedAllConstraints.lean`.)
- Normalised Tower: `Gamma(u) = e^{u(rho-1/2)}/rho` (`rescaledTower_eq`, `TowerFourSectors.lean`); central symmetry of the normalised Tower iff `beta = 1/2` (`towerSymmetric_iff_onLine`, `tower_two_symmetries`, `EngagedAllConstraints.lean`); half turn with factor `e^{(beta-1/2)pi/T}` (`rescaledTower_half_turn`, `zeroTerm_half_turn`, `OnLineBetaEqPrevious.lean`); conjugation gives the Tower of the conjugate (`tower_topBottom_symmetric`).
- Contacts: real values, alternating sign, `step = pi/T`, tangent inversion `T = pi/log(C_{k+1}/C_k)`, `beta = T/tan(T log C_k)` (equivalently `beta = T cot(T log C_k)`), valid for every zero and every `k` (`ContactRealValue.lean`, `TangentialInversion.lean`, `AmplitudeContact.lean`). Contacts read beta exactly; an interval of contacts is determined by the frequency AND the amplitude. Two distinct zeros never share two consecutive contacts. Real part at contacts: `zeroTerm_re_at_contact` (`MirrorPairExactSum.lean`).
- Reading difference in one Tower: `theta_z(q') - theta_z(q) = T log(q'/q)/pi`, independent of `beta` and `phi` (`gap_reading_height_only`, `DoubleRigidity.lean`); it cancels the common offset `D/pi` without proving it is zero.
- Line Tower and normal form: `C_k(z) = c_0(T,k) r(z)`; `r = 1 <=> beta = 1/2`; `D = arctan 2T - arctan(T/beta)`, `theta_z = theta_0 + D/pi`, `-1/(2T) < D < 1/T`, `D = 0 <=> beta = 1/2` (`radialFactor_eq_one_iff`, `DiagonalPassage.lean`).
- Winding: for `e < l`, there is `K` with `C_k(l) < C_k(e)` for all `k >= K` (`windingNestedAtInfinity_of_precedes`, `TowerTwoSidedRoom.lean`).
- Mirror pair: `|F_rho + F_rho*|^2 = |F_rho|^2 + |F_rho*|^2 + 2 Re(x/(rho(1-rho)))`, with `Re(rho(1-rho)) = beta(1-beta) + T^2 > 0`, hence the pair sum strictly exceeds each member (no internal compensation), raw and smoothed forms (`mirror_pair_no_internal_compensation`, `mirror_cross_re_pos`, `MirrorPairExactSum.lean`).

**Order, passages, regimes**
- Passage: `n_l = n_e + 1`, `Occ(e) < Occ(l) = p_min(e)`, `p_min(e) < p_min(l)`; same-height passage with `n+1` exists off the line; `n = h` (index = number of distinct heights) iff every fibre is a singleton iff RH.
- Regimes: vertical `V(p): T_e < T_l`; horizontal `H(p): T_e = T_l`; exclusive and exhaustive. Junction rules: `V` then `V` implies `beta_m = 1/2`; `V` then `H` implies `beta_m < 1/2`; `H` then `V` implies `beta_m > 1/2`.
- Existence of a vertical passage (`exists_verticalPassage`, `NoRegimeChange.lean`); the passage after an engaged state advances in height (`engaged_regime_kept`, `RegimeTrigger.lean`).
- `PNoRegimeChange <=> RH` (`NoRegimeChange.lean`).
- Cell `a -> e -> l -> b` (`T_a < T_e = T_l < T_b`) exists only if RH fails; RH implies no cell.

**Grammar mod 6**
- Primes `p > 3` satisfy `GoodMod6`; `gapClass6` transitions; three consecutive primes `> 3` satisfy `r >= p + 6`; signed identity `sum_i (1[A->B] - 1[B->A]) = 1[s_m = B] - 1[s_0 = B]`; exact identity for the grammatical dwells (quasi-compensation = equidistribution of primes between classes 1 and 5 up to one unit) (`GrammarDwellDecomposition.lean`); Abel bound for the oriented channel (`GrammarWeightedG4.lean`).

**Explicit formula and identities of members**
- Reconstruction of `psi` from the zeros for `x >= 2`; identity of each member (the exponent family `(s_i, c_i)` representing the channel recovers each `(beta, T, m)`); `RH <=> exists a representation with all nonzero coefficients on Re s = 1/2` `[<=>RH]`.
- Growth reading: `|A(x)| <= C x^theta` for all `x > 1` implies `beta(rho) <= theta` for every zero; `RH <=> exists C, |A(x)| <= C sqrt(x)` `[<=>RH]` (`riemannHypothesis_iff_remainder_sqrt_growth`, `ArithmeticReading.lean`). The bound `|A(x)| <= C sqrt(x)` itself is `[ND]`.
- Collective budget: an off-line member of height `> H` refutes the collective budget `B_H`; `B_H <=> every member of height > H is on the line` (`offLine_following_refutes_collectiveBudget`, `collectiveBudget_iff_following_onLine`, `RemainderRepresentation.lean`).

**Single premise and conditional closure**
- `ExpectedFrequencyRises <=> RH` (`DemonstrationChain.lean`); `ExpectedFrequencyRisesAtMeetings` is the same statement (`MeetingPoint.lean`); `riemannHypothesis_iff_conservation_and_base` (`EngagedClosureVerdict.lean`).
- On a passage from an engaged (on-line) state: `onLine_beta_eq_previous` (`OnLineBetaEqPrevious.lean`, hypotheses declared, no `sorry`).
- Raccord hierarchy at every junction (with contracted step) `<=> RH` (`raccordHierarchy_iff_riemannHypothesis`, `TowerHierarchy.lean`).

**Zero-free band and counting**
- Zero-free band applied to the actual zeros (`ZeroFreeRegionBand.lean`); radial rigidity of a bounded finite exponential sum (`FiniteRadialRigidity.lean`, conditional tool); counting deficit identities `N = N0 + 2W` (`CountingDeficit.lean`); frequency cascade increasing on the line, its strict increase everywhere `<=> RH` (`FrequencyCascadeStability.lean`).

**Off-line carrier and meetings**
- Canonical OFF carrier (`OffCarrier.lean`): low arrival (`beta < 1/2`), finite fibre, frozen outgoing step; `low_arrival_precedes_mirror`, `low_entry_not_expected` (`PairArrivalPassage.lean`).
- Frequency capped above and below by rank (`FrequencyCap.lean`); three-zero window (`ThreeZeroWindow.lean`); meetings between Towers (`TowerMeetings.lean`).
- Finite regime with one prime per meeting cell, for every Tower (`MeetingRegimeFinite.lean`); exact amplitude of the break on the line `sqrt(q) e^{-pi f/(2T)}` and Abel balance (`BreakMechanismOnLine.lean`).
- The word of gaps determines the Tower `(T, phi, beta)` (tangential formula; the cause is the ported PNT); break of the pair at the shared prime and order of the zero (`PairBreakOfZero.lean`); imposition of the meeting, same sign iff same word (`PairMeetingImposition.lean`); pair read as a passage (`PairArrivalPassage.lean`).
- Meeting point and constant relative amplitude: `sharedPrime_eq_meeting` (`AuthenticRaccordLock.lean`): `M = expectedMinimumPrime e = occurrence l = meetingPoint (occurrenceGap e) = p_{n+1}`; `constantRelativeAmplitude_iff_onLine` (`MeetingPoint.lean`).

**Cumulative series (isolated modules)**
- `MemberConstancySeries.lean`, `FiberAnnihilator.lean`, `PairAsymmetryOverPrimes.lean`, `AlternatingCellSeries.lean`: the relative share of a Tower is multiplied by `e^{pi(beta-1/2)/T}` per cell; constant iff on the line; the mirror is unbounded, the low member vanishes, the pair is unbounded; the cumulative asymmetry of the pair over primes is `(1-2beta) theta(N)`, zero iff on the line; the alternating sum of shares is a geometric series, bounded on the line and divergent for the mirror; per cell and per prime the difference is a fraction (at most `e^{pi/(2T)} - 1` per cell, at most `log p` per prime).
- `ArithmeticBudgetSeparation.lean`: separation of the arithmetic alternating budget from the background.

**Cell areas, tent, break weight**
- `CellAreaGrammar.lean`: area of a cell = (demand at entry contact × length) − (half square of length) + weight of integers crossed weighted by distance to exit; local grammar `a_{k+1} - e^{pi/T} a_k = eps_{k+1} + e^{pi/T} eta_k` (the demand at the contact is eliminated); budget recurrence `(1+e^{pi/T}) A_{N+1} = a_0 + (-1)^N e^{pi/T} a_N - sum (-1)^n L_n`; unconditional scale: `|a_k| <= (1/2+eps) l_k^2` from some rank on (PNT ported), window budget at scale `x_N^2`.
- `CellAreaTent.lean` and `CellAreaIntegral.lean` (section 5.1).
- `TentBreakObligation.lean` (isolated, 10 statements; section 5.2).

### 3.2 Equivalent to RH (characterisations, not proofs)

`ExpectedFrequencyRises`; `PNoRegimeChange`; the growth bound `|A(x)| <= C sqrt(x)`; `n = h`; every passage vertical; the collective budget with all following zeros on the line; raccord hierarchy at every junction; `ContinuationForced` (the outgoing step of the first break rises; `TwoRaccordReadingTransport.lean`). "Equivalent to RH" is not an objection (section 6): only admitting such a statement as a premise is forbidden.

### 3.3 Measured only [N]

- Tower geometry on the first 300 zeros: the cell containing `p_min` for 300/300 zeros; 15/15 historical contacts (`m = 1`); up to 3006 primes in one cell (primes `<= 200000`).
- Grammar mod 6: alternation verified up to 2,000,000 primes (blind to beta); 0 violation on 378,566 pairs (`p <= 10^7`).
- Cell-area modules (E473 twin): local terms `|L_k|/C_k^{3/2} <= 0.07`, areas `<= 0.033`, budget `<= 0.04`, all decreasing with `T`; `T |L_k|/C_k^{3/2}` between 0.40 and 2.07 (thirteen Towers); `|rawDemand|/sqrt(x)` up to 0.92.
- Exponents of the pair measured 0.223 / 0.112 / 0.039 for expected 0.20 / 0.10 / 0.05.
- Shared prime: `expectedMinimumPrime e = occurrence l = meetingPoint = p_{n+1}` exact on 2000 canonical junctions.

---

## 4. The open frontier

Stated neutrally. Starting from the primes alone and the exact reconstruction of a gap between two consecutive primes, no arithmetic constraint has been obtained that the first off-line Tower and its mirror cannot satisfy.

Compiled obligations at the meeting at the shared prime:

```text
O1  identity of the gap: demand of the gap = sum of the shares of ALL zeros         (all_signals_meet, localSynchronization)
O2  no finite family closes the gap; the jump at the meeting is carried by the rest
O3  the meeting cell of a Tower contains exactly one prime; imposed amplitude
O4  form of the pair at the shared prime: common word (shift in {-1,0,1}), same sign iff same word, no compensation
O5  exact, unbounded price of the pair; exact transport at the shared prime (energyRatio e l M = M^{beta_l - beta_e} |rho_e|/|rho_l|)
O6  constant relative amplitude at meetings                                          (constantRelativeAmplitude_iff_onLine)
O7  expected frequency rises at each meeting                                         (ExpectedFrequencyRisesAtMeetings)
```

- O1, O2, O3, O4, O5 are satisfied by every family of zeros, the off-line pair included. In particular, an authentic family reconstructs any radial position (`authentic_family_reconstructs_any_radial`), and `imposedShare_eq` gives the share of one member as the target minus the others: no relation on the share of a single member derived from the identity alone constrains `beta`.
- O6 and O7 are the only predicates the pair violates (`relativeAmplitude_strictAnti_of_low`, `pairRelativeAmplitude_unbounded`, `low_entry_not_expected`). They are not derived from the reconstruction: O6 is a property of one member's term, equivalent to the line by definition; O7 is the single premise, equivalent to RH.
- The frontier is the missing link from O1 (together with the grammar of the shared prime: minimum expected of the outgoing member, occurrence of the incoming member, gap `occurrenceGap e`) to a per-member property of the share imposed at meetings that fails off the line. Active question Q475: what new constraint does the exact reconstruction of a gap impose on the first off-line Tower that its contacts and those of its mirror cannot satisfy. Not demonstrated.
- Where the pair differs from a line family: in the enumeration. Two members of the same height have two consecutive indices (`low_arrival_precedes_mirror`) and two consecutive occurrences; the junction `l -> mirror` at the shared prime `p_{n+2}` is a detour, with no compiled transport conservation law.
- The measured sensitivity of the share of a pair to `beta` is exactly `cosh((beta - 1/2) log x)`: the price (O5), already compiled.
- Terminal reduction: the whole chain closes under `ExpectedFrequencyRises`; the content of that hypothesis is that, from the exact gaps of the primes, the next signal's frequency is strictly larger than the current one. Deriving it from the primes alone requires the infinite prime tail; this is the single open arrow.
- Auxiliary (compiled, no demonstrative reach towards RH): cell-area grammar, tent identity, memory-one form, integral of the demand. The closest compiled reduction of the alternating-budget target is: budget at scale `x_N^{3/2}` follows from `|rawDemand| <= M` on the window with `M = O(sqrt(x) (log x)^2)`, which is of RH strength.

---

## 5. The latest attempt: tent, break weight, shifted-prime band

Aim: combine the tent (area grammar) and the break (demand jump at a prime) to create an arithmetic obligation on the OFF pair at the shared prime. Measured on a fictitious pair (no off-line zero is known): Tower `(beta, T)` and mirror `(1-beta, T)`, `beta` in {0.45, 0.40, 0.30}, heights `T_1`, `T_10`, `T_100`, witness `beta = 1/2`.

### 5.1 Tent identity and memory-one form (`CellAreaTent.lean`, `CellAreaIntegral.lean`) [C]

With `L_k` the local grammar term of two consecutive cells:

```text
tent_k(t) = min( e^{pi/T} (t - C_k),  C_{k+2} - t )        continuous hat, apex at C_{k+1}, height l_{k+1} = e^{pi/T} l_k
integral of tent_k = e^{pi/T} (1 + e^{pi/T}) l_k^2 / 2
L_k = sum_{n in (C_k, C_{k+2}]} Lambda(n) tent_k(n) - integral of tent_k          (localGrammarTerm_eq_tent_sum)
L_k = eps_{k+1} - e^{pi/T} eps_k + e^{pi/T} l_k Delta_k                            (localGrammarTerm_eq_memory_one)
```

`eps_k` is the exit deviation of cell `k`, `Delta_k` the variation of the demand on cell `k`. Also compiled: the area of the demand is the integral of `rawDemand` (`demandArea_eq_integral`); `eps_k = integral over the cell of (D(t) - D(C_k)) dt`; bound `|L_k| <= 2 e^{pi/T} l_k M` if `|rawDemand| <= M` on the two cells (`abs_localGrammarTerm_le_of_demand_bound`); and `|rawDemand| <= M` on the window implies `(1+e^{pi/T}) |A_N| <= M (1+e^{pi/T})^2 C_{k_0+N}` (`budget_le_of_demand_bound'`), without alternation. The `1/T` law of `|L_k|` is the cell length: `l_k = (e^{pi/T} - 1) C_k` with `T (e^{pi/T} - 1) -> pi`; it is not a cancellation.

Measured [N]: the two parts `A = eps_{k+1} - e^{pi/T} eps_k` and `B = e^{pi/T} l_k Delta_k` have comparable root mean squares (ratio 0.83 to 1.39) and are nearly opposed: corr(A, B) = -0.998 (Tower 1), -0.91, -0.81, ..., -0.62 (Tower 5000). The cancellation is a measurement, not a theorem. Lag-1 autocorrelation of `L_k`: sign as predicted (negative for low Towers, weak positive 0.10 to 0.14 for Towers 500 to 5000), amplitude predicted above 0.2 not reached.

### 5.2 Break weight inside the tent (`TentBreakObligation.lean`, isolated) [C]

Statements hold for every real `x > 0` and every `beta`; `x` is never a prime sitting on a contact, `f` is its relative position between contacts.

```text
breakTentWeight(beta,T,x) := tentKernel(beta, T, lastContactBefore(x), x)         (tent of the cell containing x, ascending branch)
w = e^{pi/T} x (1 - e^{-pi f/T}),   f = cellFraction                              (breakTentWeight_eq)
previous tent, descending branch:  x (e^{pi/T} e^{-pi f/T} - 1)                   (breakTentWeight_prev_eq)
L_k = Lambda(q) tent_k(q) + rest - integral of tent_k                              (localGrammarTerm_break_split)
```

Amplitude paid at the last contact before `x`:

```text
|v_beta(k(x))| = x^beta (1 - w/(e^{pi/T} x))^beta / |rho|                          (break_amplitude_reads_tent)
```

The weight of the break in the area grammar and the amplitude paid by the Tower are two readings of the same cell fraction.

### 5.3 The alternating budget, sawtooth, neutral point [C]

```text
w - w_prev = (1 + e^{pi/T}) x - 2 C_{k+1}                                          (tent_difference_eq_sawtooth)
(-1)^{j+1} tent_prev(x) + (-1)^j w = (-1)^j ((1 + e^{pi/T}) x - 2 C_{k+1})         (alternating_break_weight)
saw(x) = (1 + e^{pi/T}) x - 2 C_{k+1};   saw > 0  <=>  2 e^{pi/T} e^{-pi f/T} < 1 + e^{pi/T}     (sawtooth_pos_iff)
```

`saw` vanishes at the neutral point of the cell. Each break enters the alternating sum of local terms with weight `(-1)^j saw(x)`. Measured: the interior sawtooth alone is at scale `x^2` (its integral over a cell is `l^3/(2 C_k) > 0`); it carries the background and is compensated by the tent integrals. In measure `x` (primes equidistributed in `x`), the fraction of breaks with positive weight is `e^{pi/T}/(1 + e^{pi/T})` (0.555 for Tower 1, measured 0.551).

### 5.4 Same weight for Tower and mirror iff the zero is on the line [C]

```text
breakTentWeight(1-beta, T, x) = breakTentWeight(beta, T, x)   <=>   beta = 1/2        (0 < beta < 1, T > 0, x > 0)   (pair_breakTentWeight_eq_iff)
```

with `pair_breakTentWeight_sub` giving the form of the difference, and `pair_same_sign_iff` (`PairMeetingImposition.lean`): same sign in the two alternating budgets iff same word. This is an equivalence of FORM (same weight iff line). No compiled theorem forbids a prime from being written with two weights by the two members of a pair; to distinguish is not to contradict. It localises exactly where a law "one prime, one break weight per height" would be violated by the pair: on the fraction `|delta|/pi` of primes whose word is shifted, where the break enters the two alternating budgets with opposite signs.

Measured [N]: median relative difference of the pair weights `|w(1-beta) - w(beta)|/(e^{pi/T} x) = (pi/T)(|delta|/pi) e^{-pi f/T}` (4.5e-4, 8.9e-4, 1.8e-3 for beta = 0.45, 0.40, 0.30 at Tower 1), maximum 0.199 (about one fifth of a cell), reached on the shifted fraction; the fraction of primes with shifted word equals `|delta|/pi` (0.0021, 0.0041, 0.0081).

### 5.5 Shifted-prime band, first order, second order

In the shifted band `u = 1 - f` in `(0, |delta|/pi]`: `saw_beta ~ (e^{pi/T} - 1) x > 0` and `saw_{1-beta} ~ -(e^{pi/T} - 1) x < 0`, and the parities differ by one unit.

1. First-order equality. The two alternating weights are equal at first order: the parity compensates the sign difference of the sawtooth teeth. Their difference `D = alt_beta - alt_{1-beta}` obeys, on a shifted prime (measured to 1e-3 median, Towers 1, 10, 100):
```text
D = (-1)^j (2x/T) [ e^{pi/T} delta - (1 + e^{pi/T}) pi u ] + O((delta/T)^2 x)
```
Median `|D|` is about `x delta/T`; mean over the band `(delta/T)(e^{pi/T} - 1) x`; sign variable in the band (positive near the mirror contact, negative near the Tower contact).

2. Second-order mean effect. The restricted sum, de-alternated, is of SECOND order in `delta` (`Lambda`-mass on the band `= (|delta|/pi) l_k`, PNT ported):
```text
S_k ~ (-1)^j ( delta^2 (e^{pi/T} - 1) / (pi T) ) l_k C_{k+1}
```
Measured ratio `R` (observed over this prediction), Tower 1: 1.31, 1.21, 1.16 for beta = 0.45, 0.40, 0.30 (constant within 13 percent; `R delta` varies by a factor 3.5, so first order is rejected); the factor contains the measure correction 1.115. Tower 10: dispersion 70 percent (noise), `R delta` varies by 7.8, first order rejected. The effect is alternating in `k` and at background scale `x^2` with constant `delta^2 (e^{pi/T} - 1)^2 / (pi T)`.

3. First-order identity on the non-shifted primes (same word, same parity):
```text
alt_beta - alt_{1-beta} = (-1)^{j+1} 2 C_{k+1} (1 - e^{-delta/T})       (algebraic; saw_beta - saw_{1-beta} = 2 C_{k+1}(e^{-delta/T} - 1) on a same word)
```
Summed and de-alternated, it equals the first-order prediction `(2 delta/T)(1 - delta/pi) l_k C_{k+1}` to 0.1 percent. This is where the pair writes the largest weight difference, but it is alternating and at background scale as well.

4. Why the cumulative restricted sum is fluctuation-dominated. The cumulative sum `S_pair(X)` over an even number of cells is not bounded by the second-order mean of the last two cells; it is dominated by the fluctuation of the individual terms, first order in `delta` and of variable sign. Estimated standard deviation (post hoc): `sqrt((delta/pi)(log X)/3) (delta/T) X^{3/2}`, the same order as the measurement on Towers 10 and 100; on Tower 1 the measure exceeds it and stays of the order of the mean of one cell. Log-log slopes 1.43 to 1.88; ratio to `x^{3/2}` from 1e-8 to 3e-3; nothing grows monotonically and nothing exceeds the background. Witness `beta = 1/2`: no shifted prime, `D = 0` exactly.

### 5.6 Predicted, measured, corrected

| Item | Predicted | Measured | Correction |
|---|---|---|---|
| Fraction of shifted primes | `|delta|/pi` (log measure of the cell) | Tower 1: +11 to +12 percent off | primes are equidistributed in `x`, band at the top of the cell: fraction `= (1 - e^{-delta/T})/(1 - e^{-pi/T})`, error 0.1 to 0.6 percent on Tower 1 (2 to 6 percent on Towers 10, 100: sampling noise); the correction tends to 1 as `T` grows (1.115, 1.032, 1.007) |
| Positive-weight fraction of breaks (Tower 1) | 0.528 (log measure) | 0.551 | `e^{pi/T}/(1 + e^{pi/T})` = 0.555; last cell truncated at 3·10^7 weighs most; Towers >= 10 agree to 0.001 |
| Relative pair weight difference | threshold 1e-3 | 8.9e-4 at beta = 0.40 | threshold mis-calibrated; law above |
| Identity on non-shifted primes | residual < 1e-10 | 1e-12 on Tower 1; 1e-10 to 3e-9 on Towers 10, 100 | floating-point floor of `1 - e^{-delta/T}` for `delta/T ~ 1e-6`; the identity is algebraic |
| First-order law on shifted primes | median residual ratio <= 0.1 | 0.000 to 0.001 | passed |
| Restricted sum, order in `delta` | second order | Tower 1: second order confirmed | passed |
| Cumulative sum bounded by the mean of the last two cells | bounded, slope >= 1.7 | dominated by fluctuations, slopes 1.43 to 1.88 | prediction wrong in nature, not just in threshold |
| Autocorrelation of `L_k` (high Towers) | above 0.2 | 0.10 to 0.14 | write "weak positive sign" |
| Lag >= 3 autocorrelations for Towers of fewer than 110 cells | — | sampling noise | not to be cited |

### 5.7 Conclusion of the attempt

The weight obligation is a compiled FORM: one prime, two break weights for the two members of an off-line pair, equal iff `beta = 1/2`. Its two natural restrictions (shifted primes, non-shifted primes) are alternating and at background scale (`x^2`); the first-order effect is not a mean effect, and the cumulative restricted sum is fluctuation-dominated and neither grows above `x^{3/2}` nor above the background. The pre-written rule "second order implies no theorem" applies: there is no theorem to write on this restriction. The localisation of the break weight to the shifted primes carries no new obligation. The thread (tent, break weight) is measured to its end without a closing route. RH is not proved; nothing was admitted. The active question returns to Q475: the constraint must come from the arithmetic data of the junction at the meeting (form O7, frequency before height), not from a restriction of the area budget.

---

## 6. Standing mathematical rules

Never assert:

1. That the contacts of a Tower do not read beta. Contacts read beta exactly, through the compiled inversions; an interval of contacts is defined by the frequency AND the amplitude. Never write "blind to beta", "depends only on the frequency", or "nothing radial" about contacts.
2. That a Tower contact coincides with a prime, or tie the contact grid to the exact position of a prime. The intervals between contacts are partial remainders of gaps, reconstructed collectively. A meeting at a shared prime is defined by the real grammar of the primes, not by a geometric construction.
3. That counting is a cause. The counting channel is a downstream observation of the reconstruction, not a mechanism.
4. That the useful range for the arrival is every `beta` in `(0,1)`. The useful range for the arrival is `beta <= 1/2`.
5. That "equivalent to RH" is an objection, brake or frontier in itself. Admitting such a statement as a premise remains forbidden.
6. That a statement is proved when it is only a characterisation, a conditional theorem or a measurement. Four degrees stay separate: compiled theorem; conditional theorem with classified hypotheses; algebraic identity or definitional reduction; numerical observation. Rewriting a goal is not a mathematical reduction.
7. That RH is proved, or that the terminal theorem is unconditional.
8. That a conclusion rejected by the author stands: the E301 conclusions; any tying of a Tower to the exact position of a prime; the spectral conclusion of E445; the "tail property" reading of E457; the obligation tying the OFF contradiction to the amplitude and the variation of the raw demand; the naive E2M correspondence.
9. Frequency before height: the meeting point imposes a frequency, then a height; never derive the height from the gap directly.
10. Fractions of primes in a cell band are always computed in the measure `x` (primes are equidistributed in `x`, not in the logarithm of the cell). A sum restricted to a sub-family of primes is read first through its fluctuations, never directly as a budget.
11. Do not write "the areas alternate" without stating the cell partition (alternation depends on the partition: with cells aligned on real contacts, about 50 percent sign changes for Tower 1). Use the cell formula (not the cumulative area formula) in twins beyond 10^6.
12. Distinguishing is not contradicting: a compiled form that the pair violates is not a contradiction unless a theorem forbids the alternative.
