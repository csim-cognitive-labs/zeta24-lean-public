# RHV6Fresh: semantic master document (English, condensed)

> Condensed English master document (current state and latest attempt only). The complete French master with the full research history is `RHV6final_STRATEGIE_SEMANTIQUE.md`.

State: 15 November 2026 (HEAD `4d4114c6` of the private research repository). Author: Charles S.

---

## 1. Purpose and status

**Goal.** A compiled Lean term of type `RiemannHypothesis`, obtained without any assumed premise, depending only on the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorry`, no `admit`, no added axiom. No such term exists today.

**The Riemann Hypothesis (RH) is NOT proved.** This document describes an open research programme, not a proof.

**What is true of the code.**
- No axiom declaration and no `sorry`/`admit` in the project's Lean sources (pattern search of 15 November 2026 over `RHV6Fresh/RHV6Fresh` and `rhv3_lean`).
- `lake build RHV6Fresh` completes successfully (9064 jobs). This green build does not prove RH.
- The only theorem whose conclusion is RH is `riemannHypothesis_terminal` (in `RHV6Fresh/Terminal/DemonstrationChain.lean`). It takes the named hypothesis `ExpectedFrequencyRises` (the expected frequency rises at every meeting). That hypothesis is proved equivalent to RH, so the terminal theorem is conditional and does not close the problem. The hypothesis is never asserted.
- Isolated modules written for experiments (for example `TentBreakObligation.lean`) are not imported by the root `RHV6Fresh.lean`; each was compiled individually, with its logs in the `attempts/` folder of its experiment.

**Four degrees of certainty, never to be merged.**
1. A Lean theorem recompiled without `sorryAx`, axioms inspected.
2. A conditional theorem, with its hypotheses kept and classified.
3. An algebraic identity or a definitional reduction.
4. A numerical observation (a deterministic twin: a Python script that recomputes the quantity independently, with real primes and real zeros).

Rewriting a goal is not a mathematical reduction. The compiled theorem comes first; the twin is used to measure, never to conclude; if a text conflicts with a compiled theorem, the text is corrected.

**Scope vocabulary.** A theorem that classifies an object already given characterizes it; it neither decides nor generates it. An equivalence with the presence of an off-line zero is a certificate, not a trigger or a cause.

---

## 2. The objects in plain words

**Zeros and the explicit formula.** Each non-trivial zero rho = beta + iT contributes to the explicit formula a term: a positive number x raised to the power rho, divided by rho. The proof effort concerns three objects only: the ordered set of true non-trivial zeros; the Tower of each zero; and the single ordered history of the primes, as reconstructed from the zeros by the Chebyshev / von Mangoldt channel with its full grammar (ranks, occurrences, primality, gaps, states, transitions, progression).

**Tower.** The Tower of a zero is the trace in the complex plane of its term as x runs over the positive reals: one continuous spiral, entirely determined by the real part and the height of the zero. Its argument advances with the logarithm of x at an angular speed per unit of log x equal to the height T, shifted by a phase fixed by beta and T. Its modulus (the amplitude) grows like x to the power beta divided by the norm of rho. One Tower per zero; a Tower never carries two zeros. The origin of the Tower plane is the pole of rotation of every Tower. The normalized Tower (divided by the square root of x) is a circle centred at the origin exactly when the zero is on the line (compiled); an off-line zero gives a spiral that grows (beta above 1/2) or decays (beta below 1/2).

**Contacts.** The contacts of a Tower are the points where it crosses the real axis, that is, exactly the values of x where the term is real. There is one per half-turn, endlessly in both directions, and the side of the axis alternates strictly. Two consecutive contacts have ratio e^{pi/T}: the logarithmic step of the Tower is pi/T. This step is a property of the Tower, not a gap between primes. A contact is never "at" a prime (see section 7).

**Cell.** The interval between two consecutive contacts of a Tower. Its length is (e^{pi/T} - 1) times its left endpoint, which is why many quantities scale like 1/T (the cell length), not through any cancellation.

**Word of a Tower on the primes.** For each prime (more generally each real x > 0), the index k(x) of the last contact before x, together with the fraction f(x) of the cell in which x falls. The sequence of these indices is the word. The tangential formulas rebuild (T, beta) from two consecutive contacts (T = pi / log(C_{k+1}/C_k); beta = T / tan(T log C_k - k pi), on a verified branch). The word determines the Tower (same word implies same T, same phase, same beta), for any Tower, zero or not.

**Gap and the reconstruction of a gap.** A gap here is the interval between two consecutive primes. Its exact arithmetic ends are certain. The collective reconstruction through all the true zeros gives back, event by event, the weights, the primality, the counting, the ranks and the gaps ("M^Z = M"). The counting reads; it never selects and never enters the construction of a Tower. No finite family of zeros reconstitutes a gap: the jump at the meeting is carried by the remainder.

**Mirror.** The reflection through the critical line: it keeps the height and sends beta to 1 - beta. A zero off the line (OFF) of positive height comes in a square of four distinct zeros (itself, conjugate, mirror, reflected), of equal multiplicity; two of them are members of the upper half: the zero and its mirror, at the same height with complementary real parts. On the line the mirror is the member itself. Off the line, no contact of the mirror coincides with a contact of the zero: the mirror's contacts interlace strictly inside the zero's cells, with a uniform translation of the contact grid (a phase shift delta, zero if and only if beta = 1/2).

**Pair.** A zero off the line together with its mirror: two members of the same height and complementary beta, two consecutive indices in the enumeration, two consecutive prime occurrences.

**Succession, passage, shared prime.** Members are enumerated by increasing height (then by increasing real part). A passage is a pair of consecutive members: the rank advances by exactly one, the height never decreases, the occurrence of the successor is the expected minimum of the predecessor, and the expected minima strictly increase (compiled, no hypothesis on the real part). The shared prime of a passage is the prime that is both the expected minimum of the departing member and the occurrence of the arriving member; it is unique and determined by the rank.

**Junction.** The junction (raccord) of two consecutive members at their shared prime, where the exact meeting is imposed by the grammar of the real primes (`localSynchronization`), not by any geometric coincidence of a contact with a prime.

**Break.** The break at a prime q: the instant at which the raw demand jumps by log q. A Tower pays it with amplitude fixed by the value of its last contact before q: on the line, |v| = sqrt(q) e^{-pi f/(2T)} / ||(1/2,T)||, f being the cell fraction of q. In the area grammar (below) the break enters with a weight read on the same cell fraction.

**Tent.** The tent kernel of two consecutive cells of a Tower: the continuous hat function tent_k(t) = min(e^{pi/T}(t - C_k), C_{k+2} - t), with apex at the contact C_{k+1}. The local term of the area grammar is the discrepancy of the primes of the two cells against this kernel.

**Area grammar.** The area of a cell is the integral of the raw demand over it. The relation between two consecutive cell areas is local (the demand at the contact, the only memory of earlier primes, is eliminated); the alternating budget over a window is the first area plus the last area plus an alternating sum of local terms. These are compiled and classed as auxiliary (section 5).

**On-line (ON) and off-line (OFF).** ON: beta = 1/2. OFF: beta different from 1/2. The useful range for the arrival of an off-line zero is beta at most 1/2 (the arrival is the low member), never "every beta in (0,1)".

---

## 3. The strategy

**Intended causal chain** (author's order, frequency before height):

1. The primes and their exact gaps are the starting data.
2. A demand of gaps produces obligatory meetings; at each meeting the expected frequency is a generic point; the first zero on the line is the rank-one instance of it. Counting is downstream: it reads, it does not cause.
3. Each zero defines a Tower, whose contacts mark out the real axis; contacts read beta exactly (through the compiled tangential formulas), and an interval between contacts is defined by the frequency AND the amplitude.
4. The junction at the shared prime is defined by the real grammar of the primes.
5. The aim: find the arithmetic constraint that the exact reconstruction of a gap imposes on a first off-line Tower, a constraint that its contacts and those of its mirror cannot satisfy. That would exclude the OFF zero.

**Discipline of the route.**
- Collective reconstruction (all the zeros together) is allowed. The route never ties a Tower to the exact position of a prime; contact intervals are partial remainders of gaps, reconstructed collectively.
- Cumulative, not pointwise, doctrine: per step the deviation of an OFF pair is a fraction (compiled: at most e^{pi/(2T)} - 1 per cell, at most log p per prime); only accumulation could make it large. Nothing so far closes the accumulation.
- Every target is written with a "Strategy" section (target, accumulated object, why not pointwise, signature, what follows in both outcomes). No closure is recorded as a "frontier" without having been attacked.
- Before any compilation or run: a committed pre-registration with numeric thresholds, at most two compilation attempts, a deterministic twin for every figure, nothing fabricated. Verdicts: A (all pre-registered criteria met), B (partly met, some tests failed by the letter), C (failure). B verdicts are frequent and are not successes.

---

## 4. What is established, and what is only measured

All files below exist under `formalization/RHV6Fresh/RHV6Fresh/Terminal/` (verified with `find`) unless stated.

### 4.1 Compiled (Lean)

- **Zero-free band** for the actual zeros: above height 3 the real part stays in a band widening toward 1/2. It does not separate the line from off-line positions. `ZeroFreeRegionBand.lean`.
- **Grammar modulo 6**: exact identity for the dwells (the quasi-compensation of the dwells is the equidistribution of the primes between classes 1 and 5 up to one unit) and an Abel bound on the oriented channel. `GrammarDwellDecomposition.lean`, `GrammarWeightedG4.lean`. This is not an independent constraint on beta.
- **Finite radial rigidity** of a bounded finite exponential sum (a conditional tool: the bound for the infinite signal is not established). `FiniteRadialRigidity.lean`.
- **Prime number theorem (Chebyshev form)** is ported (third-party code under `PNTPort`, Apache 2.0). Consequences as theorems: the logarithmic gaps tend to zero, and the meetings sample the frequencies. `LogGapsTheorem.lean`; also the vertical summit sub-case in `SummitVertical.lean`.
- **Canonical OFF carrier**: low arrival, finite fibre, frozen outgoing step, trichotomy of the outgoing member. `OffCarrier.lean`, `OnRegimeStabilityPackage.lean`. Related isolated modules: `ThreeZeroWindow.lean` (gap bracketed unconditionally via Riemann-von Mangoldt), `FrequencyCap.lean` (frequency capped above and below by rank; the caps are radially blind, so they are not a lever against an OFF zero).
- **Meeting point and junction** definitions and theorems: `MeetingPoint.lean` (meeting at the shared prime, `imposedShare`, `all_signals_meet`).
- **Frequency cascade**: on the line it strictly increases at every rank; its strict increase everywhere is equivalent to RH. `FrequencyCascadeStability.lean`, cited in `DemonstrationChain.lean`.
- **Contacts**: real value at each contact, tangential inversion of (T, beta), interlacing. `ContactRealValue.lean`, `TangentialInversion.lean`, `AmplitudeContact.lean`; meetings between Towers in `TowerMeetings.lean`.
- **Words**: the word of gaps determines the Tower (E449). The mirror's word is a function of the Tower's word: k* = k + s with s in {-1, 0, 1}; the words are equal if and only if the cell fraction falls in a window fixed by beta, full on the line. Modules `PairBreakOfZero.lean`, `PairMeetingImposition.lean`, `PairArrivalPassage.lean` (break of the pair at the shared prime, same sign if and only if same word, the pair never compensates itself at the shared prime, the OFF pair read as a passage).
- **Finite regime**: a regime with one prime per meeting cell is finite for every Tower (PNT ported). `MeetingRegimeFinite.lean`. **Break mechanism on the line**, exact break amplitude, Abel balance of the demand at the contacts. `BreakMechanismOnLine.lean`.
- **Cumulative modules** (31 statements): the relative share of a Tower is multiplied per cell by e^{pi(beta - 1/2)/T}, constant exactly on the line; the mirror is unbounded, the low member vanishes, the pair is unbounded in cumulative terms; the pair asymmetry accumulated over the primes equals (1 - 2 beta) times a Chebyshev quantity, zero if and only if on the line; the alternating sums are geometric series (bounded on the line, divergent for the mirror). Fibre annihilator: over two consecutive cells the Tower drops out of the total, over three the pair drops out. `MemberConstancySeries.lean`, `FiberAnnihilator.lean`, `PairAsymmetryOverPrimes.lean`, `AlternatingCellSeries.lean`.
- **Arithmetic budget separation** (budget of the primes isolated from the background, which is itself bounded and negligible at line scale): `ArithmeticBudgetSeparation.lean`. **Cell-area grammar**, auxiliary: `CellAreaGrammar.lean`, `CellAreaTent.lean`, `CellAreaIntegral.lean` (the local term equals a discrepancy against the tent kernel; memory-one form; the area equals the integral of the raw demand; budget bounded by the supremum of the demand times (1 + e^{pi/T})^2 x_N).
- **Tent-and-break obligation** (the latest compiled module, section 6): `TentBreakObligation.lean`, isolated, ten statements.
- **Terminal chain**: `DemonstrationChain.lean`, conditional as stated in section 1.

### 4.2 Measured only (deterministic twins; not proofs)

Data: Odlyzko zeros up to 2,001,052; primes up to 3x10^7. Experiment folders: `experiments/E4xx_*`. Examples: exact shared prime over 2000 junctions; identities to 1e-14 over eight Towers; the lateral predictor (a measured horizon, not a theorem). A numerical superposition is never a canonical map.

### 4.3 What no compiled theorem provides

- No transport conservation law (a conservation law would itself be RH).
- No arithmetic lemma bounding the alternating budget of the primes at line scale from the primes alone (the ported PNT gives o(x), not x^{1/2}).
- No derivation of the constant relative amplitude, or of the rise of the expected frequency, from the exact reconstruction of a gap.

---

## 5. The active question

**Question (called Q475).** What new mathematical constraint does the exact reconstruction of a gap between two consecutive primes impose on the first off-line Tower, a constraint that its contacts and those of its mirror cannot satisfy? That constraint is not yet proved. It is the thing to look for, without adding geometric constructions that carry no arithmetic obligation.

**The five points of the strategy** are already compiled objects (nothing to invent): the real gap of two consecutive primes (`PrimeGapInterval`); two certain arithmetic ends; exact collective reconstruction by the true zeros; the obligation imposed on the Towers at the meeting at the shared prime (`meetingPoint = p_{n+1}`, `imposedShare`, `all_signals_meet`, `TowerRaccord`, `sharedPrime_eq_meeting`); verification on the first OFF arrival and its mirror (`OffCarrier`, `mirrorMember`).

**Audit table of the obligations at the meeting.**

| Id | Obligation | Satisfied by the OFF pair? |
|---|---|---|
| O1 | Identity of the gap: the demand of the gap is the sum of the shares of all the zeros | Yes (holds for any family of zeros) |
| O2 | No finite family closes the gap; the jump at the meeting is carried by the remainder | Yes |
| O3 | The meeting cell of a Tower contains exactly one prime; the amplitude at the meeting contact is imposed | Yes, member by member |
| O4 | Form of the pair at the shared prime: a common word (shift in {-1,0,1}), same sign if and only if same word, no compensation | Yes (it is the form of the pair) |
| O5 | Exact and unbounded price of the pair; exact transport at the shared prime | Yes (the pair pays it; no transport conservation is compiled) |
| O6 | Constant relative amplitude at the meetings | **No**: the only compiled predicate the pair violates; equivalent to being on the line by definition, not derived from the reconstruction |
| O7 | The expected frequency rises at each meeting (`ExpectedFrequencyRisesAtMeetings`) | **No**: any low arrival refutes it; it is a named hypothesis, never posed |

**Reading.** Every obligation actually derived from the reconstruction (O1 to O5) is satisfied by every family, the OFF pair included. The two predicates the pair violates (O6, O7) are statements about one member, not derived from the reconstruction. The sought constraint is therefore exactly the link O1 implies O6, member by member (the author's question P5, never attacked head-on). By its force it is a statement of the strength of RH by construction; this is not an objection.

**Compiled obstacle that fixes the form of the question.** `imposedShare_eq` and `authentic_family_reconstructs_any_radial`: no relation on the share of a single member drawn from the sole identity O1 can constrain beta. The constraint must therefore use what the grammar fixes in addition: at the shared prime, the expected minimum of the outgoing member, the occurrence of the incoming member, and the gap `occurrenceGap`.

**What the measurements at the shared prime showed (E475, verdict B).**
- M1 exact: over 2000 canonical junctions, `expectedMinimumPrime e = occurrence l = meetingPoint = p_{n+1}`.
- M2 failed by the letter; the law is recorded: the ratio of the imposed shares of the two members over the transport equals exactly (||rho_e + 1|| / ||rho_l + 1||)(Phi_l / Phi_e), Phi_w being the modulus of the gap read by the member's frequency. Over the first ten junctions it lies between 0.096 and 2.10, with median 1 and tightening toward 1 (consecutive heights are close). This is an identity, not a constraint.
- M3 sensitive, but the radial sensitivity of a pair's share is exactly cosh((beta - 1/2) log x): this is the price O5, already compiled.
- Consequence: the question posed on the shares of a gap is empty. The only place where the pair changes the arithmetic assignment is the enumeration: two members of the same height, two consecutive indices, two consecutive occurrences; the junction from the low member to the mirror at the next shared prime p_{n+2} is a detour with no compiled conservation law.

**The author's constraints on the question.**
- Never suppose that a contact of a Tower coincides with a prime; the meeting at the shared prime is defined by the real grammar of the primes, not by a triangle.
- Add no geometric construction that has no arithmetic obligation.
- Classify the cell-area results (area grammar, tent identity, alternating budget at scale x^{3/2}) as auxiliary, with no demonstrative bearing on RH; that target is out of the route.
- Frequency before height: the meeting point imposes a frequency, then a height; never go from gap to height directly.
- Do not tie the OFF contradiction to a variation of the raw demand per cell.
- Admitting an RH-equivalent target as a premise stays forbidden (section 7).

---

## 6. The latest attempt: tent and break, then shifted primes

The author's order: combine the tent (area grammar) with the break, which creates an obligation. The chain was executed in two experiments, both with a verdict B, and closed without a closure lead.

### 6.1 Tent-and-break obligation (E476)

Pre-registered before compilation (four hypotheses with numeric thresholds; twin and module written first). Module `TentBreakObligation.lean`: isolated, **ten statements**, standard axioms only, two compilation attempts (the first failed on one error, a `fract_fract` rewrite blocked because `cellFraction` was not unfolded; the second succeeded), full build green. Twin: primes up to 3x10^7, Towers = zeros number 1, 2, 3, 5, 10, 20, 100, 1000, 22 s.

**Compiled content** (valid for every real x > 0 and every beta; never "x is a prime on a contact": f is only the relative position of x among the contacts).
- H1. The weight of a break at x in the local term is Lambda(x) tent_k(x) (`localGrammarTerm_break_split`); it equals w = e^{pi/T} x (1 - e^{-pi f/T}), f the cell fraction of x (`breakTentWeight_eq`); the weight in the preceding tent and its non-negativity are also compiled.
- H2. The amplitude paid at the last contact before x is x^beta (1 - w/(e^{pi/T} x))^beta / ||rho|| (`break_amplitude_reads_tent`): the break weight in the area grammar and the amplitude paid are two readings of the same cell fraction.
- H3. In the alternating sum of local terms each break weighs (-1)^j((1 + e^{pi/T}) x - 2 C_{k+1}) (`alternating_break_weight`), a sawtooth that vanishes at the neutral point of the cell (`sawtooth_pos_iff`; `tent_difference_eq_sawtooth`).
- H4. **Obligation of the pair** (`pair_breakTentWeight_eq_iff`): the mirror gives at the same x the weight that the Tower gives if and only if beta = 1/2.

**Measured.**
- H1, H2, regrouping H3a: identities to 1e-14 over eight Towers.
- H3b (fraction of breaks with positive weight) failed by the letter on Tower 1 only (0.551 measured against 0.528 predicted); on Towers 10 and above, agreement to 0.001. Why: the prediction was written as a fraction in log measure of the cell, whereas primes are equidistributed in x; the corrected prediction is e^{pi/T}/(1 + e^{pi/T}) = 0.555, and the last cell is truncated.
- H4 failed by 11% on a badly calibrated threshold. Law measured: the median relative difference of the weights of a fictitious pair is (pi/T)(|delta|/pi) e^{-pi f/T}, namely 4.5e-4, 8.9e-4, 1.8e-3 for beta = 0.45, 0.40, 0.30; maximum 0.199, reached on the fraction |delta|/pi of primes whose word shifts by one unit (0.0021, 0.0041, 0.0081: exactly |delta|/pi).
- The interior sawtooth alone is at scale x^2 (its integral over a cell is l^3/(2 C_k) > 0): it carries the background, compensated by the tent integrals; it is not a useful object by itself.

**What the obligation is and is not.** It is compiled as a FORM: one prime, two break weights for the two members of an off-line pair. No compiled theorem forbids two weights (to distinguish is not to contradict). It localizes exactly where a law "one prime, one break weight per height" would be violated: on the fraction |delta|/pi of primes with shifted word, where the break enters the two alternating budgets with opposite signs (`pair_same_sign_iff`). No contradiction is posed; nothing is admitted.

### 6.2 Shifted primes, Tower minus mirror (E477)

The measurement proposed at the end of E476, run before any hypothesis and without a module. Pre-registered (six tests P1 to P6 with thresholds); twin 15 s; fictitious pair at the heights of zeros 1, 10, 100, beta in {0.45, 0.40, 0.30}; control beta = 1/2.

**Outcomes.**
- P2 passed. On a prime with shifted word, the difference of the alternating weights, Tower minus mirror, follows the first-order law (-1)^j (2x/T)[e^{pi/T} delta - (1 + e^{pi/T}) pi u] to 1e-3. The two alternating weights are EQUAL at first order (the parity compensates the sign of the sawtooths); the difference is first order in delta, with variable sign in the band.
- P4 passed. The restricted sum, de-alternated, is of SECOND order in delta: sum of (delta^2 (e^{pi/T} - 1)/(pi T)) l_k C_{k+1}, within a factor 1.16 to 1.31 on Tower 1. On the primes whose word is not shifted, the difference is the first-order identity -(-1)^j 2 C_{k+1}(1 - e^{-delta/T}), summed to 0.1%.
- Control passed: with beta = 1/2 there is no shifted prime and the difference is exactly 0.
- P1 failed by the letter (Tower 1, +11%): the same defect as in E476/H3b, a fraction written in log measure. Corrected law (computed after reading the twin): (1 - e^{-delta/T})/(1 - e^{-pi/T}), within 0.1 to 0.6% on Tower 1.
- P3 failed by the letter: floating-point floor (1e-10 to 3e-9) for delta/T of about 1e-6; the algebraic identity is exact (1e-12 on Tower 1).
- P5 failed, and the prediction was wrong in nature, not only in threshold: the cumulative sum is dominated by the fluctuation of the individual terms (first order in delta, variable sign), log-log slopes 1.43 to 1.88, ratio to x^{3/2} at most 3e-3. Nothing grows.
- P6: second order confirmed (on Tower 1, R constant to 13%; R times delta varies by a factor 3.5, so first order is rejected). Pre-written rule: second order means **no theorem to write** on this restriction.

**Verdict B.** The localization of E476 (primes with shifted word) carries no new obligation: no growth above x^{3/2}, no first-order mean. The two natural restrictions of the pair's weight (shifted, not shifted) are alternating and at the background scale. The tent-and-break thread (tent identity, then E476, then E477) is measured to the end with no closure lead. Nothing admitted; RH not proved.

### 6.3 Corrected laws and methodological rectifications from the chain

- The fraction of primes in a cell band is computed in x-measure, not in log measure: the fraction of breaks past the neutral point is e^{pi/T}/(1 + e^{pi/T}); the fraction of primes with shifted word is (1 - e^{-delta/T})/(1 - e^{-pi/T}), which tends to |delta|/pi as T grows.
- The 1/T scaling of the local terms is the cell length (compiled), not a cancellation.
- The two parts of the memory-one form of the local term are almost opposite (a measurement), but there is no theorem bounding the local term from the primes alone at scale x^{3/2}.
- A sum restricted to a sub-family of primes is dominated by its fluctuations before it can be read as a budget.

---

## 7. Standing rules and forbidden statements

**On what is claimed.**
- RH is never presented as proved; no conditional statement is presented as unconditional; "without hypothesis" is never written for a theorem that has hypotheses.
- Only a theorem that classifies is said to "characterize"; an equivalence with an off-line zero is a "certificate".
- A compiled theorem prevails over any text; in case of conflict the text is corrected.

**Contacts and Towers.**
- Contacts read beta exactly (through the compiled tangential inversion; the interval between contacts is defined by the frequency AND the amplitude). Never write "blind to beta", "depends only on the frequency", or "nothing radial".
- Never write that "a Tower touches a prime": no contact grid is tied to the exact position of a prime. Intervals between contacts are partial remainders of gaps, reconstructed collectively. No formula is to tie the contact grid to an exact prime.
- A Tower is exactly one zero; it is not centred on its zero; the pole of rotation (origin of the Tower plane) is not the midpoint of a mirror pair (an object of the zero plane).
- Useful range of the arrival of an OFF zero: beta at most 1/2; never "every beta in (0,1)".
- Never say "half" for the mirror symmetry: an off-line zero always comes in a square of four.

**On RH-equivalence.**
- "Equivalent to RH" is NOT an objection, a brake, or a reason not to formulate or attack a target: the project seeks RH directly, so what it formulates is RH or a form entailing it, by construction. Any older mention read as an objection is void.
- What remains forbidden, unchanged: admitting such a target as a hypothesis of a theorem (premise, axiom, `sorry`).

**Forbidden links and conclusions.**
- Never link the off-line contradiction to a variation of the raw demand (amplitude versus variation of rawDemand per cell).
- Never use or cite the conclusions of the E301 audit (declared false by the author), the naive E2M zero-to-transition correspondence, the conclusion of a spectral study in E445 (revoked), the "tail property" reading of E457 (E457 says that no predicate on a finite window of the word characterizes the selection), or "smoothed contact = arithmetic meeting" (false).
- Never read "no independent constraint found" as "frontier": nothing is declared missing that does not miss.

**Measurement hygiene.**
- Prime fractions in a cell band are always in x-measure.
- A sum restricted to a prime sub-family is read first by its fluctuations, never directly as a budget.
- "Distinguish is not contradict": a compiled form that differentiates the pair from the line is not a contradiction.

---

## 8. Next step

- Return to the active question Q475: the constraint must come from the arithmetic data of the junction at the meeting (the expected minimum of the outgoing member, the occurrence of the incoming member, the gap between occurrences), not from a restriction of the area budget. The tent-and-break thread offers no closure lead.
- The formulation proposed for the next attempt: put the obligation on the enumeration, not on the shares. Take two consecutive gaps, and three members e, then l, then l', where l' is either a higher zero (on the line) or the mirror of l (the pair); look in `localSynchronization` over the two gaps for what distinguishes the two cases, the other zeros being the same. This is the question P5 in the form O7 (frequency before height).
- No pre-registration is to be written without the author's decision on this formulation.
