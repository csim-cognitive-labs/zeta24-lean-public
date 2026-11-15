# E445 — The Price Theorem at the meeting point: pre-registration (copy of §19.65, 2026-11-07)

> Français : [README.fr.md](README.fr.md)

### 19.65 Author's attack plan (2026-11-07): the Price Theorem at the meeting point — pre-registration of E445

**Order.** Chain: `(β, T)` → contacts → amplitudes and fractions → signed balance of the meetings → arithmetic
junction. The builds E441–E443 establish real properties of the cells and the meetings but do not prove that the
radial position has no effect; the acquired inversion theorems make this exclusion unjustified. Priority track:
(1) the factor `x^{β−1/2}` is exactly the radial amplitude gap between an OFF Tower and an ON Tower; (2) for
`β < 1/2` it decreases, that of the mirror `x^{1/2−β}` increases; (3) the contacts return `β` and `T` exactly: the
gap is identifiable; (4) at the meeting point the amplitude is imposed by the zero; (5) the Price Theorem must
quantify the exact cost of this difference at the junction; (6) the signed balance preserves phases, signs and
amplitudes of the two members; (7) the complete constellation realizes exactly the arithmetic break: this is the
collective budget; (8) an exact and finite budget at each meeting is not a uniform bound; (9) the contradiction
requires that the other contributions cannot satisfy both the budget and the OFF price at once; (10) prove the
incompatibility. Requirement: at least three closure attempts, one of them free, exact error and compiler requests
logged. Amendment recorded in `CLAUDE.md` (private research repository): the constellation enters only at the
confrontation step (7)–(10).

**E445 pre-registration (`experiments/E445_MeetingPrice/`).** Isolated module `Terminal/MeetingPriceTheorem.lean`
(compilable part, one Tower and the pair `(β, T)`, `(1−β, T)` in real amplitudes): P1 `offPrice β x =
cosh((β−1/2) log x)` and `x^β + x^{1−β} = 2 x^{1/2} · offPrice` (exact price of the pair against two ON Towers); P2
`offPrice ≥ 1 + ((β−1/2) log x)²/2`, unbounded as soon as `β ≠ 1/2`; P3 price identified by the values at the
meetings (`radial_of_meeting_values`); P4 amplitude imposed at the meeting cell: `p^β e^{−βπ/T}/‖ρ‖ < |v| ≤ p^β/‖ρ‖`;
P5 answer to the §19.64 question: `|valueCellSum| ≤ |v_last| · D · q/(q−1)` (`q = e^{βπ/T}`) if all cell slopes are
bounded by `D`; P6 the price beats the budget of one meeting: `K log x < x^r` for large `x` (`r > 0`).
**Three closure attempts** (trial files kept in `attempts/*.lean.txt` with the exact compiler output): T1 price
against budget at one meeting via `complement_break_lower_bound` (E435); T2 weighted balance of the series (P5) of the
two members against the cumulative budget (Chebyshev `ψ ≤ (log 4 + 4) x`); T3 free: internal non-compensation of
the mirror + unbounded price + break carried by the complement. Criterion: A if `False` compiles without new
hypothesis; otherwise record the exact statement the compiler demands and its status in the corpus (⟺ RH or not).
Numerical experiment: price and budget at the meetings for witness `β` ∈ {0.3; 0.4; 0.45}, bounds P4–P5 on the seven
real Towers, mpmath twin.

**Revocation (2026-11-07, §19.67)**: the amendment "constellation at the confrontation step" is cancelled; T1 and T3
and their conclusions are cancelled (spectral study); see `RESULTS.md`, section "Revocation".
