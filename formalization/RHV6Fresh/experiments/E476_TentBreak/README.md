# E476 — Tent and break: the obligation of the break weight (pre-registration, 2026-11-14)

> Français : [README.fr.md](README.fr.md)

Author's order: "you can use the combined method between your tent and the break, it creates an obligation; continue".
Combined objects: the tent of E474 (`tentKernel`, `localGrammarTerm_eq_tent_sum`) and the break at the prime of E447/E450
(`break_amplitude_exact`: exact amplitude of the value at the last contact before `x`, `contact_of_fraction`, `mirror_cellFraction`).

## Strategy (R-Ψ)
Cumulative doctrine. The break of the demand at a prime `q` (jump `Λ(q)`) enters the local term `L_k` with the weight
`Λ(q)·tent_k(q)` (Abel: `L_k = −∫ D·tent_k'`); the Tower pays at `q` the amplitude `q^β e^{−βπf/T}/‖ρ‖`, `f` = cell fraction of `q`.
Both are functions of the SAME fraction `f`, which is a datum of position of `q` with respect to the contacts (partial remainder of a gap,
§19.51: `q` is never assumed on a contact). The obligation: the weight of the break in the grammar of the areas is fixed by the amplitude
paid (and `β`), and the weight that the mirror gives to the SAME prime differs from that of the Tower as soon as `β ≠ 1/2`. No contradiction
is posed; the exact form is written and measured. No infinite sum taken as an object; contacts ≠ primes.

## Hypotheses (pre-written tests)
**H1 — tent weight of the break (theorems).** `breakTentWeight β T x := tentKernel β T (lastContactBefore β T x) x
= e^{π/T}·x·(1 − e^{−πf/T})` (rising branch of the cell containing `x`); preceding tent `tentKernel (k−1) x = x(e^{π/T}e^{−πf/T} − 1)`.
Twin: relative residual < 1e-10 on all primes of all cells.
**H2 — the break reads the tent (theorem).** `|v_β(k(x))| = x^β (1 − w/(e^{π/T}x))^β / ‖ρ‖`, `w = breakTentWeight`: the amplitude paid by the
Tower at the prime is a function of the weight of this prime in its grammar. Twin: relative residual < 1e-10.
**H3 — sawtooth of the alternating budget (theorems + grouping test).** A prime `x` in the cell `k` belongs to two tents
(`k−1` and `k`); in the alternating sum of the local terms its weight is `(−1)^j·((1+e^{π/T})x − 2C_{k+1})`, zero at the neutral point
`f₀ = (T/π)·log(2e^{π/T}/(1+e^{π/T}))`, negative before, positive after. Compiled: `tent_difference_eq_sawtooth`, `alternating_break_weight`,
`sawtooth_pos_iff`. Twin: (a) grouping `Σ_{n<N}(−1)^n L_{k₀+n} = Σ_q Λ(q)(−1)^{j(q)} saw(q) + edges − Σ(−1)^n ∫tent` to 1e-9 relative
(identity to be compiled next if it passes); (b) fraction of primes with positive weight = `1 − f₀` within 0.02 for Towers with ≥ 10⁴ primes.
**H4 — obligation of the pair (theorem).** `breakTentWeight (1−β) T x = breakTentWeight β T x ⟺ β = 1/2` (for `0<β<1`, `T>0`, `x>0`):
the mirror never gives the shared prime the weight the Tower gives it, except on the line. Twin: for the fictitious pair at `T_1`,
median relative difference `|w(1−β) − w(β)|/(e^{π/T}x)` < 1e-12 at `β = 1/2`, > 1e-3 at `β = 0.40`.

## Modules and data
Isolated module `RHV6Fresh/Terminal/TentBreakObligation.lean` (imports `CellAreaTent`, `PairBreakAtPrime`; NOT added to `RHV6Fresh.lean`);
two attempts max (`attempts/`). Twin `twin_e476.py`: primes ≤ 3·10^7, Towers = zeros no. 1, 2, 3, 5, 10, 20, 100, 1000, `β = 1/2`,
cells with `C_k ≥ 1000`. TDD order: twin and compilation launched in parallel after this commit; verdict on both.

## Verdicts
A: H1–H4 passed and module green. B: module green, a twin test fails by the letter (recorded). C: module red after two attempts.
No verdict concludes on RH; R-RH; nothing admitted.
