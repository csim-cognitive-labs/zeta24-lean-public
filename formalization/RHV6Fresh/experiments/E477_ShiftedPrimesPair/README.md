# E477 — Alternating break weights, Tower minus mirror, on the primes with shifted word (pre-registration, 2026-11-14)

> Français : [README.fr.md](README.fr.md)

Sequel ordered by "continue" after E476 (§19.110): measurement proposed at the end of E476, executed BEFORE any hypothesis and without module.
Objects: `alternating_break_weight` (weight `(−1)^j·saw(q)`, `saw = (1+e^{π/T})x − 2C_{k+1}`, E476), `mirror_cellFraction` and
`mirrorWordShift` (E450/E452: the word of the mirror is shifted by one unit on a fraction `|δ|/π` of the reals, `δ = φ_β − φ_{1−β}`),
`pair_same_sign_iff` (same sign in the two alternating budgets ⟺ same word). No contact/prime coincidence (§19.51); fictitious pair
(no off-line zero known); real contacts of the Tower `(β, T)` and of the mirror `(1−β, T)`.

## Strategy (R-Ψ)
Cumulative doctrine. E476 localized the place where a law "one prime, one break weight per height" would be violated by the pair:
the primes with shifted word, where the break enters the two alternating budgets with opposite signs. Before looking for a theorem,
the order of magnitude of this effect in `δ` and its scale in `x` are measured. Prior computation (recorded here to be tested, not admitted):
in the shifted band `u = 1 − f ∈ (0, |δ|/π]`, `saw_β ≈ (e^{π/T}−1)·x > 0` and `saw_{1−β} ≈ −(e^{π/T}−1)·x < 0`; the parities differ by one
unit; the two ALTERNATING weights are therefore equal to first order and their difference is `D = (−1)^j·(2x/T)·[e^{π/T}δ − (1+e^{π/T})πu] + O((δ/T)²·x)`,
with mean `(δ/T)(e^{π/T}−1)·x` over the band. The sum restricted per cell would then be of SECOND order in `δ`: `S_k ≈ (−1)^j·(δ²(e^{π/T}−1)/(πT))·ℓ_k·C_{k+1}`
(mass of `Λ` on the band `= (|δ|/π)·ℓ_k`, PNT ported). If the measurement confirms second order, there is no theorem to write on
this restriction: the localization of E476 carries an alternating effect at background scale (`x²`, constant `δ²`). If the measurement gives first
order, write the theorem (sum of `Λ` over a fixed fraction of the cells) before any hypothesis. Nothing admitted; R-RH.

## Hypotheses (pre-written tests; fictitious pair at `T_1`, `T_10`, `T_100`; `β ∈ {0.45; 0.40; 0.30}`; witness `β = 1/2`)
**P1 — shifted fraction.** Mass of `Λ` of the primes with shifted word over the complete cells, relative to the total mass, `= |δ|/π` within 5 %
relative (measure `x`, last truncated cell excluded).
**P2 — first-order law on the shifted primes.** `D = alt_β − alt_{1−β}`; median of `|D − D_lin|/(x|δ|/T) ≤ 0.1` with
`D_lin = (−1)^j(2x/T)[e^{π/T}δ − (1+e^{π/T})πu]`; and median of `|D|/(x|δ|/T)` in `[0.2; 3]`.
**P3 — identity on the unshifted primes.** `alt_β − alt_{1−β} = (−1)^{j+1}·2C_{k+1}(1 − e^{−δ/T})` exactly (same word, same parity):
relative residual < 1e-10.
**P4 — order in `δ` of the restricted sum, de-alternated.** `R = Σ_k (−1)^{j_k} S_k / Σ_k (δ²(e^{π/T}−1)/(πT))·ℓ_k·C_{k+1}`; `R ∈ [0.5; 2]` for `T_1`
(all `β`), `R ∈ [0.3; 3]` for `T_10`; `T_100` reported without test (fewer than a thousand shifted primes).
**P5 — scale in `x`.** Restricted sum cumulated over an even number of cells `S_pair(X)`: `|S_pair(X)| ≤ 3·(δ²(e^{π/T}−1)²/(πT))·X²` (bounded by
the last two cells); log-log slope of `|S_pair|` against `X` on the even endpoints `≥ 1.7` (background scale, not `x^{3/2}`).
**P6 — decision.** `R(β)` constant within 30 % between `β = 0.45; 0.40; 0.30` ⟹ second order confirmed, no theorem; `R·|δ|` constant ⟹ first
order, write the theorem. Witness `β = 1/2`: no shifted prime, `D = 0`.

## Data and execution
Twin `twin_e477.py`: primes ≤ 3·10^7, cells with `C_k ≥ 1000`, Odlyzko zeros; output `twin_results.json`, log `logs_twin_run.txt`.
No Lean module in this experiment (measurement before hypothesis); `attempts/` empty.

## Verdicts
A: P1–P5 passed (P6 recorded whatever it is). B: a test fails by the letter (measured law recorded). No verdict concludes on RH.
