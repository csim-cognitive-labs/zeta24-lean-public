# E441 — The signed balance of the meetings along the series: explicit indexing of the meeting cells, what the growth of the lengths imposes on the bound, and numerical rules

> Français : [README.fr.md](README.fr.md)

Pre-registration (2026-11-07), before any compilation and any execution. Author's order: "OK settle the
next Question. In addition conduct one or more numerical experiments to determine the rules from these
experiments. Careful: define them well with the results already established in the theorems linked to the
new and old contacts." Spectral prohibition in force (§19.55); work order §19.53.

## Verification of the nine mistakes
1. No new hypothesis (the hypotheses `GapHasContact` and "the meeting is not a contact" are those
   of E439–E440, and their frequency of validity is MEASURED here). 2. The compiler decides. 3. Names checked by grep
   (`meetingSignedSum`, `signedPrimeSum`, `signedNonPrimeSum`, `signedLengthSum`, `meetingOffset` free;
   `meetingCell`, `cellPrimeWeight`, `cellNonPrimeWeight`, `cellLength`, `signedCellSum`, `meeting_cell_primes`,
   `cellPrimeWeight_inner_eq_zero`, `lt_contact_succ`, `lastContact_le`, `cell_linear_length`,
   `signed_cells_bounded_by_last` reused). 4. `lake build RHV6Fresh` after any change. 5. No prime or
   OFF tested directly: a single Tower, β = ½ fixed, heights of the Tower = Odlyzko heights (data). 6. No
   radial position. 7. No family, no sum of Towers. 8. Isolated module. 9. Intervals = partial remainders.

## Question settled
Over the series of gaps ⟨n⟩, …, ⟨n+J⟩ of ONE Tower, write the signed balance of the cells between the meeting cell of
⟨n⟩ and that of ⟨n+J⟩ with the explicit indexing of the meetings: the signed prime weight is exactly the sum over
the meetings of `(−1)^{offset of the meeting cell} · log p`, the rest of the balance is the signed non-prime weight
minus the signed descent; the signed descent has a geometric closed form (ratio `e^{π/T}`) and its bound is
bracketed by the two extreme meetings of the series and the frequency alone.

## Targeted statements (isolated module `Terminal/MeetingSignedSeries.lean`, imports `SignedCellBalance`)
- M1 `meetingOffset`, `meetingSignedSum`: offset of the meeting cell of ⟨n+j⟩ relative to that of ⟨n⟩;
  signed sum of the meetings `Σ_{j<J} (−1)^{offset_j} · log p_{n+j+1}`.
- M2 `meetingOffset_succ_pos`, `meetingOffset_mono`: the offsets increase strictly if each gap has a
  contact.
- M3 `signedPrimeSum_eq_meetings`: the signed sum of the prime weights of the cells `[m_n, m_{n+J})` is exactly
  `meetingSignedSum` (hypotheses: each gap of the series has a contact and no meeting is a contact).
- M4 `series_signed_balance`: the signed sum of the slopes over these cells = `meetingSignedSum` + signed non-prime
  weights − signed lengths.
- M5 `signedLengthSum_closed_form`: signed lengths = `L_{k₀} · (1 − (−r)^{M}) / (1 + r)`, `r = e^{π/T}` (closed
  form, no approximate bound).
- M6 `signedLengthSum_bounds_by_meetings`: the length of the last cell of the series is < `p_{n+J+1}·(r − 1)`
  and the first > `p_{n+1}·(1 − 1/r)`: the bound of the uncancelled descent is bracketed by the two extreme
  meetings and the frequency alone.
- M7 `series_balance_near_meetings`: |signed sum of the slopes − meetingSignedSum − signed non-prime weights| <
  `p_{n+J+1}·(r − 1)`.

## Numerical experiments (scripts `scripts/e441a_series_balance.py`, twin `scripts/e441b_twin_mpmath.py`)
Authorized objects only: contacts of a Tower (β = ½, T = Odlyzko height of rank 1, 100, 10³, 10⁴, 10⁵, 10⁶,
2,001,052), cells, signs `(−1)^k`, gaps, exact Λ (integer sieve), raw demand `ψ(x) − x`.
Measures (all with the compiled identities as control, 0 violations expected on the identities):
- (a) frequency of validity of the hypotheses: share of gaps with a contact; share of meetings that are contacts
  (expected 0); contacts per gap against `T·log(p'/p)/π` (compiled: difference < 1).
- (b) identity M3 on all maximal series where each gap has a contact (exact, 0 violations); in the general case
  (gaps without contact), measure of the difference and of what a cell carrying two meetings carries.
- (c) closed form M5: relative error; ratio |signed lengths| / last cell (expected: `1/(1+r)` ≈ ½ up to
  alternation); bracketing M6: 0 violations.
- (d) sign rule between consecutive meetings: share of sign changes; prediction by the parity of the
  integer nearest to `T·log(p'/p)/π` (reading by frequency, E439): measured agreement rate.
- (e) rise rule: share of meeting cells where `L ≤ log p` (B7) against the deterministic threshold
  `x* : x*(r−1) = log x*`; prediction of the threshold against the measurement.
- (f) growth of `meetingSignedSum` with J: |S_J| against `√J · log p` and against the bound `p_{n+J+1}(r−1)`;
  regime rule (where the signed weight of the meetings dominates or not the uncancelled descent).
Deterministic twin: mpmath 30 digits on a subsample (cell indices, signs, lengths, closed form).

## Protocol and criteria
Unversioned probe, at most two attempts for the final module, logs, `#print axioms`, complete build;
bounded scripts (< 10 min), `nohup`, no polling in a loop, no fabricated output.
A: contradiction; B: everything compiles and all identities at 0 violations; C: failure in two attempts. Expected: B.
The "rules" will be declared only if (i) they are read from the logs, (ii) they are consistent with a compiled statement
or explicitly designated as measurement without theorem.
