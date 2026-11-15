# E429 — The meeting points handled by the contacts: radial reading at the meetings, value at the meeting from the last contact, break residual to absorb over a series (pre-registered 2026-11-04)

> Français : [README.fr.md](README.fr.md)

Context: revision requested by the author (2026-11-04). The contacts are **not blind to the radial**: two consecutive contacts
return the frequency and then the radial position (`inversion_from_consecutive_contacts`,
`radial_of_contact_value_ratio`, `radial_of_contact_tangent`, `radial_from_amplitude_step`). E428 had shown
"frequency alone" only for the integer of cells; this conclusion does not extend to the contacts. E429 starts from this fact
and confronts it with the **meeting points** (end of a prime gap, §19) and the **breaks** (exact deposit at each
meeting). Directives: series of gaps, never an isolated gap; contacts, frequency, phase, amplitude, meetings and
breaks at the core; no OFF hypothesis posed; no anticipated contradiction; deterministic twin; criteria fixed
here, never modified afterwards; synthetic Towers never at the heights of a real zero when inserted into the
authentic family.

Lean module compiled BEFORE execution: `Terminal/MeetingContactReading.lean` (isolated, not added to `RHV6Fresh.lean`,
25 declarations, no `sorry`, no hypothesis). **Three compilation attempts** logged
(`logs/lean_attempt{1,2,3}.log`): the limit of two is exceeded by one, declared here; the third
fixes only a superfluous tactic (`ring` after a `field_simp` that had already closed the goal) and overly long lines.

## Objects reused (never rebuilt)
`stagePosition`, `cellIndexAt` (FirstExceedanceRaccord, CellRestitution); `contactAt`, `towerPhase`,
`accumulationFrom`, `contact_accumulation_eq_endpoint_difference` (ContactValueGeometry); `contactRealValue`,
`radial_of_contact_value_ratio`, `radial_of_contact_tangent`, `mirror_contacts_coincide_iff` (ContactRealValue);
`towerRe`, `slowMeetingLog`, `fastMeetingLog`, `unit_difference` (TowerMeetings); `mirrorPhaseShift`,
`mirror_stagePosition_difference`, `stagePosition_sub` (ContactSeriesReading); `meetingDeposit_norm`,
`mirror_deposit_ratio` (AmplitudeContact); `background_psi1`, `sum_integrated`, `sieve_lambda`
(`E414/scripts/contact_common.py`).

## Compiled predictions that the measurement must recover (statements of the module)
* **P1** `lastContact_le`, `lt_contact_succ`: `C_k ≤ x < C_{k+1}`, `k = ⌊stagePosition⌋`; `log_div_lastContact`:
  `log(x/C_k) = πf/T`, `f = fract(stagePosition) ∈ [0,1)`.
* **P2** `towerRe_from_lastContact`: `Re Tower(x) = v_k·(x/C_k)^β·cos(πf)`; `growth_factor_eq`: `(x/C_k)^β = e^{βπf/T}`.
  The position `C_k` and the value `v_k` read `β`; the fraction `f` reads the frequency; the growth reads `β`.
* **P3** `radialReadingAt_eq`: the reading at the two contacts enclosing a meeting equals `β`;
  `radial_of_meeting_value`: away from the zeros of the trajectory, `β` is read on the value at the meeting and the
  value at the last contact.
* **P4** `mirror_readings_sum_one`: Tower + mirror read `1`; `meetingReadingsAgree_iff_line`: coincidence ⟺ line;
  `mirror_stage_shift_ne_zero`: off the line, the cell fractions of Tower/mirror are shifted by a nonzero constant.
* **P5** `lastContact_difference_bounds`: the number of contacts between two meetings differs from `T·log(q/p)/π` by
  less than one unit, any `β`; `cellIndexAt_le_lastContactBefore`: pivot ≤ last contact.
* **P6** `meetingValueDeposit_eq_accumulation`: deposit over a gap = accumulation over the own contacts;
  `breakResidual_erase`, `breakResidual_erase_pair`: removing a Tower (a pair) adds exactly its value
  (the sum of the two) to the residual that the others must deposit.

## Data
Zeros `experiments/data/odlyzko_zeros6_2001052.txt` (SHA-256 checked); primes by sieve (exact integers);
meeting points = primes of ranks 2..2001 (`5 ≤ p ≤ 17,393`), series of lengths 12, 120, 1,200 from
the anchors 5, 541, 7,919. Authentic Towers: zeros of ranks 1, 10, 100, 1,000, 10,000, 100,000, 1,000,000,
2,001,052 (β = ½). Separation Towers (E429(a) only, comparison at the same frequency): same heights,
β ∈ {0.3; 0.7} in mirror pair. Pairs inserted into the authentic family (E429(b), (c)): synthetic heights
`T_s = 17.5` and `T_s' = 23.0` (between zeros 1–2 and 2–3, never a real height), β ∈ {0.3; 0.7}, and control pair
**on the line** (β = ½, two Towers) at the same synthetic heights.

## E429(a) — radial reading and value at the meeting points (`scripts/e429a_meeting_readings.py`)
For each Tower (8 ranks × β ∈ {0.5; 0.3; 0.7}) and each meeting point `p` (2,000 events):
last contact `k`, fraction `f`, bracketing `C_k ≤ p < C_{k+1}` (P1); direct value `Re Tower(p)` against
`v_k·(p/C_k)^β·cos(πf)` and growth factor (P2); radial reading at the two enclosing contacts, tangential
reading at the last contact, reading on the value at the meeting when `f > 0.05` and `|cos πf| > 0.05` (P3);
sum Tower + mirror, difference Tower − mirror (P4: `0` on the line, `1 − 2β` off the line); cell fractions at the
meeting: 10-class histogram per Tower, Tower/mirror shift measured against `(φ_β − φ_{1−β})/π` modulo 1;
number of contacts between consecutive meetings against `T·log(q/p)/π` (P5), fraction of gaps where this number
differs between β = 0.3 and β = ½ (radial information of the count, measured with no expectation); pivot ≤ last contact
and fraction of equality.
Criteria: (i) P1, P5, pivot: **0 violations**; (ii) P2, P3, P4: relative error ≤ 10⁻⁹ (identities); otherwise a
compiled statement is contradicted by the measurement and the error is to be located (never masked); (iii) histograms and
radial fraction of the count: measures recorded, no expectation.
Twin: mpmath 30 digits, zeros of ranks 1 and 2,001,052, β ∈ {0.5; 0.3}, first 10 meeting points
(`k`, `f`, value, radial reading); numpy agreement required (identical integers, reals to 10⁻¹⁰).

## E429(b) — break residual and absorption over a series (`scripts/e429b_break_absorption.py`)
Exact smoothed channel (the only one where the break is computable without limit): `ψ₁(x) = Σ_{n≤x} Λ(n)(x − n)` (sieve,
exact); authentic family `F_H` = zeros of height ≤ 1,000 (β = ½, conjugates counted), contribution of the Tower
`−2Re[x^{ρ+1}/(ρ(ρ+1))]`, background `background_psi1`. Over the 2,000 consecutive gaps of the series:
1. **Truncation residual** per gap: `ε_j = [ψ₁(p_{j+1}) − ψ₁(p_j)] − [ψ̂₁,H(p_{j+1}) − ψ̂₁,H(p_j)]` (baseline,
   measurement); identity `breakResidual_erase` checked numerically (removing the Tower of zero 1: residual + its value,
   10⁻¹⁰).
2. **Radial reading at the meetings on the smoothed channel**: for each Tower of `F_H` and each meeting, modulus of
   the contribution at `p_{j+1}` over modulus at `p_j` against `(p_{j+1}/p_j)^{β+1}` (consequence of `meetingDeposit_norm`,
   β read = `log(ratio)/log(p_{j+1}/p_j) − 1`): error ≤ 10⁻⁹ expected (identity).
3. **Insertion** of an off-line pair `(0.3; 0.7)` at `T_s = 17.5`, of a second at `T_s' = 23.0`, and of the control pair
   on the line `(½, ½)` at `T_s`: deposit of the pair per gap `d_j` (= sum of the two values, identity
   `breakResidual_erase_pair`); share of the pair: `|d_j|` relative to `|exact break|` and to the sum of the
   `|deposits|` of `F_H`; fraction of gaps where `|d_j|` exceeds the exact break, for OFF and control.
4. **Absorption cost (Obligations One and Two)**: free real weights `a_i` on the Towers of `F_H`,
   system `Σ_i a_i·d_{ij} = d_j` over the first `m` gaps of the series, `m ∈ {12, 120, 600, 1,200, 2,000}`;
   minimal-norm solution (SVD, `lstsq`); recorded: `‖a‖₂`, `max|a_i|`, relative residual. **Ill-posed, declared**:
   for `m < |F_H|` (≈ 649) an exact solution always exists; the measurement is the **cost**, not the possibility.
   Control: same computation for the pair on the line. Pre-registered criterion for Obligation Two (local version):
   the ratio `‖a_OFF‖₂ / ‖a_control‖₂` **grows** from `m = 12` to `m = 600`; if it does not grow, the local reading
   "the off-line amplitude step exceeds what a finite on-line family absorbs" is not supported under
   truncation and is recorded as negative.
5. **Obligation Three**: the two off-line pairs (`T_s`, `T_s'`): cancellation ratio
   `c_j = |A_j + B_j| / (|A_j| + |B_j|)` at the 2,000 meetings; fraction `c_j < 0.1`; longest run of consecutive meetings
   with `c_j < 0.1`; absorption cost of A by B alone (one free scalar, relative residual).
   Compiled prediction confronted: the unit cancellations of two Towers fall on the slow and fast lattices
   (`slowMeetingLog`, `fastMeetingLog`); measurement: distance (as a fraction of a cell of the higher Tower) of the
   meetings with `c_j < 0.1` to the nearest lattice, against the same distance for all meetings.
   Criterion: a "mutual payment" is declared only if a run of at least 12 consecutive meetings has
   `c_j < 0.1`; expected: none (the slow and fast lattices are isolated points).
Twin: mpmath 30 digits on the first 10 gaps: exact `ψ₁`, deposits of the pairs, one residual `ε_j` (zeros of
height ≤ 100 only for the twin); numpy agreement to 10⁻⁸ relative required on the deposits, recorded on `ε_j`.

## Verdict on three levels (criteria fixed)
* **Identities (P1–P6, radial reading at the meetings)**: succeeded ⟺ 0 violations and errors ≤ 10⁻⁹; otherwise error
  recorded and located.
* **Obligation Two (absorption cost)**: supported under truncation ⟺ growth criterion of point 4; otherwise negative.
* **Obligation Three (mutual payment)**: negative expected ⟺ no run of 12 cancelled meetings; a run
  found would be recorded without interpretation.
* **Obligation One** (does the exact break force the coincidence of the readings?): **not decidable by this
  experiment** (finite family, truncation); E429 provides only the orders of magnitude of the residual to absorb and
  the cost; this is stated before execution.
Bounded protocol: `nohup`, output `logs/`, results `data/*.json`, no fabricated output.
