# E403 — Real sum of the deposits at the true meeting points, with the true amplitudes (2026-11-02)

> Français : [README.fr.md](README.fr.md)

## Pre-registration (written BEFORE execution)

Author's question (2026-11-02): do the claims "OFF violates no constraint of the meetings" rest on the
projection (π(x), li(x), Riemann–von Mangoldt counting) or on the true gaps and the sum of the contacts on the real
axis? Recorded answer: on the projection or on a definition of contact without amplitude. E403 makes the
comparison that had never been made, with the COMPILED smoothed channel (`smoothedRemainder`, `nontrivialZeroResidueTerm`,
module `Terminal/AmplitudeContact.lean`) and no other.

### Objects (all deterministic)
* **True gaps**: primes `p ≤ 10 000` plus the next one (1,229 gaps, same as E402), true meeting points
  `p_{n+1}`. Exact prime demand `A(x) = Σ_{m<x} Λ(m)(1 − m/x)` (sieve, no asymptotic formula), background `B(x)`
  (formula of E401/E402), zero target `Z_n = ΔA − ΔB`.
* **Zeros**: `../data/odlyzko_zeros6_2001052.txt` (SHA-256 checked), heights placed on the line (data hypothesis).
* **Deposit of a zero at the meeting point**: `d_ρ(x) = −x^ρ/(ρ(ρ+1))` (multiplicity 1), modulus `|d_ρ(x)| = x^β/(|ρ||ρ+1|)`
  (= `meetingDeposit_norm`). Contribution to the gap: `c_ρ(n) = d_ρ(p_{n+1}) − d_ρ(p_n)`.
* **Amplitude-carrying contact**: for each member of the crowd that crosses a contact `C_k` in the gap,
  amplitude `A_k = |d_ρ(C_k)|` and amplitude step `A_{k+1}/A_k`; reading `β_read = T·log(A_{k+1}/A_k)/π`
  (= `radial_from_amplitude_step`).
* **Sum of the amplitudes** (moduli) of the crowd at the meeting, `Σ|c_ρ(n)|`; signed sum `2Re Σ c_ρ(n)`.

### Synthetic twin, SEPARATE (never read as a measurement of β)
An ON zero is REPLACED by an OFF pair: the real zero of rank `j₀ = 2000` is removed from the sum, the pair
`β* = 0.3 / 0.7` is added at height `T* = (T_{2000} + T_{2001})/2` (height of no existing zero, distance
checked `> 10⁻³`). For each true gap: required complement `Δ_n = 2Re(c_pair(n) − c_{j₀}(n))`, compared
(a) to the observed residual `|R_n|` of the real reconstruction, (b) to the line-scale tail bound `eps_online`,
(c) to the unconditional bound `eps_uncond`; amplitudes `|d_{0.3}(p_{n+1})|`, `|d_{0.7}(p_{n+1})|`, `|d_{j₀}(p_{n+1})|`
and their growth with `p_{n+1}` (slope of `log|d_{0.7}/d_{0.3}|` against `log p_{n+1}`: expected exactly `0.4`).
Second twin, mpmath dps 30, on 3 gaps (first one with non-empty crowd, median, last).

### Predictions stated in advance
1. Real identity `Z_n = 2Re Σ_ρ c_ρ(n)` at the level of the data (residual ~10⁻⁷, as E402): this is `gap_demand_eq_deposits`.
2. `β_read = 0.5` on all real contacts (up to floating-point error): this is the data hypothesis, not a measurement.
   On the synthetic: `β_read = 0.3` and `0.7` exactly: the amplitude-carrying contact is NOT blind to the radial.
3. The sum of the amplitudes `Σ|c|` of the crowd is much larger than `|2Re Σ c|` (median phase share ~0.06 in E402);
   the sum of moduli is not the demand.
4. Synthetic: `Δ_n` exceeds the observed residual for most gaps (E402: 468 gaps with pair, complement
   up to 2,800× the residual); `Δ_n` exceeds neither `eps_online` nor `eps_uncond` for any gap (E402: 0/468).
   The ratio `|d_{0.7}|/|d_{0.3}|` grows like `p_{n+1}^{0.4}` (= `mirror_deposit_ratio`).
5. **No conclusion about β of the real zeros.** What the experiment can say: the real comparison (true gaps ×
   true amplitudes) distinguishes a pair from the replaced zero ONLY with respect to the observed residual, which depends on the
   completeness of the list of zeros; no compiled bound (all at exponent 1 or at line scale) distinguishes it.
   If this point 5 is contradicted, it will be recorded as is.

### Protocol
`nohup timeout 900 python3 -I e403_amplitude_meetings.py ../data/odlyzko_zeros6_2001052.txt 10000 . > e403_run.log`
(bounded < 5 min, numpy + mpmath; no fabricated output). Outputs: `e403_summary.txt`, `e403_per_gap.txt`,
`e403_contacts_chosen_gaps.txt`, `e403_synthetic.txt`, `e403_run.log`.

## Execution (2026-11-02, 103.2 s, `e403_run.log`) — results against the predictions

| # | Prediction | Result |
|---|---|---|
| 1 | real identity at the level of the data | max residual 1.44·10⁻⁷ (n = 1), median 2.1·10⁻⁹; 1229/1229 under `eps_online`; mpmath dps 30 twins: differences ≤ 2.1·10⁻¹⁴ (sums), ≤ 1.6·10⁻¹² (exact demand) |
| 2 | `β_read = 0.5` on the real (data), `0.3 / 0.7` on the synthetic | 1,655,515 crowd contacts, max difference 8.3·10⁻¹²; synthetic 0.300000000000 ± 10⁻¹², 0.700000000000 ± 2·10⁻¹²: **the amplitude-carrying contact reads the radial position** |
| 3 | sum of moduli ≫ signed sum | median phase share 0.057; sum of amplitudes at the meeting point = 103 × the demand (median); sum of moduli of the contributions = 17 × the demand |
| 4 | replacement complement > observed residual for most gaps; never > bounds; growth `p^{0.4}` | **1229/1229** gaps (not only the 468 whose crowd contains the pair: recorded, not stated in advance); complement/residual ratio up to 3.4·10⁷; `> eps_online`: 0/1229; `> eps_uncond`: 0/1229; measured slope 0.400000000000; `|d_{0.7}|/|d_{0.3}|` from 1.55 to 39.8 |
| 5 | no conclusion about β of the real zeros | held |

## Honest reading
1. The comparison requested by the author is made: true gaps on the left, sum of the deposits of all zeros at the true
   meeting points with their true amplitudes on the right. It is an identity (`gap_demand_eq_deposits`), checked
   at the level of the data.
2. The amplitude-carrying contact is not blind: on the synthetic, it returns `β* = 0.3` and `0.7` to `10⁻¹²`. On the
   real it returns `0.5` because the data place `0.5`. This is not a measurement of `β`: it is the reading of a datum.
3. Replacing an ON zero by an OFF pair changes the real sum at ALL meeting points, by an amount
   up to 3.4·10⁷ times the observed residual, and growing like `p^{0.4}`; but this amount stays under every
   compiled bound (line, exponent 1). The detector is therefore the observed residual, which depends on the completeness of the list of
   zeros; no compiled constraint on the real axis is violated by the pair. The claim "OFF violates no
   constraint of the meetings" is replaced by: "the pair changes the real sum at every meeting, and no compiled
   bound sees this change".
4. Nothing is concluded about β of the real zeros.
