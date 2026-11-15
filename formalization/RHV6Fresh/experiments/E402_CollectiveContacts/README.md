# E402 — Collective reconstruction by contacts (mission R9, §19.30) — EXECUTED on 2026-11-01

> Français : [README.fr.md](README.fr.md)

Pre-registration: master document §19.29.5 (2026-11-01, before execution), checked before launch; extension requested by
mission R9 (entry/exit phases, contacts crossed, shift at the meeting, crowd/tail/background, residual, bounds,
transitions, separate drift in β / T, separate synthetic). Author's green light: "run the experiments you need".

## Protocol (as executed)
* Script: `e402_collective_contacts.py` (numpy + mpmath), launched `nohup timeout 900 python3 -I … 10000 .`, duration 108.6 s.
* Zeros: `../data/odlyzko_zeros6_2001052.txt`, SHA-256 `2ef7b752…78e7c6` checked against `.sha256`; 2,001,052 heights,
  strictly increasing, `T_1 = 14.134725142`, `T_max = 1132490.658714411`. Data hypothesis: heights of known zeros
  placed on the line (`β = 1/2`); they do not certify the absence of OFF zeros.
* Primes: sieve, `p ≤ 10 000` plus the next one (1,229 gaps, from `[2, 3]` to `[9973, 10007]`); every crowd is in the
  data (`K_max = 16,924 < 2,001,052`).
* Channel: the compiled smoothed channel (same formula as E401, no other). Prime demand `D_n = Δ Σ_{m<x} Λ(m)(1 − m/x)`;
  background `B_n = Δ[x/2 − ζ'/ζ(0) + (ζ'/ζ)(−1)/x + Σ_j −x^{s_j}/(s_j(s_j+1))]`; zero target `Z_n = D_n − B_n`; complex
  contribution of a zero `c_ρ(n) = −(p_{n+1}^ρ − p_n^ρ)/(ρ(ρ+1))`, demand `= 2 Re Σ_ρ c_ρ(n)` (conjugates). Complex sum
  kept throughout; the sum of moduli is given only separately (phase share).
* Crowd of the gap: `T_ρ ≤ π/ℓ_n`; tail: the rest of the 2,001,052 zeros; truncation beyond `T_max` bounded
  independently of the residual: `Σ_{γ>T_max} 1/γ² ≤ 1.841·10⁻⁶` (N(T) ≤ N_up(T), Trudgian 2014, N(T_max) = 2,001,052 exact),
  `eps_uncond = 2(p_n + p_{n+1})·σ` (|x^ρ| ≤ x, any radial position of the tail), `eps_online = 2(√p_n + √p_{n+1})·σ`
  (if the tail is on the line).
* Contacts: phase `θ = T log p − arctan(T/β)` at entry and exit, contacts crossed `⌊θ_out/π⌋ − ⌊θ_in/π⌋`,
  shift of the contact at the meeting `(log p_{n+1} − log C_k)/ℓ` (quarters counted), exact meetings `log C_k = log p_{n+1}`.
* Transitions: `K_{n+1} − K_n` (windows of a fixed set).
* Drift (3 gaps × 10 zeros): `∂c/∂β = dc/dρ`, `∂c/∂T = i·dc/dρ` (analytic), `∂u_k/∂β = −1/(β²+T²)`,
  `∂u_k/∂T = β/(T(β²+T²)) − u_k/T`, `∂(π/T)/∂β = 0` exact: the two effects are separated.
* Twins: E401 (dps 30, 168 gaps) against `Z_n`; telescoping over 100 zeros; compiled identities (`|u| = 2|sin(Tℓ/2)|/T`,
  plateau `≤ ℓ`, envelope `≤ 2/T`) on the whole crowd of three gaps at two precisions; crowd sums and `A(x)` in mpmath.
* Synthetic, SEPARATE (`e402_synthetic.txt`): pair `β* = 0.3 / 0.7` at `T* = 2515.928766` (midpoint of zeros 2000 and 2001,
  height of no real zero); contributions, required complement, residual "with pair"; never read as a measurement of β.

## Results (files: `e402_summary.txt`, `e402_per_gap.txt`, `e402_members_chosen_gaps.txt`, `e402_drift.txt`, `e402_synthetic.txt`, `e402_run.log`)
| Quantity | Value |
|---|---|
| residual `R_n = Z_n − 2Re(S_crowd + S_tail)` | max 1.44·10⁻⁷ (n = 1), median 2.1·10⁻⁹ |
| `|R_n| ≤ eps_uncond` / `≤ eps_online` | 1229/1229 / 1229/1229 (eps_online from 1.2·10⁻⁵ to 7.4·10⁻⁴) |
| crowds | `K_min = 0`; 6 gaps with EMPTY crowd (ranks 0,1,2,3,5,8: threshold `π/ℓ < T_1`); `K_max = 16,924` (n = 1223) |
| share of crowd / tail in `Z_n` (medians) | 1.0003 / 0.0335 |
| phase share of the crowd `|S|/Σ|c|` | min 0.0009, median 0.057, max 1 |
| contacts crossed by the crowd | 1,655,515 in total; 7 gaps with no crowd contact at all; exact meetings: 0 |
| quarters of the gap (from the meeting) | 414,409 / 414,234 / 413,158 / 413,714 |
| transitions `K_{n+1} − K_n` | from −15,025 to +15,544; 636 increases, 587 decreases, 5 constant |
| E401 twin | max difference 4.7·10⁻¹³; telescoping 4.4·10⁻¹⁶; identities 2·10⁻¹⁶ to 1.8·10⁻¹⁵; mpmath crowds ≤ 2.1·10⁻¹⁴ |
| synthetic | 468 gaps contain the pair in their crowd; required complement from 5.8·10⁻⁷ to 4.0·10⁻⁴; **0/468 exceeds `eps_online`, 0/468 exceeds `eps_uncond`**; against the observed residual (1.4·10⁻⁷), 4.0·10⁻⁴ is 2,800 times larger |

## Honest reading
1. **Exact identity checked numerically**: the prime demand of each gap is reconstituted by the complex sum of
   all zeros (crowd + tail) plus the background, at the level of the data precision; this is `localSynchronization` (C126),
   not a new result. The phases strongly compensate in the crowd (median phase share 0.057).
2. **Results stated in advance**: huge crowds for ordinary gaps (up to 16,924 for `p ≈ 10⁴`) — but the first six
   short gaps have an EMPTY crowd (which had not been stated in advance: recorded); no contact is a
   meeting; no comparison to an average; no conclusion about β.
3. **The reconstruction defect is not a detector**: the compiled error bound (exponent 1, `collective_residual_bound`)
   and even the bound at line scale are never exceeded by the complement required by the synthetic pair
   (0/468). Only the comparison with the OBSERVED residual (which relies on the completeness of the list of zeros) distinguishes it: this is a
   numerical check, never a proof concerning the real zeros (mission §7).
4. **Nothing is concluded about β.** Rigidity of the contacts is not assumed; it is not obtained.
