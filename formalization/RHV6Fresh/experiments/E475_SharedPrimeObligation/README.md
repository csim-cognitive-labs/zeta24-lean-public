# E475 — Measurements M1–M3 at the meeting at the shared prime (pre-registration, 2026-11-14)

> Français : [README.fr.md](README.fr.md)

Author's order (§19.108): look for the constraint that the exact reconstruction of a gap imposes on the first OFF Tower at the shared prime,
without geometric construction lacking an arithmetic obligation; never a contact/prime coincidence. Prior audit:
`AUDIT_20261114.md` (table O1–O7, question Q475). Here: MEASUREMENTS only, no Lean module, no contradiction hypothesis.

## Strategy (R-Ψ)
Compiled objects reproduced identically in the twin (definitions, not approximations):
- `canonicalMember n` = upper member preceded by exactly `n` members (zero number `n+1` by increasing height);
- `occurrence z = fnPrimeAtRank (nZeroSourceIndex z)`; `expectedMinimumPrime z = fnPrimeAtRank (index + 1)`; `fnPrimeAtRank 0 = 2`;
- junction `e = canonicalMember n → l = canonicalMember (n+1)` at the shared prime `M = expectedMinimumPrime e = occurrence l`;
- `meetingPoint ⟨n⟩ = fnPrimeAtRank (n+1)`; `sharedPrime_eq_meeting : M = meetingPoint (occurrenceGap e)`;
- `imposedShare w I = memberJoint σ_w (meetingPoint I) − memberJoint σ_w I.lower`, with
  `memberJoint σ x = −m · (x^β/N) · exp(i(T log x − θ))`, `N = ‖ρ‖·‖ρ+1‖`, `θ = arctan(T/β) + arctan(T/(β+1))` (`imposedShare_at_meeting`);
- `energyRatio e l q = ‖zeroTerm l q‖/‖zeroTerm e q‖ = q^{β_l−β_e}·‖ρ_e‖/‖ρ_l‖` (`energyRatio_eq`);
- `pairJoint l x = memberJoint l x + memberJoint (mirrorMember l) x` (M3, fictitious pair `(β,T_l)`, `(1−β,T_l)`).
Data: Odlyzko zeros (`experiments/data/odlyzko_zeros6_2001052.txt`, `β = 1/2`, multiplicity 1: computational hypothesis recorded,
never a Lean premise), primes by sieve. Junctions `n = 0 … 1999` (detailed measurements on the first ten).

## Measurements and thresholds (written BEFORE execution)
**M1** — For `n = 0 … 1999`: `M_n = p_{n+1}` computed by the two definitions (`expectedMinimumPrime e`, `occurrence l`) and compared with
`meetingPoint ⟨n⟩`. Test: exact integer equality everywhere (this point is a compiled theorem; the twin verifies the indexing).
**M2** — For each `n`: `s_e = imposedShare e ⟨n⟩`, `s_l = imposedShare l ⟨n⟩` (compiled formula), ratio `r_n = |s_l|/|s_e|`, and
transport `E_n = energyRatio e l M_n` (on the line `‖ρ_e‖/‖ρ_l‖`). Identity control: `|s_w|` against the closed form
`(m/N_w)·|p_{n+1}^{1/2} e^{iT_w log p_{n+1}} − p_n^{1/2} e^{iT_w log p_n}|` (residual < 1e-12). Main test: `|r_n/E_n − 1| < 1e-6` on the
first ten junctions. If it fails: record the exact decomposition `r_n/E_n = (‖ρ_e+1‖/‖ρ_l+1‖)·(Φ_l/Φ_e)` with `Φ_w = |p_{n+1}^{1/2}
e^{iT_w log p_{n+1}} − p_n^{1/2} e^{iT_w log p_n}|` (phase factor of the gap read by the frequency of the member), and the law of `Φ_l/Φ_e` in `n`
(median, quartiles, by slices of 200 junctions).
**M3** — Radial sensitivity control: at the member `l`, substitute the fictitious pair `(β, T_l)`, `(1−β, T_l)` for `β ∈ {0.30; 0.40;
0.45; 0.50}`; measure `|pairShare|/|s_e|` and its relative variation with respect to `β = 1/2` (where the pair equals `2 s_l`). Test: relative
variation > 1e-3 for `β = 0.40` on at least one of the first ten junctions ⟹ "sensitive"; otherwise "insensitive" (the relation would fall under
O1–O5 and would not be the constraint).

## Verdicts
A: M1 exact, M2 < 1e-6, M3 sensitive. B: M1 exact, M2 fails but law recorded, M3 any. C: M1 fails (wrong indexing).
No verdict concludes on RH; nothing is declared missing that is not missing; R-RH.
