# E456 — K6: contact shift at the same height, audit of the "transitions modulo 6" text, ON/OFF causality (pre-registration, 2026-11-08)

> Français : [README.fr.md](README.fr.md)

Reference: `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.79. Author's questions: (Q1) "if something is assigned to β, T
suffers from it" at the targeted same height; (Q2) "the OFF are perhaps necessary at large heights to realize the
break"; (Q3) correct the pasted text on the four transitions modulo 6 and conduct ON/OFF causality studies; (Q4) is the
distribution of the transitions Gaussian?

## Audit (before execution) — §19.79.2
* Q1 already studied: `gap_reading_height_only`, `windingContact_lt_of_radial_lt`, `windingContact_sameHeight`, `contact_eq_iff_phase`,
  `contact_radial_formula`, `tower_eq_of_same_word`. Compilable without hypothesis: no shared contact at the same height (all indices);
  common meeting ⟹ different heights; shift < half-cell; cell ratio blind to β. → K6.
* Q2: the sentence "high frequencies ⟹ break" comes from the summation channel (E404/E408), forbidden; authorized form compiled for
  every Tower: `log_ratio_ge_cell_of_meeting`, `two_consecutive_contacts_finite`; resolving power = T alone.
* Q3: the text = E427 altered; errors e1–e5 (§19.79.2); compiled: `card_validWords_twelve`, `orientedBalance_abs_le_one`,
  `eventOrientation_of_gap`.
* Q4: finite support of thirteen values ⟹ not Gaussian; shifted binomial expected; approximate normal at long windows.

## Lean part
`RHV6Fresh/Terminal/SameHeightContactShift.lean`, isolated, M1–M5 (§19.79.3). No amplitude, no hypothesis.

## Deterministic part
`e456_causal_mod6_contact_shift.py`: P1 twin of K6; P2 recount and exact enumeration; P3 Gauss; P4 intervention on β at fixed T
and on T at fixed β. Data: `experiments/data/odlyzko_zeros1_first5000.txt`; primes ≤ 10⁶ by sieve.

## Expected answers (recorded in advance)
P1 exact; P2 counts of the text inconsistent, |τ15 − τ51| ≤ 1, shares B + C + D = 1; P3 shifted binomial, not Gaussian at twelve;
P4 high but not total overlap, mod 6 composition identical up to noise, zero contingency, T changes everything. No OFF
contradiction expected.

## Protocol
At most two Lean attempts, unversioned scratch probes, outputs captured in `attempts/`; grep of the ban before build;
full `lake build RHV6Fresh` after the green attempt; script run once under `nohup`, output in `logs/`.
