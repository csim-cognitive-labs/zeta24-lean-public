# E400 — Deterministic twin of the numbers in the pasted "three Towers" text (2026-11-01)

> Français : [README.fr.md](README.fr.md)

Purpose: verify, with no model and no statistics, the contacts `C_0…C_10` of the first three zeros and their contributions
per prime gap (raw channel `−2 Re((p_{n+1}^ρ − p_n^ρ)/ρ)`, counting channel `J` by difference of `Ei`, compiled smoothed
channel `−2 Re((p_{n+1}^ρ − p_n^ρ)/(ρ(ρ+1)))`) on the eleven gaps from 2–3 to 31–37. mpmath, 30 digits, 3 certified zeros
(`FirstThreeZerosCertified`), no synthetic zero, no window, no average. Duration < 1 s.

Result: contacts and contributions identical to the pasted text (ten and seven displayed digits). Scope: characterizes three
exact contributions; constrains nothing (`no_finite_family_accomplishes_demand`). See
`AUDIT_REORIENTATION_CONTACTS_ECARTS_20261101.md` §2.
