# E414 — Identity of the accumulations by contacts (pre-registered on 2026-11-03, before execution)

> Français : [README.fr.md](README.fr.md)

**Question.** Is the signed accumulation of the complex VALUES of a Tower over its successive contact intervals
(boundary portions included) equal to the direct difference of its spectral contribution, zero by zero and
collectively, for the raw channel (x^ρ/ρ) and the integrated channel (x^ρ/(ρ(ρ+1)))?

**Corresponding Lean theorem (compiled before execution).** `Terminal/ContactValueGeometry.lean`:
`contact_accumulation_eq_endpoint_difference` (any F, any partition) and
`Terminal/CollectiveContactAccumulation.lean`: `finite_contact_accumulation_eq_spectral_difference`.
The numerical twin can therefore only check the identity up to rounding; an error BEYOND rounding would signal
a defect in the code, not in the mathematics.

**Data.** 2,001,052 Odlyzko heights (`data/odlyzko_zeros6_2001052.txt`, SHA-256 checked), placed on the
line (data hypothesis), multiplicity 1, two branches (2·Re).

**Protocol.** See `PROTOCOL.md`. **Results.** `RESULTS.md` (filled after execution), `data/e414_results.json`,
`logs/e414.log`.
