# E467 (Ψ1) — member constancy as a series law — pre-registration (2026-11-13)

> Français : [README.fr.md](README.fr.md)

Module `Terminal/MemberConstancySeries.lean` (isolated). Plan Ψ §19.100, target H3 validated by the author. Commit BEFORE compilation; at most two
attempts, exact log in `attempts/`.
## Strategy (rule R-Ψ)
* Target: the relative share of a realized Tower stays bounded along the series of its cells (⟺ line, R-RH: not an objection).
* Cumulative object: sequence of cell shares (E463) relative to the scale of the line x^{3/2}, composed over N cells.
* Why the pointwise reading is not enough: on a cell the share is non-zero for every realized Tower and nothing more; the cell factor had never been composed.
* Expected signature of an off-line zero: geometric growth of the relative share of the mirror, ratio e^{π(β−1/2)/T} per cell, A^{β−1/2} over a range of factor A; the low member vanishes; the pair is unbounded.
* Continuation in both outcomes: if everything compiles: primes side by Ψ2; otherwise record the statement demanded by the compiler and move to Ψ3 (independent).
## Statements (C1–C7): see the header of the module. Expected: all compile, standard axioms.
## Twin (twin_psi.py, section Ψ1): first 20 real Towers, 2 000 cells, relative share constant to 10^-12; witness pair
0.4 / 0.6 at the height of zero 1 000: measured growth against the closed form (relative error < 10^-10). Verdict A if everything conforms.
