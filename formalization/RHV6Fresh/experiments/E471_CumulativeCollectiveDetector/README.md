# E471 (Ψ5) — cumulative collective detector (support, lesson of E464/E466) — pre-registration (2026-11-13)

> Français : [README.fr.md](README.fr.md)

Supporting numerical experiment, no Lean module (the resolution law in the direct direction is S9 of E465; the converse is measured).
## Strategy (rule R-Ψ)
* Target: measure the cumulative signature of an off-line pair in the collective recomposition of the 2 001 052 zeros.
* Cumulative object: recomposition residual (sharp cut-off, without Fejér, lesson E466) on a geometric grid 10^3 → 3·10^5; then the cumulative defect required if the zero of rank 1 000 is replaced by a pair β ∈ {0.3; 0.4; 0.45} at its height.
* Why the pointwise reading is not enough: a point does not separate a pair from a line zero (E402: never above the proved bounds).
* Expected signature of an off-line zero: cumulative defect growing like x^{1/2−β}·(constant); exponent fitted on the grid expected within ±0.05 of 1/2 − β (written expectation; may be refuted).
* Continuation in both outcomes: support for Ψ1–Ψ4; proves nothing alone; an exponent measured outside ±0.05 is recorded as such.
Bounded execution under nohup (twin_psi.py, section Ψ5), versioned log.
