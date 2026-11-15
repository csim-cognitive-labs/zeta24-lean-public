# E421 — Interleaving of contacts of different Towers on the same real axis (pre-registered 2026-11-03)

> Français : [README.fr.md](README.fr.md)

Objective: describe, without primes, gaps or whole cells, how the contacts of Towers of different heights
interleave on the real axis: number of contacts of one Tower between two consecutive contacts of another, shifts, coincidences,
and radial sensitivity of the interleaving (separate synthetic Tower, never at the height of a real zero).

Predictions (Lean module `ContactRealValue.lean`, written before execution):
* between two consecutive contacts of (β₁,T₁) there are ⌊T₂/T₁⌋ or ⌈T₂/T₁⌉ contacts of (β₂,T₂) (logarithmic steps π/T₁, π/T₂);
* exact shift: log C_j^{(2)} − log C_k^{(1)} = (φ₂ + jπ)/T₂ − (φ₁ + kπ)/T₁;
* the radial position enters only through φ(β) = arctan(T/β) ∈ (0, π/2); the displacement of a contact from β to ½ equals
  (φ(β) − φ(½))/T, of modulus < π/(2T): less than half a step; the count of contacts between two contacts of another Tower
  is therefore blind to β up to one unit, and the interleaving order can change by at most one notch per contact;
* two contacts of a mirror pair (β, 1−β) at the same height coincide if and only if β = ½ (arctan injective).
None of these predictions is read as an exclusion of OFF zeros.
