# E458 — Φ2: exact geometry of the mirror strip, B1–B4, plus B5 (fibre weight ↔ strip) (pre-registration, 2026-11-09)

> Français : [README.fr.md](README.fr.md)

Reference: `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.80 (plan Φ, step Φ2), §19.85 (validated resumption order), §19.86 (audit E460: addition of
B5). No hypothesis admitted, no axiom, no `sorry`; isolated module `RHV6Fresh/Terminal/MirrorStrip.lean`, NOT added to
`RHV6Fresh.lean`. No spectral theory. FORBIDDEN: asserting a density of the strip; only infinitude is targeted.

## Named objects (before compilation)
* `mirrorStrip β T`: set of RANKS of primes where the word of the mirror `(1 − β, T)` differs from the word of the Tower `(β, T)`
  (`towerWord` of E457);
* `zeroStrip z`: strip of a true zero.

## Statements to compile
* **B0** (orientation): on the strip the gap between the two words is exactly one in absolute value; for `β < 1/2` the word of the mirror
  equals the word of the Tower plus one on the strip, and equals it off the strip.
* **B1**: for `0 < β < 1`, `T > 0`: empty strip ⟺ `β = 1/2`.
* **B2**: infinite strip ⟺ `β ≠ 1/2`.
* **B3**: non-empty finite strip impossible; dichotomy: empty or infinite.
* **B4** (bracketing, `0 < β < 1/2`, `T > 0`): the rank `n` is in the strip ⟺ there exists an integer index `k` such that the prime
  of rank `n` lies in the left-closed, right-open interval that goes from the contact of index `k` of the mirror to the contact of the SAME
  index of the Tower; these two contacts are never confounded (the mirror strictly before) and their ratio is strictly
  smaller than half a cell (`e^{π/(2T)}`). The statement places a prime BETWEEN two contacts; it never asserts that a contact
  is a prime (§19.51).
* **B5** (fibre weight ↔ strip, without hypothesis; audit E460): for a true zero, fibre weight at its height strictly
  less than two ⟹ empty strip; non-empty strip ⟹ fibre weight at least two.
* **B6** (reformulations, NEVER posed): RH ⟺ the strip of every true zero is empty ⟺ the strip of every true zero is finite
  (this is hypothesis H-c of the plan, classified as equivalent: recorded as a reformulation).

Forecast: everything compiles; no contradiction is expected or sought; every off-line Tower, carrier or not, has the same strip:
the geometry of the strip does not carry the edge.

## Deterministic part (twin of B1, B4) — `e458_mirror_strip.py`
First 200 Odlyzko heights; primes ≤ 10⁶ (sieve); line (`β = 1/2`) and controls `β ∈ {0.3; 0.4; 0.45}` at the same heights
(control Towers, non-carriers: no off-line zero is assumed or tested). Measurements: size of the strip, first rank of
the strip; verification of B0 (gap exactly plus one on the strip) and of B4 in both directions (every prime of the strip lies in
the interval of its index; no prime off the strip lies in it). Expected, written in advance: line, size zero for the 200 heights;
controls, B0 and B4 with zero violations except cases below double-precision noise (counted separately and re-checked in
extended precision if any); strip size of the controls: reported as is, NO expectation of positivity up to 10⁶ (the theorem
gives only infinitude), no law, no density.

## Protocol
At most two attempts; unversioned `*_SCRATCH.lean` probes deleted after capture; `attempts/`; `#print axioms`; grep of the ban
at zero on the module; full `lake build RHV6Fresh` green; script once under `nohup`, output in `logs/`.
