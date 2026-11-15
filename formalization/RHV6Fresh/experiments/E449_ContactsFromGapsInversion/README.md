# E449 — The inverse path: from prime gaps to the contacts, then to the zero through the tangential formula (pre-registration, §19.71, 2026-11-08)

> Français : [README.fr.md](README.fr.md)

New priority of the author (2026-11-08): "Reconstruct the contacts from the prime gaps exactly with all the
established rules. Recover the zeros on the critical line for now if necessary… the tangential formula recovers β and
T of the zero if you have established the contact correctly. Inverse path: gaps / breaks / zeros. All the necessary
experiments and the corresponding Lean if you find something (root cause and not a finding)."
Orders maintained: total spectral ban; third order (the contacts read β, frequency AND amplitude); no search for an
OFF contradiction; one Tower at a time.

## What the established rules say about the contacts in the gaps (compiled, E436–E448)
A prime `p` falls in the cell `k(p) = ⌊(T·log p − φ)/π⌋` (`lastContactBefore`), `φ = arctan(T/β)` the tangential
phase (`towerPhase`); the break `log p` is paid by the last contact `C_{k(p)} = p·e^{−π f(p)/T}` (E447); from one
prime to the next the cell advances by the exact displacement R1 (E442) and the fraction follows the orbit of E448.
The **word** of a Tower on the primes is the sequence `k(p_n)` (equivalently: the displacements, that is, how many
contacts each gap contains). Inverse question: does the word determine the Tower, and by what cause?

## Hypotheses (to be decided by the compiler, then by the numbers)
* H1 (tangential formula, exact inversion from two contacts): `T = π / log(C_{k+1}/C_k)` and
  `φ = T·log C_k − kπ`, then `β = T / tan φ`: two consecutive contacts return `(β, T)` exactly.
* H2 (bracketing by the word): for every `x`, `T·log x − π(k(x)+1) < φ ≤ T·log x − π·k(x)`; each prime brackets the
  phase in a window of width `π`; the word on the primes brackets `(T, φ)` in a convex polygon.
* H3 (frequency first): `k(x)/log x → T/π`: the slope of the word returns the frequency, without amplitude.
* H4 (cause: the logarithmic gaps vanish, PNT ported): the cell fraction at the primes approaches `0` and `1`
  as closely as desired (`∀ ε, ∃ n, f(p_n) < ε` and `∃ n, f(p_n) > 1 − ε`), because the steps of the orbit
  `T·log(p_{n+1}/p_n)/π` tend to `0` (`logGapsVanish_holds`) while the stage position is unbounded: at each
  crossing of an integer by a small step, the fraction is small just after and close to `1` just before.
* H5 (the word determines the phase, then β): the polygon of H2 reduces to a point: `φ = inf_n (T·log p_n − π·k(p_n))`;
  two Towers with the same word on all the primes have the same `T`, the same `φ`, hence the same `β` (tangential
  formula, `β > 0`).
* H6 (what the word does not do, to be recorded honestly): H1–H5 hold for EVERY Tower `(β, T)`, zero or not; the
  inverse path returns the Tower whose word we have, it does not say at this stage why this word is that of a zero.

## Planned statements (isolated module `Terminal/ContactsFromGapsInversion.lean`, import `BreakAmplitudeSequence`, `LogGapsTheorem`)
L1 `frequency_of_two_contacts`, `phase_of_contact`, `beta_of_phase` (`β = T / tan φ`), `tower_of_two_contacts` (H1);
L2 `phase_bracket` (H2), `phase_bracket_prime`; L3 `lastContactBefore_div_log_tendsto` (H3);
L4 `cellFraction_small_eventually`, `cellFraction_near_one_eventually` (H4, via `logGapsVanish_holds`);
L5 `phase_eq_of_same_word` (H5), `tower_eq_of_same_word` (`T = T' ∧ β = β'`).
At most two compilation attempts on the final module, probes in `*_SCRATCH.lean`, outputs in `attempts/`.

## Experiments (after compilation; Odlyzko zeros, primes ≤ 10⁷)
(a) **reconstruction from the word**: for 6 heights on the line (ranks 1, 10, 10², 10³, 10⁴, 10⁵), the word `k(p_n)`
is computed then FORGOTTEN except for the integers; linear program (2 × 664 578 half-planes) giving `[T_lo, T_hi]` and
`[φ_lo, φ_hi]`, then `[β_lo, β_hi]` by the tangential formula; widths as a function of the number of primes used
(10³, 10⁴, 10⁵, 10⁶, 10⁷); the true `(1/2, T)` must be in the polygon; (b) **control**: three heights that are not
zeros (midpoints between consecutive zeros) treated identically: the reconstruction must succeed just the same (H6);
(c) **cause**: `min f`, `1 − max f` and the maximal step `T·log(p_{n+1}/p_n)/π` per decade; (d) **exact tangential
formula**: from two computed consecutive contacts, `(β, T)` recovered to floating-point accuracy. mpmath twin with 30
digits: (d) and the phase width on the primes ≤ 10⁶ for two heights.
Criterion: A if the true point is always in the polygon, if the widths decrease with the number of primes and if
(d) is exact; B if an identity compiles but the number contradicts; C otherwise. H6 is recorded whatever the outcome.
