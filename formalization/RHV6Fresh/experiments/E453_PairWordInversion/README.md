# E453 — K3: the inversion of E449 applied to the word of the mirror — pre-registration

> Français : [README.fr.md](README.fr.md)

Date: 2026-11-08. Status: pre-registered before any compilation and any execution (§19.75). Direction K3 validated by
the author ("continue with K3"). Orders: total spectral ban (use and citation; two terms only, no sum of Towers);
third order (contacts read `β`; frequency AND amplitude); R-E446; §19.44; forbidden "amplitude against budget"; no
premise equivalent to RH; at most two compilation attempts, each logged in `attempts/`.

## Question K3 (§19.74, recorded before)
E449 compiled that the word of the gaps determines the Tower (`T`, `φ`, `β`). The pair requires, at the same frequency,
two words that differ exactly on the window of K2b. What does the inversion of E449 applied to the word of the mirror
give: does it return `(1−β, T)` (two readable Towers, no contradiction) or does it require a datum that the gaps carry
only once?

## Check of non-equivalence with RH (done before pre-registration, §19.75.2)
K3 poses no hypothesis: all its statements are theorems for every `β ∈ (0,1)`, `T > 0`. The equivalences
"the two words coincide on all the primes ⟺ `β = 1/2`" and "differ beyond every rank ⟺ `β ≠ 1/2`" relate two properties
of ONE given pair; neither side is posed, nothing is asserted about the existence of off-line zeros. The risk identified
in §19.72 (reducing to the uniqueness of the meeting) is avoided: K3 uses only E449 L5 (the word determines the Tower),
a compiled theorem, never a uniqueness of the meeting. No comparison with `log q`, `ψ`, `rawDemand`, a cell.
Expected answer, recorded in advance: the inversion returns `(1−β, T)` exactly; two readable Towers; the word of the
mirror is a FUNCTION of the word of the Tower (no new datum); NO contradiction. If this is the result, the plan K0–K3
closes without contradiction hypothesis, and this is recorded as is; the decision returns to the author.

## Object
Pair `(β, T)`, `(1−β, T)`; words on the primes `k(p_n) = lastContactBefore β T p_n`, `k*(p_n) = lastContactBefore (1−β) T p_n`;
contacts of the mirror `C*_k = contactAt (1−β) T k`; phase `φ* = towerPhase (1−β) T`; shift `δ = mirrorPhaseShift β T`.

## Hypotheses
* H1 (tangential inversion of the mirror): `T = π/log(C*_{k+1}/C*_k)` and `1−β = T/tan(T·log C*_k − kπ)`.
* H2 (same frequency read by each word): `k*(p_n)/log p_n → T/π`; deterministic bracketing
  `|k/log x − T/π| ≤ (|φ| + π)/(π·log x)` for each word.
* H3 (uniqueness): every Tower `(β', T')`, `β' > 0`, having the word of the mirror on all the primes is the mirror: `T' = T`, `β' = 1−β`.
* H4 (no new datum): two Towers with the same word have mirrors with the same word; the word of the mirror is a function of the word of the Tower.
* H5 (line): `∀ n, k*(p_n) = k(p_n) ⟺ β = 1/2`.
* H6 (off-line): `(∀ N, ∃ n ≥ N, k*(p_n) ≠ k(p_n)) ⟺ β ≠ 1/2` (cause: E449 L4, the fraction approaches 0 and 1 beyond every rank).
* H7 (true zero, E451): H5/H6 at the parameter of a true zero and its mirror (`mirrorMember`).

## Lean statements (isolated module `Terminal/PairWordInversion.lean`, imports `PairMeetingImposition` + `ContactsFromGapsInversion`)
L1 `mirror_tower_of_two_contacts`, `mirror_word_slope_tendsto`, `word_slope_bracket`; L2 `mirror_word_determines_mirror`;
L3 `mirror_word_of_same_word`, `pair_of_same_word`; L4 `pair_words_eq_iff`; L5 `cellFraction_primes_small_and_near_one_from`,
`pair_words_differ_beyond`, `pair_words_differ_beyond_iff`; L6 `zero_pair_words_eq_iff`, `zero_pair_words_differ_beyond`.

## Experiments
* (a) `scripts/e453a_pair_inversion.py` (numpy): the 24 couples of E452 (`β ∈ {0.3; 0.4; 0.45; 0.5}` × zeros of ranks
  1, 10, 100, 1000, 10000, 100000); primes ≤ 10⁷; H1 with three contacts (`10⁻¹⁰` relative); H2 bracketing verified on all
  the primes; polygon of E449 applied to the word of the mirror (X = 10⁴, 10⁶): true point `(T, φ*)` inside; H4: word of
  the mirror recomputed from `(β, T)` returned by the inversion of the word of the Tower, bit-identical; H5/H6: number of
  primes with distinct words per decade (zero on the line, > 0 at each decade off the line).
* (b) `scripts/e453b_twin_mpmath.py`: mpmath twin with 30 digits, 10 primes per couple; H1, H2, words; gap to the numpy values.

## Criterion
A: module green (≤ 2 attempts), standard axioms, empty grep of the ban, H1 to `10⁻¹⁰`, H2 and H4 without violation,
polygon contains the true point, H5/H6 conform, twin in agreement; B: a point is missing (recorded). No hypothesis
posed, no contradiction drawn; if the answer is "two readable Towers, nothing new", it is recorded as the closure of K3.
