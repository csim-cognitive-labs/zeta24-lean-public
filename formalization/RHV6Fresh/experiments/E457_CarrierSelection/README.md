# E457 — Φ0 + Φ1: naming the missing edge (three exact reformulations) and isolation theorem for the selection of carriers (pre-registration, 2026-11-08)

> Français : [README.fr.md](README.fr.md)

Reference: `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.80 (plan Φ, validated by the author on 2026-11-08: "I validate the plan, record it
and execute each proposal"), §19.82. No hypothesis admitted, no axiom, no `sorry`; isolated module `RHV6Fresh/Terminal/CarrierSelection.lean`,
NOT added to `RHV6Fresh.lean`.

## Named objects (before compilation)
* `towerWord β T n`: word of the Tower `(β, T)` at the prime of rank `n` (= `lastContactBefore β T p_n`, E449/E453);
* `zeroWord z n`: word of a true zero; `IsCarrier β T`: the Tower `(β, T)` carries a zero (non-zero weight `zeroMult`, E451);
* `CarrierWordsSelfMirror` (R1): every carrier word equals the word of its mirror;
* `HeightInjectiveOnCarriers` (R2): two upper true zeros of the same height are the same;
* `PriceRadiallyBlindOnCarriers` (R3): the price of E445 (`offPrice`) equals that of the line at every prime for every true zero;
  variant R3': the terms of a zero and of its mirror have the same modulus at every prime.

## Statements to compile (Φ0)
1. R1 ⟺ RH; 2. R2 ⟺ RH; 3. R3 ⟺ RH and R3' ⟺ RH; 3bis. equality of the moduli at TWO distinct primes already forces `β = 1/2`;
4. R2 ⟹ `NoMixedHeight` (FixedGapRaccords). Non-triviality control: `NoMixedHeight ⟹ RH` must NOT compile without RH; a scratch
probe tries it, the failure is recorded in `attempts/` (a non-implication cannot be proved in Lean: it is a probe finding).

## Statements to compile (Φ1 — isolation)
5. `stagePosition_floor_stable_right`: for every Tower `(β, T)`, every prime of rank `n`, there exists `δ > 0` such that every Tower `(β', T)` with
   `β < β' < β + δ` has the same word at rank `n` (stage position increasing and continuous in `β`, E444);
6. `exists_nonCarrier_same_word_on_finset`: for every true zero `z`, every FINITE set of ranks `S` and every `ε > 0`, there exists `β'` with
   `β < β' < min(β + ε, 1)` such that `(β', T)` is NOT a carrier (zeta does not vanish, zero weight) and has the same word as `z` on `S`
   (isolation of zeros: `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, `analyticOrderAt_riemannZeta_ne_top`);
7. `finite_window_predicate_not_carrier_selective`: every predicate on words that depends on only a finite number of ranks, true on the word of a
   zero, is true on the word of a non-carrier Tower of the same frequency.
Deviation from the plan: the neighbouring Tower is taken at the SAME height `T` and radial position `β' > β` (simpler: no bound on `log q`
is required); the plan proposed `T' > T`. Statement 6 is therefore stronger on one point: exactly the same frequency.

## Deterministic part (twin of Φ1) — `e457_carrier_isolation.py`
On the first 200 Odlyzko heights (line, β = 1/2) and on 200 controls with perturbed β (0.3; 0.4; 0.45 at the same heights),
primes ≤ 10⁶ (sieve): (a) maximal radial margin `Δβ_max` preserving the whole word (exact, by the tangential formula); (b) height margin
`ΔT_max` preserving the whole word (monotone resolution), compared with the half-gap to the next height. Expected, recorded in advance:
`Δβ_max > 0` and `ΔT_max > 0` always (twin of 6); `ΔT_max` far smaller than the half-gap between zeros (order 10⁻⁶ against 10⁻¹…1); margins
of the controls of the same order as those of the line (the margin is a property of the word, not of the weight). Measurement, no law.

## Protocol
At most two attempts, unversioned `*_SCRATCH.lean` probes deleted after capture; `attempts/`; `#print axioms`; grep of the ban at zero
on the module; full `lake build RHV6Fresh` green; script once under `nohup`, output in `logs/`.
