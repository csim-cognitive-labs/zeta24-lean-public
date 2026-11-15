/-
Ported into `RhGapCriterion` for P4.4a from
`AlexKontorovich/PrimeNumberTheoremAnd`,
commit `6739793850d3eaa031e3543ed72d7f026f8080f5`.
Only import prefixes and proof bodies may differ from the source.
-/
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Divisors of holomorphic functions

Holomorphic functions on `ℂ` have non-negative divisors, since zeros contribute non-negative
multiplicity and poles cannot occur.

## Main results

* `Differentiable.divisor_nonneg` : the divisor of an entire function is non-negative
-/

@[expose] public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The divisor of an entire function is non-negative. -/
theorem Differentiable.divisor_nonneg {f : ℂ → E} (hf : Differentiable ℂ f) :
    0 ≤ MeromorphicOn.divisor f (univ : Set ℂ) :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.differentiableOn.analyticOnNhd isOpen_univ)
