/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.OccurrenceHeightComposition
import RHV6Fresh.Terminal.PrimeGrammarQuantitative

/-!
# Le transport au premier partagé, écrit avec le seul canal arithmétique local : `Λ(M) = log M` (§19.18, 2026-10-30)

Module isolé (non ajouté à `RHV6Fresh.lean`). Exécution du plan §19.17.4 avec la consigne de l'auteur : aucune fonction
statistique, aucun reste de logarithme prévisionnel, aucune valeur estimée ; les VRAIES valeurs connues (la table exacte des
premiers, le poids exact `Λ`), la logique d'abord, puis le compilateur.

## Logique (avant toute compilation)

1. Le transport d'énergie d'un membre `e` à un membre `l` au premier partagé `M` est `M^(β_l − β_e) · ‖ρ_e‖ / ‖ρ_l‖` (compilé,
   `energyRatio_eq`). Le premier n'y entre que par la base `M` de l'exponentielle. Or `M^(x) = exp(x · log M)` et, pour un
   premier, `log M = Λ(M)`, le poids de von Mangoldt, c'est-à-dire exactement le SAUT DE PENTE de la primitive arithmétique en
   `M` (`arithmetic_primitive_slope_jump`, canal compilé sans aucun zéro dans son énoncé). Donc : **le seul canal arithmétique
   local à un premier qui entre dans le transport est `Λ(M)`, et il y entre multiplié par la différence des positions
   radiales.** Sur un passage vertical, ce produit est nul : le premier est invisible (`energyRatio_vertical_prime_free`).
   Pour la paire OFF, il est multiplié par deux fois le décalage radial : le premier devient visible.

2. Les vraies valeurs : sur tout porteur, `n ≥ 1` (le premier membre canonique est ON, compilé `one_le_n`), donc l'occurrence
   du zéro OFF est au moins `3` et le premier partagé de la sortie est au moins `5` (table exacte `2, 3, 5, 7, 11, 13`,
   `primeAtRank_one_eq`, `primeAtRank_two_eq`). Le facteur arithmétique de la sortie vaut au moins `5^(2δ) > 1`. Aucune
   estimation : ce sont les deux premiers premiers impairs.

3. Le détour OFF (arrivée en `p_n`, sortie en `p_{n+1}`, reprise en `p_{n+2}` : trois premiers CONSÉCUTIFS, exacts) a un
   contenu arithmétique total qui se calcule depuis les premiers seuls : le produit des trois transports vaut
   `exp(δ · (2Λ(p_{n+1}) − Λ(p_n) − Λ(p_{n+2}))) · ‖ρ_prev‖ / ‖ρ_next‖` lorsque le membre de reprise est sur la ligne,
   c'est-à-dire `(p_{n+1}² / (p_n · p_{n+2}))^δ` fois la valeur que transporte la chaîne ON de `prev` à `next` (toutes les
   bases valent `1` sur la ligne). La base `p_{n+1}² / (p_n · p_{n+2})` est un rationnel exact de la table des premiers, et
   elle n'est JAMAIS égale à `1` : `p_{n+1}² = p_n · p_{n+2}` est impossible (un premier qui divise un produit de deux
   premiers distincts de lui est l'un d'eux). Donc le détour OFF ne transporte jamais la même énergie que la chaîne ON entre
   les mêmes deux membres extrêmes : son contenu arithmétique est fixé par les premiers seuls, à la puissance `δ` près.
   Cette base est `exp(ℓ_n − ℓ_{n+1})` où `ℓ_k` est le logarithme de l'écart `p_k → p_{k+1}` : elle dépasse `1` exactement
   quand le pas propre de la paire (`p_n → p_{n+1}`) est, en logarithme, plus long que le pas suivant.

4. Ce que ceci ne fait PAS, dit avant de compiler : la puissance `δ` est la donnée radiale du zéro ; les premiers fixent la
   base, jamais l'exposant. Aucune loi compilée n'impose au détour de transporter la valeur de la chaîne ON ; l'inégalité des
   deux transports n'est donc pas une contradiction. Le canal local existe (c'est `Λ`), il est exact, et il est aveugle à `δ`.
   Le plan §19.17.4 (a) « fixer ou borner le transport depuis les premiers seuls » est réalisé pour la base et irréalisable
   pour l'exposant ; la frontière reste `ContinuationForced ⟺ RH`.

Aucune hypothèse de type « un pas d'écart vaut au moins une cellule », aucune comparaison à des zéros ON fictifs, aucune
moyenne. Le cas miroir est une hypothèse explicite (`h`), jamais posée comme acquise.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Le transport au premier partagé s'écrit avec `Λ(M)` : le canal local exact -/

/-- **Transport = `exp(Δβ · Λ(M)) · ‖ρ_e‖ / ‖ρ_l‖`** pour tout premier `M`. Le premier n'entre que par `Λ(M)`, multiplié par
la différence des positions radiales. -/
theorem energyRatio_eq_exp_vonMangoldt (e l : TrueZero) {q : ℕ} (hq : q.Prime) :
    energyRatio e l q =
      Real.exp ((rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * ArithmeticFunction.vonMangoldt q) *
        (‖zeroPoint e‖ / ‖zeroPoint l‖) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  rw [energyRatio_eq e l hq0, Real.rpow_def_of_pos hq0, ArithmeticFunction.vonMangoldt_apply_prime hq]
  congr 2
  ring

/-- **Passage vertical : le premier est invisible.** Même position radiale ⟹ le transport ne dépend pas du premier. -/
theorem energyRatio_vertical_prime_free (e l : TrueZero)
    (hβ : rZeroRadialPosition e.1 = rZeroRadialPosition l.1) {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime) :
    energyRatio e l q = energyRatio e l q' := by
  rw [energyRatio_eq_exp_vonMangoldt e l hq, energyRatio_eq_exp_vonMangoldt e l hq', hβ, sub_self,
    zero_mul, zero_mul]

/-- **Passage vertical : le transport est le seul rapport des normes.** -/
theorem energyRatio_vertical_eq (e l : TrueZero)
    (hβ : rZeroRadialPosition e.1 = rZeroRadialPosition l.1) {q : ℕ} (hq : q.Prime) :
    energyRatio e l q = ‖zeroPoint e‖ / ‖zeroPoint l‖ := by
  rw [energyRatio_eq_exp_vonMangoldt e l hq, hβ, sub_self, zero_mul, Real.exp_zero, one_mul]

/-- **Le poids `Λ(M)` est le saut de pente de la primitive arithmétique en `M`** (instance du canal compilé sans zéro). -/
theorem vonMangoldt_eq_slope_jump {N : ℕ} (hN : N.Prime) {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    (ArithmeticFunction.vonMangoldt N : ℂ) =
      (smoothedMangoldtPrimitive ((N : ℝ) + h) - smoothedMangoldtPrimitive N) / (h : ℂ)
        - (smoothedMangoldtPrimitive N - smoothedMangoldtPrimitive ((N : ℝ) - h)) / (h : ℂ) :=
  (arithmetic_primitive_slope_jump hN.one_lt.le h0 h1).symm

/-! ## 2. Vraies valeurs sur le porteur : occurrence `≥ 3`, premier partagé `≥ 5` -/

namespace OffCarrier

variable (C : OffCarrier)

/-- Le premier partagé de la sortie est premier. -/
theorem sharedPrime_prime : (fnPrimeAtRank (C.n + 1)).Prime := thm_primeAtRank_isPrime _

/-- **Vraie valeur** : l'occurrence du zéro OFF est au moins `3` (le premier membre canonique est ON, `p_1 = 3`). -/
theorem zero_occurrence_ge_three : 3 ≤ occurrence C.zero := by
  rw [C.zero_occurrence]
  have h := thm_primeAtRank_strictMono.monotone C.one_le_n
  rwa [primeAtRank_one_eq] at h

/-- **Vraie valeur** : le premier partagé de la sortie est au moins `5` (`p_2 = 5`). -/
theorem sharedPrime_ge_five : 5 ≤ fnPrimeAtRank (C.n + 1) := by
  have h2 : 2 ≤ C.n + 1 := by have := C.one_le_n; omega
  have h := thm_primeAtRank_strictMono.monotone h2
  rwa [primeAtRank_two_eq] at h

/-- **Transport de la paire au premier partagé, écrit avec `Λ`** : `exp(2δ · Λ(p_{n+1})) · ‖ρ‖ / ‖ρ*‖`. -/
theorem pair_transport_exp_vonMangoldt :
    energyRatio C.zero (mirrorMember C.zero) (fnPrimeAtRank (C.n + 1) : ℝ) =
      Real.exp (2 * C.radialShift * ArithmeticFunction.vonMangoldt (fnPrimeAtRank (C.n + 1))) *
        (‖zeroPoint C.zero‖ / ‖zeroPoint (mirrorMember C.zero)‖) := by
  rw [energyRatio_eq_exp_vonMangoldt _ _ C.sharedPrime_prime, C.mirror_radial_eq, C.zero_radial_eq]
  congr 2
  ring

/-- **Le facteur arithmétique de la sortie vaut au moins `5^(2δ)`**, vraie valeur, et dépasse `1`. -/
theorem pair_arithmetic_factor_ge_five_pow :
    (5 : ℝ) ^ (2 * C.radialShift) ≤ (fnPrimeAtRank (C.n + 1) : ℝ) ^ (2 * C.radialShift) ∧
      1 < (5 : ℝ) ^ (2 * C.radialShift) := by
  have hδ : 0 < 2 * C.radialShift := by have := C.radialShift_pos; linarith
  refine ⟨Real.rpow_le_rpow (by norm_num) (by exact_mod_cast C.sharedPrime_ge_five) hδ.le, ?_⟩
  exact Real.one_lt_rpow (by norm_num) hδ

/-! ## 3. Le détour OFF : trois premiers consécutifs, contenu arithmétique exact, jamais égal à `1` -/

/-- Le dernier membre ON avant le zéro OFF (membre de départ du raccord d'arrivée). -/
noncomputable def prevMember : TrueZero := ⟨C.arrival.zEarlierMember, C.arrival_earlier_pos⟩

theorem prevMember_onLine : rZeroRadialPosition C.prevMember.1 = 1 / 2 := C.arrival_earlier_onLine

theorem prevMember_occurrence : occurrence C.prevMember = fnPrimeAtRank (C.n - 1) :=
  C.arrival_earlier_occurrence

/-- Le premier partagé du raccord d'arrivée est `p_n`, premier minimal attendu de `prev` et occurrence du zéro OFF. -/
theorem prevMember_expectedMinimumPrime : expectedMinimumPrime C.prevMember = fnPrimeAtRank C.n := by
  rw [← C.arrivalRaccord_M, C.arrivalRaccord.exit_eq]

/-- L'occurrence du membre de reprise (rang `n + 2`) est `p_{n+2}`. -/
theorem nextMember_occurrence_eq : occurrence C.nextMember = fnPrimeAtRank (C.n + 2) := by
  change occurrence (canonicalMember (C.n + 1 + 1)) = _
  rw [occurrence_eq_primeAtRank, canonicalMember_index]

/-- Dans le cas miroir, le premier minimal attendu du miroir est `p_{n+2}` : le raccord de reprise est partagé en `p_{n+2}`. -/
theorem mirror_expectedMinimumPrime (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    expectedMinimumPrime (mirrorMember C.zero) = fnPrimeAtRank (C.n + 2) := by
  have hidx : nZeroSourceIndex (mirrorMember C.zero).1 = C.n + 1 := by
    rw [← h]; exact canonicalMember_index (C.n + 1)
  unfold expectedMinimumPrime; rw [hidx]; rfl

/-- **Les trois premiers partagés du détour sont consécutifs** : `p_n < p_{n+1} < p_{n+2}`. -/
theorem detour_primes_consecutive :
    fnPrimeAtRank C.n < fnPrimeAtRank (C.n + 1) ∧ fnPrimeAtRank (C.n + 1) < fnPrimeAtRank (C.n + 2) :=
  ⟨thm_primeAtRank_strictMono (by omega), thm_primeAtRank_strictMono (by omega)⟩

/-- **Fait exact sur la table des premiers** : `p_{k+1}² ≠ p_k · p_{k+2}` pour tout rang `k`. -/
theorem primeAtRank_sq_ne_mul (k : ℕ) :
    fnPrimeAtRank (k + 1) ^ 2 ≠ fnPrimeAtRank k * fnPrimeAtRank (k + 2) := by
  intro hEq
  have hp := thm_primeAtRank_isPrime (k + 1)
  have hdvd : fnPrimeAtRank (k + 1) ∣ fnPrimeAtRank k * fnPrimeAtRank (k + 2) := by
    rw [← hEq]; exact dvd_pow_self _ two_ne_zero
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
  · have := thm_primeAtRank_injective
      ((Nat.prime_dvd_prime_iff_eq hp (thm_primeAtRank_isPrime k)).mp h1)
    omega
  · have := thm_primeAtRank_injective
      ((Nat.prime_dvd_prime_iff_eq hp (thm_primeAtRank_isPrime (k + 2))).mp h1)
    omega

/-- **Contenu premier du détour** : `p_{n+1}² / (p_n · p_{n+2})`, rationnel exact de la table des premiers. -/
noncomputable def detourPrimeContent : ℝ :=
  (fnPrimeAtRank (C.n + 1) : ℝ) ^ 2 / ((fnPrimeAtRank C.n : ℝ) * (fnPrimeAtRank (C.n + 2) : ℝ))

theorem detourPrimeContent_pos : 0 < C.detourPrimeContent := by
  unfold detourPrimeContent
  have h0 : (0 : ℝ) < fnPrimeAtRank C.n := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  have h1 : (0 : ℝ) < fnPrimeAtRank (C.n + 1) := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  have h2 : (0 : ℝ) < fnPrimeAtRank (C.n + 2) := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  positivity

/-- **Le contenu premier du détour n'est jamais `1`.** -/
theorem detourPrimeContent_ne_one : C.detourPrimeContent ≠ 1 := by
  unfold detourPrimeContent
  intro hEq
  have h0 : (0 : ℝ) < fnPrimeAtRank C.n := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  have h2 : (0 : ℝ) < fnPrimeAtRank (C.n + 2) := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  rw [div_eq_one_iff_eq (mul_pos h0 h2).ne'] at hEq
  exact primeAtRank_sq_ne_mul C.n (by exact_mod_cast hEq)

/-- **Le contenu premier du détour est `exp(ℓ_n − ℓ_{n+1})`** : différence des deux logarithmes d'écart consécutifs
(`rPrimeGapLogRatio`, objet de rang seul). -/
theorem detourPrimeContent_eq_exp_logGaps :
    C.detourPrimeContent = Real.exp (rPrimeGapLogRatio C.n - rPrimeGapLogRatio (C.n + 1)) := by
  unfold detourPrimeContent rPrimeGapLogRatio
  have h0 : (0 : ℝ) < fnPrimeAtRank C.n := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  have h1 : (0 : ℝ) < fnPrimeAtRank (C.n + 1) := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  have h2 : (0 : ℝ) < fnPrimeAtRank (C.n + 2) := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  have hs1 : (fnPrimeSuccessor C.n : ℝ) = fnPrimeAtRank (C.n + 1) := rfl
  have hs2 : (fnPrimeSuccessor (C.n + 1) : ℝ) = fnPrimeAtRank (C.n + 2) := rfl
  rw [hs1, hs2, Real.log_div h1.ne' h0.ne', Real.log_div h2.ne' h1.ne', ← Real.exp_log (by positivity :
    (0 : ℝ) < (fnPrimeAtRank (C.n + 1) : ℝ) ^ 2 / ((fnPrimeAtRank C.n : ℝ) * (fnPrimeAtRank (C.n + 2) : ℝ)))]
  congr 1
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul h0.ne' h2.ne', Real.log_pow]
  push_cast
  ring

/-- **Produit des trois transports du détour**, identité exacte, sans hypothèse sur la position radiale du membre de
reprise : arrivée en `p_n` (depuis la ligne), sortie en `p_{n+1}` (vers le miroir), reprise en `p_{n+2}`. -/
theorem detour_transport_product :
    energyRatio C.prevMember C.zero (fnPrimeAtRank C.n : ℝ) *
      energyRatio C.zero (mirrorMember C.zero) (fnPrimeAtRank (C.n + 1) : ℝ) *
      energyRatio (mirrorMember C.zero) C.nextMember (fnPrimeAtRank (C.n + 2) : ℝ) =
    Real.exp (C.radialShift * (2 * ArithmeticFunction.vonMangoldt (fnPrimeAtRank (C.n + 1))
        - ArithmeticFunction.vonMangoldt (fnPrimeAtRank C.n)
        - ArithmeticFunction.vonMangoldt (fnPrimeAtRank (C.n + 2)))
      + (rZeroRadialPosition C.nextMember.1 - 1 / 2) * ArithmeticFunction.vonMangoldt (fnPrimeAtRank (C.n + 2))) *
      (‖zeroPoint C.prevMember‖ / ‖zeroPoint C.nextMember‖) := by
  rw [energyRatio_eq_exp_vonMangoldt _ _ (thm_primeAtRank_isPrime C.n),
    energyRatio_eq_exp_vonMangoldt _ _ (thm_primeAtRank_isPrime (C.n + 1)),
    energyRatio_eq_exp_vonMangoldt _ _ (thm_primeAtRank_isPrime (C.n + 2)),
    C.prevMember_onLine, C.mirror_radial_eq, C.zero_radial_eq]
  have hz := zeroPoint_norm_pos C.zero
  have hm := zeroPoint_norm_pos (mirrorMember C.zero)
  have hp := zeroPoint_norm_pos C.prevMember
  have hn := zeroPoint_norm_pos C.nextMember
  have key : Real.exp ((1 / 2 - C.radialShift - 1 / 2) * ArithmeticFunction.vonMangoldt (fnPrimeAtRank C.n)) *
      Real.exp ((1 / 2 + C.radialShift - (1 / 2 - C.radialShift)) *
        ArithmeticFunction.vonMangoldt (fnPrimeAtRank (C.n + 1))) *
      Real.exp ((rZeroRadialPosition C.nextMember.1 - (1 / 2 + C.radialShift)) *
        ArithmeticFunction.vonMangoldt (fnPrimeAtRank (C.n + 2))) =
      Real.exp (C.radialShift * (2 * ArithmeticFunction.vonMangoldt (fnPrimeAtRank (C.n + 1))
        - ArithmeticFunction.vonMangoldt (fnPrimeAtRank C.n)
        - ArithmeticFunction.vonMangoldt (fnPrimeAtRank (C.n + 2)))
      + (rZeroRadialPosition C.nextMember.1 - 1 / 2) * ArithmeticFunction.vonMangoldt (fnPrimeAtRank (C.n + 2))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [← key]
  field_simp
  ring

/-- **Reprise sur la ligne : le détour transporte `(p_{n+1}² / (p_n · p_{n+2}))^δ` fois la valeur de la chaîne ON.** -/
theorem detour_transport_product_onLine (hON : rZeroRadialPosition C.nextMember.1 = 1 / 2) :
    energyRatio C.prevMember C.zero (fnPrimeAtRank C.n : ℝ) *
      energyRatio C.zero (mirrorMember C.zero) (fnPrimeAtRank (C.n + 1) : ℝ) *
      energyRatio (mirrorMember C.zero) C.nextMember (fnPrimeAtRank (C.n + 2) : ℝ) =
    C.detourPrimeContent ^ C.radialShift * (‖zeroPoint C.prevMember‖ / ‖zeroPoint C.nextMember‖) := by
  rw [C.detour_transport_product, hON, sub_self, zero_mul, add_zero,
    Real.rpow_def_of_pos C.detourPrimeContent_pos, C.detourPrimeContent_eq_exp_logGaps, Real.log_exp]
  unfold rPrimeGapLogRatio
  have h0 : (0 : ℝ) < fnPrimeAtRank C.n := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  have h1 : (0 : ℝ) < fnPrimeAtRank (C.n + 1) := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  have h2 : (0 : ℝ) < fnPrimeAtRank (C.n + 2) := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  have hs1 : (fnPrimeSuccessor C.n : ℝ) = fnPrimeAtRank (C.n + 1) := rfl
  have hs2 : (fnPrimeSuccessor (C.n + 1) : ℝ) = fnPrimeAtRank (C.n + 2) := rfl
  rw [hs1, hs2, Real.log_div h1.ne' h0.ne', Real.log_div h2.ne' h1.ne',
    ArithmeticFunction.vonMangoldt_apply_prime (thm_primeAtRank_isPrime C.n),
    ArithmeticFunction.vonMangoldt_apply_prime (thm_primeAtRank_isPrime (C.n + 1)),
    ArithmeticFunction.vonMangoldt_apply_prime (thm_primeAtRank_isPrime (C.n + 2))]
  congr 2
  ring

/-- **La chaîne ON entre les mêmes extrêmes transporte le seul rapport des normes** (toutes les bases valent `1`) : c'est
la valeur de référence, écrite ici comme produit de trois transports verticaux fictifs n'existe pas ; on l'écrit directement
comme le transport de `prev` à `next` à n'importe quel premier, lorsque `next` est sur la ligne. -/
theorem onLine_chain_transport (hON : rZeroRadialPosition C.nextMember.1 = 1 / 2) {q : ℕ} (hq : q.Prime) :
    energyRatio C.prevMember C.nextMember q = ‖zeroPoint C.prevMember‖ / ‖zeroPoint C.nextMember‖ :=
  energyRatio_vertical_eq _ _ (by rw [C.prevMember_onLine, hON]) hq

/-- **Le facteur arithmétique du détour n'est jamais `1`** : `(p_{n+1}² / (p_n · p_{n+2}))^δ ≠ 1` dès que `δ > 0`. -/
theorem detour_arithmetic_factor_ne_one : C.detourPrimeContent ^ C.radialShift ≠ 1 := by
  rw [Real.rpow_def_of_pos C.detourPrimeContent_pos, Real.exp_eq_one_iff, mul_eq_zero, not_or]
  refine ⟨?_, C.radialShift_pos.ne'⟩
  intro hlog
  rcases Real.log_eq_zero.mp hlog with h | h | h
  · exact C.detourPrimeContent_pos.ne' h
  · exact C.detourPrimeContent_ne_one h
  · linarith [C.detourPrimeContent_pos]

/-- **Le détour OFF ne transporte jamais la valeur de la chaîne ON** entre les mêmes deux membres extrêmes (reprise sur la
ligne). La différence est fixée par les premiers seuls, à la puissance `δ` près. -/
theorem detour_transport_ne_onLine_chain (hON : rZeroRadialPosition C.nextMember.1 = 1 / 2) {q : ℕ} (hq : q.Prime) :
    energyRatio C.prevMember C.zero (fnPrimeAtRank C.n : ℝ) *
      energyRatio C.zero (mirrorMember C.zero) (fnPrimeAtRank (C.n + 1) : ℝ) *
      energyRatio (mirrorMember C.zero) C.nextMember (fnPrimeAtRank (C.n + 2) : ℝ) ≠
    energyRatio C.prevMember C.nextMember q := by
  rw [C.detour_transport_product_onLine hON, C.onLine_chain_transport hON hq]
  intro hEq
  have hpos : 0 < ‖zeroPoint C.prevMember‖ / ‖zeroPoint C.nextMember‖ :=
    div_pos (zeroPoint_norm_pos _) (zeroPoint_norm_pos _)
  have : C.detourPrimeContent ^ C.radialShift = 1 := by
    have := mul_right_cancel₀ hpos.ne' (hEq.trans (one_mul _).symm)
    exact this
  exact C.detour_arithmetic_factor_ne_one this

/-- **Signe du contenu premier, lu sur les deux logarithmes d'écart** : le détour amplifie (`> 1`) exactement quand le pas
propre de la paire est, en logarithme, plus long que le pas suivant. -/
theorem detourPrimeContent_gt_one_iff :
    1 < C.detourPrimeContent ↔ rPrimeGapLogRatio (C.n + 1) < rPrimeGapLogRatio C.n := by
  rw [C.detourPrimeContent_eq_exp_logGaps, Real.one_lt_exp_iff]
  constructor <;> intro h <;> linarith

end OffCarrier

#print axioms energyRatio_eq_exp_vonMangoldt
#print axioms energyRatio_vertical_prime_free
#print axioms energyRatio_vertical_eq
#print axioms vonMangoldt_eq_slope_jump
#print axioms OffCarrier.zero_occurrence_ge_three
#print axioms OffCarrier.sharedPrime_ge_five
#print axioms OffCarrier.pair_transport_exp_vonMangoldt
#print axioms OffCarrier.pair_arithmetic_factor_ge_five_pow
#print axioms OffCarrier.prevMember_expectedMinimumPrime
#print axioms OffCarrier.nextMember_occurrence_eq
#print axioms OffCarrier.mirror_expectedMinimumPrime
#print axioms OffCarrier.detour_primes_consecutive
#print axioms OffCarrier.primeAtRank_sq_ne_mul
#print axioms OffCarrier.detourPrimeContent_ne_one
#print axioms OffCarrier.detourPrimeContent_eq_exp_logGaps
#print axioms OffCarrier.detour_transport_product
#print axioms OffCarrier.detour_transport_product_onLine
#print axioms OffCarrier.onLine_chain_transport
#print axioms OffCarrier.detour_arithmetic_factor_ne_one
#print axioms OffCarrier.detour_transport_ne_onLine_chain
#print axioms OffCarrier.detourPrimeContent_gt_one_iff

end RHV6Fresh
