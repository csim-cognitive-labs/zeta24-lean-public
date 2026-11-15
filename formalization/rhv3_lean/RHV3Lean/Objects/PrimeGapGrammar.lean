/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.AlgebraicAxis

/-!
# RHV3Lean — O6, la grammaire des écarts premiers

    TRACE_ID              : RHV3-O6
    SEMANTIC_OBJECT       : O6 — la grammaire des écarts premiers
    SEMANTIC_STATEMENT    : la grammaire des écarts premiers est l'objet
                            découvert par l'étude des écarts entre premiers
                            successifs, indépendamment de tout zéro, portant la
                            positivité stricte de tout écart et l'unicité de
                            l'histoire première qui les porte tous.
    MATHEMATICAL_STATEMENT: la suite fixe des premiers, l'écart successif
                            strictement positif, l'absence de tout premier
                            strictement entre deux premiers successifs, et
                            l'écart ne dépendant que du rang, jamais du zéro qui
                            vient le lire.
    MATHEMATICAL_PARENT   : O2 — l'axe algébrique.
    PROOF_STRATEGY        : l'énumération est celle de Mathlib ; la stricte
                            croissance donne la positivité ; le corridor vide
                            vient du comptage des premiers ; l'unicité de
                            l'histoire première est prouvée par récurrence forte
                            sur le rang, à partir de la seule stricte croissance
                            et de l'image.
    REQUIRED_LEMMAS       : Nat.nth_strictMono, Nat.prime_nth_prime,
                            Nat.nth_count, Nat.infinite_setOfPred_prime
    WHY_EACH_LEMMA_EXISTS : les deux premiers portent l'ordre et la primalité ;
                            le troisième renvoie tout premier à son rang, ce qui
                            ferme le corridor et donne l'unicité.
    LEAN_DEFINITION       : fnPrimeAtRank, fnPrimeSuccessor, nPrimeGap
    LEAN_THEOREM          : thm_primeGap_positive,
                            thm_noPrimeStrictlyBetweenSuccessivePrimes,
                            thm_primeGap_depends_on_rank_alone,
                            thm_primeHistory_unique
    SAME_MEMBER_CHECK     : sans objet — cet objet ne mentionne aucun zéro.
    SAME_PASSAGE_CHECK    : sans objet.
    SAME_MIDDLE_CHECK     : sans objet.
    SAME_HISTORY_CHECK    : thm_primeHistory_unique est précisément la clause
                            d'unicité : toute énumération strictement croissante
                            d'image exactement les premiers EST celle-ci.
    FORBIDDEN_PREMISES    : toute dépendance en un zéro, une Tour, un contact,
                            une cellule ou un comptage de cellule.
    NEXT_CONSUMER         : O5 (occurrence première), la loi locale du
                            transport, et la séparation des extrémités qui en
                            dérive.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

/-! ## 1. L'énumération de l'histoire première -/

/-- Le premier de rang `nRank`, rang zéro-basé : le rang `0` porte `2`. -/
noncomputable def fnPrimeAtRank (nRank : ℕ) : ℕ := Nat.nth Nat.Prime nRank

/-- Le premier successeur du rang `nRank`. -/
noncomputable def fnPrimeSuccessor (nRank : ℕ) : ℕ := fnPrimeAtRank (nRank + 1)

@[simp]
theorem thm_primeAtRank_isPrime (nRank : ℕ) : Nat.Prime (fnPrimeAtRank nRank) :=
  Nat.prime_nth_prime nRank

/-- **L'ordre de l'histoire première.** -/
theorem thm_primeAtRank_strictMono : StrictMono fnPrimeAtRank :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem thm_primeAtRank_injective : Function.Injective fnPrimeAtRank :=
  thm_primeAtRank_strictMono.injective

/-- **Tout premier occupe un rang, et un seul.**  C'est la surjectivité de
l'énumération sur les premiers. -/
theorem thm_primeAtRank_surjective_onPrimes {nPrime : ℕ} (hPrime : Nat.Prime nPrime) :
    fnPrimeAtRank (Nat.count Nat.Prime nPrime) = nPrime :=
  Nat.nth_count hPrime

/-! ## 2. L'écart successif, et sa positivité stricte -/

/-- L'écart entre deux premiers successifs. -/
noncomputable def nPrimeGap (nRank : ℕ) : ℕ :=
  fnPrimeSuccessor nRank - fnPrimeAtRank nRank

theorem thm_primeAtRank_lt_successor (nRank : ℕ) :
    fnPrimeAtRank nRank < fnPrimeSuccessor nRank :=
  thm_primeAtRank_strictMono (Nat.lt_succ_self nRank)

/-- **RIGIDITE PRIMITIVE — aucune place nulle.**  Tout écart entre deux premiers
successifs est strictement positif.  Cette positivité est antérieure à tout
zéro et indépendante de toute hypothèse sur zêta ; c'est d'elle, et d'elle
seule, que dérivera plus tard la séparation des extrémités d'un passage. -/
theorem thm_primeGap_positive (nRank : ℕ) : 0 < nPrimeGap nRank :=
  Nat.sub_pos_of_lt (thm_primeAtRank_lt_successor nRank)

/-- **Aucune place nulle, forme en extrémités.**  Les deux extrémités d'une
place sont toujours distinctes. -/
theorem thm_successivePrimes_distinct (nRank : ℕ) :
    fnPrimeAtRank nRank ≠ fnPrimeSuccessor nRank :=
  (thm_primeAtRank_lt_successor nRank).ne

/-! ## 3. Le corridor est vide -/

/-- **Aucun premier ne se glisse strictement entre deux premiers successifs.**
C'est le voisinage de la grammaire : une place n'a pas d'intérieur. -/
theorem thm_noPrimeStrictlyBetweenSuccessivePrimes
    (nRank : ℕ) {nCandidate : ℕ} (hPrime : Nat.Prime nCandidate)
    (hLeft : fnPrimeAtRank nRank < nCandidate)
    (hRight : nCandidate < fnPrimeSuccessor nRank) : False := by
  set nCandidateRank := Nat.count Nat.Prime nCandidate with hCandidateRank
  have hAtRank : fnPrimeAtRank nCandidateRank = nCandidate :=
    thm_primeAtRank_surjective_onPrimes hPrime
  have hLeftRank : nRank < nCandidateRank := by
    by_contra hNot
    exact absurd (thm_primeAtRank_strictMono.le_iff_le.mpr (Nat.le_of_not_lt hNot))
      (by rw [hAtRank] at *; omega)
  have hRightRank : nCandidateRank < nRank + 1 := by
    by_contra hNot
    have hLe : fnPrimeAtRank (nRank + 1) ≤ fnPrimeAtRank nCandidateRank :=
      thm_primeAtRank_strictMono.le_iff_le.mpr (Nat.le_of_not_lt hNot)
    rw [hAtRank] at hLe
    exact absurd hRight (by unfold fnPrimeSuccessor; omega)
  omega

/-! ## 4. Rigidités de transport de O6 -/

/-- **RIGIDITE.**  L'écart ne dépend que du rang.  Deux lectures du même rang
donnent le même écart, quelles que soient les circonstances de la lecture :
aucune lecture issue des zéros ne fabrique une seconde suite d'écarts. -/
theorem thm_primeGap_depends_on_rank_alone
    {nLeftRank nRightRank : ℕ} (hSameRank : nLeftRank = nRightRank) :
    nPrimeGap nLeftRank = nPrimeGap nRightRank :=
  congrArg nPrimeGap hSameRank

/-- **RIGIDITE — unicité de l'histoire première.**

Toute énumération strictement croissante des entiers dont l'image est
exactement l'ensemble des premiers EST l'énumération canonique.  Il n'existe
donc pas de seconde histoire première : aucune lecture, d'où qu'elle vienne, ne
peut en fabriquer une autre. -/
theorem thm_primeHistory_unique
    (fnEnumeration : ℕ → ℕ)
    (hStrictMono : StrictMono fnEnumeration)
    (hRange : ∀ nValue : ℕ, Nat.Prime nValue ↔ ∃ nRank : ℕ, fnEnumeration nRank = nValue)
    (nRank : ℕ) :
    fnEnumeration nRank = fnPrimeAtRank nRank := by
  induction nRank using Nat.strong_induction_on with
  | _ nRank hInduction =>
    have hPrimeValue : Nat.Prime (fnEnumeration nRank) :=
      (hRange (fnEnumeration nRank)).mpr ⟨nRank, rfl⟩
    set nImageRank := Nat.count Nat.Prime (fnEnumeration nRank) with hImageRank
    have hImage : fnPrimeAtRank nImageRank = fnEnumeration nRank :=
      thm_primeAtRank_surjective_onPrimes hPrimeValue
    -- le rang canonique de la valeur est au moins `nRank`
    have hLower : nRank ≤ nImageRank := by
      by_contra hNot
      have hLt : nImageRank < nRank := Nat.lt_of_not_le hNot
      have hEqBelow : fnEnumeration nImageRank = fnPrimeAtRank nImageRank :=
        hInduction nImageRank hLt
      have hValueEq : fnEnumeration nImageRank = fnEnumeration nRank := by
        rw [hEqBelow, hImage]
      exact absurd (hStrictMono.injective hValueEq) (Nat.ne_of_lt hLt)
    -- et il est au plus `nRank`, par la surjectivité de l'énumération
    have hUpper : nImageRank ≤ nRank := by
      obtain ⟨nSourceRank, hSource⟩ :=
        (hRange (fnPrimeAtRank nRank)).mp (thm_primeAtRank_isPrime nRank)
      have hSourceGe : nRank ≤ nSourceRank := by
        by_contra hNot
        have hLt : nSourceRank < nRank := Nat.lt_of_not_le hNot
        have hEqBelow : fnEnumeration nSourceRank = fnPrimeAtRank nSourceRank :=
          hInduction nSourceRank hLt
        rw [hEqBelow] at hSource
        exact absurd (thm_primeAtRank_injective hSource) (Nat.ne_of_lt hLt)
      have hLe : fnEnumeration nRank ≤ fnPrimeAtRank nRank := by
        rw [← hSource]
        exact hStrictMono.le_iff_le.mpr hSourceGe
      rw [← hImage] at hLe
      exact thm_primeAtRank_strictMono.le_iff_le.mp hLe
    have hRankEq : nImageRank = nRank := Nat.le_antisymm hUpper hLower
    rw [← hImage, hRankEq]

/-! ## 5. Garde d'indexation — `0` est un rang, jamais un premier -/

/-- **Le rang `0` porte exactement `2`.**  Garde d'indexation : la convention
est 0-based (`fnPrimeAtRank 0 = 2`), jamais `fnPrimeAtRank 0 = 0` ni un
décalage implicite. -/
theorem thm_primeAtRank_zero_eq_two : fnPrimeAtRank 0 = 2 := by
  have hLe : fnPrimeAtRank 0 ≤ 2 := by
    have := thm_primeAtRank_surjective_onPrimes (nPrime := 2) Nat.prime_two
    have hMono := thm_primeAtRank_strictMono.monotone (Nat.zero_le (Nat.count Nat.Prime 2))
    rw [this] at hMono
    exact hMono
  have hGe : 2 ≤ fnPrimeAtRank 0 := (thm_primeAtRank_isPrime 0).two_le
  omega

/-- **Aucun rang ne porte un premier inférieur à `2`.**  `0` et `1` ne sont
jamais traités comme des premiers par `fnPrimeAtRank` : le rang `0` est déjà le
plancher absolu de la suite. -/
theorem thm_primeAtRank_ge_two (nRank : ℕ) : 2 ≤ fnPrimeAtRank nRank := by
  rw [← thm_primeAtRank_zero_eq_two]
  exact thm_primeAtRank_strictMono.monotone (Nat.zero_le nRank)

end RHV3Lean
