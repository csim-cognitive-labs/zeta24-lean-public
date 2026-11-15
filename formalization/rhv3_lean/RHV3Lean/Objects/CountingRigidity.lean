/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.PrimeGapGrammar
import RHV3Lean.Objects.ContactsAndCell
import Mathlib.NumberTheory.PrimeCounting

/-!
# RHV3Lean — O10, la rigidité de comptage Von Mangoldt/Chebyshev

    TRACE_ID              : RHV3-O10
    SEMANTIC_OBJECT       : O10 — la rigidité de comptage
    SEMANTIC_STATEMENT    : la rigidité de comptage n'est pas un objet
                            géométrique mais l'instrument qui rend mesurable le
                            contenu d'une cellule DEJA produite ; il lit, il ne
                            sélectionne jamais, et donne le cardinal de
                            l'ensemble trouvé puis le rang du premier central.
    MATHEMATICAL_STATEMENT: a = pi(C-), b = pi(C+), N = b - a, et le rang
                            central r = a + ceil(N/2), fonctions de I_C seul ;
                            l'intervalle rencontre les premiers exactement aux
                            rangs a+1, ..., b.
    MATHEMATICAL_PARENT   : O4 — les contacts et la cellule ; O2 — l'axe
                            algébrique ; O6 — la grammaire des écarts premiers.
    PROOF_STRATEGY        : la dualité comptage/rang de l'énumération première
                            donne l'équivalence « le premier de rang k est dans
                            (m, M] » avec « pi(m) <= k < pi(M) » ; l'ensemble
                            trouvé est donc l'image d'un intervalle de rangs par
                            l'énumération, qui est injective, d'où le cardinal ;
                            le rang central est alors dans l'intervalle des
                            rangs dès que le cardinal est non nul.
    REQUIRED_LEMMAS       : Nat.lt_nth_iff_count_lt, Nat.nth_count,
                            Nat.floor_lt, Nat.le_floor_iff,
                            thm_primeAtRank_injective
    WHY_EACH_LEMMA_EXISTS : la première est la dualité exacte entre le comptage
                            aux bords et le rang ; la deuxième renvoie tout
                            premier à son rang ; les deux suivantes passent des
                            bords réels aux bords entiers sans perte ; la
                            dernière donne le cardinal par injectivité.
    LEAN_DEFINITION       : nEdgePrimeRank, nCellLeftEdgeRank,
                            nCellRightEdgeRank, nCellFoundCount,
                            nCellCentralRank, nCellCentralPrime
    LEAN_THEOREM          : thm_foundPrime_iff_rank_between,
                            thm_foundPrimes_eq_image_rankInterval,
                            thm_cellFoundCount_eq_edgeRankDifference,
                            thm_cellCentralRank_between_edges,
                            thm_cellCentralPrime_mem_found,
                            thm_countingReads_doesNotMoveContacts
    SAME_MEMBER_CHECK     : le comptage ne mentionne jamais le membre ; il ne
                            lit que la cellule déjà produite par la Tour de ce
                            membre.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : l'énumération lue est celle de O6, unique ; le
                            comptage n'en fabrique pas une seconde.
    FORBIDDEN_PREMISES    : faire dépendre un contact, une adresse d'entrée, un
                            nombre d'étages ou une cellule d'une quantité de
                            comptage ; imposer que l'ensemble trouvé soit un
                            singleton.
    NEXT_CONSUMER         : O5 (l'occurrence première) et R-ATT.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

open Finset

/-! ## 1. Le rang de comptage à un bord -/

/-- **Le rang de comptage au bord** : le nombre de premiers inférieurs ou égaux
au bord.  C'est `pi(x)` du maître, lu sur un point de l'axe algébrique. -/
noncomputable def nEdgePrimeRank (rPoint : ℝ) : ℕ :=
  Nat.count Nat.Prime (⌊rPoint⌋₊ + 1)

/-- **La dualité comptage/rang.**  Le premier de rang `k` dépasse strictement un
point de l'axe exactement quand `k` atteint le rang de comptage de ce point.
C'est la clause qui fait que le comptage CONFIRME un rang au lieu de choisir un
premier. -/
theorem thm_edgeRank_le_iff_lt_primeAtRank
    {rPoint : ℝ} (hPointNonneg : 0 ≤ rPoint) (nRank : ℕ) :
    nEdgePrimeRank rPoint ≤ nRank ↔ rPoint < (fnPrimeAtRank nRank : ℝ) := by
  have hInfinite : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have hNat : nEdgePrimeRank rPoint ≤ nRank ↔ ⌊rPoint⌋₊ < fnPrimeAtRank nRank := by
    unfold nEdgePrimeRank fnPrimeAtRank
    constructor
    · intro hLe
      by_contra hNot
      have hLt : Nat.nth Nat.Prime nRank < ⌊rPoint⌋₊ + 1 := by omega
      have hCount : nRank < Nat.count Nat.Prime (⌊rPoint⌋₊ + 1) :=
        (Nat.lt_nth_iff_count_lt hInfinite).mpr hLt
      omega
    · intro hLt
      by_contra hNot
      have hCount : nRank < Nat.count Nat.Prime (⌊rPoint⌋₊ + 1) := by omega
      have hNth : Nat.nth Nat.Prime nRank < ⌊rPoint⌋₊ + 1 :=
        (Nat.lt_nth_iff_count_lt hInfinite).mp hCount
      omega
  rw [hNat]
  exact (Nat.floor_lt hPointNonneg)

/-! ## 2. Les deux rangs aux bords de la cellule, et le cardinal -/

variable (tInterval : TAlgebraicInterval)

/-- **Le rang au bord gauche**, `a = pi(C-)`. -/
noncomputable def nCellLeftEdgeRank : ℕ :=
  nEdgePrimeRank tInterval.rLeftEndpoint

/-- **Le rang au bord droit**, `b = pi(C+)`. -/
noncomputable def nCellRightEdgeRank : ℕ :=
  nEdgePrimeRank tInterval.rRightEndpoint

/-- **Le cardinal de l'ensemble trouvé**, `N`. -/
noncomputable def nCellFoundCount : ℕ :=
  (sAlgebraicIntervalFoundPrimes tInterval).card

/-- **L'intervalle algébrique rencontre les premiers exactement aux rangs
`a, ..., b-1`** (rangs zéro-basés, donc `p_(a+1), ..., p_b` en rangs du maître).

C'est l'énoncé du maître pour l'ensemble trouvé, obtenu de la seule dualité
comptage/rang : le comptage aux deux bords borne les rangs présents, il ne
choisit aucun premier. -/
theorem thm_foundPrime_iff_rank_between (nRank : ℕ) :
    fnPrimeAtRank nRank ∈ sAlgebraicIntervalFoundPrimes tInterval ↔
      nCellLeftEdgeRank tInterval ≤ nRank ∧
        nRank < nCellRightEdgeRank tInterval := by
  have hLeftNonneg : (0 : ℝ) ≤ tInterval.rLeftEndpoint :=
    le_of_lt tInterval.hLeftPositive
  have hRightNonneg : (0 : ℝ) ≤ tInterval.rRightEndpoint :=
    le_of_lt tInterval.rightPositive
  rw [thm_mem_foundPrimes_iff]
  constructor
  · rintro ⟨_, hAboveLeft, hBelowRight⟩
    refine ⟨(thm_edgeRank_le_iff_lt_primeAtRank hLeftNonneg nRank).mpr hAboveLeft, ?_⟩
    by_contra hNot
    have hLe : nCellRightEdgeRank tInterval ≤ nRank := by omega
    exact absurd hBelowRight
      (not_le.mpr ((thm_edgeRank_le_iff_lt_primeAtRank hRightNonneg nRank).mp hLe))
  · rintro ⟨hLeftRank, hRightRank⟩
    refine ⟨thm_primeAtRank_isPrime nRank,
      (thm_edgeRank_le_iff_lt_primeAtRank hLeftNonneg nRank).mp hLeftRank, ?_⟩
    by_contra hNot
    have hLt : tInterval.rRightEndpoint < (fnPrimeAtRank nRank : ℝ) := not_le.mp hNot
    have hLe : nCellRightEdgeRank tInterval ≤ nRank :=
      (thm_edgeRank_le_iff_lt_primeAtRank hRightNonneg nRank).mpr hLt
    omega

/-- L'ensemble trouvé est exactement l'image de l'intervalle des rangs. -/
theorem thm_foundPrimes_eq_image_rankInterval :
    sAlgebraicIntervalFoundPrimes tInterval =
      (Finset.Ico (nCellLeftEdgeRank tInterval)
        (nCellRightEdgeRank tInterval)).image fnPrimeAtRank := by
  ext nCandidate
  constructor
  · intro hMember
    have hPrime : Nat.Prime nCandidate := thm_foundPrimes_isPrime hMember
    have hRank : fnPrimeAtRank (Nat.count Nat.Prime nCandidate) = nCandidate :=
      thm_primeAtRank_surjective_onPrimes hPrime
    rw [Finset.mem_image]
    refine ⟨Nat.count Nat.Prime nCandidate, ?_, hRank⟩
    rw [Finset.mem_Ico]
    apply (thm_foundPrime_iff_rank_between tInterval _).mp
    rw [hRank]
    exact hMember
  · intro hImage
    obtain ⟨nRank, hRankMember, hValue⟩ := Finset.mem_image.mp hImage
    rw [← hValue]
    exact (thm_foundPrime_iff_rank_between tInterval nRank).mpr
      (Finset.mem_Ico.mp hRankMember)

/-- **Le cardinal de l'ensemble trouvé est la différence des rangs aux deux
bords** : `N = b - a`.  C'est le théorème qui donne le cardinal FROM les rangs
aux bords, exactement comme le maître le demande. -/
theorem thm_cellFoundCount_eq_edgeRankDifference :
    nCellFoundCount tInterval =
      nCellRightEdgeRank tInterval - nCellLeftEdgeRank tInterval := by
  unfold nCellFoundCount
  rw [thm_foundPrimes_eq_image_rankInterval,
    Finset.card_image_of_injective _ thm_primeAtRank_injective,
    Nat.card_Ico]

/-- `N_P = 1` est exactement l'existence d'un unique premier dans la même
cellule. Ce theorem ne produit pas T1 : il en fixe la forme extensionnelle
sans accepter de premier, de rang ou de non-vacuité comme entrée. -/
theorem thm_cellFoundCount_eq_one_iff_existsUniquePrime :
    nCellFoundCount tInterval = 1 ↔
      ∃! p : ℕ,
        Nat.Prime p ∧
          tInterval.rLeftEndpoint < (p : ℝ) ∧
          (p : ℝ) ≤ tInterval.rRightEndpoint := by
  change (sAlgebraicIntervalFoundPrimes tInterval).card = 1 ↔ _
  constructor
  · intro hCard
    obtain ⟨p, hSet⟩ := Finset.card_eq_one.mp hCard
    refine ⟨p, ?_, ?_⟩
    · apply (thm_mem_foundPrimes_iff tInterval p).mp
      rw [hSet]
      exact Finset.mem_singleton_self p
    · intro q hq
      have hMem : q ∈ sAlgebraicIntervalFoundPrimes tInterval :=
        (thm_mem_foundPrimes_iff tInterval q).mpr hq
      rw [hSet] at hMem
      exact Finset.mem_singleton.mp hMem
  · rintro ⟨p, hp, hUnique⟩
    apply Finset.card_eq_one.mpr
    refine ⟨p, ?_⟩
    ext q
    simp only [Finset.mem_singleton]
    constructor
    · intro hq
      exact hUnique q ((thm_mem_foundPrimes_iff tInterval q).mp hq)
    · intro hq
      subst q
      exact (thm_mem_foundPrimes_iff tInterval p).mpr hp

/-! ## 3. Le rang central, et le premier central -/

/-- **Le rang central du maître** : `r = a + ceil(N/2)`, en rangs du maître,
donc à base un. -/
noncomputable def nCellCentralRank : ℕ :=
  nCellLeftEdgeRank tInterval + (nCellFoundCount tInterval + 1) / 2

/-- **Le premier central de la cellule** : le premier du rang central. Le rang
zéro-basé de Lean est le rang du maître diminué de un. -/
noncomputable def nCellCentralPrime : ℕ :=
  fnPrimeAtRank (nCellCentralRank tInterval - 1)

theorem thm_cellCentralPrime_isPrime : Nat.Prime (nCellCentralPrime tInterval) :=
  thm_primeAtRank_isPrime _

/-- **Le rang central tombe entre les deux rangs aux bords**, dès que l'ensemble
trouvé est non vide. -/
theorem thm_cellCentralRank_between_edges
    (hFoundNonempty : 0 < nCellFoundCount tInterval) :
    nCellLeftEdgeRank tInterval ≤ nCellCentralRank tInterval - 1 ∧
      nCellCentralRank tInterval - 1 < nCellRightEdgeRank tInterval := by
  have hDifference :
      nCellFoundCount tInterval =
        nCellRightEdgeRank tInterval - nCellLeftEdgeRank tInterval :=
    thm_cellFoundCount_eq_edgeRankDifference tInterval
  unfold nCellCentralRank
  omega

/-- **Le premier central appartient à l'ensemble trouvé de la cellule.**

Il est donc un vrai premier, situé dans l'intervalle algébrique, et son rang est
confirmé par les deux rangs aux bords.  Rien n'a exigé que l'ensemble trouvé
soit un singleton : le cardinal peut valoir un, deux, ou davantage. -/
theorem thm_cellCentralPrime_mem_found
    (hFoundNonempty : 0 < nCellFoundCount tInterval) :
    nCellCentralPrime tInterval ∈ sAlgebraicIntervalFoundPrimes tInterval :=
  (thm_foundPrime_iff_rank_between tInterval _).mpr
    (thm_cellCentralRank_between_edges tInterval hFoundNonempty)

/-- Le premier central est dans l'intervalle algébrique. -/
theorem thm_cellCentralPrime_in_interval
    (hFoundNonempty : 0 < nCellFoundCount tInterval) :
    tInterval.rLeftEndpoint < (nCellCentralPrime tInterval : ℝ) ∧
      (nCellCentralPrime tInterval : ℝ) ≤ tInterval.rRightEndpoint :=
  thm_foundPrimes_in_interval (thm_cellCentralPrime_mem_found tInterval hFoundNonempty)

/-! ## 4. Rigidité de transport de O10 -/

/-- **RIGIDITE — le comptage lit, il ne déplace rien.**

Les deux rangs aux bords, le cardinal, le rang central et le premier central
sont tous fonctions de la seule cellule.  Deux cellules de mêmes bords donnent
exactement les mêmes quantités de comptage ; réciproquement, aucune de ces
quantités n'entre dans la définition d'un contact. -/
theorem thm_countingReads_doesNotMoveContacts
    {tLeftInterval tRightInterval : TAlgebraicInterval}
    (hLeft : tLeftInterval.rLeftEndpoint = tRightInterval.rLeftEndpoint)
    (hRight : tLeftInterval.rRightEndpoint = tRightInterval.rRightEndpoint) :
    nCellLeftEdgeRank tLeftInterval = nCellLeftEdgeRank tRightInterval ∧
      nCellRightEdgeRank tLeftInterval = nCellRightEdgeRank tRightInterval ∧
        nCellFoundCount tLeftInterval = nCellFoundCount tRightInterval ∧
          nCellCentralPrime tLeftInterval = nCellCentralPrime tRightInterval := by
  have hFound :
      sAlgebraicIntervalFoundPrimes tLeftInterval =
        sAlgebraicIntervalFoundPrimes tRightInterval :=
    thm_foundPrimes_determined_by_endpoints hLeft hRight
  have hLeftRank :
      nCellLeftEdgeRank tLeftInterval = nCellLeftEdgeRank tRightInterval := by
    unfold nCellLeftEdgeRank; rw [hLeft]
  have hRightRank :
      nCellRightEdgeRank tLeftInterval = nCellRightEdgeRank tRightInterval := by
    unfold nCellRightEdgeRank; rw [hRight]
  have hCount :
      nCellFoundCount tLeftInterval = nCellFoundCount tRightInterval := by
    unfold nCellFoundCount; rw [hFound]
  refine ⟨hLeftRank, hRightRank, hCount, ?_⟩
  unfold nCellCentralPrime nCellCentralRank
  rw [hLeftRank, hCount]

/-! ## 5. Le comptage lu sur la cellule d'une Tour -/

variable (zUpperZero : TUpperNonTrivialZetaZero) (tWindow : TTowerWindow)

/-- **Le premier central du membre**, lu sur la cellule que sa propre Tour a
produite.  L'ordre causal est respecté : le membre donne sa Tour, la Tour donne
ses contacts, les contacts donnent la cellule, la cellule donne son ensemble
trouvé et son centre, et le comptage confirme le rang. -/
noncomputable def nMemberCentralPrime : ℕ :=
  nCellCentralPrime (tCellAlgebraicInterval zUpperZero tWindow)

/-- Le premier central du membre est un vrai premier. -/
theorem thm_memberCentralPrime_isPrime :
    Nat.Prime (nMemberCentralPrime zUpperZero tWindow) :=
  thm_cellCentralPrime_isPrime _

/-- Le premier central du membre est dans la cellule de sa propre Tour. -/
theorem thm_memberCentralPrime_in_cell
    (hFoundNonempty :
      0 < nCellFoundCount (tCellAlgebraicInterval zUpperZero tWindow)) :
    (nMemberCentralPrime zUpperZero tWindow : ℝ) ∈
      sCellCarrier zUpperZero tWindow :=
  thm_cellCentralPrime_in_interval _ hFoundNonempty

end RHV3Lean
