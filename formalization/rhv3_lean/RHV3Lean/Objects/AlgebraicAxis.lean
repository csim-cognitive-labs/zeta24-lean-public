/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Sort

/-!
# RHV3Lean — O2, l'axe algébrique

    TRACE_ID              : RHV3-O2
    SEMANTIC_OBJECT       : O2 — l'axe algébrique
    SEMANTIC_STATEMENT    : l'axe algébrique est l'axe réel positif portant les
                            nombres premiers, muni de ses coordonnées
                            logarithmique et linéaire, où tout couple de points
                            découpe un intervalle algébrique contenant un
                            ensemble fini, ordonné et déterminé de nombres
                            premiers, dit ensemble des nombres trouvés.
    MATHEMATICAL_STATEMENT: (R_{>0}, <) muni de u = log x, x = e^u exactement,
                            portant la suite fixe des premiers ; pour
                            C- < C+, l'intervalle (C-, C+] rencontre les premiers
                            en un ensemble fini ordonné, EN GENERAL PLURIEL.
    MATHEMATICAL_PARENT   : aucun — objet de base, sans amont.
    PROOF_STRATEGY        : transcription directe ; l'ensemble trouvé est un
                            Finset filtré par la primalité et l'appartenance à
                            l'intervalle, donc fini, ordonné et fonction du seul
                            intervalle.
    REQUIRED_LEMMAS       : Real.exp_log, Real.log_exp, Nat.le_floor, Nat.lt_succ
    WHY_EACH_LEMMA_EXISTS : les deux premiers portent la conversion exacte des
                            deux coordonnées ; les deux derniers bornent
                            l'ensemble trouvé par le bord droit.
    LEAN_DEFINITION       : TAlgebraicInterval, sAlgebraicIntervalFoundPrimes
    LEAN_THEOREM          : thm_algebraicAxis_exp_log, thm_algebraicAxis_log_exp,
                            thm_mem_foundPrimes_iff,
                            thm_foundPrimes_determined_by_endpoints,
                            thm_foundPrimes_generallyPlural
    SAME_MEMBER_CHECK     : sans objet — cet objet ne mentionne aucun zéro.
    SAME_PASSAGE_CHECK    : sans objet.
    SAME_MIDDLE_CHECK     : sans objet.
    SAME_HISTORY_CHECK    : la suite des premiers est celle de Mathlib, fixe,
                            indépendante de tout paramètre.
    FORBIDDEN_PREMISES    : toute clause forçant l'ensemble trouvé à un
                            singleton ; toute dépendance en un zéro, une Tour,
                            un contact ou un comptage.
    NEXT_CONSUMER         : O4 (contacts et cellule), O10 (comptage).
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

/-! ## 1. Les deux coordonnées de l'axe, et leur conversion exacte -/

/-- **Conversion exacte, sens linéaire.**  Sur l'axe algébrique, la coordonnée
linéaire se retrouve exactement depuis la coordonnée logarithmique. -/
theorem thm_algebraicAxis_exp_log {rPoint : ℝ} (hPositive : 0 < rPoint) :
    Real.exp (Real.log rPoint) = rPoint :=
  Real.exp_log hPositive

/-- **Conversion exacte, sens logarithmique.** -/
theorem thm_algebraicAxis_log_exp (rLogPoint : ℝ) :
    Real.log (Real.exp rLogPoint) = rLogPoint :=
  Real.log_exp rLogPoint

/-- **L'ordre total est le même dans les deux coordonnées.**  La coordonnée
logarithmique n'est pas une reparamétrisation approchée : elle préserve
exactement l'ordre de l'axe. -/
theorem thm_algebraicAxis_log_lt_log_iff
    {rLeft rRight : ℝ} (hLeft : 0 < rLeft) (hRight : 0 < rRight) :
    Real.log rLeft < Real.log rRight ↔ rLeft < rRight :=
  Real.log_lt_log_iff hLeft hRight

/-! ## 2. L'intervalle algébrique -/

/-- **Un intervalle algébrique** est un couple ordonné de points de l'axe
algébrique.  Il ne connaît ni zéro, ni Tour, ni comptage. -/
structure TAlgebraicInterval where
  /-- Bord gauche. -/
  rLeftEndpoint : ℝ
  /-- Bord droit. -/
  rRightEndpoint : ℝ
  /-- Le bord gauche est sur l'axe algébrique, donc strictement positif. -/
  hLeftPositive : 0 < rLeftEndpoint
  /-- Les deux bords sont ordonnés. -/
  hOrdered : rLeftEndpoint < rRightEndpoint

namespace TAlgebraicInterval

variable (tInterval : TAlgebraicInterval)

/-- Le bord droit est lui aussi sur l'axe algébrique. -/
theorem rightPositive : 0 < tInterval.rRightEndpoint :=
  lt_trans tInterval.hLeftPositive tInterval.hOrdered

/-- Le diamètre logarithmique de l'intervalle est strictement positif. -/
theorem logDiameter_positive :
    0 < Real.log tInterval.rRightEndpoint - Real.log tInterval.rLeftEndpoint := by
  have hLog :
      Real.log tInterval.rLeftEndpoint < Real.log tInterval.rRightEndpoint :=
    (thm_algebraicAxis_log_lt_log_iff tInterval.hLeftPositive
      tInterval.rightPositive).mpr tInterval.hOrdered
  linarith

end TAlgebraicInterval

/-! ## 3. L'ensemble des nombres trouvés -/

/-- **L'ensemble des nombres trouvés de l'intervalle algébrique.**

Fini par construction, ordonné par l'ordre de l'axe, et fonction du seul
intervalle.  Rien ici ne restreint son cardinal : il est EN GENERAL PLURIEL, et
le cas d'un élément unique n'est qu'un cas particulier. -/
def PIsFoundNumber (tInterval : TAlgebraicInterval) (nCandidate : ℕ) : Prop :=
  Nat.Prime nCandidate ∧
    tInterval.rLeftEndpoint < (nCandidate : ℝ) ∧
    (nCandidate : ℝ) ≤ tInterval.rRightEndpoint

noncomputable instance instDecidableIsFoundNumber (tInterval : TAlgebraicInterval) :
    DecidablePred (PIsFoundNumber tInterval) := fun _ => Classical.dec _

noncomputable def sAlgebraicIntervalFoundPrimes
    (tInterval : TAlgebraicInterval) : Finset ℕ :=
  (Finset.range (⌊tInterval.rRightEndpoint⌋₊ + 1)).filter (PIsFoundNumber tInterval)

/-- **Caractérisation exacte de l'appartenance.**  Un nombre est trouvé si et
seulement s'il est premier et situé dans l'intervalle demi-ouvert. -/
theorem thm_mem_foundPrimes_iff
    (tInterval : TAlgebraicInterval) (nCandidate : ℕ) :
    nCandidate ∈ sAlgebraicIntervalFoundPrimes tInterval ↔
      Nat.Prime nCandidate ∧
        tInterval.rLeftEndpoint < (nCandidate : ℝ) ∧
        (nCandidate : ℝ) ≤ tInterval.rRightEndpoint := by
  simp only [sAlgebraicIntervalFoundPrimes, Finset.mem_filter, Finset.mem_range,
    PIsFoundNumber]
  constructor
  · exact fun hMember => hMember.2
  · intro hSpec
    refine ⟨?_, hSpec⟩
    have hFloor : nCandidate ≤ ⌊tInterval.rRightEndpoint⌋₊ :=
      Nat.le_floor (by exact_mod_cast hSpec.2.2)
    omega

/-- Tout nombre trouvé est un vrai premier. -/
theorem thm_foundPrimes_isPrime
    {tInterval : TAlgebraicInterval} {nCandidate : ℕ}
    (hMember : nCandidate ∈ sAlgebraicIntervalFoundPrimes tInterval) :
    Nat.Prime nCandidate :=
  ((thm_mem_foundPrimes_iff tInterval nCandidate).mp hMember).1

/-- Tout nombre trouvé est strictement au-dessus du bord gauche et au plus au
bord droit. -/
theorem thm_foundPrimes_in_interval
    {tInterval : TAlgebraicInterval} {nCandidate : ℕ}
    (hMember : nCandidate ∈ sAlgebraicIntervalFoundPrimes tInterval) :
    tInterval.rLeftEndpoint < (nCandidate : ℝ) ∧
      (nCandidate : ℝ) ≤ tInterval.rRightEndpoint :=
  ((thm_mem_foundPrimes_iff tInterval nCandidate).mp hMember).2

/-- **L'ensemble trouvé est ordonné.**  Son énumération croissante est la liste
triée du Finset : l'ordre lu dans la cellule est l'ordre de l'axe, jamais un
ordre reconstruit. -/
theorem thm_foundPrimes_sorted (tInterval : TAlgebraicInterval) :
    ((sAlgebraicIntervalFoundPrimes tInterval).sort).SortedLT :=
  Finset.sortedLT_sort _

/-! ## 4. Rigidité de transport de O2 -/

/-- **RIGIDITE.**  L'ensemble trouvé est fonction du seul intervalle : deux
intervalles de mêmes bords portent le même ensemble trouvé.  Aucune lecture,
aucun contact, aucun comptage n'y ajoute ni n'en retire un élément. -/
theorem thm_foundPrimes_determined_by_endpoints
    {tLeftInterval tRightInterval : TAlgebraicInterval}
    (hLeft : tLeftInterval.rLeftEndpoint = tRightInterval.rLeftEndpoint)
    (hRight : tLeftInterval.rRightEndpoint = tRightInterval.rRightEndpoint) :
    sAlgebraicIntervalFoundPrimes tLeftInterval =
      sAlgebraicIntervalFoundPrimes tRightInterval := by
  ext nCandidate
  rw [thm_mem_foundPrimes_iff, thm_mem_foundPrimes_iff, hLeft, hRight]

/-- **RIGIDITE.**  Aucun premier n'est déplacé : l'appartenance d'un premier à
l'ensemble trouvé se décide sur sa seule valeur, comparée aux deux bords. -/
theorem thm_foundPrimes_no_prime_is_moved
    (tInterval : TAlgebraicInterval) {nPrime : ℕ} (hPrime : Nat.Prime nPrime) :
    nPrime ∈ sAlgebraicIntervalFoundPrimes tInterval ↔
      (tInterval.rLeftEndpoint < (nPrime : ℝ) ∧
        (nPrime : ℝ) ≤ tInterval.rRightEndpoint) := by
  rw [thm_mem_foundPrimes_iff]
  exact ⟨fun hMember => hMember.2, fun hRange => ⟨hPrime, hRange⟩⟩

/-! ## 5. L'ensemble trouvé est EN GENERAL PLURIEL -/

/-- L'intervalle algébrique `(1, 4]`. -/
noncomputable def tWitnessInterval : TAlgebraicInterval where
  rLeftEndpoint := 1
  rRightEndpoint := 4
  hLeftPositive := by norm_num
  hOrdered := by norm_num

/-- Un second intervalle algébrique témoin, `(1, 8]`, distinct du premier. -/
noncomputable def tWitnessSecondInterval : TAlgebraicInterval where
  rLeftEndpoint := 1
  rRightEndpoint := 8
  hLeftPositive := by norm_num
  hOrdered := by norm_num

/-- **La loi de centralité a un sens : l'ensemble trouvé est en général
pluriel.**  L'intervalle `(1, 4]` porte les deux nombres trouvés `2` et `3`.

Ce théorème est le garde-fou permanent contre la lecture retirée « la cellule
ne contient qu'un seul premier » : un ensemble trouvé de cardinal au moins deux
existe, donc le cardinal un n'est jamais la loi générale. -/
theorem thm_foundPrimes_generallyPlural :
    2 ≤ (sAlgebraicIntervalFoundPrimes tWitnessInterval).card := by
  have hTwo : (2 : ℕ) ∈ sAlgebraicIntervalFoundPrimes tWitnessInterval := by
    rw [thm_mem_foundPrimes_iff]
    exact ⟨Nat.prime_two, by norm_num [tWitnessInterval],
      by norm_num [tWitnessInterval]⟩
  have hThree : (3 : ℕ) ∈ sAlgebraicIntervalFoundPrimes tWitnessInterval := by
    rw [thm_mem_foundPrimes_iff]
    exact ⟨Nat.prime_three, by norm_num [tWitnessInterval],
      by norm_num [tWitnessInterval]⟩
  have hSubset : ({2, 3} : Finset ℕ) ⊆ sAlgebraicIntervalFoundPrimes tWitnessInterval := by
    intro nCandidate hMember
    rcases Finset.mem_insert.mp hMember with hEq | hEq
    · exact hEq ▸ hTwo
    · exact (Finset.mem_singleton.mp hEq) ▸ hThree
  have hCard : ({2, 3} : Finset ℕ).card = 2 := by decide
  calc 2 = ({2, 3} : Finset ℕ).card := hCard.symm
    _ ≤ _ := Finset.card_le_card hSubset

end RHV3Lean
