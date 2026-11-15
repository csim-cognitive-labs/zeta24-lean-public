/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# RHV3Lean — multiplicité analytique des zéros de ζ et troncation radiale finie

    TRACE_ID              : RHV3-ZETA-ZERO-MULTIPLICITY
    SEMANTIC_OBJECT       : l'objet spectral fini requis avant toute formule
                            de Perron — les zéros de `riemannZeta` dans un
                            disque fermé, comptés avec leur multiplicité
                            analytique. Aucune formule explicite, aucun reste
                            borné ici.
    SEMANTIC_STATEMENT    : ce module ne parle d'aucune Tour, d'aucun membre
                            RHV3 — il construit, uniquement depuis Mathlib
                            (`riemannZeta`, `analyticOrderAt`), l'objet
                            spectral canonique consommé par le côté ZÉRO du
                            canal M9a.
    MATHEMATICAL_STATEMENT: tout zéro de ζ a un ordre analytique fini et
                            strictement positif ; tout disque fermé ne
                            contient qu'un nombre fini de zéros ; la somme
                            spectrale tronquée pondérée par la multiplicité
                            est ℂ-linéaire.
    MATHEMATICAL_PARENT   : Mathlib (`Mathlib.Analysis.Analytic.Order`,
                            `Mathlib.NumberTheory.LSeries.ZetaZeros`).
    PROOF_STRATEGY        : transcription directe du corps déjà vérifié dans
                            `rh_gap_criterion` (mathlib `fabf563a`, 15/06),
                            revérifiée ici contre le mathlib de RHV3
                            (`51e6992e`, 03/08) sans aucune adaptation requise
                            — aucune preuve nouvelle, portage mécanique.
    REQUIRED_LEMMAS       : analyticOn_riemannZeta, riemannZeta_ne_zero_of_one_le_re,
                            analyticOrderAt_eq_top, Nat.cast_analyticOrderNatAt,
                            IsCompact.inter_riemannZetaZeros_finite
    WHY_EACH_LEMMA_EXISTS : les deux premiers donnent l'analyticité et la
                            non-annulation en `2` (ancre du principe
                            d'identité) ; les deux suivants relient l'ordre
                            analytique `ℕ∞` à sa version `ℕ` ; le dernier donne
                            la finitude radiale.
    LEAN_DEFINITION       : IsTrivialZetaZero, IsNontrivialZetaZero,
                            zetaZeroMultiplicity, zetaZerosInClosedBall,
                            zetaZerosFinset, nontrivialZetaZerosFinset,
                            truncatedZetaZeroSum
    LEAN_THEOREM          : zetaZeroMultiplicity_pos, zetaZerosInClosedBall_finite,
                            zetaZerosFinset_mono, truncatedZetaZeroSum_add
    SAME_MEMBER_CHECK     : sans objet — aucun membre RHV3 ici.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet à ce niveau — objet purement spectral.
    FORBIDDEN_PREMISES    : ce module ne mentionne aucun zéro RHV3
                            (`TUpperNonTrivialZetaZero`), aucune Tour, aucun
                            T1/T2/PMirrorCollision/RH ; il ne construit que
                            l'objet spectral ANALYTIQUE brut de Mathlib.
    NEXT_CONSUMER         : la formule de Perron (encore à porter), qui devra
                            exprimer `truncatedZetaZeroSum` en fonction de
                            l'intégrale de contour, puis se raccorder à
                            `rPsiZeroChannel`.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED (portage mécanique, revérifié)

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV3Lean

open Set Filter Finset BigOperators
open scoped Topology

/-- Un zéro trivial de ζ est un entier pair strictement négatif. -/
def IsTrivialZetaZero (ρ : ℂ) : Prop :=
  ∃ n : ℕ, ρ = -2 * (n + 1)

/-- Prédicat de zéro non trivial. -/
def IsNontrivialZetaZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ ¬ IsTrivialZetaZero ρ ∧ ρ ≠ 1

/-- Un zéro de ζ ne peut pas être le pôle `1`. -/
theorem zetaZero_ne_one {ρ : ℂ} (hρ : riemannZeta ρ = 0) : ρ ≠ 1 := by
  intro h
  subst ρ
  exact riemannZeta_one_ne_zero hρ

/-- ζ est analytique en chacun de ses zéros. -/
theorem analyticAt_riemannZeta_of_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    AnalyticAt ℂ riemannZeta ρ := by
  apply analyticOn_riemannZeta
  simpa using zetaZero_ne_one hρ

/-- Le complément du pôle est préconnexe dans `ℂ`. -/
lemma isPreconnected_compl_one_complex :
    IsPreconnected (({1} : Set ℂ)ᶜ) := by
  exact (isConnected_compl_singleton_of_one_lt_rank (E := ℂ) (by simp) 1).isPreconnected

/-- L'ordre analytique de ζ en un zéro est fini. -/
theorem riemannZeta_analyticOrderAt_ne_top {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  intro htop
  have hevent : riemannZeta =ᶠ[𝓝 ρ] 0 :=
    analyticOrderAt_eq_top.mp htop
  have hρmem : ρ ∈ ({1}ᶜ : Set ℂ) := by
    simpa using zetaZero_ne_one hρ
  have hzero_on : Set.EqOn riemannZeta 0 ({1}ᶜ : Set ℂ) :=
    analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_compl_one_complex hρmem hevent
  have htwo_mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have htwo_zero : riemannZeta (2 : ℂ) = 0 := by
    simpa using hzero_on htwo_mem
  exact (riemannZeta_ne_zero_of_one_le_re (by norm_num)) htwo_zero

/-- Multiplicité analytique naturelle d'un zéro de ζ. -/
noncomputable def zetaZeroMultiplicity (ρ : ℂ) : ℕ :=
  analyticOrderNatAt riemannZeta ρ

/-- Chaque zéro de ζ a une multiplicité strictement positive. -/
theorem zetaZeroMultiplicity_pos {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    0 < zetaZeroMultiplicity ρ := by
  have hana := analyticAt_riemannZeta_of_zero hρ
  have horder_ne : analyticOrderAt riemannZeta ρ ≠ 0 :=
    hana.analyticOrderAt_ne_zero.mpr hρ
  have hfinite := riemannZeta_analyticOrderAt_ne_top hρ
  have hnat_ne : zetaZeroMultiplicity ρ ≠ 0 := by
    intro hnat
    have hnat' : analyticOrderNatAt riemannZeta ρ = 0 := by
      simpa [zetaZeroMultiplicity] using hnat
    have hcast := Nat.cast_analyticOrderNatAt hfinite
    have hzero : analyticOrderAt riemannZeta ρ = 0 := by
      rw [← hcast, hnat']
      simp
    exact horder_ne hzero
  exact Nat.pos_of_ne_zero hnat_ne

/-- Ensemble des zéros de ζ dans le disque fermé centré en `0`. -/
def zetaZerosInClosedBall (R : ℝ) : Set ℂ :=
  Metric.closedBall 0 R ∩ riemannZetaZeros

/-- Tout disque fermé contient un nombre fini de zéros de ζ. -/
theorem zetaZerosInClosedBall_finite (R : ℝ) :
    (zetaZerosInClosedBall R).Finite := by
  exact (isCompact_closedBall (0 : ℂ) R).inter_riemannZetaZeros_finite

/-- Troncation finie canonique des zéros par rayon. -/
noncomputable def zetaZerosFinset (R : ℝ) : Finset ℂ :=
  (zetaZerosInClosedBall_finite R).toFinset

@[simp] theorem mem_zetaZerosFinset {R : ℝ} {ρ : ℂ} :
    ρ ∈ zetaZerosFinset R ↔
      ρ ∈ Metric.closedBall (0 : ℂ) R ∧ riemannZeta ρ = 0 := by
  simp [zetaZerosFinset, zetaZerosInClosedBall, mem_riemannZetaZeros]

/-- Les troncations radiales sont emboîtées. -/
theorem zetaZerosFinset_mono {R S : ℝ} (hRS : R ≤ S) :
    zetaZerosFinset R ⊆ zetaZerosFinset S := by
  intro ρ hρ
  rw [mem_zetaZerosFinset] at hρ ⊢
  exact ⟨Metric.closedBall_subset_closedBall hRS hρ.1, hρ.2⟩

/-- Zéros non triviaux dans la troncation radiale. -/
noncomputable def nontrivialZetaZerosFinset (R : ℝ) : Finset ℂ := by
  classical
  exact (zetaZerosFinset R).filter fun ρ =>
    ¬ IsTrivialZetaZero ρ ∧ ρ ≠ 1

@[simp] theorem mem_nontrivialZetaZerosFinset {R : ℝ} {ρ : ℂ} :
    ρ ∈ nontrivialZetaZerosFinset R ↔
      ‖ρ‖ ≤ R ∧ IsNontrivialZetaZero ρ := by
  classical
  simp [nontrivialZetaZerosFinset, IsNontrivialZetaZero,
    mem_zetaZerosFinset, and_assoc]

/-- Somme spectrale finie, pondérée par la multiplicité analytique. -/
noncomputable def truncatedZetaZeroSum (R : ℝ) (F : ℂ → ℂ) : ℂ :=
  ∑ ρ ∈ nontrivialZetaZerosFinset R,
    (zetaZeroMultiplicity ρ : ℂ) * F ρ

/-- Linéarité exacte de la somme spectrale tronquée. -/
theorem truncatedZetaZeroSum_add (R : ℝ) (F G : ℂ → ℂ) :
    truncatedZetaZeroSum R (fun ρ => F ρ + G ρ)
      = truncatedZetaZeroSum R F + truncatedZetaZeroSum R G := by
  unfold truncatedZetaZeroSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

/-- La somme nulle vaut zéro. -/
@[simp] theorem truncatedZetaZeroSum_zero (R : ℝ) :
    truncatedZetaZeroSum R (fun _ => 0) = 0 := by
  simp [truncatedZetaZeroSum]

#check IsNontrivialZetaZero
#check zetaZeroMultiplicity
#check zetaZeroMultiplicity_pos
#check zetaZerosFinset
#check nontrivialZetaZerosFinset
#check truncatedZetaZeroSum
#check truncatedZetaZeroSum_add

end RHV3Lean
