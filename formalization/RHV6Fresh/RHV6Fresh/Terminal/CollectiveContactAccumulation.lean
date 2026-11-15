/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ContactValueGeometry
import RHV6Fresh.Terminal.HeightPacket

/-!
# RHV6Fresh — accumulation collective des valeurs des Tours (mission, 2026-11-03, module B)

Chaque zéro non trivial `ρ` (indice `ExplicitIndex`, deux branches) porte une Tour dont les
contacts sont ceux de ses propres paramètres `(Re ρ, Im ρ)`. Pour une famille finie `s` d'indices
et une contribution `F ρ`, l'accumulation collective est la somme, sur `s`, des accumulations
signées de chaque Tour sur ses propres intervalles de contacts, bords compris.

Résultats (inconditionnels, aucune prémisse, aucun `sorry`) :

* `finite_contact_accumulation_eq_spectral_difference` : `A_s(a, x) = Σ_{ρ∈s} (F_ρ(x) − F_ρ(a))`.
* `finite_contact_accumulation_add`, `_chain`, `_split` : additivité sur les familles disjointes,
  enchaînement `a → b → c`, découpage par un prédicat sur les indices.
* `finite_contact_accumulation_order_independent` : toute énumération sans répétition de `s`
  donne la même somme.
* `geometricTower_conj`, `rawTowerTerm_conj`, `integratedTowerTerm_conj` : conjugaison exacte des
  contributions (multiplicité conservée par `zetaZeroMultiplicity_conj`).
* `finite_contact_accumulation_real` : sur une famille stable par conjugaison, l'accumulation
  collective est réelle (partie imaginaire nulle) — c'est la convention de conjugaison explicitée.
* `finite_contact_accumulation_partition_independent` : les découpages ne changent rien.

Les deux canaux sont tenus séparés : `rawTowerTerm ρ x = −m·x^ρ/ρ` (canal brut) et
`integratedTowerTerm ρ x = −m·x^ρ/(ρ(ρ+1)) = nontrivialZeroResidueTerm x ρ` (canal intégré compilé).
-/

namespace RHV6Fresh

open RHV3Lean Complex ComplexConjugate

/-! ## 1. Les deux canaux d'une Tour indexée -/

/-- Canal brut : `−m(ρ) · x^ρ/ρ`. -/
noncomputable def rawTowerTerm (ρ : ExplicitIndex) (x : ℝ) : ℂ :=
  -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * towerValue (ρ : ℂ) x

/-- Canal intégré : `−m(ρ) · x^ρ/(ρ(ρ+1))`. -/
noncomputable def integratedTowerTerm (ρ : ExplicitIndex) (x : ℝ) : ℂ :=
  -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * integratedTower (ρ : ℂ) x

/-- Le canal intégré est exactement le terme résiduel de la formule explicite compilée. -/
theorem integratedTowerTerm_eq_residue (ρ : ExplicitIndex) (x : ℝ) :
    integratedTowerTerm ρ x = nontrivialZeroResidueTerm x ρ := rfl

/-- Passage brut → intégré, indice par indice : division par `ρ + 1`. -/
theorem integratedTowerTerm_eq_raw_div (ρ : ExplicitIndex) (x : ℝ) :
    integratedTowerTerm ρ x = rawTowerTerm ρ x / ((ρ : ℂ) + 1) := by
  unfold integratedTowerTerm rawTowerTerm
  rw [integratedTower_eq_geometric_div, mul_div_assoc]

/-! ## 2. Accumulation d'une Tour sur ses propres contacts, puis collective -/

/-- L'accumulation d'une Tour indexée sur SES contacts `(Re ρ, Im ρ)`, de `a` à `x`. -/
noncomputable def towerAccumulation (F : ExplicitIndex → ℝ → ℂ) (ρ : ExplicitIndex)
    (k₀ : ℤ) (n : ℕ) (a x : ℝ) : ℂ :=
  accumulationFrom (F ρ) (ρ : ℂ).re (ρ : ℂ).im k₀ n a x

theorem towerAccumulation_eq (F : ExplicitIndex → ℝ → ℂ) (ρ : ExplicitIndex) (k₀ : ℤ) (n : ℕ)
    (a x : ℝ) : towerAccumulation F ρ k₀ n a x = F ρ x - F ρ a :=
  contact_accumulation_eq_endpoint_difference _ _ _ _ _ _ _

/-- **L'accumulation collective** sur une famille finie `s`, chaque Tour avec son propre découpage
(`k₀ ρ` intervalles de départ, `n ρ` intervalles complets). -/
noncomputable def collectiveAccumulation (s : Finset ExplicitIndex) (F : ExplicitIndex → ℝ → ℂ)
    (k₀ : ExplicitIndex → ℤ) (n : ExplicitIndex → ℕ) (a x : ℝ) : ℂ :=
  ∑ ρ ∈ s, towerAccumulation F ρ (k₀ ρ) (n ρ) a x

/-- **Accumulation collective = différence spectrale finie.** -/
theorem finite_contact_accumulation_eq_spectral_difference (s : Finset ExplicitIndex)
    (F : ExplicitIndex → ℝ → ℂ) (k₀ : ExplicitIndex → ℤ) (n : ExplicitIndex → ℕ) (a x : ℝ) :
    collectiveAccumulation s F k₀ n a x = ∑ ρ ∈ s, (F ρ x - F ρ a) := by
  unfold collectiveAccumulation
  exact Finset.sum_congr rfl (fun ρ _ => towerAccumulation_eq F ρ _ _ a x)

/-- Additivité sur deux familles disjointes. -/
theorem finite_contact_accumulation_add {s t : Finset ExplicitIndex} (hd : Disjoint s t)
    (F : ExplicitIndex → ℝ → ℂ) (k₀ : ExplicitIndex → ℤ) (n : ExplicitIndex → ℕ) (a x : ℝ) :
    collectiveAccumulation (s ∪ t) F k₀ n a x =
      collectiveAccumulation s F k₀ n a x + collectiveAccumulation t F k₀ n a x := by
  unfold collectiveAccumulation
  exact Finset.sum_union hd

/-- Enchaînement `a → b → c`. -/
theorem finite_contact_accumulation_chain (s : Finset ExplicitIndex) (F : ExplicitIndex → ℝ → ℂ)
    (k₀ k₀' : ExplicitIndex → ℤ) (n n' : ExplicitIndex → ℕ) (a b c : ℝ) :
    collectiveAccumulation s F k₀ n a b + collectiveAccumulation s F k₀' n' b c =
      collectiveAccumulation s F k₀ n a c := by
  rw [finite_contact_accumulation_eq_spectral_difference,
    finite_contact_accumulation_eq_spectral_difference,
    finite_contact_accumulation_eq_spectral_difference, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun ρ _ => by ring)

/-- Découpage par un prédicat sur les indices (fréquences basses / hautes, etc.). -/
theorem finite_contact_accumulation_split (s : Finset ExplicitIndex) (P : ExplicitIndex → Prop)
    [DecidablePred P] (F : ExplicitIndex → ℝ → ℂ) (k₀ : ExplicitIndex → ℤ)
    (n : ExplicitIndex → ℕ) (a x : ℝ) :
    collectiveAccumulation s F k₀ n a x =
      collectiveAccumulation (s.filter P) F k₀ n a x +
        collectiveAccumulation (s.filter (fun ρ => ¬ P ρ)) F k₀ n a x := by
  unfold collectiveAccumulation
  exact (Finset.sum_filter_add_sum_filter_not s P _).symm

/-- **Indépendance de l'ordre** : toute énumération sans répétition de `s` donne la même somme. -/
theorem finite_contact_accumulation_order_independent (l : List ExplicitIndex) (hl : l.Nodup)
    (F : ExplicitIndex → ℝ → ℂ) (k₀ : ExplicitIndex → ℤ) (n : ExplicitIndex → ℕ) (a x : ℝ) :
    (l.map (fun ρ => towerAccumulation F ρ (k₀ ρ) (n ρ) a x)).sum =
      collectiveAccumulation l.toFinset F k₀ n a x := by
  unfold collectiveAccumulation
  rw [List.sum_toFinset _ hl]

/-- **Indépendance du découpage** : deux systèmes de découpages donnent la même accumulation. -/
theorem finite_contact_accumulation_partition_independent (s : Finset ExplicitIndex)
    (F : ExplicitIndex → ℝ → ℂ) (k₀ k₀' : ExplicitIndex → ℤ) (n n' : ExplicitIndex → ℕ)
    (a x : ℝ) : collectiveAccumulation s F k₀ n a x = collectiveAccumulation s F k₀' n' a x := by
  rw [finite_contact_accumulation_eq_spectral_difference,
    finite_contact_accumulation_eq_spectral_difference]

/-! ## 3. Conjugaison -/

/-- L'indice conjugué. -/
noncomputable def conjugateIndex (ρ : ExplicitIndex) : ExplicitIndex :=
  ⟨conj (ρ : ℂ), (isNontrivialZetaZero_conj_iff _).mpr ρ.2⟩

theorem conjugateIndex_conjugateIndex (ρ : ExplicitIndex) :
    conjugateIndex (conjugateIndex ρ) = ρ := by
  unfold conjugateIndex
  apply Subtype.ext
  simp

theorem conjugateIndex_val (ρ : ExplicitIndex) : (conjugateIndex ρ : ℂ) = conj (ρ : ℂ) := rfl

/-- `x^{ρ̄}/ρ̄ = conj(x^ρ/ρ)` pour `x > 0`. -/
theorem geometricTower_conj (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    towerValue (conj ρ) x = conj (towerValue ρ x) := by
  unfold towerValue
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm
  rw [map_div₀, Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

theorem integratedTower_conj (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    integratedTower (conj ρ) x = conj (integratedTower ρ x) := by
  rw [integratedTower_eq_geometric_div, integratedTower_eq_geometric_div, map_div₀,
    geometricTower_conj ρ hx]
  simp

theorem rawTowerTerm_conj (ρ : ExplicitIndex) {x : ℝ} (hx : 0 < x) :
    rawTowerTerm (conjugateIndex ρ) x = conj (rawTowerTerm ρ x) := by
  unfold rawTowerTerm
  rw [conjugateIndex_val, geometricTower_conj _ hx, zetaZeroMultiplicity_conj ρ.2.1]
  simp

theorem integratedTowerTerm_conj (ρ : ExplicitIndex) {x : ℝ} (hx : 0 < x) :
    integratedTowerTerm (conjugateIndex ρ) x = conj (integratedTowerTerm ρ x) := by
  unfold integratedTowerTerm
  rw [conjugateIndex_val, integratedTower_conj _ hx, zetaZeroMultiplicity_conj ρ.2.1]
  simp

/-- Une famille stable par conjugaison. -/
def ConjClosed (s : Finset ExplicitIndex) : Prop := ∀ ρ ∈ s, conjugateIndex ρ ∈ s

/-- Une somme sur une famille stable par conjugaison d'une contribution conj-équivariante est
réelle. -/
theorem sum_im_eq_zero_of_conjClosed {s : Finset ExplicitIndex} (hs : ConjClosed s)
    {G : ExplicitIndex → ℂ} (hG : ∀ ρ, G (conjugateIndex ρ) = conj (G ρ)) :
    (∑ ρ ∈ s, G ρ).im = 0 := by
  rw [← Complex.conj_eq_iff_im, map_sum]
  symm
  refine Finset.sum_nbij' conjugateIndex conjugateIndex (fun ρ hρ => hs ρ hρ) (fun ρ hρ => hs ρ hρ)
    (fun ρ _ => conjugateIndex_conjugateIndex ρ) (fun ρ _ => conjugateIndex_conjugateIndex ρ)
    (fun ρ _ => ?_)
  rw [hG, Complex.conj_conj]

/-- **Réalité de l'accumulation collective** sur une famille stable par conjugaison, pour le canal
brut comme pour le canal intégré (`a, x > 0`). -/
theorem finite_contact_accumulation_real {s : Finset ExplicitIndex} (hs : ConjClosed s)
    (k₀ : ExplicitIndex → ℤ) (n : ExplicitIndex → ℕ) {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (collectiveAccumulation s rawTowerTerm k₀ n a x).im = 0 ∧
      (collectiveAccumulation s integratedTowerTerm k₀ n a x).im = 0 := by
  rw [finite_contact_accumulation_eq_spectral_difference,
    finite_contact_accumulation_eq_spectral_difference]
  constructor
  · exact sum_im_eq_zero_of_conjClosed hs (fun ρ => by
      rw [rawTowerTerm_conj ρ hx, rawTowerTerm_conj ρ ha, map_sub])
  · exact sum_im_eq_zero_of_conjClosed hs (fun ρ => by
      rw [integratedTowerTerm_conj ρ hx, integratedTowerTerm_conj ρ ha, map_sub])

#print axioms finite_contact_accumulation_eq_spectral_difference
#print axioms finite_contact_accumulation_real

end RHV6Fresh
