/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaPerronFiniteRectangle
import RHV3Lean.Objects.ZetaConjugationOrbit

/-!
# Tour 23-B - P3c3: finite Perron residue classification

This module classifies the finite singularities used by the P3c2 rectangle,
computes the corresponding residues, and keeps all P3c2 boundary terms.
-/

open Set Filter Finset BigOperators Complex
open scoped Topology ComplexConjugate

namespace RHV3Lean

/-! ## Zero partition -/

/-- Existing canonical trivial zero predicate, restated as a theorem for the P3c3 contract. -/
theorem isTrivialZetaZero_riemannZeta_zero
    {ρ : ℂ} (hρ : IsTrivialZetaZero ρ) :
    riemannZeta ρ = 0 := by
  rcases hρ with ⟨n, rfl⟩
  exact riemannZeta_neg_two_mul_nat_add_one n

/-- Every zero of `ζ` is either trivial or nontrivial in the RH-compatible predicate. -/
theorem zetaZero_trivial_or_nontrivial
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    IsTrivialZetaZero ρ ∨ IsNontrivialZetaZero ρ := by
  by_cases htriv : IsTrivialZetaZero ρ
  · exact Or.inl htriv
  · exact Or.inr ⟨hρ, htriv, zetaZero_ne_one hρ⟩

/-- Trivial and nontrivial zero predicates are disjoint by definition. -/
theorem trivialZetaZero_not_nontrivial
    {ρ : ℂ} :
    ¬ (IsTrivialZetaZero ρ ∧ IsNontrivialZetaZero ρ) := by
  rintro ⟨htriv, hnon⟩
  exact hnon.2.1 htriv

/-! ## Finite sets in the P3c2 rectangle -/

def zetaPerronTrivialZeroSet (σR : ℝ) (N : ℕ) (T : ℝ) : Set ℂ :=
  Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) ∩
    {ρ | IsTrivialZetaZero ρ}

def zetaPerronNontrivialZeroSet (σR : ℝ) (N : ℕ) (T : ℝ) : Set ℂ :=
  Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) ∩
    {ρ | IsNontrivialZetaZero ρ}

def zetaPerronClassifiedSingularitySet (_x : ℝ) (σR : ℝ) (N : ℕ) (T : ℝ) : Set ℂ :=
  Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) ∩
    (({1} : Set ℂ) ∪ {0} ∪ {-1} ∪
      {ρ | IsTrivialZetaZero ρ} ∪ {ρ | IsNontrivialZetaZero ρ})

def zetaPerronSpecialPointSet : Set ℂ :=
  ({1} : Set ℂ) ∪ {0} ∪ {-1}

private lemma p3c3_perronRectangle_isCompact (N : ℕ) (σR T : ℝ) :
    IsCompact (Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T)) := by
  rw [Rectangle]
  exact isCompact_uIcc.reProdIm isCompact_uIcc

private lemma p3c3_perronRectangle_re_le {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    (perronRectangleLowerLeft N T).re ≤ (perronRectangleUpperRight σR T).re := by
  simp [perronRectangleLowerLeft, perronRectangleUpperRight, perronRectangleSigmaL]
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast h.N_ge_one
  nlinarith [h.sigmaR_gt]

private lemma p3c3_perronRectangle_im_le {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    (perronRectangleLowerLeft N T).im ≤ (perronRectangleUpperRight σR T).im := by
  simp [perronRectangleLowerLeft, perronRectangleUpperRight]
  linarith [h.T_pos]

lemma one_mem_zetaPerronRectangle {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    (1 : ℂ) ∈ Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) := by
  rw [mem_Rect (p3c3_perronRectangle_re_le h) (p3c3_perronRectangle_im_le h)]
  simp [perronRectangleLowerLeft, perronRectangleUpperRight, perronRectangleSigmaL]
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast h.N_ge_one
  constructor
  · nlinarith
  · constructor
    · linarith [h.sigmaR_gt]
    · linarith [h.T_pos]

lemma zero_mem_zetaPerronRectangle {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    (0 : ℂ) ∈ Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) := by
  rw [mem_Rect (p3c3_perronRectangle_re_le h) (p3c3_perronRectangle_im_le h)]
  simp [perronRectangleLowerLeft, perronRectangleUpperRight, perronRectangleSigmaL]
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast h.N_ge_one
  constructor
  · nlinarith
  · constructor
    · linarith [h.sigmaR_gt]
    · linarith [h.T_pos]

lemma neg_one_mem_zetaPerronRectangle {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    (-1 : ℂ) ∈ Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) := by
  rw [mem_Rect (p3c3_perronRectangle_re_le h) (p3c3_perronRectangle_im_le h)]
  simp [perronRectangleLowerLeft, perronRectangleUpperRight, perronRectangleSigmaL]
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast h.N_ge_one
  repeat' constructor <;> nlinarith [h.sigmaR_gt, h.T_pos, hN]

lemma zetaPerron_trivial_zero_set_subset_zeros {σR : ℝ} {N : ℕ} {T : ℝ} :
    zetaPerronTrivialZeroSet σR N T ⊆ riemannZetaZeros := by
  intro ρ hρ
  rw [mem_riemannZetaZeros]
  exact isTrivialZetaZero_riemannZeta_zero hρ.2

lemma zetaPerron_nontrivial_zero_set_subset_zeros {σR : ℝ} {N : ℕ} {T : ℝ} :
    zetaPerronNontrivialZeroSet σR N T ⊆ riemannZetaZeros := by
  intro ρ hρ
  rw [mem_riemannZetaZeros]
  exact hρ.2.1

theorem zetaPerron_trivial_zero_set_finite (σR : ℝ) (N : ℕ) (T : ℝ) :
    (zetaPerronTrivialZeroSet σR N T).Finite := by
  have hzero :
      (Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) ∩
        riemannZetaZeros).Finite :=
    (p3c3_perronRectangle_isCompact N σR T).inter_riemannZetaZeros_finite
  exact hzero.subset (by
    intro ρ hρ
    exact ⟨hρ.1, zetaPerron_trivial_zero_set_subset_zeros hρ⟩)

theorem zetaPerron_nontrivial_zero_set_finite (σR : ℝ) (N : ℕ) (T : ℝ) :
    (zetaPerronNontrivialZeroSet σR N T).Finite := by
  have hzero :
      (Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) ∩
        riemannZetaZeros).Finite :=
    (p3c3_perronRectangle_isCompact N σR T).inter_riemannZetaZeros_finite
  exact hzero.subset (by
    intro ρ hρ
    exact ⟨hρ.1, zetaPerron_nontrivial_zero_set_subset_zeros hρ⟩)

theorem zetaPerron_classified_singularity_set_finite
    (x σR : ℝ) (N : ℕ) (T : ℝ) :
    (zetaPerronClassifiedSingularitySet x σR N T).Finite := by
  have hpoints :
      (Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) ∩
        (({1} : Set ℂ) ∪ {0} ∪ {-1})).Finite := by
    exact (Set.Finite.union (Set.Finite.union (Set.finite_singleton _) (Set.finite_singleton _))
      (Set.finite_singleton _)).inter_of_right _
  have htriv := zetaPerron_trivial_zero_set_finite σR N T
  have hnon := zetaPerron_nontrivial_zero_set_finite σR N T
  have heq :
      zetaPerronClassifiedSingularitySet x σR N T =
        (Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) ∩
          (({1} : Set ℂ) ∪ {0} ∪ {-1})) ∪
        zetaPerronTrivialZeroSet σR N T ∪
        zetaPerronNontrivialZeroSet σR N T := by
    ext ρ
    simp [zetaPerronClassifiedSingularitySet, zetaPerronTrivialZeroSet,
      zetaPerronNontrivialZeroSet, and_or_left, or_assoc]
  rw [heq]
  exact Set.Finite.union (Set.Finite.union hpoints htriv) hnon

noncomputable def zetaPerronTrivialZeroFinset (σR : ℝ) (N : ℕ) (T : ℝ) : Finset ℂ :=
  (zetaPerron_trivial_zero_set_finite σR N T).toFinset

noncomputable def zetaPerronNontrivialZeroFinset (σR : ℝ) (N : ℕ) (T : ℝ) : Finset ℂ :=
  (zetaPerron_nontrivial_zero_set_finite σR N T).toFinset

noncomputable def zetaPerronClassifiedSingularityFinset
    (x σR : ℝ) (N : ℕ) (T : ℝ) : Finset ℂ :=
  (zetaPerron_classified_singularity_set_finite x σR N T).toFinset

noncomputable def zetaPerronSpecialPointFinset : Finset ℂ :=
  ({1, 0, -1} : Finset ℂ)

theorem zetaPerron_classified_singularity_set_eq_union
    {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    zetaPerronClassifiedSingularitySet x σR N T =
      zetaPerronSpecialPointSet ∪
        zetaPerronTrivialZeroSet σR N T ∪
        zetaPerronNontrivialZeroSet σR N T := by
  ext ρ
  constructor
  · intro hρ
    rcases hρ with ⟨hrect, hcat⟩
    rcases hcat with (((h1 | h0) | hn) | htriv) | hnon
    · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h0)))
    · exact Or.inl (Or.inl (Or.inr hn))
    · exact Or.inl (Or.inr ⟨hrect, htriv⟩)
    · exact Or.inr ⟨hrect, hnon⟩
  · intro hρ
    rcases hρ with (hsp | htriv) | hnon
    · rcases hsp with (h1 | h0) | hn
      · have hρ1 : ρ = 1 := by simpa using h1
        exact ⟨by simpa [hρ1] using one_mem_zetaPerronRectangle h,
          Or.inl (Or.inl (Or.inl (Or.inl h1)))⟩
      · have hρ0 : ρ = 0 := by simpa using h0
        exact ⟨by simpa [hρ0] using zero_mem_zetaPerronRectangle h,
          Or.inl (Or.inl (Or.inl (Or.inr h0)))⟩
      · have hρn : ρ = -1 := by simpa using hn
        exact ⟨by simpa [hρn] using neg_one_mem_zetaPerronRectangle h,
          Or.inl (Or.inl (Or.inr hn))⟩
    · exact ⟨htriv.1, Or.inl (Or.inr htriv.2)⟩
    · exact ⟨hnon.1, Or.inr hnon.2⟩

theorem zetaPerron_classified_singularity_finset_eq_union
    {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    zetaPerronClassifiedSingularityFinset x σR N T =
      (zetaPerronSpecialPointFinset ∪ zetaPerronTrivialZeroFinset σR N T) ∪
        zetaPerronNontrivialZeroFinset σR N T := by
  classical
  ext ρ
  simp [zetaPerronClassifiedSingularityFinset, zetaPerronTrivialZeroFinset,
    zetaPerronNontrivialZeroFinset, zetaPerronSpecialPointFinset,
    zetaPerronSpecialPointSet, zetaPerron_classified_singularity_set_eq_union h]
  tauto

lemma zetaPerron_special_disjoint_trivial (σR : ℝ) (N : ℕ) (T : ℝ) :
    Disjoint zetaPerronSpecialPointFinset (zetaPerronTrivialZeroFinset σR N T) := by
  classical
  rw [Finset.disjoint_left]
  intro ρ hsp htr
  simp [zetaPerronSpecialPointFinset] at hsp
  have htriv : IsTrivialZetaZero ρ := by
    have hmem : ρ ∈ zetaPerronTrivialZeroSet σR N T := by
      simpa [zetaPerronTrivialZeroFinset] using htr
    exact hmem.2
  rcases hsp with h1 | h0 | hn
  · exact zetaZero_ne_one (isTrivialZetaZero_riemannZeta_zero htriv) (by simpa using h1)
  · exact zetaZero_ne_zero (isTrivialZetaZero_riemannZeta_zero htriv) (by simpa using h0)
  · exact zetaZero_ne_negOne (isTrivialZetaZero_riemannZeta_zero htriv) (by simpa using hn)

lemma zetaPerron_special_disjoint_nontrivial (σR : ℝ) (N : ℕ) (T : ℝ) :
    Disjoint zetaPerronSpecialPointFinset (zetaPerronNontrivialZeroFinset σR N T) := by
  classical
  rw [Finset.disjoint_left]
  intro ρ hsp hnonmem
  simp [zetaPerronSpecialPointFinset] at hsp
  have hnon : IsNontrivialZetaZero ρ := by
    have hmem : ρ ∈ zetaPerronNontrivialZeroSet σR N T := by
      simpa [zetaPerronNontrivialZeroFinset] using hnonmem
    exact hmem.2
  rcases hsp with h1 | h0 | hn
  · exact hnon.2.2 (by simpa using h1)
  · exact zetaZero_ne_zero hnon.1 (by simpa using h0)
  · exact zetaZero_ne_negOne hnon.1 (by simpa using hn)

lemma zetaPerron_trivial_disjoint_nontrivial (σR : ℝ) (N : ℕ) (T : ℝ) :
    Disjoint (zetaPerronTrivialZeroFinset σR N T)
      (zetaPerronNontrivialZeroFinset σR N T) := by
  classical
  rw [Finset.disjoint_left]
  intro ρ htrmem hnonmem
  have htriv : IsTrivialZetaZero ρ := by
    have hmem : ρ ∈ zetaPerronTrivialZeroSet σR N T := by
      simpa [zetaPerronTrivialZeroFinset] using htrmem
    exact hmem.2
  have hnon : IsNontrivialZetaZero ρ := by
    have hmem : ρ ∈ zetaPerronNontrivialZeroSet σR N T := by
      simpa [zetaPerronNontrivialZeroFinset] using hnonmem
    exact hmem.2
  exact hnon.2.1 htriv

lemma zetaPerron_special_union_trivial_disjoint_nontrivial
    (σR : ℝ) (N : ℕ) (T : ℝ) :
    Disjoint (zetaPerronSpecialPointFinset ∪ zetaPerronTrivialZeroFinset σR N T)
      (zetaPerronNontrivialZeroFinset σR N T) := by
  classical
  rw [Finset.disjoint_left]
  intro ρ hleft hnon
  rw [Finset.mem_union] at hleft
  rcases hleft with hsp | htr
  · exact Finset.disjoint_left.mp (zetaPerron_special_disjoint_nontrivial σR N T) hsp hnon
  · exact Finset.disjoint_left.mp (zetaPerron_trivial_disjoint_nontrivial σR N T) htr hnon

/-! ## Classification predicates -/

inductive ZetaPerronSingularityCategory (x σR : ℝ) (N : ℕ) (T : ℝ) (s : ℂ) : Prop
  | one : s = 1 → ZetaPerronSingularityCategory x σR N T s
  | zero : s = 0 → ZetaPerronSingularityCategory x σR N T s
  | negOne : s = -1 → ZetaPerronSingularityCategory x σR N T s
  | trivialZero : IsTrivialZetaZero s → ZetaPerronSingularityCategory x σR N T s
  | nontrivialZero : IsNontrivialZetaZero s → ZetaPerronSingularityCategory x σR N T s

inductive ZetaPerronSingularityKind where
  | one
  | zero
  | negOne
  | trivialZero
  | nontrivialZero
  deriving DecidableEq, Repr

def ZetaPerronSingularityKind.Holds
    (k : ZetaPerronSingularityKind) (s : ℂ) : Prop :=
  match k with
  | .one => s = 1
  | .zero => s = 0
  | .negOne => s = -1
  | .trivialZero => IsTrivialZetaZero s
  | .nontrivialZero => IsNontrivialZetaZero s

lemma isTrivialZetaZero_ne_zero {ρ : ℂ} (hρ : IsTrivialZetaZero ρ) : ρ ≠ 0 :=
  zetaZero_ne_zero (isTrivialZetaZero_riemannZeta_zero hρ)

lemma isTrivialZetaZero_ne_negOne {ρ : ℂ} (hρ : IsTrivialZetaZero ρ) : ρ ≠ -1 :=
  zetaZero_ne_negOne (isTrivialZetaZero_riemannZeta_zero hρ)

lemma isTrivialZetaZero_ne_one {ρ : ℂ} (hρ : IsTrivialZetaZero ρ) : ρ ≠ 1 :=
  zetaZero_ne_one (isTrivialZetaZero_riemannZeta_zero hρ)

lemma isNontrivialZetaZero_ne_zero {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) : ρ ≠ 0 :=
  zetaZero_ne_zero hρ.1

lemma isNontrivialZetaZero_ne_negOne {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) : ρ ≠ -1 :=
  zetaZero_ne_negOne hρ.1

theorem zetaPerron_categories_pairwise_disjoint {s : ℂ}
    {k l : ZetaPerronSingularityKind} (hkl : k ≠ l) :
    ¬ (k.Holds s ∧ l.Holds s) := by
  cases k <;> cases l <;> dsimp [ZetaPerronSingularityKind.Holds] at hkl ⊢
  · intro _; exact hkl rfl
  · rintro ⟨hs1, hs0⟩; norm_num [hs1] at hs0
  · rintro ⟨hs1, hsn⟩; norm_num [hs1] at hsn
  · rintro ⟨hs1, htriv⟩; exact isTrivialZetaZero_ne_one htriv hs1
  · rintro ⟨hs1, hnon⟩; exact hnon.2.2 hs1
  · rintro ⟨hs0, hs1⟩; norm_num [hs0] at hs1
  · intro _; exact hkl rfl
  · rintro ⟨hs0, hsn⟩; norm_num [hs0] at hsn
  · rintro ⟨hs0, htriv⟩; exact isTrivialZetaZero_ne_zero htriv hs0
  · rintro ⟨hs0, hnon⟩; exact isNontrivialZetaZero_ne_zero hnon hs0
  · rintro ⟨hsn, hs1⟩; norm_num [hs1] at hsn
  · rintro ⟨hsn, hs0⟩; norm_num [hs0] at hsn
  · intro _; exact hkl rfl
  · rintro ⟨hsn, htriv⟩; exact isTrivialZetaZero_ne_negOne htriv hsn
  · rintro ⟨hsn, hnon⟩; exact isNontrivialZetaZero_ne_negOne hnon hsn
  · rintro ⟨htriv, hs1⟩; exact isTrivialZetaZero_ne_one htriv hs1
  · rintro ⟨htriv, hs0⟩; exact isTrivialZetaZero_ne_zero htriv hs0
  · rintro ⟨htriv, hsn⟩; exact isTrivialZetaZero_ne_negOne htriv hsn
  · intro _; exact hkl rfl
  · rintro ⟨htriv, hnon⟩; exact hnon.2.1 htriv
  · rintro ⟨hnon, hs1⟩; exact hnon.2.2 hs1
  · rintro ⟨hnon, hs0⟩; exact isNontrivialZetaZero_ne_zero hnon hs0
  · rintro ⟨hnon, hsn⟩; exact isNontrivialZetaZero_ne_negOne hnon hsn
  · rintro ⟨hnon, htriv⟩; exact hnon.2.1 htriv
  · intro _; exact hkl rfl

theorem zetaPerron_pole_category_unique
    {x σR : ℝ} {N : ℕ} {T : ℝ}
    (_h : PerronRectangleAdmissible x σR N T)
    {s : ℂ} (_hs : s ∈ zetaPerronRectanglePoleSet x σR N T)
    {k l : ZetaPerronSingularityKind}
    (hk : k.Holds s) (hl : l.Holds s) :
    k = l := by
  by_contra hkl
  exact zetaPerron_categories_pairwise_disjoint hkl ⟨hk, hl⟩

theorem zetaPerron_poles_in_rectangle_classified
    {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T)
    {s : ℂ} (hs : s ∈ zetaPerronRectanglePoleSet x σR N T) :
    ZetaPerronSingularityCategory x σR N T s := by
  by_cases hs_one : s = 1
  · exact ZetaPerronSingularityCategory.one hs_one
  by_cases hs_zero : s = 0
  · exact ZetaPerronSingularityCategory.zero hs_zero
  by_cases hs_neg_one : s = -1
  · exact ZetaPerronSingularityCategory.negOne hs_neg_one
  by_cases hzeta : riemannZeta s = 0
  · rcases zetaZero_trivial_or_nontrivial hzeta with htriv | hnon
    · exact ZetaPerronSingularityCategory.trivialZero htriv
    · exact ZetaPerronSingularityCategory.nontrivialZero hnon
  · have xpos : 0 < x := lt_trans zero_lt_one h.x_gt
    have hL : AnalyticAt ℂ (fun z ↦ -logDeriv riemannZeta z) s :=
      (analyticAt_logDeriv_riemannZeta hs_one hzeta).neg
    have hK : AnalyticAt ℂ (Perron.f x) s :=
      analyticAt_perronKernel xpos hs_zero hs_neg_one
    have hprod : AnalyticAt ℂ (zetaPerronIntegrand x) s := by
      rw [show zetaPerronIntegrand x =
          (fun z ↦ -logDeriv riemannZeta z * Perron.f x z) by rfl]
      exact hL.mul hK
    exact False.elim ((not_le_of_gt hs.2) hprod.meromorphicOrderAt_nonneg)

/-! ## Residue support -/

theorem residue_eq_zero_of_meromorphicOrderAt_nonneg {F : ℂ → ℂ} {s : ℂ}
    (hs_mero : MeromorphicAt F s) (hs_not_pole : 0 ≤ meromorphicOrderAt F s) :
    residue F s = 0 :=
  residue_eq_zero_of_not_pole_of_meromorphicAt hs_mero hs_not_pole

theorem sumResiduesIn_poleSet_eq_classified_singularity_sum
    {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    sumResiduesIn (zetaPerronIntegrand x) (zetaPerronRectanglePoleSet x σR N T) =
      sumResiduesIn (zetaPerronIntegrand x)
        (zetaPerronClassifiedSingularitySet x σR N T) := by
  let R := Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T)
  let P : Set ℂ := {s | meromorphicOrderAt (zetaPerronIntegrand x) s < 0}
  change sumResiduesIn (zetaPerronIntegrand x) (R ∩ P) =
      sumResiduesIn (zetaPerronIntegrand x)
        (zetaPerronClassifiedSingularitySet x σR N T)
  apply sumResiduesIn_inter_eq_of_set_eq (F := zetaPerronIntegrand x) (Rn := R)
    (S2 := zetaPerronClassifiedSingularitySet x σR N T) (P := P)
  · ext s
    constructor
    · intro hs
      have hcat := zetaPerron_poles_in_rectangle_classified h
        (s := s) (by simpa [zetaPerronRectanglePoleSet, R, P] using hs)
      constructor
      · constructor
        · exact hs.1
        · cases hcat with
          | one hone => simp [hone]
          | zero hzero => simp [hzero]
          | negOne hneg => simp [hneg]
          | trivialZero htriv => simp [htriv]
          | nontrivialZero hnon => simp [hnon]
      · exact hs.2
    · intro hs
      exact ⟨hs.1.1, hs.2⟩
  · intro s hsClass hsNotPole
    have hnonneg : 0 ≤ meromorphicOrderAt (zetaPerronIntegrand x) s := not_lt.mp hsNotPole
    have hmero : MeromorphicAt (zetaPerronIntegrand x) s := by
      rw [show zetaPerronIntegrand x =
          (fun z ↦ -logDeriv riemannZeta z * Perron.f x z) by rfl]
      exact meromorphicAt_perronZetaIntegrand (x := x) (lt_trans zero_lt_one h.x_gt) s
    exact residue_eq_zero_of_meromorphicOrderAt_nonneg hmero hnonneg

private lemma sumResiduesIn_finite_eq_finset_sum (F : ℂ → ℂ) {S : Set ℂ} (hS : S.Finite) :
    sumResiduesIn F S = ∑ s ∈ hS.toFinset, residue F s := by
  classical
  haveI : Fintype S := hS.fintype
  unfold sumResiduesIn
  rw [tsum_fintype]
  exact (Finset.sum_subtype (s := hS.toFinset) (p := fun z ↦ z ∈ S)
    (f := fun z ↦ residue F z) (by simp)).symm

/-! ## Point residues already available from P3a, with P3c3 names -/

theorem zetaPerron_residue_at_one
    {x : ℝ} (x_gt : 1 < x) :
    residue (zetaPerronIntegrand x) 1 = Perron.f x 1 := by
  rw [show zetaPerronIntegrand x =
      (fun s ↦ -logDeriv riemannZeta s * Perron.f x s) by
        rfl]
  exact residue_perronZetaIntegrand_pole (x := x) (lt_trans zero_lt_one x_gt)

theorem zetaPerron_residue_at_one_eq
    {x : ℝ} (x_gt : 1 < x) :
    residue (zetaPerronIntegrand x) 1 = (x : ℂ) / 2 := by
  rw [zetaPerron_residue_at_one x_gt]
  simp [Perron.f]
  ring

theorem residue_perronKernel_zero {x : ℝ} (xpos : 0 < x) :
    residue (Perron.f x) 0 = 1 := by
  apply residue_eq_of_tendsto
  have hcont : ContinuousAt (fun s : ℂ ↦ (x : ℂ) ^ s / (s + 1)) 0 := by
    have hpow := (analyticAt_const_cpow_of_pos xpos 0).continuousAt
    have hden : ContinuousAt (fun s : ℂ ↦ s + 1) 0 := by fun_prop
    exact hpow.div hden (by norm_num)
  have hlim : Filter.Tendsto (fun s : ℂ ↦ (x : ℂ) ^ s / (s + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds ((x : ℂ) ^ (0 : ℂ) / ((0 : ℂ) + 1))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  simpa using hlim.congr' (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := hs
    field_simp [Perron.f, hs0])

theorem residue_perronKernel_neg_one {x : ℝ} (xpos : 0 < x) :
    residue (Perron.f x) (-1) = -((x : ℂ)⁻¹) := by
  apply residue_eq_of_tendsto
  have hcont : ContinuousAt (fun s : ℂ ↦ (x : ℂ) ^ s / s) (-1) := by
    have hpow := (analyticAt_const_cpow_of_pos xpos (-1)).continuousAt
    exact hpow.div continuousAt_id (by norm_num)
  have hlim : Filter.Tendsto (fun s : ℂ ↦ (x : ℂ) ^ s / s)
      (nhdsWithin (-1) {(-1 : ℂ)}ᶜ)
      (nhds ((x : ℂ) ^ (-1 : ℂ) / (-1 : ℂ))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have htarget : (x : ℂ) ^ (-1 : ℂ) / (-1 : ℂ) = -((x : ℂ)⁻¹) := by
    rw [Complex.cpow_neg_one]
    ring
  rw [← htarget]
  simpa using hlim.congr' (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs : s ≠ -1 := hs
    have hsadd : s + 1 ≠ 0 := by
      intro h
      exact hs (by linear_combination h)
    field_simp [Perron.f, hsadd])

theorem zetaPerron_residue_at_zero
    {x : ℝ} (x_gt : 1 < x) :
    residue (zetaPerronIntegrand x) 0 =
      -logDeriv riemannZeta 0 := by
  apply residue_eq_of_tendsto
  have xpos : 0 < x := lt_trans zero_lt_one x_gt
  have hL : Filter.Tendsto (fun s : ℂ ↦ -logDeriv riemannZeta s)
      (nhdsWithin 0 {0}ᶜ) (nhds (-logDeriv riemannZeta 0)) :=
    ((analyticAt_logDeriv_riemannZeta (s := 0) (by norm_num) riemannZeta_zero_ne_zero).neg
      ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hK : Filter.Tendsto (fun s : ℂ ↦ s * Perron.f x s)
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    have hcont : ContinuousAt (fun s : ℂ ↦ (x : ℂ) ^ s / (s + 1)) 0 := by
      have hpow := (analyticAt_const_cpow_of_pos xpos 0).continuousAt
      have hden : ContinuousAt (fun s : ℂ ↦ s + 1) 0 := by fun_prop
      exact hpow.div hden (by norm_num)
    have hlim : Filter.Tendsto (fun s : ℂ ↦ (x : ℂ) ^ s / (s + 1))
        (nhdsWithin 0 {0}ᶜ) (nhds ((x : ℂ) ^ (0 : ℂ) / ((0 : ℂ) + 1))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hlim.congr' (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs0 : s ≠ 0 := hs
      field_simp [Perron.f, hs0])
  have hprod := hL.mul hK
  simpa [zetaPerronIntegrand, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hprod

theorem zetaPerron_residue_at_neg_one
    {x : ℝ} (x_gt : 1 < x) :
    residue (zetaPerronIntegrand x) (-1) =
      logDeriv riemannZeta (-1) * (x : ℂ)⁻¹ := by
  apply residue_eq_of_tendsto
  have xpos : 0 < x := lt_trans zero_lt_one x_gt
  have hL : Filter.Tendsto (fun s : ℂ ↦ -logDeriv riemannZeta s)
      (nhdsWithin (-1) {(-1 : ℂ)}ᶜ) (nhds (-logDeriv riemannZeta (-1))) :=
    ((analyticAt_logDeriv_riemannZeta (s := -1) (by norm_num) riemannZeta_neg_one_ne_zero).neg
      ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hK : Filter.Tendsto (fun s : ℂ ↦ (s + 1) * Perron.f x s)
      (nhdsWithin (-1) {(-1 : ℂ)}ᶜ) (nhds (-((x : ℂ)⁻¹))) := by
    have hcont : ContinuousAt (fun s : ℂ ↦ (x : ℂ) ^ s / s) (-1) := by
      have hpow := (analyticAt_const_cpow_of_pos xpos (-1)).continuousAt
      exact hpow.div continuousAt_id (by norm_num)
    have htarget : (x : ℂ) ^ (-1 : ℂ) / (-1 : ℂ) = -((x : ℂ)⁻¹) := by
      rw [Complex.cpow_neg_one]
      ring
    rw [← htarget]
    have hlim : Filter.Tendsto (fun s : ℂ ↦ (x : ℂ) ^ s / s)
        (nhdsWithin (-1) {(-1 : ℂ)}ᶜ)
        (nhds ((x : ℂ) ^ (-1 : ℂ) / (-1 : ℂ))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    exact hlim.congr' (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs : s ≠ -1 := hs
      have hsadd : s + 1 ≠ 0 := by
        intro h
        exact hs (by linear_combination h)
      field_simp [Perron.f, hsadd])
  have hprod := hL.mul hK
  have htarget : -logDeriv riemannZeta (-1) * -((x : ℂ)⁻¹)
      = logDeriv riemannZeta (-1) * (x : ℂ)⁻¹ := by ring
  rw [← htarget]
  simpa [zetaPerronIntegrand, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hprod

theorem zetaPerron_residue_at_zeta_zero
    {x : ℝ} (x_gt : 1 < x)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    residue (zetaPerronIntegrand x) ρ =
      -(zetaZeroMultiplicity ρ : ℂ) * Perron.f x ρ := by
  rw [show zetaPerronIntegrand x =
      (fun s ↦ -logDeriv riemannZeta s * Perron.f x s) by
        rfl]
  exact residue_perronZetaIntegrand_zero (x := x) (lt_trans zero_lt_one x_gt) hρ

theorem zetaPerron_trivial_zero_residue_sum
    {x σR : ℝ} {N : ℕ} {T : ℝ} (x_gt : 1 < x) :
    sumResiduesIn (zetaPerronIntegrand x) (zetaPerronTrivialZeroSet σR N T) =
      ∑' ρ : zetaPerronTrivialZeroSet σR N T,
        -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ) := by
  unfold sumResiduesIn
  apply tsum_congr
  intro ρ
  exact zetaPerron_residue_at_zeta_zero x_gt
    (isTrivialZetaZero_riemannZeta_zero ρ.property.2)

theorem zetaPerron_nontrivial_zero_residue_sum
    {x σR : ℝ} {N : ℕ} {T : ℝ} (x_gt : 1 < x) :
    sumResiduesIn (zetaPerronIntegrand x) (zetaPerronNontrivialZeroSet σR N T) =
      ∑' ρ : zetaPerronNontrivialZeroSet σR N T,
        -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ) := by
  unfold sumResiduesIn
  apply tsum_congr
  intro ρ
  exact zetaPerron_residue_at_zeta_zero x_gt ρ.property.2.1

theorem zetaPerron_special_residue_sum_eq
    {x : ℝ} (x_gt : 1 < x) :
    ∑ s ∈ zetaPerronSpecialPointFinset, residue (zetaPerronIntegrand x) s =
      (x : ℂ) / 2 - logDeriv riemannZeta 0 +
        logDeriv riemannZeta (-1) * (x : ℂ)⁻¹ := by
  classical
  norm_num [zetaPerronSpecialPointFinset, Finset.sum_insert,
    zetaPerron_residue_at_one_eq x_gt,
    zetaPerron_residue_at_zero x_gt, zetaPerron_residue_at_neg_one x_gt]
  ring_nf

theorem sumResiduesIn_classified_eq_special_plus_zeros
    {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    sumResiduesIn (zetaPerronIntegrand x)
        (zetaPerronClassifiedSingularitySet x σR N T) =
      (∑ s ∈ zetaPerronSpecialPointFinset, residue (zetaPerronIntegrand x) s)
      + sumResiduesIn (zetaPerronIntegrand x) (zetaPerronTrivialZeroSet σR N T)
      + sumResiduesIn (zetaPerronIntegrand x) (zetaPerronNontrivialZeroSet σR N T) := by
  classical
  let hClass := zetaPerron_classified_singularity_set_finite x σR N T
  let hTriv := zetaPerron_trivial_zero_set_finite σR N T
  let hNon := zetaPerron_nontrivial_zero_set_finite σR N T
  rw [sumResiduesIn_finite_eq_finset_sum (zetaPerronIntegrand x) hClass]
  change ∑ s ∈ zetaPerronClassifiedSingularityFinset x σR N T,
      residue (zetaPerronIntegrand x) s =
      (∑ s ∈ zetaPerronSpecialPointFinset, residue (zetaPerronIntegrand x) s)
      + sumResiduesIn (zetaPerronIntegrand x) (zetaPerronTrivialZeroSet σR N T)
      + sumResiduesIn (zetaPerronIntegrand x) (zetaPerronNontrivialZeroSet σR N T)
  rw [zetaPerron_classified_singularity_finset_eq_union h]
  rw [Finset.sum_union (zetaPerron_special_union_trivial_disjoint_nontrivial σR N T)]
  rw [Finset.sum_union (zetaPerron_special_disjoint_trivial σR N T)]
  rw [sumResiduesIn_finite_eq_finset_sum (zetaPerronIntegrand x)
    (zetaPerron_trivial_zero_set_finite σR N T)]
  rw [sumResiduesIn_finite_eq_finset_sum (zetaPerronIntegrand x)
    (zetaPerron_nontrivial_zero_set_finite σR N T)]
  abel

theorem zetaPerron_finite_residue_decomposition
    {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    sumResiduesIn (zetaPerronIntegrand x) (zetaPerronRectanglePoleSet x σR N T) =
      (x : ℂ) / 2
      - logDeriv riemannZeta 0
      + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹
      - (∑' ρ : zetaPerronTrivialZeroSet σR N T,
          (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ))
      - (∑' ρ : zetaPerronNontrivialZeroSet σR N T,
          (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ)) := by
  have x_gt : 1 < x := h.x_gt
  calc
    sumResiduesIn (zetaPerronIntegrand x) (zetaPerronRectanglePoleSet x σR N T)
        = sumResiduesIn (zetaPerronIntegrand x)
            (zetaPerronClassifiedSingularitySet x σR N T) := by
          exact sumResiduesIn_poleSet_eq_classified_singularity_sum h
    _ =
        (∑ s ∈ zetaPerronSpecialPointFinset, residue (zetaPerronIntegrand x) s)
        + sumResiduesIn (zetaPerronIntegrand x) (zetaPerronTrivialZeroSet σR N T)
        + sumResiduesIn (zetaPerronIntegrand x) (zetaPerronNontrivialZeroSet σR N T) := by
          exact sumResiduesIn_classified_eq_special_plus_zeros h
    _ =
      (x : ℂ) / 2
      - logDeriv riemannZeta 0
      + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹
      + (∑' ρ : zetaPerronTrivialZeroSet σR N T,
          -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ))
      + (∑' ρ : zetaPerronNontrivialZeroSet σR N T,
          -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ)) := by
          rw [zetaPerron_special_residue_sum_eq x_gt,
            zetaPerron_trivial_zero_residue_sum x_gt,
            zetaPerron_nontrivial_zero_residue_sum x_gt]
    _ =
      (x : ℂ) / 2
      - logDeriv riemannZeta 0
      + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹
      - (∑' ρ : zetaPerronTrivialZeroSet σR N T,
          (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ))
      - (∑' ρ : zetaPerronNontrivialZeroSet σR N T,
          (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ)) := by
          simp_rw [neg_mul, tsum_neg]
          abel

theorem smoothedVonMangoldtSum_eq_classified_residues_and_boundary_terms
    {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    smoothedVonMangoldtSum x =
      ((x : ℂ) / 2
      - logDeriv riemannZeta 0
      + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹
      - (∑' ρ : zetaPerronTrivialZeroSet σR N T,
          (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ))
      - (∑' ρ : zetaPerronNontrivialZeroSet σR N T,
          (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ)))
      + rightVerticalLowerTail' (zetaPerronIntegrand x) σR T
      + rightVerticalUpperTail' (zetaPerronIntegrand x) σR T
      - HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR (-T)
      + HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR T
      + VIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) (-T) T := by
  rw [smoothedVonMangoldtSum_eq_finite_residues_and_boundary_terms h]
  rw [zetaPerron_finite_residue_decomposition h]

/-! ## Conjugation -/

theorem perronKernel_conj {x : ℝ} (xpos : 0 < x) (ρ : ℂ) :
    conj (Perron.f x ρ) = Perron.f x (conj ρ) := by
  exact (Perron.map_conj xpos.le ρ).symm

theorem isTrivialZetaZero_conj_iff (ρ : ℂ) :
    IsTrivialZetaZero (conj ρ) ↔ IsTrivialZetaZero ρ := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := congrArg conj hn
    rw [map_mul, map_neg] at h
    simp only [starRingEnd_self_apply] at h
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      norm_num [starRingEnd_apply]
    rw [htwo] at h
    simpa using h
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    rw [map_mul, map_neg]
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      norm_num [starRingEnd_apply]
    rw [htwo]
    simp

theorem isNontrivialZetaZero_conj_iff (ρ : ℂ) :
    IsNontrivialZetaZero (conj ρ) ↔ IsNontrivialZetaZero ρ := by
  constructor
  · intro h
    have hz : riemannZeta ρ = 0 := by
      have hc := riemannZeta_conj_eq_zero_of_zero h.1
      simpa using hc
    refine ⟨hz, ?_, ?_⟩
    · intro htriv
      exact h.2.1 ((isTrivialZetaZero_conj_iff ρ).mpr htriv)
    · intro hρ1
      exact h.2.2 (by simp [hρ1])
  · intro h
    have hz : riemannZeta (conj ρ) = 0 := riemannZeta_conj_eq_zero_of_zero h.1
    refine ⟨hz, ?_, ?_⟩
    · intro htriv
      exact h.2.1 ((isTrivialZetaZero_conj_iff ρ).mp htriv)
    · exact zetaZero_ne_one hz

theorem zetaPerronRectangle_conj_iff
    {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) (ρ : ℂ) :
    ρ ∈ Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) ↔
      conj ρ ∈ Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) := by
  constructor
  · intro hρ
    rw [mem_Rect (p3c3_perronRectangle_re_le h) (p3c3_perronRectangle_im_le h)] at hρ
    rw [mem_Rect (p3c3_perronRectangle_re_le h) (p3c3_perronRectangle_im_le h)]
    simp [perronRectangleLowerLeft, perronRectangleUpperRight] at hρ ⊢
    rcases hρ with ⟨left_le, right_le, lower_le, upper_le⟩
    constructor
    · exact left_le
    · constructor
      · exact right_le
      · constructor <;> linarith
  · intro hρ
    rw [mem_Rect (p3c3_perronRectangle_re_le h) (p3c3_perronRectangle_im_le h)] at hρ
    rw [mem_Rect (p3c3_perronRectangle_re_le h) (p3c3_perronRectangle_im_le h)]
    simp [perronRectangleLowerLeft, perronRectangleUpperRight] at hρ ⊢
    rcases hρ with ⟨left_le, right_le, lower_le, upper_le⟩
    constructor
    · exact left_le
    · constructor
      · exact right_le
      · constructor <;> linarith

theorem zetaPerronNontrivialZeroSet_conj_iff
    {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) (ρ : ℂ) :
    ρ ∈ zetaPerronNontrivialZeroSet σR N T ↔
      conj ρ ∈ zetaPerronNontrivialZeroSet σR N T := by
  constructor
  · intro hρ
    exact ⟨(zetaPerronRectangle_conj_iff h ρ).mp hρ.1,
      (isNontrivialZetaZero_conj_iff ρ).mpr hρ.2⟩
  · intro hρ
    exact ⟨(zetaPerronRectangle_conj_iff h ρ).mpr hρ.1,
      (isNontrivialZetaZero_conj_iff ρ).mp hρ.2⟩

theorem zetaPerron_residue_conj
    {x : ℝ} (x_gt : 1 < x) {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    residue (zetaPerronIntegrand x) (conj ρ) =
      conj (residue (zetaPerronIntegrand x) ρ) := by
  have hρc : riemannZeta (conj ρ) = 0 := riemannZeta_conj_eq_zero_of_zero hρ
  rw [zetaPerron_residue_at_zeta_zero x_gt hρc,
    zetaPerron_residue_at_zeta_zero x_gt hρ]
  have hm : zetaZeroMultiplicity (conj ρ) = zetaZeroMultiplicity ρ :=
    zetaZeroMultiplicity_conj hρ
  have hk : conj (Perron.f x ρ) = Perron.f x (conj ρ) :=
    perronKernel_conj (lt_trans zero_lt_one x_gt) ρ
  rw [hm, ← hk]
  simp [map_mul, map_neg]

theorem zetaPerron_conjugate_orbit_pairing
    {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    conj
      (sumResiduesIn (zetaPerronIntegrand x)
        (zetaPerronNontrivialZeroSet σR N T)) =
    sumResiduesIn (zetaPerronIntegrand x)
      (zetaPerronNontrivialZeroSet σR N T) := by
  classical
  let S := zetaPerronNontrivialZeroSet σR N T
  let hfin : S.Finite := zetaPerron_nontrivial_zero_set_finite σR N T
  change conj (sumResiduesIn (zetaPerronIntegrand x) S) =
    sumResiduesIn (zetaPerronIntegrand x) S
  rw [sumResiduesIn_finite_eq_finset_sum (zetaPerronIntegrand x) hfin]
  rw [map_sum]
  refine Finset.sum_bij
    (s := hfin.toFinset) (t := hfin.toFinset)
    (fun ρ hρ ↦ conj ρ) ?hmem ?hinj ?hsurj ?hterm
  · intro ρ hρ
    rw [hfin.mem_toFinset] at hρ ⊢
    exact (zetaPerronNontrivialZeroSet_conj_iff h ρ).mp hρ
  · intro ρ₁ _ ρ₂ _ hconj
    have hback := congrArg conj hconj
    simpa using hback
  · intro ρ hρ
    refine ⟨conj ρ, ?_, ?_⟩
    · rw [hfin.mem_toFinset] at hρ ⊢
      exact (zetaPerronNontrivialZeroSet_conj_iff h ρ).mp hρ
    · simp
  · intro ρ hρ
    rw [hfin.mem_toFinset] at hρ
    exact (zetaPerron_residue_conj h.x_gt hρ.2.1).symm

/-! ## Contract examples for completed imported fragments -/

example {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    IsTrivialZetaZero ρ ∨ IsNontrivialZetaZero ρ :=
  zetaZero_trivial_or_nontrivial hρ

example {ρ : ℂ} :
    ¬ (IsTrivialZetaZero ρ ∧ IsNontrivialZetaZero ρ) :=
  trivialZetaZero_not_nontrivial

example (σR : ℝ) (N : ℕ) (T : ℝ) :
    (zetaPerronTrivialZeroSet σR N T).Finite :=
  zetaPerron_trivial_zero_set_finite σR N T

example (σR : ℝ) (N : ℕ) (T : ℝ) :
    (zetaPerronNontrivialZeroSet σR N T).Finite :=
  zetaPerron_nontrivial_zero_set_finite σR N T

example (x σR : ℝ) (N : ℕ) (T : ℝ) :
    (zetaPerronClassifiedSingularitySet x σR N T).Finite :=
  zetaPerron_classified_singularity_set_finite x σR N T

example {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T)
    {s : ℂ} (hs : s ∈ zetaPerronRectanglePoleSet x σR N T) :
    ZetaPerronSingularityCategory x σR N T s :=
  zetaPerron_poles_in_rectangle_classified h hs

example {s : ℂ} {k l : ZetaPerronSingularityKind} (hkl : k ≠ l) :
    ¬ (k.Holds s ∧ l.Holds s) :=
  zetaPerron_categories_pairwise_disjoint hkl

example {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T)
    {s : ℂ} (hs : s ∈ zetaPerronRectanglePoleSet x σR N T)
    {k l : ZetaPerronSingularityKind}
    (hk : k.Holds s) (hl : l.Holds s) :
    k = l :=
  zetaPerron_pole_category_unique h hs hk hl

example {F : ℂ → ℂ} {s : ℂ}
    (hs_mero : MeromorphicAt F s) (hs_not_pole : 0 ≤ meromorphicOrderAt F s) :
    residue F s = 0 :=
  residue_eq_zero_of_meromorphicOrderAt_nonneg hs_mero hs_not_pole

example {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    sumResiduesIn (zetaPerronIntegrand x) (zetaPerronRectanglePoleSet x σR N T) =
      sumResiduesIn (zetaPerronIntegrand x)
        (zetaPerronClassifiedSingularitySet x σR N T) :=
  sumResiduesIn_poleSet_eq_classified_singularity_sum h

example {x : ℝ} (x_gt : 1 < x) :
    residue (zetaPerronIntegrand x) 1 = Perron.f x 1 :=
  zetaPerron_residue_at_one x_gt

example {x : ℝ} (x_gt : 1 < x) :
    residue (zetaPerronIntegrand x) 1 = (x : ℂ) / 2 :=
  zetaPerron_residue_at_one_eq x_gt

example {x : ℝ} (x_gt : 1 < x) :
    residue (zetaPerronIntegrand x) 0 =
      -logDeriv riemannZeta 0 :=
  zetaPerron_residue_at_zero x_gt

example {x : ℝ} (x_gt : 1 < x) :
    residue (zetaPerronIntegrand x) (-1) =
      logDeriv riemannZeta (-1) * (x : ℂ)⁻¹ :=
  zetaPerron_residue_at_neg_one x_gt

example {x : ℝ} (x_gt : 1 < x) {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    residue (zetaPerronIntegrand x) ρ =
      -(zetaZeroMultiplicity ρ : ℂ) * Perron.f x ρ :=
  zetaPerron_residue_at_zeta_zero x_gt hρ

example {x σR : ℝ} {N : ℕ} {T : ℝ} (x_gt : 1 < x) :
    sumResiduesIn (zetaPerronIntegrand x) (zetaPerronTrivialZeroSet σR N T) =
      ∑' ρ : zetaPerronTrivialZeroSet σR N T,
        -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ) :=
  zetaPerron_trivial_zero_residue_sum x_gt

example {x σR : ℝ} {N : ℕ} {T : ℝ} (x_gt : 1 < x) :
    sumResiduesIn (zetaPerronIntegrand x) (zetaPerronNontrivialZeroSet σR N T) =
      ∑' ρ : zetaPerronNontrivialZeroSet σR N T,
        -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ) :=
  zetaPerron_nontrivial_zero_residue_sum x_gt

example {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    sumResiduesIn (zetaPerronIntegrand x)
        (zetaPerronClassifiedSingularitySet x σR N T) =
      (∑ s ∈ zetaPerronSpecialPointFinset, residue (zetaPerronIntegrand x) s)
      + sumResiduesIn (zetaPerronIntegrand x) (zetaPerronTrivialZeroSet σR N T)
      + sumResiduesIn (zetaPerronIntegrand x) (zetaPerronNontrivialZeroSet σR N T) :=
  sumResiduesIn_classified_eq_special_plus_zeros h

example {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    sumResiduesIn (zetaPerronIntegrand x) (zetaPerronRectanglePoleSet x σR N T) =
      (x : ℂ) / 2
      - logDeriv riemannZeta 0
      + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹
      - (∑' ρ : zetaPerronTrivialZeroSet σR N T,
          (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ))
      - (∑' ρ : zetaPerronNontrivialZeroSet σR N T,
          (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ)) :=
  zetaPerron_finite_residue_decomposition h

example {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    smoothedVonMangoldtSum x =
      ((x : ℂ) / 2
      - logDeriv riemannZeta 0
      + logDeriv riemannZeta (-1) * (x : ℂ)⁻¹
      - (∑' ρ : zetaPerronTrivialZeroSet σR N T,
          (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ))
      - (∑' ρ : zetaPerronNontrivialZeroSet σR N T,
          (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * Perron.f x (ρ : ℂ)))
      + rightVerticalLowerTail' (zetaPerronIntegrand x) σR T
      + rightVerticalUpperTail' (zetaPerronIntegrand x) σR T
      - HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR (-T)
      + HIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) σR T
      + VIntegral' (zetaPerronIntegrand x) (perronRectangleSigmaL N) (-T) T :=
  smoothedVonMangoldtSum_eq_classified_residues_and_boundary_terms h

example {x : ℝ} (xpos : 0 < x) (ρ : ℂ) :
    conj (Perron.f x ρ) = Perron.f x (conj ρ) :=
  perronKernel_conj xpos ρ

example (ρ : ℂ) :
    IsTrivialZetaZero (conj ρ) ↔ IsTrivialZetaZero ρ :=
  isTrivialZetaZero_conj_iff ρ

example (ρ : ℂ) :
    IsNontrivialZetaZero (conj ρ) ↔ IsNontrivialZetaZero ρ :=
  isNontrivialZetaZero_conj_iff ρ

example {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) (ρ : ℂ) :
    ρ ∈ Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) ↔
      conj ρ ∈ Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) :=
  zetaPerronRectangle_conj_iff h ρ

example {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) (ρ : ℂ) :
    ρ ∈ zetaPerronNontrivialZeroSet σR N T ↔
      conj ρ ∈ zetaPerronNontrivialZeroSet σR N T :=
  zetaPerronNontrivialZeroSet_conj_iff h ρ

example {x : ℝ} (x_gt : 1 < x) {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    residue (zetaPerronIntegrand x) (conj ρ) =
      conj (residue (zetaPerronIntegrand x) ρ) :=
  zetaPerron_residue_conj x_gt hρ

example {x σR : ℝ} {N : ℕ} {T : ℝ}
    (h : PerronRectangleAdmissible x σR N T) :
    conj
      (sumResiduesIn (zetaPerronIntegrand x)
        (zetaPerronNontrivialZeroSet σR N T)) =
    sumResiduesIn (zetaPerronIntegrand x)
      (zetaPerronNontrivialZeroSet σR N T) :=
  zetaPerron_conjugate_orbit_pairing h

#print axioms RHV3Lean.zetaPerron_poles_in_rectangle_classified
#print axioms RHV3Lean.residue_eq_zero_of_meromorphicOrderAt_nonneg
#print axioms RHV3Lean.sumResiduesIn_poleSet_eq_classified_singularity_sum
#print axioms RHV3Lean.zetaPerron_residue_at_one
#print axioms RHV3Lean.zetaPerron_residue_at_zero
#print axioms RHV3Lean.zetaPerron_residue_at_neg_one
#print axioms RHV3Lean.zetaPerron_residue_at_zeta_zero
#print axioms RHV3Lean.zetaPerron_trivial_zero_residue_sum
#print axioms RHV3Lean.zetaPerron_nontrivial_zero_residue_sum
#print axioms RHV3Lean.zetaPerron_finite_residue_decomposition
#print axioms RHV3Lean.smoothedVonMangoldtSum_eq_classified_residues_and_boundary_terms
#print axioms RHV3Lean.perronKernel_conj
#print axioms RHV3Lean.zetaPerron_residue_conj
#print axioms RHV3Lean.zetaPerron_conjugate_orbit_pairing

end RHV3Lean
