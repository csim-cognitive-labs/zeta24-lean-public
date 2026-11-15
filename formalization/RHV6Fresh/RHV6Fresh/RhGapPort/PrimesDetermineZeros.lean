/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Port (directive R11, 2026-11-01) de `formalization/rh_gap_criterion` (paquet `RhGapCriterion`, Lean v4.31.0, Mathlib
`fabf563a`) vers RHV6Fresh (Lean v4.33.0-rc2). Une dépendance Lake est impossible (chaînes d'outils différentes) ; les
énoncés et les preuves sont repris à l'identique, sous le même nom, dans l'espace `RHV6Fresh.RhGap`.

Fichiers source et commits :
* `RhGapCriterion/ZeroPrimeReconstruction.lean` (`primes_determine_zeta_in_halfplane`, commit bf85044e) ;
* `RhGapCriterion/PrimeDeterminesZetaAndZeros.lean` (`primes_determine_zeta_meromorphic_continuation`,
  `primes_determine_nontrivial_zero_multiset`, commit bf85044e) ;
* `RhGapCriterion/PrimeDeterminedZeroCompleteGrammar.lean` §1–§5 (`ZeroSource`, sources canonique et déterminée,
  `primeDeterminedZeroSource_eq_canonical`, `prime_determined_any_zero_source_object_eq`, fenêtre ordonnée,
  commit f05c2b47) ;
* `RhGapCriterion/PrimeDeterminedZeroRecovery.lean` (`prime_determined_zero_window_eq_canonical_any_length`,
  commit f05c2b47 ; les corollaires à 5 et 100 membres en sont des instances, non reportés).

Objets communs : `IsTrivialZetaZero`, `IsNontrivialZetaZero`, `zetaZeroMultiplicity`, `isPreconnected_compl_one_complex`
(`RHV3Lean.Objects.ZetaZeroMultiplicity`, mêmes définitions que dans le paquet source) ; `nontrivialZetaZerosByHeight`,
sa finitude et `isNontrivialZetaZero_re_mem_Ioo` (`RHV3Lean.Objects.ZetaZeroHeightTruncation`, port Kadiri déjà présent
dans `rhv3_lean`). La spécialisation canonique (§5) est raccordée en plus à la fenêtre ouverte de RHV6Fresh
(`upperWindowOpen`, `AnchorStructure`). Aucun axiome, aucun `sorry`, aucune hypothèse. Non ajouté à `RHV6Fresh.lean`.
-/
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import RHV3Lean.Objects.ZetaZeroHeightTruncation
import RHV6Fresh.Terminal.AnchorStructure

/-!
# Les nombres premiers déterminent ζ et le multiensemble de ses zéros (port RhGap)

Sens exact : toute fonction `F`, analytique hors du pôle et égale au produit d'Euler sur les premiers dans `Re s > 1`,
coïncide avec `riemannZeta` hors de `1`, a les mêmes zéros non triviaux avec les mêmes multiplicités, et toute fenêtre
de sa constellation ordonnée est la fenêtre canonique. C'est une DÉTERMINATION exacte, pas un calcul ; et la classe des
`F` admissibles est réduite à `riemannZeta` hors du pôle (`primeDetermined_unique`, `riemannZeta_isPrimeDetermined`,
raccord R11).
-/

open Set Filter Finset Complex RHV3Lean
open scoped Topology

noncomputable section

namespace RHV6Fresh.RhGap

/-! ## 1. Produit d'Euler et continuation déterminée par les premiers (PrimeDeterminesZetaAndZeros.lean) -/

/-- Produit d'Euler sur les nombres premiers. -/
noncomputable def primeEulerProduct (s : ℂ) : ℂ :=
  ∏' q : Nat.Primes, (1 - (q : ℂ) ^ (-s))⁻¹

/-- `F` est une continuation déterminée par les premiers : analytique hors de `1`, égale au produit d'Euler sur
`Re s > 1`. -/
def IsPrimeDeterminedZetaContinuation (F : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ F (({1} : Set ℂ)ᶜ) ∧ ∀ s : ℂ, 1 < s.re → F s = primeEulerProduct s

/-- Le produit d'Euler sur les premiers détermine `ζ` dans `Re s > 1` (Mathlib, `riemannZeta_eulerProduct_tprod`). -/
theorem primes_determine_zeta_in_halfplane {s : ℂ} (hs : 1 < s.re) :
    ∏' q : Nat.Primes, (1 - (q : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  riemannZeta_eulerProduct_tprod hs

/-- **Les premiers déterminent la continuation méromorphe** : `F = ζ` hors de `1`. -/
theorem primes_determine_zeta_meromorphic_continuation (F : ℂ → ℂ)
    (hF : IsPrimeDeterminedZetaContinuation F) :
    Set.EqOn F riemannZeta (({1} : Set ℂ)ᶜ) := by
  have hhalf : ∀ s : ℂ, 1 < s.re → F s = riemannZeta s := by
    intro s hs
    rw [hF.2 s hs, primeEulerProduct]
    exact primes_determine_zeta_in_halfplane hs
  have hevent : F =ᶠ[𝓝 (2 : ℂ)] riemannZeta := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
    exact hhalf s hs
  have htwo : (2 : ℂ) ∈ (({1} : Set ℂ)ᶜ) := by norm_num
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF.1 analyticOn_riemannZeta
    isPreconnected_compl_one_complex htwo hevent

/-- Raccord R11 : `riemannZeta` elle-même est une continuation déterminée par les premiers. -/
theorem riemannZeta_isPrimeDetermined : IsPrimeDeterminedZetaContinuation riemannZeta :=
  ⟨analyticOn_riemannZeta, fun s hs => (primes_determine_zeta_in_halfplane hs).symm⟩

/-- Raccord R11 : deux continuations déterminées par les premiers coïncident hors du pôle. La classe des `F`
admissibles est un singleton hors de `1`. -/
theorem primeDetermined_unique {F G : ℂ → ℂ} (hF : IsPrimeDeterminedZetaContinuation F)
    (hG : IsPrimeDeterminedZetaContinuation G) : Set.EqOn F G (({1} : Set ℂ)ᶜ) :=
  fun s hs => (primes_determine_zeta_meromorphic_continuation F hF hs).trans
    (primes_determine_zeta_meromorphic_continuation G hG hs).symm

/-- Zéro non trivial de `F`. -/
def IsNontrivialZeroOf (F : ℂ → ℂ) (ρ : ℂ) : Prop :=
  F ρ = 0 ∧ ¬ IsTrivialZetaZero ρ ∧ ρ ≠ 1

/-- Même multiensemble de zéros non triviaux que `ζ` : mêmes points, mêmes multiplicités. -/
def SameNontrivialZeroMultiset (F : ℂ → ℂ) : Prop :=
  (∀ ρ : ℂ, IsNontrivialZeroOf F ρ ↔ IsNontrivialZetaZero ρ) ∧
  (∀ ρ : ℂ, IsNontrivialZetaZero ρ → analyticOrderNatAt F ρ = zetaZeroMultiplicity ρ)

/-- **Les premiers déterminent le multiensemble des zéros non triviaux.** -/
theorem primes_determine_nontrivial_zero_multiset (F : ℂ → ℂ)
    (hF : IsPrimeDeterminedZetaContinuation F) : SameNontrivialZeroMultiset F := by
  constructor
  · intro ρ
    constructor
    · intro hρ
      have hmem : ρ ∈ (({1} : Set ℂ)ᶜ) := by simpa using hρ.2.2
      have heq := primes_determine_zeta_meromorphic_continuation F hF hmem
      exact ⟨by simpa [heq.symm] using hρ.1, hρ.2.1, hρ.2.2⟩
    · intro hρ
      have hmem : ρ ∈ (({1} : Set ℂ)ᶜ) := by simpa using hρ.2.2
      have heq := primes_determine_zeta_meromorphic_continuation F hF hmem
      exact ⟨by simpa [heq] using hρ.1, hρ.2.1, hρ.2.2⟩
  · intro ρ hρ
    have hevent : F =ᶠ[𝓝 ρ] riemannZeta := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hρ.2.2] with z hz
      exact primes_determine_zeta_meromorphic_continuation F hF (by simpa using hz)
    unfold zetaZeroMultiplicity analyticOrderNatAt
    rw [analyticOrderAt_congr hevent]

/-! ## 2. La source de zéros et les deux égalités de transport (PrimeDeterminedZeroCompleteGrammar.lean §1–§3) -/

/-- Une source de zéros : le prédicat d'appartenance et la multiplicité, sur `ℂ`. -/
structure ZeroSource where
  member : ℂ → Prop
  mult : ℂ → ℕ

/-- Multiplicité canonique normalisée (zéro hors des zéros non triviaux). -/
def canonicalZeroMultiplicity (ρ : ℂ) : ℕ :=
  open Classical in if IsNontrivialZetaZero ρ then zetaZeroMultiplicity ρ else 0

/-- Multiplicité normalisée du côté déterminé par les premiers. -/
def primeDeterminedZeroMultiplicity (F : ℂ → ℂ) (ρ : ℂ) : ℕ :=
  open Classical in if IsNontrivialZeroOf F ρ then analyticOrderNatAt F ρ else 0

/-- Source canonique : zéros non triviaux de `ζ`, multiplicité analytique. -/
def canonicalZetaZeroSource : ZeroSource where
  member := IsNontrivialZetaZero
  mult := canonicalZeroMultiplicity

/-- Source déterminée par les premiers : écrite uniquement avec `F`. -/
def primeDeterminedZeroSource (F : ℂ → ℂ) : ZeroSource where
  member := IsNontrivialZeroOf F
  mult := primeDeterminedZeroMultiplicity F

/-- Égalité des prédicats d'appartenance. -/
theorem primeDeterminedZeroMember_eq (F : ℂ → ℂ) (hF : IsPrimeDeterminedZetaContinuation F) :
    IsNontrivialZeroOf F = IsNontrivialZetaZero :=
  funext fun ρ => propext ((primes_determine_nontrivial_zero_multiset F hF).1 ρ)

/-- Égalité des multiplicités normalisées, sur `ℂ` tout entier. -/
theorem primeDeterminedZeroMultiplicity_eq (F : ℂ → ℂ) (hF : IsPrimeDeterminedZetaContinuation F) :
    primeDeterminedZeroMultiplicity F = canonicalZeroMultiplicity := by
  classical
  have hpred := primes_determine_nontrivial_zero_multiset F hF
  funext ρ
  unfold primeDeterminedZeroMultiplicity canonicalZeroMultiplicity
  by_cases hρ : IsNontrivialZetaZero ρ
  · rw [if_pos ((hpred.1 ρ).mpr hρ), if_pos hρ]
    exact hpred.2 ρ hρ
  · rw [if_neg (fun h => hρ ((hpred.1 ρ).mp h)), if_neg hρ]

/-- **Les deux sources sont le même objet.** -/
theorem primeDeterminedZeroSource_eq_canonical (F : ℂ → ℂ) (hF : IsPrimeDeterminedZetaContinuation F) :
    primeDeterminedZeroSource F = canonicalZetaZeroSource := by
  unfold primeDeterminedZeroSource canonicalZetaZeroSource
  rw [primeDeterminedZeroMember_eq F hF, primeDeterminedZeroMultiplicity_eq F hF]

/-- **Transport universel** : tout objet construit depuis la source déterminée par les premiers est l'objet canonique. -/
theorem prime_determined_any_zero_source_object_eq (F : ℂ → ℂ) (hF : IsPrimeDeterminedZetaContinuation F)
    {α : Sort*} (G : ZeroSource → α) :
    G (primeDeterminedZeroSource F) = G canonicalZetaZeroSource :=
  congrArg G (primeDeterminedZeroSource_eq_canonical F hF)

/-! ## 3. La constellation générique bornée et ordonnée (§4 du fichier source) -/

/-- Zéros de la source de hauteur `|Im| < T`. -/
def zeroHeightSet (S : ZeroSource) (T : ℝ) : Set ℂ := {ρ | S.member ρ ∧ |ρ.im| < T}

/-- Constellation bornée générique, définition TOTALE (`∅` si l'ensemble n'est pas fini). -/
def zeroHeightFinset (S : ZeroSource) (T : ℝ) : Finset ℂ :=
  open Classical in if h : (zeroHeightSet S T).Finite then h.toFinset else ∅

/-- Représentants de hauteur strictement positive. -/
def zeroPositiveMembers (S : ZeroSource) (T : ℝ) : Finset ℂ :=
  open Classical in (zeroHeightFinset S T).filter (fun ρ => 0 < ρ.im)

/-- Clé d'ordre : hauteur d'abord, partie réelle en départage (jamais `Re = 1/2` supposé). -/
def complexZeroOrderKey (ρ : ℂ) : Lex (ℝ × ℝ) := toLex (ρ.im, ρ.re)

theorem complexZeroOrderKey_injective : Function.Injective complexZeroOrderKey := by
  intro ρ σ hkey
  have hpair : (ρ.im, ρ.re) = (σ.im, σ.re) := toLex_inj.mp hkey
  exact Complex.ext (congrArg Prod.snd hpair) (congrArg Prod.fst hpair)

/-- Ordre canonique dérivé sur `ℂ`. -/
def ComplexZeroLe (ρ σ : ℂ) : Prop := complexZeroOrderKey ρ ≤ complexZeroOrderKey σ

instance : DecidableRel ComplexZeroLe :=
  fun ρ σ => inferInstanceAs (Decidable (complexZeroOrderKey ρ ≤ complexZeroOrderKey σ))

instance : IsTrans ℂ ComplexZeroLe := ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩

instance : Std.Antisymm ComplexZeroLe :=
  ⟨fun _ _ hab hba => complexZeroOrderKey_injective (le_antisymm hab hba)⟩

instance : Std.Total ComplexZeroLe :=
  ⟨fun ρ σ => le_total (complexZeroOrderKey ρ) (complexZeroOrderKey σ)⟩

theorem complexZeroLe_antisymm {ρ σ : ℂ} (hab : ComplexZeroLe ρ σ) (hba : ComplexZeroLe σ ρ) : ρ = σ :=
  complexZeroOrderKey_injective (le_antisymm hab hba)

/-- Vue ordonnée générique : représentants positifs triés. -/
def zeroOrderedMembers (S : ZeroSource) (T : ℝ) : List ℂ := (zeroPositiveMembers S T).sort ComplexZeroLe

/-- Fenêtre : `k` membres consécutifs à partir du rang `n`. -/
def zeroConstellationWindow (S : ZeroSource) (T : ℝ) (n k : ℕ) : List ℂ :=
  ((zeroOrderedMembers S T).drop n).take k

/-- Hauteurs de la fenêtre. -/
def zeroConstellationWindowHeights (S : ZeroSource) (T : ℝ) (n k : ℕ) : List ℝ :=
  (zeroConstellationWindow S T n k).map Complex.im

/-- Comptage des zéros de la source jusqu'à `t` (deux signes de hauteur). -/
def zeroCountUpTo (S : ZeroSource) (t : ℝ) : ℕ := (zeroHeightFinset S t).card

/-! ## 4. Le théorème universel de fenêtre (PrimeDeterminedZeroRecovery.lean) -/

/-- **Toute fenêtre de la constellation déterminée par les premiers est la fenêtre canonique**, pour tout `T`, tout
rang `n`, toute longueur `k`. -/
theorem prime_determined_zero_window_eq_canonical_any_length (F : ℂ → ℂ)
    (hF : IsPrimeDeterminedZetaContinuation F) (T : ℝ) (n k : ℕ) :
    zeroConstellationWindow (primeDeterminedZeroSource F) T n k
      = zeroConstellationWindow canonicalZetaZeroSource T n k :=
  prime_determined_any_zero_source_object_eq F hF (fun S => zeroConstellationWindow S T n k)

/-- Idem pour les hauteurs. -/
theorem prime_determined_zero_window_heights_eq_canonical (F : ℂ → ℂ)
    (hF : IsPrimeDeterminedZetaContinuation F) (T : ℝ) (n k : ℕ) :
    zeroConstellationWindowHeights (primeDeterminedZeroSource F) T n k
      = zeroConstellationWindowHeights canonicalZetaZeroSource T n k :=
  prime_determined_any_zero_source_object_eq F hF (fun S => zeroConstellationWindowHeights S T n k)

/-- Idem pour le comptage. -/
theorem prime_determined_zero_count_eq_canonical (F : ℂ → ℂ)
    (hF : IsPrimeDeterminedZetaContinuation F) (t : ℝ) :
    zeroCountUpTo (primeDeterminedZeroSource F) t = zeroCountUpTo canonicalZetaZeroSource t :=
  prime_determined_any_zero_source_object_eq F hF (fun S => zeroCountUpTo S t)

/-! ## 5. Spécialisation canonique : non-vacuité et raccord aux fenêtres de RHV6Fresh -/

theorem zeroHeightSet_canonical (T : ℝ) :
    zeroHeightSet canonicalZetaZeroSource T = nontrivialZetaZerosByHeight T := rfl

theorem zeroHeightSet_canonical_finite (T : ℝ) : (zeroHeightSet canonicalZetaZeroSource T).Finite :=
  nontrivialZetaZerosByHeight_finite T

/-- La branche `∅` n'est jamais prise du côté canonique. -/
theorem zeroHeightFinset_canonical (T : ℝ) :
    zeroHeightFinset canonicalZetaZeroSource T = nontrivialZetaZerosByHeightFinset T := by
  classical
  rw [zeroHeightFinset, dif_pos (zeroHeightSet_canonical_finite T)]
  ext ρ
  simp [nontrivialZetaZerosByHeightFinset, zeroHeightSet, canonicalZetaZeroSource, nontrivialZetaZerosByHeight]

theorem mem_zeroHeightFinset_canonical {T : ℝ} {ρ : ℂ} :
    ρ ∈ zeroHeightFinset canonicalZetaZeroSource T ↔ IsNontrivialZetaZero ρ ∧ |ρ.im| < T := by
  rw [zeroHeightFinset_canonical, mem_nontrivialZetaZerosByHeightFinset]

/-- Appartenance à la vue ordonnée canonique : zéro non trivial authentique de hauteur dans `]0, T[`. -/
theorem mem_zeroOrderedMembers_canonical {T : ℝ} {ρ : ℂ} :
    ρ ∈ zeroOrderedMembers canonicalZetaZeroSource T ↔ IsNontrivialZetaZero ρ ∧ 0 < ρ.im ∧ ρ.im < T := by
  classical
  rw [zeroOrderedMembers, Finset.mem_sort, zeroPositiveMembers, Finset.mem_filter, mem_zeroHeightFinset_canonical]
  constructor
  · rintro ⟨⟨hz, hT⟩, hpos⟩
    exact ⟨hz, hpos, by rwa [abs_of_pos hpos] at hT⟩
  · rintro ⟨hz, hpos, hT⟩
    exact ⟨⟨hz, by rwa [abs_of_pos hpos]⟩, hpos⟩

/-- Raccord R11 : le prédicat de zéro non trivial (style Mathlib) et le prédicat de bande de `rhv3_lean` sont
équivalents (bande : `isNontrivialZetaZero_re_mem_Ioo`, port Kadiri ; réciproque : un point de la bande ouverte n'est
ni un zéro trivial, de partie réelle négative, ni le pôle). -/
theorem isNontrivialZetaZero_iff_strip (ρ : ℂ) : IsNontrivialZetaZero ρ ↔ PIsNonTrivialZetaZero ρ := by
  constructor
  · intro h
    exact ⟨h.1, (isNontrivialZetaZero_re_mem_Ioo h).1, (isNontrivialZetaZero_re_mem_Ioo h).2⟩
  · rintro ⟨hz, h0, h1⟩
    refine ⟨hz, ?_, ?_⟩
    · rintro ⟨n, hn⟩
      have hre : ρ.re = -2 * ((n : ℝ) + 1) := by
        rw [hn]; simp
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro h
      rw [h, Complex.one_re] at h1
      exact lt_irrefl _ h1

/-- Raccord R11 : les représentants positifs canoniques sont la fenêtre ouverte de RHV6Fresh. -/
theorem zeroPositiveMembers_canonical_eq_upperWindowOpen (T : ℝ) :
    zeroPositiveMembers canonicalZetaZeroSource T = upperWindowOpen T := by
  classical
  ext ρ
  rw [zeroPositiveMembers, Finset.mem_filter, mem_zeroHeightFinset_canonical, mem_upperWindowOpen,
    isNontrivialZetaZero_iff_strip]
  constructor
  · rintro ⟨⟨hz, hT⟩, hpos⟩
    exact ⟨hz, hpos, by rwa [abs_of_pos hpos] at hT⟩
  · rintro ⟨hz, hpos, hT⟩
    exact ⟨⟨hz, by rwa [abs_of_pos hpos]⟩, hpos⟩

/-- Raccord R11 : la vue ordonnée déterminée par les premiers est exactement la fenêtre ouverte de RHV6Fresh. -/
theorem mem_zeroOrderedMembers_primeDetermined_iff (F : ℂ → ℂ) (hF : IsPrimeDeterminedZetaContinuation F)
    {T : ℝ} {ρ : ℂ} :
    ρ ∈ zeroOrderedMembers (primeDeterminedZeroSource F) T ↔ ρ ∈ upperWindowOpen T := by
  rw [prime_determined_any_zero_source_object_eq F hF (fun S => zeroOrderedMembers S T), zeroOrderedMembers,
    Finset.mem_sort, zeroPositiveMembers_canonical_eq_upperWindowOpen]

end RHV6Fresh.RhGap

end

#print axioms RHV6Fresh.RhGap.primes_determine_zeta_meromorphic_continuation
#print axioms RHV6Fresh.RhGap.primes_determine_nontrivial_zero_multiset
#print axioms RHV6Fresh.RhGap.primeDeterminedZeroSource_eq_canonical
#print axioms RHV6Fresh.RhGap.prime_determined_zero_window_eq_canonical_any_length
#print axioms RHV6Fresh.RhGap.riemannZeta_isPrimeDetermined
#print axioms RHV6Fresh.RhGap.primeDetermined_unique
#print axioms RHV6Fresh.RhGap.isNontrivialZetaZero_iff_strip
#print axioms RHV6Fresh.RhGap.mem_zeroOrderedMembers_primeDetermined_iff
