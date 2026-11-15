/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FirstGainPremise
import RHV6Fresh.Terminal.SpectralUniqueness

/-!
# Insertion dans une famille complète, unicité de la limite, complément modifié
(auteur, 2026-10-08, directive en six points, points 2 et 3 ; relecture E181–E185 ; borne racine-log signée)

**Exclusion par unicité de la limite** (point 2). Si la famille initiale reconstruit `R` (sommes partielles
ordonnées vers `R`), la famille obtenue par insertion de deux contributions `d₁, d₂` (section 22, `insertTwo`) a
ses sommes partielles vers `R + Δ`, `Δ = d₁ + d₂` (`insertTwo_sum_tendsto`) ; par unicité de la limite, si elle
reconstruit aussi `R`, alors `Δ = 0` (`defect_zero_of_insertTwo_reconstructs`) ; donc `Δ ≠ 0 ⟹` la famille insérée
ne reconstruit pas ce reste (`insertTwo_not_reconstruct`). Instance dans le canal lissé, où la représentation est
démontrée : point par point en l'abscisse (`smoothed_insertion_excluded_at`, `smoothed_insertion_excluded_fun`) et
sur un support vectoriel par une coordonnée où le défaut est non nul (`smoothed_insertion_excluded_vector`).

**Portée impérative** : cela interdit une insertion supplémentaire dans une famille déjà complète dont les autres
contributions sont conservées. Cela n'exclut pas un membre OFF appartenant à la famille authentique. Correction de
l'auteur (relecture E184) : l'énoncé est AVEUGLE à la position radiale des contributions insérées ; une insertion
ON supplémentaire produit le même défaut (`insertTwo_not_reconstruct_onLine_pair`) ; le défaut de reconstruction
doit être distingué de l'effet propre d'une paire miroir.

**Non-annulation d'une famille hypothétique** : toute famille finie de points distincts de hauteur strictement
positive, avec coefficients non nuls et au moins un poids non nul, a une contribution regroupée (avec les
conjugués) non identiquement nulle sur `x > 1` (`grouped_profiles_not_identically_zero`, par unicité spectrale
`cpow_series_fibre_sum_zero`) ; termes de même hauteur compris (points distincts de même partie imaginaire).
Instances : paire miroir hypothétique à multiplicités positives, canal brut (`hypothetical_mirror_pair_not_identically_zero`)
et canal lissé (`hypothetical_mirror_pair_smoothed_not_identically_zero`) ; composition : une paire miroir hypothétique
insérée dans la famille lissée complète ne reconstruit pas le reste en une abscisse (`hypothetical_mirror_pair_insertion_excluded`).

**Obligation du complément** (point 3) : si une famille `c'` (paire insérée + complément modifié) reconstruit le même
reste, la modification du complément a pour somme ordonnée exactement `−Δ` (`complement_modification_tendsto`), aux mêmes
canal, normalisation, coordonnées et résidu ; sur tout l'horizon par quantification sur l'abscisse
(`complement_obligation_smoothed_all_x`). Rigidité spectrale compilée : dans toute représentation spectrale du canal
(points distincts, `Re ≤ 1`, localement finie, poids absolument sommables, même noyau de Perron), un point qui n'est
pas un zéro non trivial porte le poids nul (`intruder_weight_zero`) et chaque membre authentique garde exactement sa
multiplicité (`authentic_weight_rigid`) : aucun complément modifié DE CETTE CLASSE ne fournit `−Δ`
(`no_representation_carries_intruder`). Cette unicité ne prouve pas à elle seule que la famille authentique est ON.

**Borne racine-log signée** (auteur) : `R = c₁ + S`, `|R| ≤ C√x log x ⟹ −C√x log x − c₁ ≤ S ≤ C√x log x − c₁`
(`signed_removal_sqrt_log_bounds`, instance de `signed_removal_bounds`) ; instance lissée normalisée CONDITIONNELLE
(`smoothed_first_removed_sqrt_log_bounds` : la borne `√x log x` du reste lissé est une HYPOTHÈSE, non démontrée dans
le dépôt ; la borne démontrée est linéaire, `normalizedSmoothedRemainder_abs_le_sqrt`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean Filter
open scoped InnerProductSpace Topology

/-! ## 1. Unicité de la limite : une insertion dans une famille complète change la limite -/

section LimitUniqueness

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
/-- Le reste partiel après `N` contributions est `R` moins la somme des `N` premières. -/
theorem partialRemainder_succ_eq_sub (c : ℕ → V) (R : V) (N : ℕ) :
    partialRemainder c R (N + 1) = R - ∑ j ∈ Finset.range N, c (j + 1) := by
  unfold partialRemainder
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [add_comm]

omit [InnerProductSpace ℝ V] in
/-- **La famille insérée somme vers `R + Δ`** : sous la représentation ordonnée des vrais membres, les sommes
partielles de la famille insérée tendent vers `R + (d₁ + d₂)`. -/
theorem insertTwo_sum_tendsto {c : ℕ → V} {R : V}
    (hRep : Tendsto (fun N => ∑ j ∈ Finset.range N, c (j + 1)) atTop (𝓝 R))
    {p : ℕ} (hp : 1 ≤ p) (d₁ d₂ : V) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo c p d₁ d₂ (j + 1)) atTop (𝓝 (R + (d₁ + d₂))) := by
  have h := insertTwo_residual_tendsto hRep hp d₁ d₂
  have h2 : Tendsto (fun N => R - partialRemainder (insertTwo c p d₁ d₂) R (N + 3)) atTop
      (𝓝 (R - -(d₁ + d₂))) := tendsto_const_nhds.sub h
  have h3 : (fun N => R - partialRemainder (insertTwo c p d₁ d₂) R (N + 3)) =
      fun N => ∑ j ∈ Finset.range (N + 2), insertTwo c p d₁ d₂ (j + 1) := by
    funext N
    rw [show N + 3 = (N + 2) + 1 by ring, partialRemainder_succ_eq_sub]
    abel
  rw [h3, sub_neg_eq_add] at h2
  exact (tendsto_add_atTop_iff_nat 2).mp h2

omit [InnerProductSpace ℝ V] in
/-- **Unicité de la limite** : si la famille initiale et la famille insérée reconstruisent le même reste, le
défaut est nul, `d₁ + d₂ = 0`. -/
theorem defect_zero_of_insertTwo_reconstructs {c : ℕ → V} {R : V}
    (hRep : Tendsto (fun N => ∑ j ∈ Finset.range N, c (j + 1)) atTop (𝓝 R))
    {p : ℕ} (hp : 1 ≤ p) {d₁ d₂ : V}
    (hRep' : Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo c p d₁ d₂ (j + 1)) atTop (𝓝 R)) :
    d₁ + d₂ = 0 := by
  have h := tendsto_nhds_unique hRep' (insertTwo_sum_tendsto hRep hp d₁ d₂)
  have h' : R + (d₁ + d₂) - R = R - R := by rw [← h]
  simpa using h'

omit [InnerProductSpace ℝ V] in
/-- **`d₁ + d₂ ≠ 0 ⟹` la famille insérée ne reconstruit pas ce même reste.** -/
theorem insertTwo_not_reconstruct {c : ℕ → V} {R : V}
    (hRep : Tendsto (fun N => ∑ j ∈ Finset.range N, c (j + 1)) atTop (𝓝 R))
    {p : ℕ} (hp : 1 ≤ p) {d₁ d₂ : V} (hΔ : d₁ + d₂ ≠ 0) :
    ¬ Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo c p d₁ d₂ (j + 1)) atTop (𝓝 R) :=
  fun h => hΔ (defect_zero_of_insertTwo_reconstructs hRep hp h)

omit [InnerProductSpace ℝ V] in
/-- Forme `HasSum` : sous `HasSum` de la famille initiale, `HasSum` de la famille insérée vers le même reste force
`d₁ + d₂ = 0`. -/
theorem defect_zero_of_insertTwo_hasSum {c : ℕ → V} {R : V} (hRep : HasSum (fun j => c (j + 1)) R)
    {p : ℕ} (hp : 1 ≤ p) {d₁ d₂ : V}
    (h' : HasSum (fun j => insertTwo c p d₁ d₂ (j + 1)) R) : d₁ + d₂ = 0 :=
  defect_zero_of_insertTwo_reconstructs (ordered_of_hasSum hRep) hp h'.tendsto_sum_nat

omit [InnerProductSpace ℝ V] in
theorem insertTwo_not_hasSum {c : ℕ → V} {R : V} (hRep : HasSum (fun j => c (j + 1)) R)
    {p : ℕ} (hp : 1 ≤ p) {d₁ d₂ : V} (hΔ : d₁ + d₂ ≠ 0) :
    ¬ HasSum (fun j => insertTwo c p d₁ d₂ (j + 1)) R :=
  fun h => hΔ (defect_zero_of_insertTwo_hasSum hRep hp h)

omit [InnerProductSpace ℝ V] in
/-- **Obligation du complément** (point 3) : si une autre famille `c'` reconstruit le même reste, la différence
`c' − (famille insérée)`, sommée dans l'ordre, tend exactement vers `−Δ`. Mêmes canal, normalisation et coordonnées ;
le résidu est celui de la famille `c'`. -/
theorem complement_modification_tendsto {c : ℕ → V} {R : V}
    (hRep : Tendsto (fun N => ∑ j ∈ Finset.range N, c (j + 1)) atTop (𝓝 R))
    {p : ℕ} (hp : 1 ≤ p) (d₁ d₂ : V) (c' : ℕ → V)
    (hRep' : Tendsto (fun N => ∑ j ∈ Finset.range N, c' (j + 1)) atTop (𝓝 R)) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, (c' (j + 1) - insertTwo c p d₁ d₂ (j + 1))) atTop
      (𝓝 (-(d₁ + d₂))) := by
  have h := hRep'.sub (insertTwo_sum_tendsto hRep hp d₁ d₂)
  rw [show R - (R + (d₁ + d₂)) = -(d₁ + d₂) by abel] at h
  refine h.congr fun N => ?_
  rw [Finset.sum_sub_distrib]

omit [InnerProductSpace ℝ V] in
/-- Si le complément n'est PAS modifié (`c' = ` famille insérée), la reconstruction du même reste force `Δ = 0` :
c'est la forme « famille conservée » de l'obligation. -/
theorem complement_unchanged_forces_defect_zero {c : ℕ → V} {R : V}
    (hRep : Tendsto (fun N => ∑ j ∈ Finset.range N, c (j + 1)) atTop (𝓝 R))
    {p : ℕ} (hp : 1 ≤ p) {d₁ d₂ : V}
    (hRep' : Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo c p d₁ d₂ (j + 1)) atTop (𝓝 R)) :
    d₁ + d₂ = 0 :=
  defect_zero_of_insertTwo_reconstructs hRep hp hRep'

end LimitUniqueness

/-! ## 2. Instance dans le canal lissé (représentation démontrée) -/

/-- La famille lissée canonique scalaire à l'abscisse `x` : `n ↦ c̃_n(x)`. -/
noncomputable def smoothedCanonicalAt (x : ℝ) (n : ℕ) : ℝ :=
  normalizedSmoothedPairContribution (canonicalZero n) x

theorem smoothedCanonicalAt_hasSum {x : ℝ} (hx : 1 < x) :
    HasSum (fun j => smoothedCanonicalAt x (j + 1)) (normalizedSmoothedRemainder x) :=
  normalizedSmoothedPairContribution_hasSum hx

/-- **Point par point en l'abscisse** : à toute abscisse `x > 1`, insérer deux contributions de somme non nulle dans
la famille lissée canonique détruit la reconstruction du reste lissé normalisé. -/
theorem smoothed_insertion_excluded_at {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : 1 ≤ p) {d₁ d₂ : ℝ}
    (hΔ : d₁ + d₂ ≠ 0) :
    ¬ Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo (smoothedCanonicalAt x) p d₁ d₂ (j + 1)) atTop
      (𝓝 (normalizedSmoothedRemainder x)) :=
  insertTwo_not_reconstruct (ordered_of_hasSum (smoothedCanonicalAt_hasSum hx)) hp hΔ

/-- **Fonction de l'abscisse** : si le défaut `d₁(x) + d₂(x)` est non nul en une abscisse `x > 1`, la famille insérée
ne reconstruit pas le reste lissé en cette abscisse. -/
theorem smoothed_insertion_excluded_fun {p : ℕ} (hp : 1 ≤ p) (d₁ d₂ : ℝ → ℝ)
    (h : ∃ x : ℝ, 1 < x ∧ d₁ x + d₂ x ≠ 0) :
    ∃ x : ℝ, 1 < x ∧
      ¬ Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo (smoothedCanonicalAt x) p (d₁ x) (d₂ x) (j + 1))
        atTop (𝓝 (normalizedSmoothedRemainder x)) := by
  obtain ⟨x, hx, hΔ⟩ := h
  exact ⟨x, hx, smoothed_insertion_excluded_at hx hp hΔ⟩

/-- **Support vectoriel** : une coordonnée `i` où le défaut est non nul suffit. -/
theorem smoothed_insertion_excluded_vector {m : ℕ} (xs : Fin m → ℝ) (hxs : ∀ i, 1 < xs i) {p : ℕ}
    (hp : 1 ≤ p) {d₁ d₂ : EuclideanSpace ℝ (Fin m)} (i : Fin m) (hi : (d₁ + d₂) i ≠ 0) :
    ¬ Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo (smoothedCanonicalContributions xs) p d₁ d₂ (j + 1))
      atTop (𝓝 (normalizedSmoothedRemainderVector xs)) :=
  insertTwo_not_reconstruct (ordered_of_hasSum (smoothedCanonical_hasSum xs hxs)) hp
    (fun h => hi (by rw [h]; simp))

/-- **Aveugle à la position radiale** (correction de l'auteur, relecture E184) : deux contributions ON insérées
produisent le même défaut ; l'exclusion lit la somme `d₁ + d₂`, jamais la position radiale. -/
theorem insertTwo_not_reconstruct_onLine_pair {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : 1 ≤ p) (z₁ z₂ : TrueZero)
    (_h₁ : rZeroRadialPosition z₁.1 = 1 / 2) (_h₂ : rZeroRadialPosition z₂.1 = 1 / 2)
    (hΔ : normalizedSmoothedPairContribution z₁ x + normalizedSmoothedPairContribution z₂ x ≠ 0) :
    ¬ Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo (smoothedCanonicalAt x) p
      (normalizedSmoothedPairContribution z₁ x) (normalizedSmoothedPairContribution z₂ x) (j + 1)) atTop
      (𝓝 (normalizedSmoothedRemainder x)) :=
  smoothed_insertion_excluded_at hx hp hΔ

/-- **Obligation du complément sur tout l'horizon** : pour toute abscisse `x > 1`, si une famille `c'(x)` reconstruit
le reste lissé normalisé, la modification du complément somme vers `−(d₁(x) + d₂(x))`. -/
theorem complement_obligation_smoothed_all_x {p : ℕ} (hp : 1 ≤ p) (d₁ d₂ : ℝ → ℝ) (c' : ℝ → ℕ → ℝ)
    (hRep' : ∀ x : ℝ, 1 < x →
      Tendsto (fun N => ∑ j ∈ Finset.range N, c' x (j + 1)) atTop (𝓝 (normalizedSmoothedRemainder x))) :
    ∀ x : ℝ, 1 < x →
      Tendsto (fun N => ∑ j ∈ Finset.range N,
        (c' x (j + 1) - insertTwo (smoothedCanonicalAt x) p (d₁ x) (d₂ x) (j + 1))) atTop
        (𝓝 (-(d₁ x + d₂ x))) :=
  fun x hx => complement_modification_tendsto (ordered_of_hasSum (smoothedCanonicalAt_hasSum hx)) hp _ _ _
    (hRep' x hx)

/-! ## 3. Non-annulation d'une famille hypothétique de profils regroupés -/

/-- Contribution brute regroupée d'un POINT du plan (pas nécessairement un zéro) : `−2·Re(x^ρ/ρ)`. -/
noncomputable def pointPairContribution (ρ : ℂ) (x : ℝ) : ℝ := -2 * ((x : ℂ) ^ ρ / ρ).re

/-- Contribution lissée normalisée regroupée d'un point, de multiplicité `m` : `2·Re(−m·x^ρ/(ρ(ρ+1)))/√x`. -/
noncomputable def pointSmoothedPairContribution (m : ℕ) (ρ : ℂ) (x : ℝ) : ℝ :=
  2 * (-(m : ℂ) * Perron.f x ρ).re / Real.sqrt x

theorem pairContribution_eq_point (z : TrueZero) (x : ℝ) :
    pairContribution z x = pointPairContribution (zeroPoint z) x := rfl

theorem normalizedSmoothedPairContribution_eq_point (z : TrueZero) (x : ℝ) :
    normalizedSmoothedPairContribution z x =
      pointSmoothedPairContribution (zetaZeroMultiplicity (zeroPoint z)) (zeroPoint z) x := rfl

theorem pointPairContribution_eq (ρ : ℂ) (x : ℝ) :
    pointPairContribution ρ x = 2 * ((-1 / ρ) * (x : ℂ) ^ ρ).re := by
  unfold pointPairContribution
  rw [show (-1 / ρ) * (x : ℂ) ^ ρ = -((x : ℂ) ^ ρ / ρ) by ring, Complex.neg_re]
  ring

theorem pointSmoothedPairContribution_eq (m : ℕ) (ρ : ℂ) (x : ℝ) :
    pointSmoothedPairContribution m ρ x =
      (m : ℝ) * (2 * ((-1 / (ρ * (ρ + 1))) * (x : ℂ) ^ ρ).re) / Real.sqrt x := by
  unfold pointSmoothedPairContribution
  rw [show -(m : ℂ) * Perron.f x ρ = ((m : ℝ) : ℂ) * ((-1 / (ρ * (ρ + 1))) * (x : ℂ) ^ ρ) by
    simp only [Perron.f]; push_cast; ring, Complex.re_ofReal_mul]
  ring

/-- Pour `x > 0` réel, `x^{conj ρ} = conj(x^ρ)`. -/
theorem cpow_conj_of_pos {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    (x : ℂ) ^ (starRingEnd ℂ ρ) = starRingEnd ℂ ((x : ℂ) ^ ρ) := by
  have h := Complex.cpow_conj (x : ℂ) ρ (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne)
  rwa [Complex.conj_ofReal] at h

open Classical in
/-- **Non-annulation** : une famille finie de points DISTINCTS de partie imaginaire strictement positive (même
hauteur permise), de partie réelle `≤ 1`, avec coefficients `κ_i ≠ 0` et poids réels dont l'un est non nul, a une
contribution regroupée `Σ_i w_i · 2 Re(κ_i x^{ρ_i})` non identiquement nulle sur `x > 1`. Preuve par unicité
spectrale (`cpow_series_fibre_sum_zero`) sur la famille doublée par les conjugués. -/
theorem grouped_profiles_not_identically_zero {ι : Type*} [Fintype ι] (ρ : ι → ℂ)
    (hinj : Function.Injective ρ) (hre : ∀ i, (ρ i).re ≤ 1) (him : ∀ i, 0 < (ρ i).im)
    (κ : ι → ℂ) (hκ : ∀ i, κ i ≠ 0) (w : ι → ℝ) (i₀ : ι) (hw : w i₀ ≠ 0) :
    ∃ x : ℝ, 1 < x ∧ ∑ i, w i * (2 * (κ i * (x : ℂ) ^ ρ i).re) ≠ 0 := by
  by_contra hall
  push Not at hall
  let s : ι ⊕ ι → ℂ := Sum.elim ρ fun i => starRingEnd ℂ (ρ i)
  let a : ι ⊕ ι → ℂ := Sum.elim (fun i => (w i : ℂ) * κ i) fun i => (w i : ℂ) * starRingEnd ℂ (κ i)
  have hre' : ∀ u, (s u).re ≤ 1 := by
    rintro (i | i)
    · exact hre i
    · simpa [s] using hre i
  have hfin : ∀ R : ℝ, {u | ‖s u‖ ≤ R}.Finite := fun _ => Set.toFinite _
  have ha : Summable fun u => ‖a u‖ := (hasSum_fintype _).summable
  have hzero : ∀ x : ℝ, 1 < x → ∑' u, a u * (x : ℂ) ^ s u = 0 := by
    intro x hx
    have hx0 : 0 < x := by linarith
    rw [tsum_fintype, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    have key : ∀ i, a (Sum.inl i) * (x : ℂ) ^ s (Sum.inl i) + a (Sum.inr i) * (x : ℂ) ^ s (Sum.inr i) =
        ((w i * (2 * (κ i * (x : ℂ) ^ ρ i).re) : ℝ) : ℂ) := by
      intro i
      simp only [s, a, Sum.elim_inl, Sum.elim_inr]
      rw [cpow_conj_of_pos hx0]
      have : (w i : ℂ) * κ i * (x : ℂ) ^ ρ i +
          (w i : ℂ) * starRingEnd ℂ (κ i) * starRingEnd ℂ ((x : ℂ) ^ ρ i) =
          (w i : ℂ) * (κ i * (x : ℂ) ^ ρ i + starRingEnd ℂ (κ i * (x : ℂ) ^ ρ i)) := by
        rw [map_mul]; ring
      rw [this, Complex.add_conj]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun i _ => key i, ← Complex.ofReal_sum, hall x hx, Complex.ofReal_zero]
  have key := cpow_series_fibre_sum_zero s a hre' hfin ha hzero (ρ i₀)
  rw [tsum_fintype, Fintype.sum_sum_type] at key
  have h2 : ∑ i, (if s (Sum.inr i) = ρ i₀ then a (Sum.inr i) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => if_neg ?_
    intro h
    have := congrArg Complex.im h
    simp only [s, Sum.elim_inr, Complex.conj_im] at this
    linarith [him i, him i₀]
  have h1 : ∑ i, (if s (Sum.inl i) = ρ i₀ then a (Sum.inl i) else 0) = a (Sum.inl i₀) := by
    rw [Finset.sum_eq_single i₀]
    · simp [s]
    · intro i _ hi
      exact if_neg fun h => hi (hinj h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h1, h2, add_zero] at key
  simp only [a, Sum.elim_inl] at key
  rcases mul_eq_zero.mp key with h | h
  · exact hw (by exact_mod_cast h)
  · exact hκ i₀ h

/-- **Termes de même hauteur** : la même conclusion pour une famille de points distincts de hauteur commune
`T > 0` (la distinction se fait par la position radiale). -/
theorem sameHeight_profiles_not_identically_zero {ι : Type*} [Fintype ι] (ρ : ι → ℂ)
    (hinj : Function.Injective ρ) (hre : ∀ i, (ρ i).re ≤ 1) {T : ℝ} (hT : 0 < T)
    (hhgt : ∀ i, (ρ i).im = T) (κ : ι → ℂ) (hκ : ∀ i, κ i ≠ 0) (w : ι → ℝ) (i₀ : ι) (hw : w i₀ ≠ 0) :
    ∃ x : ℝ, 1 < x ∧ ∑ i, w i * (2 * (κ i * (x : ℂ) ^ ρ i).re) ≠ 0 :=
  grouped_profiles_not_identically_zero ρ hinj hre (fun i => by rw [hhgt i]; exact hT) κ hκ w i₀ hw

theorem point_ne_zero_of_im_pos {ρ : ℂ} (h : 0 < ρ.im) : ρ ≠ 0 := by
  intro h0; rw [h0] at h; simp at h

theorem point_add_one_ne_zero_of_im_pos {ρ : ℂ} (h : 0 < ρ.im) : ρ + 1 ≠ 0 := by
  intro h0
  have := congrArg Complex.im h0
  simp at this
  linarith

/-- Le miroir `1 − conj ρ` a la même hauteur et la position radiale réfléchie. -/
theorem mirrorPoint_im (ρ : ℂ) : (1 - starRingEnd ℂ ρ).im = ρ.im := by simp

theorem mirrorPoint_re (ρ : ℂ) : (1 - starRingEnd ℂ ρ).re = 1 - ρ.re := by simp

/-- **Paire miroir hypothétique, canal brut** : pour un point `ρ` de la bande ouverte, de hauteur `> 0`, et des
multiplicités `m₁ > 0`, `m₂ ≥ 0`, la contribution `m₁·c(ρ) + m₂·c(ρ*)` n'est pas identiquement nulle sur `x > 1`.
Le cas `ρ* = ρ` (ligne) est traité par regroupement des poids. -/
theorem hypothetical_mirror_pair_not_identically_zero {ρ : ℂ} (hre0 : 0 ≤ ρ.re) (hre1 : ρ.re ≤ 1)
    (him : 0 < ρ.im)
    {m₁ m₂ : ℕ} (hm : 0 < m₁) :
    ∃ x : ℝ, 1 < x ∧
      (m₁ : ℝ) * pointPairContribution ρ x + (m₂ : ℝ) * pointPairContribution (1 - starRingEnd ℂ ρ) x ≠ 0 := by
  have hρ0 : ρ ≠ 0 := point_ne_zero_of_im_pos him
  by_cases heq : 1 - starRingEnd ℂ ρ = ρ
  · obtain ⟨x, hx, h⟩ := grouped_profiles_not_identically_zero (ι := Unit) (fun _ => ρ)
      (fun _ _ _ => rfl) (fun _ => hre1) (fun _ => him) (fun _ => -1 / ρ)
      (fun _ => div_ne_zero (by norm_num) hρ0) (fun _ => (m₁ : ℝ) + m₂) ()
      (by positivity)
    refine ⟨x, hx, ?_⟩
    rw [heq, pointPairContribution_eq]
    rw [Fintype.sum_unique] at h
    intro h0; apply h; linear_combination h0
  · have hinj : Function.Injective (fun b : Bool => if b then ρ else 1 - starRingEnd ℂ ρ) := by
      intro b₁ b₂ h
      cases b₁ <;> cases b₂
      · rfl
      · exact absurd (by simpa using h) heq
      · exact absurd (by simpa using h.symm) heq
      · rfl
    obtain ⟨x, hx, h⟩ := grouped_profiles_not_identically_zero (ι := Bool)
      (fun b => if b then ρ else 1 - starRingEnd ℂ ρ) hinj
      (fun b => by cases b <;> simp <;> linarith [hre0, hre1])
      (fun b => by cases b <;> simp [him])
      (fun b => if b then -1 / ρ else -1 / (1 - starRingEnd ℂ ρ))
      (fun b => by
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact div_ne_zero (by norm_num) (point_ne_zero_of_im_pos (by rw [mirrorPoint_im]; exact him))
        · simp only [↓reduceIte]
          exact div_ne_zero (by norm_num) hρ0)
      (fun b => if b then (m₁ : ℝ) else m₂) true (by simp; exact_mod_cast hm.ne')
    refine ⟨x, hx, ?_⟩
    rw [Fintype.sum_bool] at h
    simp only [↓reduceIte, Bool.false_eq_true] at h
    rw [pointPairContribution_eq, pointPairContribution_eq]
    intro h0; apply h; linear_combination h0

/-- **Paire miroir hypothétique, canal lissé normalisé** : même énoncé pour `m₁·c̃(ρ) + m₂·c̃(ρ*)`. -/
theorem hypothetical_mirror_pair_smoothed_not_identically_zero {ρ : ℂ} (hre0 : 0 ≤ ρ.re) (hre1 : ρ.re ≤ 1)
    (him : 0 < ρ.im)
    {m₁ m₂ : ℕ} (hm : 0 < m₁) :
    ∃ x : ℝ, 1 < x ∧
      pointSmoothedPairContribution m₁ ρ x + pointSmoothedPairContribution m₂ (1 - starRingEnd ℂ ρ) x ≠ 0 := by
  have hρ0 : ρ ≠ 0 := point_ne_zero_of_im_pos him
  have hρ1 : ρ + 1 ≠ 0 := point_add_one_ne_zero_of_im_pos him
  have hρ' : ρ * (ρ + 1) ≠ 0 := mul_ne_zero hρ0 hρ1
  have hmirIm : 0 < (1 - starRingEnd ℂ ρ).im := by rw [mirrorPoint_im]; exact him
  have hmir' : (1 - starRingEnd ℂ ρ) * ((1 - starRingEnd ℂ ρ) + 1) ≠ 0 :=
    mul_ne_zero (point_ne_zero_of_im_pos hmirIm) (point_add_one_ne_zero_of_im_pos hmirIm)
  by_cases heq : 1 - starRingEnd ℂ ρ = ρ
  · obtain ⟨x, hx, h⟩ := grouped_profiles_not_identically_zero (ι := Unit) (fun _ => ρ)
      (fun _ _ _ => rfl) (fun _ => hre1) (fun _ => him) (fun _ => -1 / (ρ * (ρ + 1)))
      (fun _ => div_ne_zero (by norm_num) hρ') (fun _ => (m₁ : ℝ) + m₂) () (by positivity)
    refine ⟨x, hx, ?_⟩
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    rw [heq, pointSmoothedPairContribution_eq, pointSmoothedPairContribution_eq, ← add_div,
      div_ne_zero_iff]
    refine ⟨?_, hs.ne'⟩
    rw [Fintype.sum_unique] at h
    intro h0; apply h; linear_combination h0
  · have hinj : Function.Injective (fun b : Bool => if b then ρ else 1 - starRingEnd ℂ ρ) := by
      intro b₁ b₂ h
      cases b₁ <;> cases b₂
      · rfl
      · exact absurd (by simpa using h) heq
      · exact absurd (by simpa using h.symm) heq
      · rfl
    obtain ⟨x, hx, h⟩ := grouped_profiles_not_identically_zero (ι := Bool)
      (fun b => if b then ρ else 1 - starRingEnd ℂ ρ) hinj
      (fun b => by cases b <;> simp <;> linarith [hre0, hre1])
      (fun b => by cases b <;> simp [him])
      (fun b => if b then -1 / (ρ * (ρ + 1)) else -1 / ((1 - starRingEnd ℂ ρ) * ((1 - starRingEnd ℂ ρ) + 1)))
      (fun b => by
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact div_ne_zero (by norm_num) hmir'
        · simp only [↓reduceIte]
          exact div_ne_zero (by norm_num) hρ')
      (fun b => if b then (m₁ : ℝ) else m₂) true (by simp; exact_mod_cast hm.ne')
    refine ⟨x, hx, ?_⟩
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    rw [pointSmoothedPairContribution_eq, pointSmoothedPairContribution_eq, ← add_div, div_ne_zero_iff]
    refine ⟨?_, hs.ne'⟩
    rw [Fintype.sum_bool] at h
    simp only [↓reduceIte, Bool.false_eq_true] at h
    intro h0; apply h; linear_combination h0

/-- **Composition** : une paire miroir hypothétique (multiplicités `m₁ > 0`, `m₂ ≥ 0`) insérée aux rangs `p, p + 1`
de la famille lissée canonique, les autres contributions étant conservées, ne reconstruit pas le reste lissé normalisé
en une abscisse `x > 1`. -/
theorem hypothetical_mirror_pair_insertion_excluded {ρ : ℂ} (hre0 : 0 ≤ ρ.re) (hre1 : ρ.re ≤ 1)
    (him : 0 < ρ.im)
    {m₁ m₂ : ℕ} (hm : 0 < m₁) {p : ℕ} (hp : 1 ≤ p) :
    ∃ x : ℝ, 1 < x ∧
      ¬ Tendsto (fun N => ∑ j ∈ Finset.range N, insertTwo (smoothedCanonicalAt x) p
        (pointSmoothedPairContribution m₁ ρ x) (pointSmoothedPairContribution m₂ (1 - starRingEnd ℂ ρ) x) (j + 1))
        atTop (𝓝 (normalizedSmoothedRemainder x)) :=
  smoothed_insertion_excluded_fun hp _ _ (hypothetical_mirror_pair_smoothed_not_identically_zero hre0 hre1 him hm)

/-! ## 4. Rigidité spectrale : ce qu'un complément modifié ne peut pas fournir -/

/-- Dans toute représentation spectrale du canal, un point qui n'est pas un zéro non trivial porte le poids nul. -/
theorem intruder_weight_zero {ι : Type*} (Rep : SpectralRepresentation ι) {ρ : ℂ}
    (hρ : ¬ IsNontrivialZetaZero ρ) (i : ι) (hi : Rep.point i = ρ) : Rep.weight i = 0 :=
  Rep.no_intruder i (hi ▸ hρ)

/-- **Aucune représentation spectrale ne porte un intrus avec un poids non nul** : un complément modifié qui resterait
dans la classe des représentations (points distincts, `Re ≤ 1`, localement finie, poids absolument sommables, même
noyau, égalité pour tout `x > 1`) ne peut pas absorber une paire hypothétique de poids non nul. -/
theorem no_representation_carries_intruder {ι : Type*} {ρ : ℂ} (hρ : ¬ IsNontrivialZetaZero ρ) :
    ¬ ∃ Rep : SpectralRepresentation ι, ∃ i, Rep.point i = ρ ∧ Rep.weight i ≠ 0 := by
  rintro ⟨Rep, i, hi, hne⟩
  exact hne (intruder_weight_zero Rep hρ i hi)

/-- **Chaque membre authentique garde exactement sa multiplicité** dans toute représentation : le complément
authentique ne peut pas être repondéré. -/
theorem authentic_weight_rigid {ι : Type*} (Rep : SpectralRepresentation ι) (z : TrueZero) :
    ∃ i, Rep.point i = zeroPoint z ∧ Rep.weight i = -(zetaZeroMultiplicity (zeroPoint z) : ℂ) :=
  Rep.contains_member (memberIndex z)

/-! ## 5. Borne racine-log signée, retrait exact du premier (auteur, 2026-10-08) -/

/-- **`R = c₁ + S`, `|R| ≤ C√x log x ⟹ −C√x log x − c₁ ≤ S ≤ C√x log x − c₁`.** Le « moins » porte sur la contribution
signée du premier ; aucune soustraction d'amplitude aux deux marges. Tout canal réel, toute abscisse `x` où la
borne est fournie. -/
theorem signed_removal_sqrt_log_bounds {R c₁ S C x : ℝ} (h : R = c₁ + S)
    (hB : |R| ≤ C * Real.sqrt x * Real.log x) :
    -(C * Real.sqrt x * Real.log x) - c₁ ≤ S ∧ S ≤ C * Real.sqrt x * Real.log x - c₁ :=
  signed_removal_bounds h hB

/-- **Instance lissée normalisée, CONDITIONNELLE** : sous l'HYPOTHÈSE `|Re R̃(x)| ≤ C√x log x` (`x > 1`, non démontrée
dans le dépôt ; la borne démontrée est linéaire), le reste lissé normalisé privé du premier membre canonique,
`S̃ = Σ_{n≥2} c̃_n` (`smoothed_first_removed_hasSum`), vérifie `−C log x − c̃₁ ≤ S̃ ≤ C log x − c̃₁`. -/
theorem smoothed_first_removed_sqrt_log_bounds {C : ℝ}
    (hB : ∀ x : ℝ, 1 < x → |(smoothedRemainder x).re| ≤ C * Real.sqrt x * Real.log x) {x : ℝ} (hx : 1 < x) :
    -(C * Real.log x) - normalizedSmoothedPairContribution (canonicalZero 1) x ≤
        normalizedSmoothedRemainder x - normalizedSmoothedPairContribution (canonicalZero 1) x ∧
      normalizedSmoothedRemainder x - normalizedSmoothedPairContribution (canonicalZero 1) x ≤
        C * Real.log x - normalizedSmoothedPairContribution (canonicalZero 1) x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hR : |normalizedSmoothedRemainder x| ≤ C * Real.log x := by
    unfold normalizedSmoothedRemainder
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    calc |(smoothedRemainder x).re| ≤ C * Real.sqrt x * Real.log x := hB x hx
      _ = C * Real.log x * Real.sqrt x := by ring
  exact signed_removal_bounds (by ring) hR


/-- **Règle de normalisation** : si le reste est divisé par `√x`, la borne l'est aussi ; de `|R| ≤ C√x log x` on tire
`|R/√x| ≤ C log x` (aucun facteur `√x` conservé artificiellement). -/
theorem normalized_abs_le_of_sqrt_log_bound {R C x : ℝ} (hx : 0 < x)
    (hB : |R| ≤ C * Real.sqrt x * Real.log x) : |R / Real.sqrt x| ≤ C * Real.log x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  calc |R| ≤ C * Real.sqrt x * Real.log x := hB
    _ = C * Real.log x * Real.sqrt x := by ring

/-- **Retrait signé du premier, canal normalisé par `√x`** : `R = c₁ + S`, `|R| ≤ B` ⟹
`−B/√x − c₁/√x ≤ S/√x ≤ B/√x − c₁/√x` (intervalle SIGNÉ, la phase de `c₁` conservée ; jamais `B − |c₁|`). -/
theorem signed_removal_normalized_bounds {R c₁ S B x : ℝ} (hx : 0 < x) (h : R = c₁ + S) (hB : |R| ≤ B) :
    -(B / Real.sqrt x) - c₁ / Real.sqrt x ≤ S / Real.sqrt x ∧
      S / Real.sqrt x ≤ B / Real.sqrt x - c₁ / Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  obtain ⟨h1, h2⟩ := signed_removal_bounds h hB
  constructor
  · have : (-B - c₁) / Real.sqrt x ≤ S / Real.sqrt x := (div_le_div_iff_of_pos_right hs).mpr h1
    rwa [sub_div, neg_div] at this
  · have : S / Real.sqrt x ≤ (B - c₁) / Real.sqrt x := (div_le_div_iff_of_pos_right hs).mpr h2
    rwa [sub_div] at this

/-- **Instance racine-log normalisée** : sous `|R| ≤ C√x log x` et `R = c₁ + S`, les marges normalisées sont
`±C log x − c₁/√x` : la borne est divisée par `√x` avec le reste. -/
theorem signed_removal_sqrt_log_normalized_bounds {R c₁ S C x : ℝ} (hx : 0 < x) (h : R = c₁ + S)
    (hB : |R| ≤ C * Real.sqrt x * Real.log x) :
    -(C * Real.log x) - c₁ / Real.sqrt x ≤ S / Real.sqrt x ∧
      S / Real.sqrt x ≤ C * Real.log x - c₁ / Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hBn : C * Real.sqrt x * Real.log x / Real.sqrt x = C * Real.log x := by
    field_simp
  have := signed_removal_normalized_bounds hx h hB
  rwa [hBn] at this
end RHV6Fresh

#print axioms RHV6Fresh.defect_zero_of_insertTwo_reconstructs
#print axioms RHV6Fresh.insertTwo_not_reconstruct
#print axioms RHV6Fresh.smoothed_insertion_excluded_at
#print axioms RHV6Fresh.smoothed_insertion_excluded_vector
#print axioms RHV6Fresh.grouped_profiles_not_identically_zero
#print axioms RHV6Fresh.hypothetical_mirror_pair_not_identically_zero
#print axioms RHV6Fresh.hypothetical_mirror_pair_smoothed_not_identically_zero
#print axioms RHV6Fresh.hypothetical_mirror_pair_insertion_excluded
#print axioms RHV6Fresh.complement_modification_tendsto
#print axioms RHV6Fresh.no_representation_carries_intruder
#print axioms RHV6Fresh.authentic_weight_rigid
#print axioms RHV6Fresh.signed_removal_sqrt_log_bounds
#print axioms RHV6Fresh.smoothed_first_removed_sqrt_log_bounds
#print axioms RHV6Fresh.insertTwo_sum_tendsto
#print axioms RHV6Fresh.smoothed_insertion_excluded_fun
#print axioms RHV6Fresh.insertTwo_not_reconstruct_onLine_pair
#print axioms RHV6Fresh.complement_unchanged_forces_defect_zero
#print axioms RHV6Fresh.complement_obligation_smoothed_all_x
#print axioms RHV6Fresh.intruder_weight_zero
#print axioms RHV6Fresh.sameHeight_profiles_not_identically_zero
#print axioms RHV6Fresh.defect_zero_of_insertTwo_hasSum
#print axioms RHV6Fresh.insertTwo_not_hasSum
#print axioms RHV6Fresh.normalized_abs_le_of_sqrt_log_bound
#print axioms RHV6Fresh.signed_removal_normalized_bounds
#print axioms RHV6Fresh.signed_removal_sqrt_log_normalized_bounds
