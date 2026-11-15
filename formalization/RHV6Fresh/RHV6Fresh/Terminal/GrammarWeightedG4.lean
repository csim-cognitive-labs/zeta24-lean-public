/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import Mathlib

/-!
# G4 : canal orienté pondéré, suite unimodale, poids `log t · (X − t)` (instanciation du raccord G4)

Classement : THÉORÈME INDÉPENDANT (grammaire de deux états et poids réels), aucun zéro, aucune prémisse
équivalente à RH, aucune borne du reste.

* §1 `weighted_orientation_identity`, `weighted_orientation_variation_bound` (recopiés du TDD
  `experiments/TDD_GrammarWeightedG4.lean`, compilé) ;
* §2 `unimodal_variation_eq` : variation exacte `2 w_r − w_0 − w_{n−1}` d'une suite croissante puis décroissante ;
* §3 `weighted_orientation_unimodal_bound` : `|Σ a_i w_i| ≤ w_r` pour `w ≥ 0` unimodale ;
* §4 `t ↦ log t · (X − t)` est concave sur `]0, ∞[`, positive sur `[1, X]`, unimodale sur toute suite
  strictement croissante (`log_mul_sub_unimodal_on_increasing`), et `|Σ a_i w_i| ≤ X log X`
  (`weighted_orientation_log_mul_sub_bound`).

Portée : majoration de constante `X log X` (croît avec `X`), aucun gain d'exposant du reste.
-/
namespace RHV6Fresh.AstraGrammarG4

open Finset

/-! ## 1. Identité et borne de variation (recopiées du TDD) -/

theorem weighted_orientation_identity
    {n : ℕ} (hn : 1 ≤ n) (s w : ℕ → ℝ)
    (hs : ∀ i, |s i| = 1) :
    (∑ i ∈ Finset.range n, ((s i - s (i + 1)) / 2) * w i) =
      (s 0 * w 0 - s n * w (n - 1) +
        ∑ i ∈ Finset.range (n - 1), s (i + 1) * (w (i + 1) - w i)) / 2 := by
  revert s w
  induction n with
  | zero =>
      intro s w hs
      omega
  | succ n ih =>
      intro s w hs
      by_cases hzero : n = 0
      · subst n
        simp
        ring
      · have hn' : 1 ≤ n := by omega
        have ih' := ih hn' s w hs
        rw [Finset.sum_range_succ, ih']
        simp only [Nat.succ_sub_one]
        have hsum :
            (∑ i ∈ Finset.range n, s (i + 1) * (w (i + 1) - w i)) =
              (∑ i ∈ Finset.range (n - 1), s (i + 1) * (w (i + 1) - w i)) +
                s n * (w n - w (n - 1)) := by
          rw [show n = (n - 1) + 1 by omega, Finset.sum_range_succ]
          simp only [Nat.sub_add_cancel hn']
        rw [hsum]
        ring

theorem weighted_orientation_variation_bound
    {n : ℕ} (hn : 1 ≤ n) (s w : ℕ → ℝ)
    (hs : ∀ i, |s i| = 1)
    (M : ℝ)
    (hvar : ∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i| ≤
      2 * M - |w 0| - |w (n - 1)|) :
    |∑ i ∈ Finset.range n, ((s i - s (i + 1)) / 2) * w i| ≤
      M := by
  have h0 : |s 0 * w 0| = |w 0| := by
    rw [abs_mul, hs 0]
    simp
  have hn' : |s n * w (n - 1)| = |w (n - 1)| := by
    rw [abs_mul, hs n]
    simp
  have hsum :
      |∑ i ∈ Finset.range (n - 1), s (i + 1) * (w (i + 1) - w i)| ≤
        ∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i| := by
    calc
      |∑ i ∈ Finset.range (n - 1), s (i + 1) * (w (i + 1) - w i)| ≤
          ∑ i ∈ Finset.range (n - 1), |s (i + 1) * (w (i + 1) - w i)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, hs (i + 1)]
        simp
  calc
    |∑ i ∈ Finset.range n, ((s i - s (i + 1)) / 2) * w i| =
        |s 0 * w 0 - s n * w (n - 1) +
          ∑ i ∈ Finset.range (n - 1), s (i + 1) * (w (i + 1) - w i)| / 2 := by
            simpa [abs_div] using
              congrArg abs (weighted_orientation_identity hn s w hs)
    _ ≤ (|s 0 * w 0| + |s n * w (n - 1)| +
          |∑ i ∈ Finset.range (n - 1), s (i + 1) * (w (i + 1) - w i)|) / 2 := by
          have htri := abs_add_le (s 0 * w 0 - s n * w (n - 1))
            (∑ i ∈ Finset.range (n - 1), s (i + 1) * (w (i + 1) - w i))
          have hsub : |s 0 * w 0 - s n * w (n - 1)| ≤
              |s 0 * w 0| + |s n * w (n - 1)| := by
            calc
              |s 0 * w 0 - s n * w (n - 1)| =
                  |s 0 * w 0 + (-(s n * w (n - 1)))| := by rfl
              _ ≤ |s 0 * w 0| + |-(s n * w (n - 1))| :=
                abs_add_le _ _
              _ = |s 0 * w 0| + |s n * w (n - 1)| := by rw [abs_neg]
          linarith
    _ ≤ (|w 0| + |w (n - 1)| +
          ∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i|) / 2 := by
          rw [h0, hn']
          gcongr
    _ ≤ M := by
          have hv := hvar
          linarith


/-! ## 2. Variation exacte d'une suite unimodale -/

/-- Partie croissante : `Σ_{i<r} |w(i+1) − w i| = w r − w 0`. -/
theorem variation_up (w : ℕ → ℝ) (r : ℕ) (hup : ∀ i, i < r → w i ≤ w (i + 1)) :
    ∑ i ∈ range r, |w (i + 1) - w i| = w r - w 0 := by
  rw [← Finset.sum_range_sub (fun i => w i) r]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact abs_of_nonneg (sub_nonneg.mpr (hup i (Finset.mem_range.mp hi)))

/-- Partie décroissante : `Σ_{i<k} |w(r+i+1) − w(r+i)| = w r − w(r+k)`. -/
theorem variation_down (w : ℕ → ℝ) (r k : ℕ)
    (hdn : ∀ i, i < k → w (r + i + 1) ≤ w (r + i)) :
    ∑ i ∈ range k, |w (r + (i + 1)) - w (r + i)| = w r - w (r + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih (fun i hi => hdn i (by omega))]
      have := hdn k (by omega)
      rw [abs_of_nonpos (by rw [← add_assoc]; linarith)]
      ring_nf

/-- **Variation exacte d'une suite unimodale** (plateaux et extrémités compris) :
croissante sur `0..r`, décroissante sur `r..n−1` ⟹ `Σ_{i<n−1}|w(i+1) − w i| = 2 w r − w 0 − w(n−1)`. -/
theorem unimodal_variation_eq {n : ℕ} (w : ℕ → ℝ) (r : ℕ) (hr : r ≤ n - 1)
    (hup : ∀ i, i < r → w i ≤ w (i + 1))
    (hdn : ∀ i, r ≤ i → i < n - 1 → w (i + 1) ≤ w i) :
    ∑ i ∈ range (n - 1), |w (i + 1) - w i| = 2 * w r - w 0 - w (n - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, n - 1 = r + k := ⟨n - 1 - r, by omega⟩
  rw [hk, Finset.sum_range_add, variation_up w r hup]
  have hd := variation_down w r k (fun i hi => hdn (r + i) (by omega) (by omega))
  have : ∀ i, r + (i + 1) = r + i + 1 := fun i => by omega
  simp only [this] at hd
  rw [hd]
  ring

/-! ## 3. Borne du canal orienté pour un poids unimodal positif -/

/-- **Borne G4 unimodale** : `w ≥ 0` unimodale (maximum en `r`) et `|s i| = 1` ⟹
`|Σ_{i<n} ((s i − s(i+1))/2) w i| ≤ w r`. -/
theorem weighted_orientation_unimodal_bound
    {n : ℕ} (hn : 1 ≤ n) (s w : ℕ → ℝ) (hs : ∀ i, |s i| = 1)
    (hw : ∀ i, 0 ≤ w i) (r : ℕ) (hr : r ≤ n - 1)
    (hup : ∀ i, i < r → w i ≤ w (i + 1))
    (hdn : ∀ i, r ≤ i → i < n - 1 → w (i + 1) ≤ w i) :
    |∑ i ∈ range n, ((s i - s (i + 1)) / 2) * w i| ≤ w r := by
  refine weighted_orientation_variation_bound hn s w hs (w r) ?_
  rw [unimodal_variation_eq w r hr hup hdn, abs_of_nonneg (hw 0), abs_of_nonneg (hw (n - 1))]

/-! ## 4. Le poids `t ↦ log t · (X − t)` -/

/-- Le poids de la masse première d'un bloc. -/
noncomputable def massWeight (X : ℝ) (t : ℝ) : ℝ := Real.log t * (X - t)

theorem massWeight_nonneg {X t : ℝ} (h1 : 1 ≤ t) (hX : t ≤ X) : 0 ≤ massWeight X t :=
  mul_nonneg (Real.log_nonneg h1) (by linarith)

theorem massWeight_le {X t : ℝ} (h1 : 1 ≤ t) (hX : t ≤ X) : massWeight X t ≤ X * Real.log X := by
  unfold massWeight
  have h0 : 0 < t := by linarith
  have hl : Real.log t ≤ Real.log X := Real.log_le_log h0 hX
  have hl0 := Real.log_nonneg h1
  have hlX : 0 ≤ Real.log X := le_trans hl0 hl
  calc Real.log t * (X - t) ≤ Real.log X * (X - t) :=
        mul_le_mul_of_nonneg_right hl (by linarith)
    _ ≤ Real.log X * X := mul_le_mul_of_nonneg_left (by linarith) hlX
    _ = X * Real.log X := by ring

/-- `t ↦ log t · (X − t)` est concave sur `]0, ∞[` (dérivée seconde `−X/t² − 1/t < 0`),
pour `X ≥ 0`. -/
theorem massWeight_concaveOn {X : ℝ} (hX : 0 ≤ X) :
    ConcaveOn ℝ (Set.Ioi 0) (massWeight X) := by
  have h1 : ConcaveOn ℝ (Set.Ioi (0:ℝ)) (fun t => X • Real.log t) :=
    strictConcaveOn_log_Ioi.concaveOn.smul hX
  have h2 : ConvexOn ℝ (Set.Ioi (0:ℝ)) (fun t : ℝ => t * Real.log t) :=
    Real.strictConvexOn_mul_log.convexOn.subset Set.Ioi_subset_Ici_self (convex_Ioi 0)
  have h3 := h1.sub h2
  have he : massWeight X = (fun t => X • Real.log t) - fun t : ℝ => t * Real.log t := by
    funext t
    simp only [massWeight, Pi.sub_apply, smul_eq_mul]
    ring
  rw [he]
  exact h3

/-- **Unimodalité de `log t · (X − t)` le long d'une suite strictement croissante** dans `]0, ∞[` :
il existe un indice `r ≤ n − 1` tel que la suite des poids croisse (au sens large) jusqu'à `r`
puis décroisse. Preuve par la concavité : les pentes successives sont antitones. -/
theorem log_mul_sub_unimodal_on_increasing {X : ℝ} (hX : 0 ≤ X) {n : ℕ} (hn : 1 ≤ n)
    (t : ℕ → ℝ) (hpos : ∀ i, i < n → 0 < t i)
    (hinc : ∀ i, i + 1 < n → t i < t (i + 1)) :
    ∃ r, r ≤ n - 1 ∧
      (∀ i, i < r → massWeight X (t i) ≤ massWeight X (t (i + 1))) ∧
      (∀ i, r ≤ i → i < n - 1 → massWeight X (t (i + 1)) ≤ massWeight X (t i)) := by
  set a : ℕ → ℝ := fun i => massWeight X (t i) with ha
  set sl : ℕ → ℝ := fun i => (a (i + 1) - a i) / (t (i + 1) - t i) with hsl
  have hc := massWeight_concaveOn hX
  have hanti : ∀ j, j + 2 < n + 0 → sl (j + 1) ≤ sl j := by
    intro j hj
    have := hc.slope_anti_adjacent (x := t j) (y := t (j + 1)) (z := t (j + 2))
      (hpos j (by omega)) (hpos (j + 2) (by omega)) (hinc j (by omega)) (hinc (j + 1) (by omega))
    simpa [hsl, ha] using this
  have hanti' : ∀ i j, i ≤ j → j + 1 < n → sl j ≤ sl i := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
        intro hj
        exact le_trans (hanti j (by omega)) (ih (by omega))
  have hsign : ∀ i, i + 1 < n → (a (i + 1) < a i ↔ sl i < 0) := by
    intro i hi
    have hd : 0 < t (i + 1) - t i := sub_pos.mpr (hinc i hi)
    simp only [hsl]
    rw [div_neg_iff]
    constructor
    · intro h; right; exact ⟨by linarith, hd⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · linarith
      · linarith
  by_cases hex : ∃ i, i + 1 < n ∧ a (i + 1) < a i
  · classical
    let r := Nat.find hex
    have hr : r + 1 < n ∧ a (r + 1) < a r := Nat.find_spec hex
    refine ⟨r, by omega, ?_, ?_⟩
    · intro i hi
      have := Nat.find_min hex hi
      push Not at this
      have hi' : i + 1 < n := by omega
      exact this hi'
    · intro i hri hi
      have hs : sl i < 0 := by
        have h0 : sl r < 0 := (hsign r hr.1).mp hr.2
        exact lt_of_le_of_lt (hanti' r i hri (by omega)) h0
      exact ((hsign i (by omega)).mpr hs).le
  · push Not at hex
    refine ⟨n - 1, le_rfl, ?_, ?_⟩
    · intro i hi
      exact hex i (by omega)
    · intro i hri hi
      omega

/-- **Borne G4 pour le poids `log t (X − t)`** : pour une suite strictement croissante `t` dans
`[1, X]` (par exemple des premiers `> 3`) et `|s i| = 1`,
`|Σ_{i<n} ((s i − s(i+1))/2) · log(t i)(X − t i)| ≤ X log X`, indépendamment de `n`. -/
theorem weighted_orientation_log_mul_sub_bound {X : ℝ} {n : ℕ} (hn : 1 ≤ n) (s : ℕ → ℝ)
    (hs : ∀ i, |s i| = 1) (t : ℕ → ℝ)
    (h1 : ∀ i, i < n → 1 ≤ t i) (hX : ∀ i, i < n → t i ≤ X)
    (hinc : ∀ i, i + 1 < n → t i < t (i + 1)) :
    |∑ i ∈ range n, ((s i - s (i + 1)) / 2) * massWeight X (t i)| ≤ X * Real.log X := by
  have hX0 : 0 ≤ X := by have := hX 0 (by omega); have := h1 0 (by omega); linarith
  obtain ⟨r, hr, hup, hdn⟩ :=
    log_mul_sub_unimodal_on_increasing hX0 hn t (fun i hi => by have := h1 i hi; linarith) hinc
  -- prolongement du poids hors de `0..n−1` par `0` n'est pas nécessaire : on tronque
  set w : ℕ → ℝ := fun i => if i < n then massWeight X (t i) else 0 with hw
  have hwnn : ∀ i, 0 ≤ w i := by
    intro i; simp only [hw]; split_ifs with h
    · exact massWeight_nonneg (h1 i h) (hX i h)
    · exact le_rfl
  have hsum : ∑ i ∈ range n, ((s i - s (i + 1)) / 2) * massWeight X (t i) =
      ∑ i ∈ range n, ((s i - s (i + 1)) / 2) * w i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [hw, Finset.mem_range.mp hi]
  rw [hsum]
  have hup' : ∀ i, i < r → w i ≤ w (i + 1) := by
    intro i hi
    simp only [hw]; rw [if_pos (by omega), if_pos (by omega)]; exact hup i hi
  have hdn' : ∀ i, r ≤ i → i < n - 1 → w (i + 1) ≤ w i := by
    intro i hri hi
    simp only [hw]; rw [if_pos (by omega), if_pos (by omega)]; exact hdn i hri hi
  have hb := weighted_orientation_unimodal_bound hn s w hs hwnn r hr hup' hdn'
  refine le_trans hb ?_
  simp only [hw]; rw [if_pos (by omega)]
  exact massWeight_le (h1 r (by omega)) (hX r (by omega))

#print axioms weighted_orientation_identity
#print axioms weighted_orientation_variation_bound
#print axioms unimodal_variation_eq
#print axioms weighted_orientation_unimodal_bound
#print axioms massWeight_concaveOn
#print axioms log_mul_sub_unimodal_on_increasing
#print axioms weighted_orientation_log_mul_sub_bound

end RHV6Fresh.AstraGrammarG4
