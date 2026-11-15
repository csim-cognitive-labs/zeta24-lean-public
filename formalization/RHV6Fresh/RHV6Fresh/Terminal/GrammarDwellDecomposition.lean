/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import Mathlib

/-!
# Décomposition des séjours internes de la grammaire mod 6 (Archétype B)

Modèle abstrait : une suite d'états `s : ℕ → Bool` (`true` = état 1, `false` = état 5), lue sur les indices
`0..n`, donc `n` transitions `i ↦ i+1`.  On note `N11`, `N55` (séjours internes), `N15`, `N51` (transitions
croisées), `N1•` (`occ1`) et `N5•` (`occ5`) les nombres d'indices de départ `i < n` en état 1, resp. 5.

Identités démontrées (aucune hypothèse, aucun axiome ajouté) :

* `orientation_telescopes` : `N15 − N51 = 1[s 0 = 1] − 1[s n = 1]`, donc `|N15 − N51| ≤ 1` ;
* `N11 = N1• − N15`, `N55 = N5• − N51` (`n11_eq`, `n55_eq`) ;
* `dwell_balance_eq_occupancy_minus_orientation` : `D = N11 − N55 = (N1• − N5•) − (N15 − N51)` ;
* `dwell_balance_iff_occupancy` : `|D − (N1• − N5•)| ≤ 1`.

Portée exacte : la quasi-compensation des séjours internes ÉQUIVAUT, à une unité près, à la quasi-égalité des
occupations des deux états, c'est-à-dire, sur les premiers, à l'équirépartition entre les classes 1 et 5 mod 6.
L'équirépartition ASYMPTOTIQUE (Dirichlet) n'est PAS démontrée ici, et une borne uniforme sur `N1• − N5•` est
fausse en général (biais de Chebyshev) : rien n'est supposé.  Ce fichier est une identité de comptage, pas une
loi sur les zéros.
-/

namespace RHV6Fresh

open Finset

/-- Séjours internes en état 1 : indices `i < n` avec `s i = s (i+1) = 1`. -/
def N11 (n : ℕ) (s : ℕ → Bool) : ℕ :=
  ((range n).filter (fun i => s i = true ∧ s (i + 1) = true)).card

/-- Séjours internes en état 5. -/
def N55 (n : ℕ) (s : ℕ → Bool) : ℕ :=
  ((range n).filter (fun i => s i = false ∧ s (i + 1) = false)).card

/-- Transitions 1 → 5. -/
def N15 (n : ℕ) (s : ℕ → Bool) : ℕ :=
  ((range n).filter (fun i => s i = true ∧ s (i + 1) = false)).card

/-- Transitions 5 → 1. -/
def N51 (n : ℕ) (s : ℕ → Bool) : ℕ :=
  ((range n).filter (fun i => s i = false ∧ s (i + 1) = true)).card

/-- Occupation de l'état 1 : nombre d'indices de départ `i < n` en état 1. -/
def occ1 (n : ℕ) (s : ℕ → Bool) : ℕ := ((range n).filter (fun i => s i = true)).card

/-- Occupation de l'état 5. -/
def occ5 (n : ℕ) (s : ℕ → Bool) : ℕ := ((range n).filter (fun i => s i = false)).card

/-- Indicatrice de l'état 1. -/
def ind1 (b : Bool) : ℤ := if b = true then 1 else 0

/-- **Télescopage de l'orientation** : `N15 − N51 = 1[s 0 = 1] − 1[s n = 1]`. -/
theorem orientation_telescopes (n : ℕ) (s : ℕ → Bool) :
    (N15 n s : ℤ) - N51 n s = ind1 (s 0) - ind1 (s n) := by
  induction n with
  | zero => simp [N15, N51, ind1]
  | succ n ih =>
    unfold N15 N51 at *
    rw [range_add_one, filter_insert, filter_insert]
    cases h1 : s n <;> cases h2 : s (n + 1) <;> simp [ind1, h1, h2] at ih ⊢ <;> omega

/-- **Corollaire** : `|N15 − N51| ≤ 1`. -/
theorem orientation_abs_le_one (n : ℕ) (s : ℕ → Bool) :
    |(N15 n s : ℤ) - N51 n s| ≤ 1 := by
  rw [orientation_telescopes]
  unfold ind1
  split_ifs <;> simp

/-- **`N1• = N11 + N15`** : tout départ en état 1 aboutit en 1 ou en 5. -/
theorem occ1_eq (n : ℕ) (s : ℕ → Bool) : occ1 n s = N11 n s + N15 n s := by
  induction n with
  | zero => simp [occ1, N11, N15]
  | succ n ih =>
    unfold occ1 N11 N15 at *
    rw [range_add_one, filter_insert, filter_insert, filter_insert]
    cases h1 : s n <;> cases h2 : s (n + 1) <;> simp [h1, h2] at ih ⊢ <;> omega

/-- **`N5• = N55 + N51`**. -/
theorem occ5_eq (n : ℕ) (s : ℕ → Bool) : occ5 n s = N55 n s + N51 n s := by
  induction n with
  | zero => simp [occ5, N55, N51]
  | succ n ih =>
    unfold occ5 N55 N51 at *
    rw [range_add_one, filter_insert, filter_insert, filter_insert]
    cases h1 : s n <;> cases h2 : s (n + 1) <;> simp [h1, h2] at ih ⊢ <;> omega

/-- **Décomposition des séjours** : `N11 = N1• − N15` (dans `ℤ`). -/
theorem n11_eq (n : ℕ) (s : ℕ → Bool) : (N11 n s : ℤ) = occ1 n s - N15 n s := by
  have := occ1_eq n s; omega

/-- **Décomposition des séjours** : `N55 = N5• − N51` (dans `ℤ`). -/
theorem n55_eq (n : ℕ) (s : ℕ → Bool) : (N55 n s : ℤ) = occ5 n s - N51 n s := by
  have := occ5_eq n s; omega

/-- **Énoncé (A2)** sous la forme demandée : `N11 = #{i<n | s i = 1} − #{i<n | s i = 1 ∧ s (i+1) = 0}`. -/
theorem dwell_decomposition (n : ℕ) (s : ℕ → Bool) :
    (N11 n s : ℤ) = ((range n).filter (fun i => s i = true)).card
      - ((range n).filter (fun i => s i = true ∧ s (i + 1) = false)).card :=
  n11_eq n s

/-- **Solde des séjours = solde d'occupation − solde d'orientation** :
`D = N11 − N55 = (N1• − N5•) − (N15 − N51)`. -/
theorem dwell_balance_eq_occupancy_minus_orientation (n : ℕ) (s : ℕ → Bool) :
    (N11 n s : ℤ) - N55 n s = ((occ1 n s : ℤ) - occ5 n s) - ((N15 n s : ℤ) - N51 n s) := by
  rw [n11_eq, n55_eq]; ring

/-- **Quasi-compensation des séjours ⟺ quasi-égalité des occupations** :
`|D − (N1• − N5•)| ≤ 1`. -/
theorem dwell_balance_iff_occupancy (n : ℕ) (s : ℕ → Bool) :
    |((N11 n s : ℤ) - N55 n s) - ((occ1 n s : ℤ) - occ5 n s)| ≤ 1 := by
  rw [dwell_balance_eq_occupancy_minus_orientation]
  have := orientation_abs_le_one n s
  have e : ((occ1 n s : ℤ) - occ5 n s - ((N15 n s : ℤ) - N51 n s)) - ((occ1 n s : ℤ) - occ5 n s)
      = -((N15 n s : ℤ) - N51 n s) := by ring
  rw [e, abs_neg]; exact this

/-- Forme à `ε` : `|D| ≤ ε + 1` dès que `|N1• − N5•| ≤ ε`, et réciproquement. -/
theorem dwell_abs_le_of_occupancy (n : ℕ) (s : ℕ → Bool) (ε : ℤ)
    (h : |(occ1 n s : ℤ) - occ5 n s| ≤ ε) : |(N11 n s : ℤ) - N55 n s| ≤ ε + 1 := by
  have h1 := dwell_balance_iff_occupancy n s
  rw [abs_le] at *; omega

theorem occupancy_abs_le_of_dwell (n : ℕ) (s : ℕ → Bool) (ε : ℤ)
    (h : |(N11 n s : ℤ) - N55 n s| ≤ ε) : |(occ1 n s : ℤ) - occ5 n s| ≤ ε + 1 := by
  have h1 := dwell_balance_iff_occupancy n s
  rw [abs_le] at *; omega

/-! ## Canaux pondérés

Pour tout système de poids, la double stabilité grammaticale transportée dans des poids se réduit à : un canal orienté
borné par la variation totale des poids (une somme d'Abel) et un canal de caractère modulo 3 ; aucune des deux
quantités ne lit la position radiale autrement qu'à travers les poids eux-mêmes.

Le poids `w i` est la contribution (non spécifiée ici) d'un zéro à l'événement premier `i` ; ce sont des identités de
sommes finies, valables pour tout `w : ℕ → ℝ`.  Aucune borne sur les poids n'est supposée. -/

/-- Canal pondéré des séjours internes en état 1. -/
noncomputable def G11 (n : ℕ) (s : ℕ → Bool) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ (range n).filter (fun i => s i = true ∧ s (i + 1) = true), w i

/-- Canal pondéré des séjours internes en état 5. -/
noncomputable def G55 (n : ℕ) (s : ℕ → Bool) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ (range n).filter (fun i => s i = false ∧ s (i + 1) = false), w i

/-- Canal pondéré des transitions 1 → 5. -/
noncomputable def G15 (n : ℕ) (s : ℕ → Bool) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ (range n).filter (fun i => s i = true ∧ s (i + 1) = false), w i

/-- Canal pondéré des transitions 5 → 1. -/
noncomputable def G51 (n : ℕ) (s : ℕ → Bool) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ (range n).filter (fun i => s i = false ∧ s (i + 1) = true), w i

/-- Masse pondérée des départs en état 1. -/
noncomputable def W1 (n : ℕ) (s : ℕ → Bool) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ (range n).filter (fun i => s i = true), w i

/-- Masse pondérée des départs en état 5. -/
noncomputable def W5 (n : ℕ) (s : ℕ → Bool) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ (range n).filter (fun i => s i = false), w i

/-- Signe de l'état : `+1` en état 1, `−1` en état 5. -/
def sgn (b : Bool) : ℝ := if b = true then 1 else -1

/-- **(W1)** `W1 = G11 + G15`. -/
theorem weighted_occ1_eq (n : ℕ) (s : ℕ → Bool) (w : ℕ → ℝ) :
    W1 n s w = G11 n s w + G15 n s w := by
  induction n with
  | zero => simp [W1, G11, G15]
  | succ n ih =>
    unfold W1 G11 G15 at *
    rw [range_add_one, filter_insert, filter_insert, filter_insert]
    cases h1 : s n <;> cases h2 : s (n + 1) <;> simp [h1, h2] at ih ⊢ <;> linarith

/-- **(W1)** `W5 = G55 + G51`. -/
theorem weighted_occ5_eq (n : ℕ) (s : ℕ → Bool) (w : ℕ → ℝ) :
    W5 n s w = G55 n s w + G51 n s w := by
  induction n with
  | zero => simp [W5, G55, G51]
  | succ n ih =>
    unfold W5 G55 G51 at *
    rw [range_add_one, filter_insert, filter_insert, filter_insert]
    cases h1 : s n <;> cases h2 : s (n + 1) <;> simp [h1, h2] at ih ⊢ <;> linarith

/-- **(W2)** Identité exacte pour tout poids : `G11 − G55 = (W1 − W5) − (G15 − G51)`. -/
theorem weighted_dwell_balance (n : ℕ) (s : ℕ → Bool) (w : ℕ → ℝ) :
    G11 n s w - G55 n s w = (W1 n s w - W5 n s w) - (G15 n s w - G51 n s w) := by
  rw [weighted_occ1_eq, weighted_occ5_eq]; ring

/-- **(W3)** Canal de caractère : `W1 − W5 = Σ_{i<n} σ_i · w_i`. -/
theorem weighted_character_channel (n : ℕ) (s : ℕ → Bool) (w : ℕ → ℝ) :
    W1 n s w - W5 n s w = ∑ i ∈ range n, (if s i then (1 : ℝ) else -1) * w i := by
  induction n with
  | zero => simp [W1, W5]
  | succ n ih =>
    unfold W1 W5 at *
    rw [sum_range_succ, ← ih, range_add_one, filter_insert, filter_insert]
    cases h1 : s n <;> simp [h1] <;> ring

/-- **(W4)** Forme d'Abel du canal orienté :
`G15 − G51 = Σ_{i<n} ((σ i − σ (i+1))/2) · w i`, avec `σ i = if s i then 1 else −1`
(même membre droit que `weighted_orientation_identity` du TDD G4, pour `σ = fun i => sgn (s i)`). -/
theorem weighted_orientation_eq_abel (n : ℕ) (s : ℕ → Bool) (w : ℕ → ℝ) :
    G15 n s w - G51 n s w =
      ∑ i ∈ range n, (((if s i then (1 : ℝ) else -1) - (if s (i + 1) then (1 : ℝ) else -1)) / 2) * w i := by
  induction n with
  | zero => simp [G15, G51]
  | succ n ih =>
    unfold G15 G51 at *
    rw [sum_range_succ, ← ih, range_add_one, filter_insert, filter_insert]
    cases h1 : s n <;> cases h2 : s (n + 1) <;> simp [h1, h2] <;> ring

namespace G4
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

end G4

/-- **(W5)** `|G15 − G51| ≤ (|w 0| + |w (n−1)| + Σ_{i<n−1} |w (i+1) − w i|)/2`
(variation totale des poids ; somme d'Abel, aucune hypothèse sur `w`). -/
theorem weighted_orientation_abs_le (n : ℕ) (s : ℕ → Bool) (w : ℕ → ℝ) :
    |G15 n s w - G51 n s w| ≤
      (|w 0| + |w (n - 1)| + ∑ i ∈ range (n - 1), |w (i + 1) - w i|) / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [G15, G51]
  · rw [weighted_orientation_eq_abel]
    have hs : ∀ i, |(fun i => if s i then (1 : ℝ) else -1) i| = 1 := by
      intro i; by_cases h : s i = true <;> simp [h]
    exact G4.weighted_orientation_variation_bound hn (fun i => if s i then (1 : ℝ) else -1) w hs
      ((|w 0| + |w (n - 1)| + ∑ i ∈ range (n - 1), |w (i + 1) - w i|) / 2)
      (by linarith)

end RHV6Fresh

#print axioms RHV6Fresh.orientation_telescopes
#print axioms RHV6Fresh.orientation_abs_le_one
#print axioms RHV6Fresh.occ1_eq
#print axioms RHV6Fresh.occ5_eq
#print axioms RHV6Fresh.dwell_decomposition
#print axioms RHV6Fresh.dwell_balance_eq_occupancy_minus_orientation
#print axioms RHV6Fresh.dwell_balance_iff_occupancy
#print axioms RHV6Fresh.dwell_abs_le_of_occupancy
#print axioms RHV6Fresh.occupancy_abs_le_of_dwell
#print axioms RHV6Fresh.weighted_occ1_eq
#print axioms RHV6Fresh.weighted_occ5_eq
#print axioms RHV6Fresh.weighted_dwell_balance
#print axioms RHV6Fresh.weighted_character_channel
#print axioms RHV6Fresh.weighted_orientation_eq_abel
#print axioms RHV6Fresh.G4.weighted_orientation_identity
#print axioms RHV6Fresh.G4.weighted_orientation_variation_bound
#print axioms RHV6Fresh.weighted_orientation_abs_le
