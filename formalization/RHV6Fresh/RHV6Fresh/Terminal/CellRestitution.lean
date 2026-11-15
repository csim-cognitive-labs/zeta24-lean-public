/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ChangePredictor
import RHV6Fresh.Terminal.CanonicalTransition
import RHV6Fresh.Terminal.RegimeWindow
import RHV6Fresh.Direct.PivotCell

/-!
# Restitution arithmétique des cellules et des passages (auteur, 2026-10-12 ; E202)

Campagne de tests sur la restitution des cellules et des passages (`experiments/e202_cell_passage_restitution.py`). Ce module
démontre les identités et contraintes FINIES que la campagne a isolées, sur les objets authentiques, sans hypothèse nouvelle.

1. **Appartenance aux cellules sous translation radiale.** Pour un membre au plus en ligne, l'indice de cellule (règle du pivot,
   `C_k < q ≤ C_{k+1}`) de tout réel est l'indice de ligne ou l'indice de ligne moins un (`arrival_cell_shift`), et il est
   inchangé exactement quand le décalage `−D/π` reste sous la position du réel dans sa cellule de ligne
   (`arrival_cell_unchanged_iff`). Forme paramétrique : sur toute famille FINIE de réels, une translation assez petite sous la
   ligne ne change aucun indice (`small_translation_cells_blind`) : l'appartenance aux cellules est un détecteur À SEUIL.
2. **Charge arithmétique d'une cellule** `Σ_{a<n≤b} Λ(n)` : additive (`cellCharge_add`) ; sous une translation des deux bords,
   la variation est la charge des deux portions déplacées (`cellCharge_translate`) ; nulle sur une portion sans puissance
   première (`cellCharge_eq_zero_of_no_primePow`). Elle ne lit aucun zéro.
3. **Paire contre simple, paire contre double.** La paire miroir `1/2 ± d` tend vers le DOUBLE en ligne quand `d → 0`
   (`pair_tendsto_double`) ; sa différence avec un point SIMPLE en ligne tend vers ce terme, non nul
   (`pair_sub_simple_tendsto`, `onTerm_ne_zero`) : une première rupture depuis un point simple n'est pas une petite
   déformation de la restitution (saut d'ordre zéro), depuis un double elle l'est (ordre deux, `mirrorPairTerm_even`).

Portée : ces énoncés valent pour toute position radiale de l'arrivée ; aucun ne fixe le facteur radial. Aucun `sorry`, aucun
`admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean Filter Topology
open scoped ArithmeticFunction

/-! ## 1. Appartenance aux cellules sous translation radiale -/

/-- Un décalage vers le bas d'au plus un tour change le plafond d'au plus une unité. -/
theorem ceil_sub_shift_cases {P δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ⌈P - δ⌉ = ⌈P⌉ ∨ ⌈P - δ⌉ = ⌈P⌉ - 1 := by
  have h1 : ⌈P - δ⌉ ≤ ⌈P⌉ := Int.ceil_le_ceil (by linarith)
  have h2 : ⌈P⌉ - 1 ≤ ⌈P - δ⌉ := by
    rw [Int.le_ceil_iff]
    push_cast
    have := Int.ceil_lt_add_one P
    linarith
  omega

/-- Le plafond est inchangé par un décalage vers le bas exactement quand le réel décalé reste au-dessus de la borne
inférieure de sa cellule. -/
theorem ceil_sub_shift_eq_iff {P δ : ℝ} (hδ0 : 0 ≤ δ) :
    ⌈P - δ⌉ = ⌈P⌉ ↔ ((⌈P⌉ : ℤ) : ℝ) - 1 < P - δ := by
  constructor
  · intro h
    have := Int.ceil_lt_add_one (P - δ)
    rw [h] at this
    linarith
  · intro h
    rw [Int.ceil_eq_iff]
    exact ⟨h, by have := Int.le_ceil P; linarith⟩

/-- Pour un membre au plus en ligne, le résidu de changement est dans `]−π/2, 0]`. -/
theorem changeResidue_mem_of_le_half (z : TrueZero) (hβ : rZeroRadialPosition z.1 ≤ 1 / 2) :
    -(Real.pi / 2) < changeResidue z.1 ∧ changeResidue z.1 ≤ 0 := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hβ0 := thm_zeroRadialPosition_positive z.1
  refine ⟨?_, ?_⟩
  · unfold changeResidue changeResidueAt linePhase
    have h1 := Real.arctan_lt_pi_div_two (rZeroHeight z.1 / rZeroRadialPosition z.1)
    have h2 : 0 < Real.arctan (rZeroHeight z.1 / (1 / 2)) := Real.arctan_pos.mpr (by positivity)
    linarith
  · rcases lt_or_eq_of_le hβ with h | h
    · exact le_of_lt ((changeResidueAt_neg_iff hβ0 hT).mpr h)
    · exact le_of_eq ((changeResidue_eq_zero_iff z.1).mpr h)

/-- **L'indice de cellule de tout réel dans la Tour d'un membre au plus en ligne est l'indice de ligne ou l'indice de ligne
moins un.** -/
theorem arrival_cell_shift (z : TrueZero) (hβ : rZeroRadialPosition z.1 ≤ 1 / 2) (q : ℝ) :
    pivotCoordinate z q = ⌈linePosition (rZeroHeight z.1) q⌉ - 1 ∨
      pivotCoordinate z q = ⌈linePosition (rZeroHeight z.1) q⌉ - 2 := by
  obtain ⟨hlo, hhi⟩ := changeResidue_mem_of_le_half z hβ
  have hπ := Real.pi_pos
  have e : towerPosition z q = linePosition (rZeroHeight z.1) q - (-(changeResidue z.1) / Real.pi) := by
    rw [towerPosition_eq_line_add_residue]; ring
  have hδ0 : 0 ≤ -(changeResidue z.1) / Real.pi := div_nonneg (by linarith) hπ.le
  have hδ1 : -(changeResidue z.1) / Real.pi < 1 := by rw [div_lt_one hπ]; linarith
  unfold pivotCoordinate
  rw [e]
  rcases ceil_sub_shift_cases (P := linePosition (rZeroHeight z.1) q) hδ0 hδ1 with h | h
  · left; rw [h]
  · right; rw [h]; ring

/-- **Seuil exact** : l'indice de cellule d'un réel dans la Tour d'un membre au plus en ligne est l'indice de ligne si et
seulement si le décalage `−D/π` est strictement sous la position de ce réel dans sa cellule de ligne. -/
theorem arrival_cell_unchanged_iff (z : TrueZero) (hβ : rZeroRadialPosition z.1 ≤ 1 / 2) (q : ℝ) :
    pivotCoordinate z q = ⌈linePosition (rZeroHeight z.1) q⌉ - 1 ↔
      -(changeResidue z.1) / Real.pi <
        linePosition (rZeroHeight z.1) q - (((⌈linePosition (rZeroHeight z.1) q⌉ : ℤ) : ℝ) - 1) := by
  obtain ⟨_, hhi⟩ := changeResidue_mem_of_le_half z hβ
  have hπ := Real.pi_pos
  have e : towerPosition z q = linePosition (rZeroHeight z.1) q - (-(changeResidue z.1) / Real.pi) := by
    rw [towerPosition_eq_line_add_residue]; ring
  have hδ0 : 0 ≤ -(changeResidue z.1) / Real.pi := div_nonneg (by linarith) hπ.le
  unfold pivotCoordinate
  rw [e, sub_left_inj, ceil_sub_shift_eq_iff hδ0]
  constructor <;> intro h <;> linarith

/-- Indice de cellule paramétrique d'un réel `q` dans la Tour de paramètres `(β, T)` (règle du pivot). -/
noncomputable def cellIndexAt (β T q : ℝ) : ℤ :=
  ⌈(T * Real.log q - Real.arctan (T / β)) / Real.pi⌉ - 1

/-- Le décalage de phase d'un paramètre `β ≤ 1/2` par rapport à la ligne est positif. -/
theorem arctan_shift_nonneg {β T : ℝ} (hβ : 0 < β) (hβ2 : β ≤ 1 / 2) (hT : 0 ≤ T) :
    0 ≤ Real.arctan (T / β) - Real.arctan (T / (1 / 2)) := by
  rw [sub_nonneg]
  exact Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left hT hβ hβ2)

/-- **Détecteur à seuil.** Sur toute famille finie de réels, une translation radiale assez petite sous la ligne ne change
l'indice de cellule d'aucun d'eux. -/
theorem small_translation_cells_blind (T : ℝ) (hT : 0 ≤ T) (Q : Finset ℝ) :
    ∀ᶠ β in 𝓝 (1 / 2 : ℝ), β ≤ 1 / 2 → ∀ q ∈ Q, cellIndexAt β T q = cellIndexAt (1 / 2) T q := by
  have hπ := Real.pi_pos
  have hcont : ContinuousAt (fun β : ℝ => Real.arctan (T / β)) (1 / 2) :=
    (Real.continuous_arctan.continuousAt).comp (continuousAt_const.div continuousAt_id (by norm_num))
  have hpos : ∀ᶠ β in 𝓝 (1 / 2 : ℝ), 0 < β := eventually_gt_nhds (by norm_num)
  have hq : ∀ q ∈ Q, ∀ᶠ β in 𝓝 (1 / 2 : ℝ),
      Real.arctan (T / β) - Real.arctan (T / (1 / 2)) <
        Real.pi * ((T * Real.log q - Real.arctan (T / (1 / 2))) / Real.pi -
          (((⌈(T * Real.log q - Real.arctan (T / (1 / 2))) / Real.pi⌉ : ℤ) : ℝ) - 1)) := by
    intro q _
    set P := (T * Real.log q - Real.arctan (T / (1 / 2))) / Real.pi
    have hgap : 0 < Real.pi * (P - (((⌈P⌉ : ℤ) : ℝ) - 1)) := by
      have := Int.ceil_lt_add_one P
      exact mul_pos hπ (by linarith)
    have hc : ContinuousAt (fun β : ℝ => Real.arctan (T / β) - Real.arctan (T / (1 / 2))) (1 / 2) :=
      hcont.sub continuousAt_const
    have h0 : (fun β : ℝ => Real.arctan (T / β) - Real.arctan (T / (1 / 2))) (1 / 2) = 0 := sub_self _
    exact hc.eventually (gt_mem_nhds (by rw [h0]; exact hgap))
  have hall := (Filter.eventually_all_finset Q).mpr hq
  filter_upwards [hall, hpos] with β hβQ hβ0 hβ2 q hqQ
  have hs := arctan_shift_nonneg hβ0 hβ2 hT
  set P := (T * Real.log q - Real.arctan (T / (1 / 2))) / Real.pi
  have hδ0 : 0 ≤ (Real.arctan (T / β) - Real.arctan (T / (1 / 2))) / Real.pi := div_nonneg hs hπ.le
  have e : (T * Real.log q - Real.arctan (T / β)) / Real.pi =
      P - (Real.arctan (T / β) - Real.arctan (T / (1 / 2))) / Real.pi := by
    simp only [P]; field_simp; ring
  unfold cellIndexAt
  rw [e, sub_left_inj, ceil_sub_shift_eq_iff hδ0]
  have h : Real.arctan (T / β) - Real.arctan (T / (1 / 2)) < Real.pi * (P - (((⌈P⌉ : ℤ) : ℝ) - 1)) := hβQ q hqQ
  have : (Real.arctan (T / β) - Real.arctan (T / (1 / 2))) / Real.pi < P - (((⌈P⌉ : ℤ) : ℝ) - 1) := by
    rw [div_lt_iff₀ hπ]; linarith
  linarith

/-! ## 2. Charge arithmétique d'une cellule -/

/-- **Charge arithmétique exacte** de la cellule `]a, b]` : `Σ_{a<n≤b} Λ(n)` (canal pondéré, côté premier). -/
noncomputable def cellCharge (a b : ℝ) : ℝ := ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, Λ n

theorem cellCharge_nonneg (a b : ℝ) : 0 ≤ cellCharge a b :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- **Additivité** : deux cellules contiguës. -/
theorem cellCharge_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    cellCharge a c = cellCharge a b + cellCharge b c := by
  unfold cellCharge
  rw [Finset.sum_Ioc_consecutive _ (Nat.floor_mono hab) (Nat.floor_mono hbc)]

/-- **Translation des bords** : la variation de charge est la charge des deux portions déplacées. -/
theorem cellCharge_translate {a a' b b' : ℝ} (h1 : a ≤ a') (h2 : a' ≤ b) (h3 : b ≤ b') :
    cellCharge a' b' = cellCharge a b - cellCharge a a' + cellCharge b b' := by
  have e1 := cellCharge_add h1 (h2.trans h3)
  have e2 := cellCharge_add (h1.trans h2) h3
  have e3 := cellCharge_add h2 h3
  have e4 := cellCharge_add h1 h2
  linarith

/-- Une portion sans puissance première a une charge nulle. -/
theorem cellCharge_eq_zero_of_no_primePow {a b : ℝ}
    (h : ∀ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ¬ IsPrimePow n) : cellCharge a b = 0 :=
  Finset.sum_eq_zero fun n hn => ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (h n hn)

/-! ## 3. Paire miroir contre point simple, contre double -/

theorem mirrorPoint_ne_zero {T : ℝ} (hT : T ≠ 0) (d : ℝ) : mirrorPoint T d ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [mirrorPoint] at this
  exact hT this

/-- Le terme d'un point en ligne simple à la hauteur `T ≠ 0`, en `q > 0`, n'est pas nul. -/
theorem onTerm_ne_zero {q T : ℝ} (hq : 0 < q) (hT : T ≠ 0) :
    (q : ℂ) ^ mirrorPoint T 0 / mirrorPoint T 0 ≠ 0 :=
  div_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => absurd (Complex.ofReal_eq_zero.mp h.1) hq.ne')
    (mirrorPoint_ne_zero hT 0)

theorem continuous_mirrorPoint (T : ℝ) : Continuous (fun d : ℝ => mirrorPoint T d) := by
  unfold mirrorPoint
  fun_prop

theorem continuousAt_mirrorTerm {q T : ℝ} (hq : 0 < q) (hT : T ≠ 0) (d₀ : ℝ) :
    ContinuousAt (fun d : ℝ => (q : ℂ) ^ mirrorPoint T d / mirrorPoint T d) d₀ := by
  have hq' : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  exact ((continuous_mirrorPoint T).const_cpow (Or.inl hq')).continuousAt.div
    (continuous_mirrorPoint T).continuousAt (mirrorPoint_ne_zero hT d₀)

theorem continuousAt_mirrorPairTerm {q T : ℝ} (hq : 0 < q) (hT : T ≠ 0) :
    ContinuousAt (fun d : ℝ => mirrorPairTerm q T d) 0 := by
  unfold mirrorPairTerm
  have h1 := continuousAt_mirrorTerm hq hT 0
  have h2 : ContinuousAt (fun d : ℝ => (q : ℂ) ^ mirrorPoint T (-d) / mirrorPoint T (-d)) 0 := by
    have := continuousAt_mirrorTerm hq hT (-(0 : ℝ))
    exact this.comp (continuousAt_neg)
  exact h1.add h2

theorem mirrorPairTerm_zero (q T : ℝ) :
    mirrorPairTerm q T 0 = 2 * ((q : ℂ) ^ mirrorPoint T 0 / mirrorPoint T 0) := by
  unfold mirrorPairTerm; rw [neg_zero]; ring

/-- **Paire contre double** : la paire miroir tend vers le double en ligne (déformation continue ; ordre deux par parité). -/
theorem pair_tendsto_double {q T : ℝ} (hq : 0 < q) (hT : T ≠ 0) :
    Tendsto (fun d : ℝ => mirrorPairTerm q T d) (𝓝 0)
      (𝓝 (2 * ((q : ℂ) ^ mirrorPoint T 0 / mirrorPoint T 0))) := by
  rw [← mirrorPairTerm_zero]
  exact continuousAt_mirrorPairTerm hq hT

/-- **Paire contre simple** : la différence entre la paire miroir et un point simple en ligne tend vers le terme de ce point,
non nul (`onTerm_ne_zero`) : saut d'ordre zéro de la restitution. -/
theorem pair_sub_simple_tendsto {q T : ℝ} (hq : 0 < q) (hT : T ≠ 0) :
    Tendsto (fun d : ℝ => mirrorPairTerm q T d - (q : ℂ) ^ mirrorPoint T 0 / mirrorPoint T 0) (𝓝 0)
      (𝓝 ((q : ℂ) ^ mirrorPoint T 0 / mirrorPoint T 0)) := by
  have h := (pair_tendsto_double hq hT).sub
    (tendsto_const_nhds (x := (q : ℂ) ^ mirrorPoint T 0 / mirrorPoint T 0))
  convert h using 2
  ring

/-! ## 4. Composition au passage -/

/-- **Restitution au passage, portée** : pour l'arrivée `l` d'un passage (au plus en ligne), (i) tout réel change de cellule
d'au plus un rang vers le bas, au seuil exact `−D/π` ; (ii) la charge arithmétique des cellules ne lit aucun zéro et sa
variation sous translation est celle des bords ; (iii) en tout `q > 0`, la paire miroir à la hauteur d'arrivée tend vers le
double en ligne et s'écarte d'un point simple d'un terme non nul. Vrai pour toute position radiale `≤ 1/2` : aucun facteur
radial n'est fixé. -/
theorem passage_restitution_scope (l : TrueZero) (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) :
    (∀ q : ℝ, (pivotCoordinate l q = ⌈linePosition (rZeroHeight l.1) q⌉ - 1 ∨
        pivotCoordinate l q = ⌈linePosition (rZeroHeight l.1) q⌉ - 2) ∧
      (pivotCoordinate l q = ⌈linePosition (rZeroHeight l.1) q⌉ - 1 ↔
        -(changeResidue l.1) / Real.pi <
          linePosition (rZeroHeight l.1) q - (((⌈linePosition (rZeroHeight l.1) q⌉ : ℤ) : ℝ) - 1))) ∧
    (∀ a a' b b' : ℝ, a ≤ a' → a' ≤ b → b ≤ b' →
      cellCharge a' b' = cellCharge a b - cellCharge a a' + cellCharge b b') ∧
    (∀ Q : Finset ℝ, ∀ᶠ β in 𝓝 (1 / 2 : ℝ), β ≤ 1 / 2 → ∀ q ∈ Q,
      cellIndexAt β (rZeroHeight l.1) q = cellIndexAt (1 / 2) (rZeroHeight l.1) q) ∧
    (∀ q : ℝ, 0 < q →
      Tendsto (fun d : ℝ => mirrorPairTerm q (rZeroHeight l.1) d) (𝓝 0)
        (𝓝 (2 * ((q : ℂ) ^ mirrorPoint (rZeroHeight l.1) 0 / mirrorPoint (rZeroHeight l.1) 0))) ∧
      Tendsto (fun d : ℝ => mirrorPairTerm q (rZeroHeight l.1) d -
          (q : ℂ) ^ mirrorPoint (rZeroHeight l.1) 0 / mirrorPoint (rZeroHeight l.1) 0) (𝓝 0)
        (𝓝 ((q : ℂ) ^ mirrorPoint (rZeroHeight l.1) 0 / mirrorPoint (rZeroHeight l.1) 0)) ∧
      (q : ℂ) ^ mirrorPoint (rZeroHeight l.1) 0 / mirrorPoint (rZeroHeight l.1) 0 ≠ 0) := by
  have hT : 0 < rZeroHeight l.1 := l.2
  refine ⟨fun q => ⟨arrival_cell_shift l hβ q, arrival_cell_unchanged_iff l hβ q⟩,
    fun a a' b b' h1 h2 h3 => cellCharge_translate h1 h2 h3,
    fun Q => small_translation_cells_blind _ hT.le Q, fun q hq => ⟨pair_tendsto_double hq hT.ne',
      pair_sub_simple_tendsto hq hT.ne', onTerm_ne_zero hq hT.ne'⟩⟩

end RHV6Fresh

#print axioms RHV6Fresh.passage_restitution_scope
