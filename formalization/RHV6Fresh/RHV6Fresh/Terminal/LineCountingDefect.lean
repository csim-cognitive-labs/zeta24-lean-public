/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.BoxCountHeight
import RHV6Fresh.Terminal.RegimeTrigger
import RHV6Fresh.Terminal.DiagonalPassage
import RHV6Fresh.Terminal.ArrivalFiberHypotheses

/-!
# Défaut de comptage sur la ligne entre deux hauteurs (auteur, 2026-10-12)

Objectif analytique unique : entre la hauteur du départ et celle de l'arrivée, le comptage supplémentaire des zéros est-il
entièrement porté par les annulations sur la ligne critique ? Multiplicités conservées ; la simplicité n'est pas exigée.

1. Accroissements entiers `ΔN = N(U) − N(T)` (`totalIncrement`), `ΔN₀ = N₀(U) − N₀(T)` (`lineIncrement`) et défaut
   `δ(T, U) = ΔN − ΔN₀` (`lineDefect`). Démontré : `δ = 2(W(U) − W(T))` (réflexion), pair, `≥ 0` pour `T ≤ U`, `≥ 2` dès
   qu'un membre bas apparaît au-dessus d'un historique sans membre bas.
2. Fermeture conditionnelle : `W(T) = 0` et `δ(T, U) = 0` ⟹ tout membre de hauteur `≤ U` est ON, facteur radial un.
3. Lecture des rectangles certifiés (15, 22, 28) : ils obtiennent `N` par le principe de l'argument sur `ξ₁`, et le rectangle
   de droite `[1 − σ₀, 2]` (fixe, `σ₀ < 1/2`) n'exclut que `Re ≥ 1 − σ₀` ; la confrontation à la ligne y est faite par la seule
   PARITÉ (`N = N₀ + 2W`) : un accroissement total `< 2` annule le défaut (`lineDefect_zero_of_total_lt_two`). Lemme réutilisable
   nouveau : un rectangle d'enroulement nul ne contient aucun zéro (`boxZeros_empty_of_integral_zero`) ; rectangles de droite
   d'abscisse arbitrairement proche de `1/2` ⟹ défaut nul (`lineDefect_zero_of_right_boxes`).
4. Lecture sur la ligne : `k` changements de signe ordonnés de la fonction réelle `lineValue` dans `[T, U]` donnent
   `ΔN₀ ≥ k` (`lineIncrement_ge_of_sign_changes`), donc `δ ≤ ΔN − k`, et `ΔN ≤ k` ⟹ `δ = 0` (critère de Turing local,
   `lineDefect_zero_of_total_le_sign_changes`). Portée : suffisant, non nécessaire (un zéro ON de multiplicité paire ne
   change pas de signe).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau. Rien ici ne démontre l'annulation du défaut sur un passage
quelconque : c'est le raccord ouvert.
-/

namespace RHV6Fresh

open RHV3Lean Complex Set Finset

/-! ## 1. Accroissements et défaut -/

/-- Accroissement total du comptage avec multiplicité, en entiers : `N(U) − N(T)`. -/
noncomputable def totalIncrement (T U : ℝ) : ℤ :=
  (upperCountWithMultiplicity U : ℤ) - upperCountWithMultiplicity T

/-- Accroissement du comptage ON avec multiplicité : `N₀(U) − N₀(T)`. -/
noncomputable def lineIncrement (T U : ℝ) : ℤ := (onCount U : ℤ) - onCount T

/-- **Défaut sur la ligne** : part de l'accroissement total qui n'est pas portée par la ligne. -/
noncomputable def lineDefect (T U : ℝ) : ℤ := totalIncrement T U - lineIncrement T U

/-- `δ(T, U) = 2(W(U) − W(T))` (réflexion `ρ ↦ 1 − ρ̄`). -/
theorem lineDefect_eq (T U : ℝ) : lineDefect T U = 2 * ((lowCount U : ℤ) - lowCount T) := by
  unfold lineDefect totalIncrement lineIncrement
  rw [upperCount_eq_on_add_two_low, upperCount_eq_on_add_two_low]; push_cast; ring

/-- Le défaut est la variation du déficit de comptage. -/
theorem lineDefect_eq_deficit_sub (T U : ℝ) : lineDefect T U = zeroCountDeficit U - zeroCountDeficit T := by
  rw [lineDefect_eq, zeroCountDeficit_eq, zeroCountDeficit_eq]; ring

theorem lineDefect_even (T U : ℝ) : 2 ∣ lineDefect T U := ⟨_, lineDefect_eq T U⟩

/-- **Positivité** : `T ≤ U ⟹ δ(T, U) ≥ 0`. -/
theorem lineDefect_nonneg {T U : ℝ} (h : T ≤ U) : 0 ≤ lineDefect T U := by
  rw [lineDefect_eq]; have := lowCount_mono h; omega

theorem lineIncrement_nonneg {T U : ℝ} (h : T ≤ U) : 0 ≤ lineIncrement T U := by
  unfold lineIncrement; have := onCount_mono h; omega

theorem lineIncrement_le_totalIncrement {T U : ℝ} (h : T ≤ U) : lineIncrement T U ≤ totalIncrement T U := by
  have := lineDefect_nonneg h; unfold lineDefect at this; omega

/-- **Première rupture** : historique sans membre bas jusqu'à `T` et membre bas de hauteur `≤ U` ⟹ `δ(T, U) ≥ 2`. -/
theorem two_le_lineDefect_of_rupture {T U : ℝ} (hT : lowCount T = 0) (z : TrueZero) (hz : rZeroHeight z.1 ≤ U)
    (hβ : rZeroRadialPosition z.1 < 1 / 2) : 2 ≤ lineDefect T U := by
  rw [lineDefect_eq, hT]; have := one_le_lowCount_of_low z hz hβ; omega

theorem lowCount_eq_of_lineDefect_zero {T U : ℝ} (h : lineDefect T U = 0) : lowCount U = lowCount T := by
  rw [lineDefect_eq] at h; omega

/-! ## 2. Fermeture conditionnelle -/

/-- `W(T) = 0` et `δ(T, U) = 0` ⟹ tout membre de hauteur `≤ U` est ON. -/
theorem onLine_of_lineDefect_zero {T U : ℝ} (hT : lowCount T = 0) (h : lineDefect T U = 0) :
    ∀ w : TrueZero, rZeroHeight w.1 ≤ U → rZeroRadialPosition w.1 = 1 / 2 := by
  have hU : lowCount U = 0 := by rw [lowCount_eq_of_lineDefect_zero h, hT]
  exact all_onLine_of_lowCount_zero hU

/-- **Défaut nul ⟹ facteur radial un.** -/
theorem radialFactor_one_of_lineDefect_zero {T U : ℝ} (hT : lowCount T = 0) (h : lineDefect T U = 0)
    (z : TrueZero) (hz : rZeroHeight z.1 ≤ U) : radialFactor z = 1 :=
  (radialFactor_eq_one_iff z).mpr (onLine_of_lineDefect_zero hT h z hz)

/-- Caractérisation (non une dérivation) : sous `W(T) = 0`, défaut nul ⟺ tout membre de hauteur `≤ U` est ON. -/
theorem lineDefect_zero_iff_onLine {T U : ℝ} (hT : lowCount T = 0) :
    lineDefect T U = 0 ↔ ∀ w : TrueZero, rZeroHeight w.1 ≤ U → rZeroRadialPosition w.1 = 1 / 2 := by
  refine ⟨onLine_of_lineDefect_zero hT, fun h => ?_⟩
  have hU : lowCount U = 0 := by
    rw [lowCount_eq_zero_iff]; intro w hw hβ; rw [h w hw] at hβ; exact lt_irrefl _ hβ
  rw [lineDefect_eq, hU, hT]; rfl

/-- Forme du passage : sur un passage qui monte, sous `W(T_e) = 0`, défaut nul ⟹ `λ_l = 1`. -/
theorem passage_radialFactor_of_lineDefect_zero (p : TZeroPassage) (hL : 0 < rZeroHeight p.zLaterMember)
    (hWe : lowCount (rZeroHeight p.zEarlierMember) = 0)
    (h : lineDefect (rZeroHeight p.zEarlierMember) (rZeroHeight p.zLaterMember) = 0) :
    radialFactor ⟨p.zLaterMember, hL⟩ = 1 :=
  radialFactor_one_of_lineDefect_zero hWe h _ le_rfl

/-! ## 3. Lecture des rectangles certifiés -/

/-- **Mécanisme des coupures 15, 22, 28** : la confrontation à la ligne est faite par la parité seule ; un accroissement total
`< 2` au-dessus d'un historique sans membre bas annule le défaut. -/
theorem lineDefect_zero_of_total_lt_two {T U : ℝ} (hTU : T ≤ U) (hT : lowCount T = 0)
    (h : totalIncrement T U < 2) : lineDefect T U = 0 := by
  have hstep : upperCountWithMultiplicity U < upperCountWithMultiplicity T + 2 := by
    unfold totalIncrement at h; omega
  rw [lineDefect_eq, lowCount_eq_zero_of_count_step hTU hT hstep, hT]; rfl

/-- **Lemme analytique réutilisable** : un rectangle sans zéro au bord et d'enroulement nul ne contient aucun zéro de `ξ₁`. -/
theorem boxZeros_empty_of_integral_zero {σa σb ta tb : ℝ} (hre : σa < σb) (him : ta < tb)
    (hB : ∀ s ∈ rectBoundary ((σa : ℂ) + ta * I) ((σb : ℂ) + tb * I), completedEntire s ≠ 0)
    (hI : rectBoundaryIntegral (logDeriv completedEntire) ((σa : ℂ) + ta * I) ((σb : ℂ) + tb * I) = 0) :
    boxZeros σa σb ta tb = ∅ := by
  have hS := box_order_sum hre him hB
  rw [hI, mul_zero] at hS
  have hsum : ∑ ρ ∈ boxZeros σa σb ta tb, analyticOrderNatAt completedEntire ρ = 0 := by exact_mod_cast hS.symm
  rw [Finset.eq_empty_iff_forall_notMem]
  intro ρ hρ
  have h1 := completedEntire_order_pos (mem_boxZeros.mp hρ).1
  have := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hρ (f := fun ρ => analyticOrderNatAt completedEntire ρ)
  rw [hsum] at this; omega

/-- Un rectangle de droite `[σ, 2] × [a, b]` d'enroulement nul exclut tout membre de partie réelle `> σ` et de hauteur
dans `]a, b[`. -/
theorem no_right_member_of_right_box {σ a b : ℝ} (hσ : σ < 2) (hab : a < b)
    (hB : ∀ s ∈ rectBoundary ((σ : ℂ) + a * I) (((2 : ℝ) : ℂ) + b * I), completedEntire s ≠ 0)
    (hI : rectBoundaryIntegral (logDeriv completedEntire) ((σ : ℂ) + a * I) (((2 : ℝ) : ℂ) + b * I) = 0)
    (w : TrueZero) (ha : a < rZeroHeight w.1) (hb : rZeroHeight w.1 < b) (hw : σ < rZeroRadialPosition w.1) :
    False := by
  have hE := boxZeros_empty_of_integral_zero hσ hab hB hI
  have hz : completedEntire (zeroPoint w) = 0 := (completedEntire_eq_zero_iff_nontrivial _).mpr w.1.2
  have hlt1 : (zeroPoint w).re < 1 := w.1.2.2.2
  have hmem : zeroPoint w ∈ boxZeros σ 2 a b :=
    mem_boxZeros.mpr ⟨hz, ⟨hw, by linarith⟩, ⟨ha, hb⟩⟩
  rw [hE] at hmem; exact Finset.notMem_empty _ hmem

/-- **Rectangles de droite arbitrairement proches de la ligne ⟹ défaut nul.** Si, pour tout `σ > 1/2`, un rectangle
`[σ', 2] × [T, b]` (`1/2 < σ' ≤ σ`, `b > U`) est sans zéro au bord et d'enroulement nul, aucun membre bas n'apparaît
dans `]T, U]` (son miroir serait à droite) et `δ(T, U) = 0`. -/
theorem lineDefect_zero_of_right_boxes {T U b : ℝ} (hTU : T ≤ U) (hUb : U < b)
    (hBoxes : ∀ σ : ℝ, 1 / 2 < σ → ∃ σ' : ℝ, 1 / 2 < σ' ∧ σ' ≤ σ ∧
      (∀ s ∈ rectBoundary ((σ' : ℂ) + T * I) (((2 : ℝ) : ℂ) + b * I), completedEntire s ≠ 0) ∧
      rectBoundaryIntegral (logDeriv completedEntire) ((σ' : ℂ) + T * I) (((2 : ℝ) : ℂ) + b * I) = 0) :
    lineDefect T U = 0 := by
  have hle : lowCount U ≤ lowCount T := by
    unfold lowCount
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
    intro ρ hρ
    rw [Finset.mem_filter] at hρ ⊢
    obtain ⟨w, rfl, hwU⟩ := mem_upperWindow_iff.mp hρ.1
    refine ⟨mem_upperWindow_iff.mpr ⟨w, rfl, ?_⟩, hρ.2⟩
    by_contra hwT
    push Not at hwT
    have hβ : rZeroRadialPosition w.1 < 1 / 2 := hρ.2
    set m := mirrorMember w
    have hmβ : rZeroRadialPosition m.1 = 1 - rZeroRadialPosition w.1 := mirrorMember_radial w
    have hmT : rZeroHeight m.1 = rZeroHeight w.1 := mirrorMember_ordinate w
    have hβpos : 0 < rZeroRadialPosition w.1 := thm_zeroRadialPosition_positive w.1
    obtain ⟨σ', h1, h2, hB, hI⟩ := hBoxes ((1 / 2 + (1 - rZeroRadialPosition w.1)) / 2) (by linarith)
    exact no_right_member_of_right_box (by linarith) (by linarith) hB hI m (by rw [hmT]; exact hwT)
      (by rw [hmT]; linarith) (by rw [hmβ]; linarith)
  have hge := lowCount_mono hTU
  rw [lineDefect_eq]; omega

/-! ## 4. Lecture sur la ligne : changements de signe de la fonction réelle -/

/-- **`k` changements de signe ordonnés dans `[T, U]` ⟹ `ΔN₀ ≥ k`** (chaque intervalle porte un zéro ON distinct, de
multiplicité `≥ 1`). -/
theorem lineIncrement_ge_of_sign_changes {T U : ℝ} (hT0 : 0 ≤ T) {k : ℕ} (t : ℕ → ℝ)
    (hmono : ∀ i, i < k → t i < t (i + 1)) (h0 : T ≤ t 0) (hk : t k ≤ U)
    (hsign : ∀ i, i < k → lineValue (t i) * lineValue (t (i + 1)) < 0) :
    (k : ℤ) ≤ lineIncrement T U := by
  have hmon : ∀ j, j ≤ k → ∀ i, i ≤ j → t i ≤ t j := by
    intro j
    induction j with
    | zero => intro _ i hi; rw [Nat.le_zero.mp hi]
    | succ j ih =>
      intro hj i hi
      rcases Nat.lt_or_eq_of_le hi with hlt | heq
      · exact (ih (by omega) i (by omega)).trans (hmono j (by omega)).le
      · rw [heq]
  have hex : ∀ i ∈ Finset.range k, ∃ τ ∈ Ioo (t i) (t (i + 1)), lineValue τ = 0 := by
    intro i hi
    obtain ⟨τ, hτ, hz⟩ := onLine_zero_of_sign_change (hmono i (Finset.mem_range.mp hi))
      (hsign i (Finset.mem_range.mp hi))
    exact ⟨τ, hτ, (onLine_zero_iff_lineValue τ).mp hz⟩
  choose! τ hτ hz using hex
  have hτT : ∀ i ∈ Finset.range k, T < τ i := fun i hi =>
    lt_of_le_of_lt (h0.trans (hmon i (by have := Finset.mem_range.mp hi; omega) 0 (Nat.zero_le _))) (hτ i hi).1
  have hτU : ∀ i ∈ Finset.range k, τ i ≤ U := fun i hi =>
    ((hτ i hi).2.trans_le ((hmon k le_rfl (i + 1) (by have := Finset.mem_range.mp hi; omega)).trans hk)).le
  have hinj : Set.InjOn (fun i => linePoint (τ i)) (Finset.range k : Set ℕ) := by
    intro i hi j hj hij
    have hij' : τ i = τ j := by simpa [linePoint_im] using congrArg Complex.im hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := (hτ i hi).2.trans_le (hmon j (by have := Finset.mem_range.mp hj; omega) (i + 1) hlt)
      linarith [(hτ j hj).1]
    · have := (hτ j hj).2.trans_le (hmon i (by have := Finset.mem_range.mp hi; omega) (j + 1) hlt)
      linarith [(hτ i hi).1]
  set S := (Finset.range k).image fun i => linePoint (τ i)
  have hcard : S.card = k := by rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  set A := (upperWindow T).filter (fun ρ => ρ.re = 1 / 2)
  set B := (upperWindow U).filter (fun ρ => ρ.re = 1 / 2)
  have hSB : S ⊆ B := by
    intro ρ hρ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hρ
    rw [Finset.mem_filter, mem_upperWindow]
    refine ⟨⟨(onLine_zero_iff_lineValue _).mpr (hz i hi), ?_, ?_⟩, linePoint_re _⟩
    · rw [linePoint_im]; linarith [hτT i hi]
    · rw [linePoint_im]; exact hτU i hi
  have hAB : A ⊆ B := by
    intro ρ hρ
    rw [Finset.mem_filter, mem_upperWindow] at hρ ⊢
    exact ⟨⟨hρ.1.1, hρ.1.2.1, hρ.1.2.2.trans (h0.trans ((hmon k le_rfl 0 (Nat.zero_le _)).trans hk))⟩, hρ.2⟩
  have hdisj : Disjoint A S := by
    rw [Finset.disjoint_left]
    intro ρ hρA hρS
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hρS
    rw [Finset.mem_filter, mem_upperWindow, linePoint_im] at hρA
    linarith [hρA.1.2.2, hτT i hi]
  have hsumS : k ≤ ∑ ρ ∈ S, zetaZeroMultiplicity ρ := by
    rw [← hcard, Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    exact one_le_multiplicity_of_mem_upperWindow (Finset.mem_filter.mp (hSB hρ)).1
  have hle : ∑ ρ ∈ A ∪ S, zetaZeroMultiplicity ρ ≤ onCount U :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hAB hSB) fun _ _ _ => Nat.zero_le _
  rw [Finset.sum_union hdisj] at hle
  have hA : ∑ ρ ∈ A, zetaZeroMultiplicity ρ = onCount T := rfl
  unfold lineIncrement
  omega

/-- `δ(T, U) ≤ ΔN − k` dès `k` changements de signe ordonnés dans `[T, U]`. -/
theorem lineDefect_le_of_sign_changes {T U : ℝ} (hT0 : 0 ≤ T) {k : ℕ} (t : ℕ → ℝ)
    (hmono : ∀ i, i < k → t i < t (i + 1)) (h0 : T ≤ t 0) (hk : t k ≤ U)
    (hsign : ∀ i, i < k → lineValue (t i) * lineValue (t (i + 1)) < 0) :
    lineDefect T U ≤ totalIncrement T U - k := by
  have := lineIncrement_ge_of_sign_changes hT0 t hmono h0 hk hsign
  unfold lineDefect; omega

/-- **Critère de Turing local** : si l'accroissement total ne dépasse pas le nombre de changements de signe de la fonction
réelle dans `[T, U]`, tout le comptage supplémentaire est porté par la ligne. Suffisant, non nécessaire. -/
theorem lineDefect_zero_of_total_le_sign_changes {T U : ℝ} (hT0 : 0 ≤ T) (hTU : T ≤ U) {k : ℕ} (t : ℕ → ℝ)
    (hmono : ∀ i, i < k → t i < t (i + 1)) (h0 : T ≤ t 0) (hk : t k ≤ U)
    (hsign : ∀ i, i < k → lineValue (t i) * lineValue (t (i + 1)) < 0)
    (hcount : totalIncrement T U ≤ k) : lineDefect T U = 0 := by
  have h1 := lineDefect_le_of_sign_changes hT0 t hmono h0 hk hsign
  have h2 := lineDefect_nonneg hTU
  omega

/-- **Portée du passage** : réunit défaut pair et positif, défaut `≥ 2` sous la rupture, fermeture par défaut nul,
mécanisme de parité, rectangles de droite, critère de Turing local. -/
theorem passage_line_defect_scope (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hV : VerticalPassage p)
    (hWe : lowCount (rZeroHeight p.zEarlierMember) = 0) :
    let Te := rZeroHeight p.zEarlierMember
    let Tl := rZeroHeight p.zLaterMember
    lineDefect Te Tl = 2 * ((lowCount Tl : ℤ) - lowCount Te) ∧ 2 ∣ lineDefect Te Tl ∧ 0 ≤ lineDefect Te Tl ∧
      (rZeroRadialPosition p.zLaterMember < 1 / 2 → 2 ≤ lineDefect Te Tl) ∧
      (lineDefect Te Tl = 0 → radialFactor ⟨p.zLaterMember, hL⟩ = 1) ∧
      (totalIncrement Te Tl < 2 → lineDefect Te Tl = 0) ∧
      (∀ b : ℝ, Tl < b → (∀ σ : ℝ, 1 / 2 < σ → ∃ σ' : ℝ, 1 / 2 < σ' ∧ σ' ≤ σ ∧
        (∀ s ∈ rectBoundary ((σ' : ℂ) + Te * I) (((2 : ℝ) : ℂ) + b * I), completedEntire s ≠ 0) ∧
        rectBoundaryIntegral (logDeriv completedEntire) ((σ' : ℂ) + Te * I) (((2 : ℝ) : ℂ) + b * I) = 0) →
        lineDefect Te Tl = 0) ∧
      (∀ (k : ℕ) (t : ℕ → ℝ), (∀ i, i < k → t i < t (i + 1)) → Te ≤ t 0 → t k ≤ Tl →
        (∀ i, i < k → lineValue (t i) * lineValue (t (i + 1)) < 0) → totalIncrement Te Tl ≤ k →
        lineDefect Te Tl = 0) := by
  intro Te Tl
  have hTl : Te ≤ Tl := hV.le
  refine ⟨lineDefect_eq _ _, lineDefect_even _ _, lineDefect_nonneg hTl,
    fun hβ => two_le_lineDefect_of_rupture hWe ⟨p.zLaterMember, hL⟩ le_rfl hβ,
    passage_radialFactor_of_lineDefect_zero p hL hWe,
    lineDefect_zero_of_total_lt_two hTl hWe,
    fun b hb hBoxes => lineDefect_zero_of_right_boxes hTl hb hBoxes,
    fun k t hmono h0 hk hsign hcount => lineDefect_zero_of_total_le_sign_changes hE.le hTl t hmono h0 hk hsign hcount⟩

#print axioms passage_line_defect_scope

/-! ## 5. Forme fibre sur un passage consécutif : le raccord analytique exact -/

/-- Partie ON de la fibre à la hauteur `T`, avec multiplicité. -/
noncomputable def onFiberCount (T : ℝ) : ℕ :=
  ∑ ρ ∈ ((upperWindow T).filter (fun ρ => ρ.im = T)).filter (fun ρ => ρ.re = 1 / 2), zetaZeroMultiplicity ρ

/-- **La partie ON de la fibre est lue sur la ligne en un seul point** : `0` si la fonction réelle ne s'annule pas en `T`,
sinon la multiplicité de `ζ` en `1/2 + iT`. -/
theorem onFiberCount_eq {T : ℝ} (hT : 0 < T) :
    onFiberCount T = if lineValue T = 0 then zetaZeroMultiplicity (linePoint T) else 0 := by
  have hset : ((upperWindow T).filter (fun ρ => ρ.im = T)).filter (fun ρ => ρ.re = 1 / 2) =
      if lineValue T = 0 then {linePoint T} else ∅ := by
    ext ρ
    simp only [Finset.mem_filter, mem_upperWindow]
    split_ifs with h
    · rw [Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨-, -, -⟩, him⟩, hre⟩
        exact Complex.ext (by simp [hre]) (by simp [him])
      · rintro rfl
        exact ⟨⟨⟨(onLine_zero_iff_lineValue T).mpr h, by simpa using hT, by simp⟩, by simp⟩, by simp⟩
    · simp only [Finset.notMem_empty, iff_false]
      rintro ⟨⟨⟨hz, -, -⟩, him⟩, hre⟩
      apply h
      rw [← onLine_zero_iff_lineValue]
      have : ρ = linePoint T := Complex.ext (by simp [hre]) (by simp [him])
      rwa [← this]
  unfold onFiberCount
  rw [hset]
  split_ifs <;> simp

/-- Sur un passage qui monte, l'accroissement ON est la partie ON de la fibre d'arrivée (consécutivité). -/
theorem passage_onCount_step_eq_fiber (p : TZeroPassage) (hV : VerticalPassage p) :
    onCount (rZeroHeight p.zLaterMember) =
      onCount (rZeroHeight p.zEarlierMember) + onFiberCount (rZeroHeight p.zLaterMember) := by
  unfold onCount onFiberCount
  rw [← Finset.sum_filter_add_sum_filter_not ((upperWindow (rZeroHeight p.zLaterMember)).filter
    (fun ρ => ρ.re = 1 / 2)) (fun ρ => ρ.im = rZeroHeight p.zLaterMember), add_comm]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext ρ
    simp only [Finset.mem_filter, mem_upperWindow]
    constructor
    · rintro ⟨⟨⟨h1, h2, h3⟩, h5⟩, h4⟩
      refine ⟨⟨h1, h2, ?_⟩, h5⟩
      by_contra hgt
      exact consecutive_no_height_between p ⟨ρ, h1⟩ ⟨lt_of_not_ge hgt, lt_of_le_of_ne h3 h4⟩
    · rintro ⟨⟨h1, h2, h3⟩, h5⟩
      have hlt : ρ.im < rZeroHeight p.zLaterMember := lt_of_le_of_lt h3 hV
      exact ⟨⟨⟨h1, h2, hlt.le⟩, h5⟩, ne_of_lt hlt⟩
  · rw [Finset.filter_comm]

/-- **Défaut d'un passage = fibre d'arrivée moins sa partie ON** (toute position radiale). -/
theorem passage_lineDefect_eq_fiber (p : TZeroPassage) (hV : VerticalPassage p) :
    lineDefect (rZeroHeight p.zEarlierMember) (rZeroHeight p.zLaterMember) =
      (fiberCountWithMultiplicity (rZeroHeight p.zLaterMember) : ℤ) - onFiberCount (rZeroHeight p.zLaterMember) := by
  unfold lineDefect totalIncrement lineIncrement
  rw [passage_count_step_eq_fiber p hV, passage_onCount_step_eq_fiber p hV]; push_cast; ring

/-- **Forme exacte du raccord** (caractérisation, non une dérivation) : sur un passage qui monte, le défaut est nul ⟺ la
multiplicité totale de la fibre d'arrivée (comptée par le principe de l'argument) égale la multiplicité de `ζ` au seul
point de la ligne `1/2 + iT_l`, lue par la fonction réelle. -/
theorem passage_lineDefect_zero_iff (p : TZeroPassage) (hV : VerticalPassage p) (hL : 0 < rZeroHeight p.zLaterMember) :
    lineDefect (rZeroHeight p.zEarlierMember) (rZeroHeight p.zLaterMember) = 0 ↔
      fiberCountWithMultiplicity (rZeroHeight p.zLaterMember) =
        (if lineValue (rZeroHeight p.zLaterMember) = 0 then
          zetaZeroMultiplicity (linePoint (rZeroHeight p.zLaterMember)) else 0) := by
  rw [passage_lineDefect_eq_fiber p hV, ← onFiberCount_eq hL]; omega

/-- **Aucun changement de signe de la fonction réelle dans un passage** : entre `T_e` et `T_l`, toute suite ordonnée
de changements de signe d'extrémités dans `[T_e, T_l]` est vide (consécutivité, `lineValue_ne_zero_between`). Le critère
de Turing local ne s'applique donc jamais sur le seul intervalle du passage : la lecture sur la ligne se fait au point
`T_l` lui-même (multiplicité), ou au-delà de `T_l`. -/
theorem passage_no_sign_change (p : TZeroPassage) {k : ℕ} (t : ℕ → ℝ)
    (hmono : ∀ i, i < k → t i < t (i + 1)) (h0 : rZeroHeight p.zEarlierMember ≤ t 0)
    (hk : t k ≤ rZeroHeight p.zLaterMember)
    (hsign : ∀ i, i < k → lineValue (t i) * lineValue (t (i + 1)) < 0) : k = 0 := by
  by_contra hk0
  have hmon : ∀ j, j ≤ k → t 1 ≤ t j ∨ j = 0 := by
    intro j
    induction j with
    | zero => intro _; right; rfl
    | succ j ih =>
      intro hj; left
      rcases ih (by omega) with h | h
      · exact h.trans (hmono j (by omega)).le
      · subst h; exact le_rfl
  obtain ⟨τ, hτ, hz⟩ := onLine_zero_of_sign_change (hmono 0 (by omega)) (hsign 0 (by omega))
  have h1k : t 1 ≤ t k := by
    rcases hmon k le_rfl with h | h
    · exact h
    · omega
  exact lineValue_ne_zero_between p (lt_of_le_of_lt h0 hτ.1) (lt_of_lt_of_le hτ.2 (h1k.trans hk))
    ((onLine_zero_iff_lineValue τ).mp hz)

#print axioms passage_lineDefect_zero_iff
#print axioms passage_no_sign_change

end RHV6Fresh
