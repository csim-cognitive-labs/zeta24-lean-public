/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CollectiveCurvature

/-!
# L'opérateur grammatical `𝓛_G` et la borne `B_G` (E344, 2026-10-19)

Fermeture proposée en 30 lignes (auteur, 2026-10-19), lignes 15–27 : construire un opérateur arithmétique `𝓛_G`
depuis les transitions et les raccords, DÉFINI SANS CONNAÎTRE `β_l`, `T_l` NI RH, qui isole la paire miroir ou borne
son complément ; poser `D_G = 𝓛_G(Q_w)` ; démontrer `grammar_operator_bound : B_G(D_G)` (grammaire) et
`off_pair_violates_bound : ¬B_G(D_G)` (OFF) ; fermer par leur composition.

Ce module compile l'opérateur et le côté OFF, exactement :
* `grammarOperator λ u` : combinaison finie de translations `a ↦ a + u_i` à poids `λ_i` ; son SYMBOLE à l'exposant
  `d` est `Σ λ_i e^{d u_i}` ; sur l'amplitude fenêtrée d'un mode d'exposant `d` l'opérateur agit par multiplication
  par son symbole (§1) ;
* instance grammaticale `classWeightedCurvature w r₀ m` : somme sur `m` écarts consécutifs depuis le rang `r₀` des
  différences secondes au pas `L_r = log(p_{r+1}/p_r)`, pondérées par la classe de transition mod 6 de l'écart
  (`w 0` maintien, `w 2` changement `2`, `w 4` changement `4`). Ses seules données sont le rang de départ, la longueur
  de fenêtre et trois poids : aucune partie réelle, aucune hauteur, aucune position de zéro n'y entre (§2) ;
* symbole de courbure `Σ_r w(a_r) · 2(cosh(d L_r) − 1)` : pair en `d`, nul en `d = 0` (le signal ON est ANNULÉ par
  l'opérateur), `≥ 0` pour des poids `≥ 0`, strictement positif dès qu'un poids est actif et `d ≠ 0`, minoré par les
  planchers grammaticaux `Σ_r w(a_r) (d log(1 + plancher(a_r)/p_r))²` (§3) ;
* **OFF ⟹ ¬B_G** : sous un demi, `𝓛_G` appliqué à la projection de la paire du zéro, à sa fréquence, n'est borné par
  aucune constante le long des translations (`off_classWeightedCurvature_unbounded`), donc toute borne `B_G` de
  `𝓛_G(paire)` ferme (`class_operator_bound_closes`) (§4) ;
* observable collective `D_G = 𝓛_G(Q)` depuis les premiers seuls, découpage exact `D_G = 𝓛_G(paire) + 𝓛_G(complément)`,
  schéma « deux lemmes » `grammar_operator_two_lemma_closes` : `B_G(D_G)` ∧ borne du complément ∧ intégrabilité ⟹
  `False` (§5) ;
* ce que la grammaire donne sur le complément : la projection du mode d'un zéro EN LIGNE, à toute fréquence, est
  bornée par la largeur de fenêtre uniformément en `a` ; une famille finie de zéros en ligne contribue au complément
  une quantité bornée ; `𝓛_G` d'une fonction bornée est bornée (§6). La borne du complément se ramène donc aux zéros
  hors de la famille finie, c'est-à-dire aux zéros de hauteur supérieure à celle de l'arrivée : elle n'est pas
  démontrée ici.

Statut : `grammar_operator_bound : B_G(D_G)` N'EST PAS démontré ; il est l'hypothèse `hCollective` du schéma. Aucun
théorème de ce module ne ferme le but ; la dépendance en `β`, `T` est intégralement dans la paire, jamais dans
l'opérateur.
-/

set_option linter.style.longLine false

namespace RHV6Fresh

open scoped BigOperators
open RHV3Lean MeasureTheory

/-! ## §1 Opérateur de translation à poids finis et son symbole -/

/-- Opérateur grammatical abstrait : `(𝓛 f)(a) = Σ_i λ_i f(a + u_i)`. -/
noncomputable def grammarOperator {n : ℕ} (lam u : Fin n → ℝ) (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∑ i, lam i * f (a + u i)

/-- Symbole de l'opérateur à l'exposant `d` : `Σ_i λ_i e^{d u_i}`. -/
noncomputable def operatorSymbol {n : ℕ} (lam u : Fin n → ℝ) (d : ℝ) : ℝ :=
  ∑ i, lam i * Real.exp (d * u i)

theorem operatorSymbol_zero {n : ℕ} (lam u : Fin n → ℝ) : operatorSymbol lam u 0 = ∑ i, lam i := by
  simp [operatorSymbol]

theorem grammarOperator_add {n : ℕ} (lam u : Fin n → ℝ) (f g : ℝ → ℝ) (a : ℝ) :
    grammarOperator lam u (fun a => f a + g a) a = grammarOperator lam u f a + grammarOperator lam u g a := by
  unfold grammarOperator
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

/-- **L'opérateur agit sur l'amplitude fenêtrée d'un mode par son symbole** : `𝓛(A_d(·, L))(a) = σ(d) A_d(a, L)`. -/
theorem grammarOperator_windowAmplitude {n : ℕ} (lam u : Fin n → ℝ) (d L a : ℝ) :
    grammarOperator lam u (fun a => windowAmplitude d a L) a = operatorSymbol lam u d * windowAmplitude d a L := by
  unfold grammarOperator operatorSymbol
  rw [Finset.sum_mul]
  congr 1; funext i
  dsimp only
  rw [windowAmplitude_translate]; ring

/-- Sur la paire miroir : `𝓛(A_d + A_{−d})(a) = σ(d) A_d(a) + σ(−d) A_{−d}(a)`. -/
theorem grammarOperator_pairAmplitudeWindow {n : ℕ} (lam u : Fin n → ℝ) (d L a : ℝ) :
    grammarOperator lam u (fun a => pairAmplitudeWindow d a L) a =
      operatorSymbol lam u d * windowAmplitude d a L + operatorSymbol lam u (-d) * windowAmplitude (-d) a L := by
  unfold pairAmplitudeWindow
  rw [grammarOperator_add, grammarOperator_windowAmplitude, grammarOperator_windowAmplitude]

/-- **Annulation du signal ON** : un opérateur de somme de poids nulle annule la paire en ligne (`d = 0`), sur toute
fenêtre et toute translation. -/
theorem grammarOperator_annihilates_onLine {n : ℕ} (lam u : Fin n → ℝ) (hsum : ∑ i, lam i = 0) (L a : ℝ) :
    grammarOperator lam u (fun a => pairAmplitudeWindow 0 a L) a = 0 := by
  rw [grammarOperator_pairAmplitudeWindow, neg_zero, operatorSymbol_zero, hsum]; ring

/-- **OFF ⟹ non borné (forme abstraite)** : si `d < 0`, `σ(d) ≥ 0` et `σ(−d) > 0`, l'opérateur appliqué à la paire
dépasse toute constante le long des translations. -/
theorem grammarOperator_pair_unbounded {n : ℕ} (lam u : Fin n → ℝ) {d L : ℝ} (hd : d < 0) (hL : 0 < L)
    (hs : 0 ≤ operatorSymbol lam u d) (hs' : 0 < operatorSymbol lam u (-d)) (K : ℝ) :
    ∃ a : ℝ, K < grammarOperator lam u (fun a => pairAmplitudeWindow d a L) a := by
  have hδ : 0 < -d := by linarith
  set c := operatorSymbol lam u (-d) with hc
  set w := windowAmplitude (-d) 0 L with hw
  have hwpos : 0 < w := windowAmplitude_pos (-d) 0 hL
  obtain ⟨a, ha⟩ : ∃ a : ℝ, K / (c * w) < Real.exp ((-d) * a) := by
    refine ⟨(Real.log (max (K / (c * w)) 1) + 1) / (-d), ?_⟩
    rw [mul_div_cancel₀ _ hδ.ne']
    calc K / (c * w) ≤ max (K / (c * w)) 1 := le_max_left _ _
      _ = Real.exp (Real.log (max (K / (c * w)) 1)) := (Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))).symm
      _ < Real.exp (Real.log (max (K / (c * w)) 1) + 1) := Real.exp_lt_exp.mpr (by linarith)
  refine ⟨a, ?_⟩
  rw [grammarOperator_pairAmplitudeWindow]
  have hmul : K < c * (Real.exp ((-d) * a) * w) := by
    have := (div_lt_iff₀ (mul_pos hs' hwpos)).mp ha
    linarith [mul_comm (c * w) (Real.exp ((-d) * a))]
  have hA : windowAmplitude (-d) a L = Real.exp ((-d) * a) * w := windowAmplitude_from_zero (-d) a L
  have h1 : 0 ≤ operatorSymbol lam u d * windowAmplitude d a L :=
    mul_nonneg hs (windowAmplitude_pos d a hL).le
  rw [hA]
  linarith

/-! ## §2 Instance grammaticale : courbure pondérée par les classes de transition mod 6 -/

/-- **L'opérateur grammatical `𝓛_G`** : sur `m` écarts consécutifs depuis le rang `r₀`, somme des différences secondes
au pas `L_r = log(p_{r+1}/p_r)` pondérées par la classe de transition mod 6 de l'écart. Données : `w` (trois poids),
`r₀`, `m` ; aucune partie réelle, aucune hauteur, aucun zéro. -/
noncomputable def classWeightedCurvature (w : ℕ → ℝ) (r₀ m : ℕ) (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∑ j : Fin m, w (eventClass (r₀ + j)) * secondDifference f a (rPrimeGapLogRatio (r₀ + j))

/-- Version complexe (pour l'observable collective et le complément). -/
noncomputable def classWeightedCurvatureC (w : ℕ → ℝ) (r₀ m : ℕ) (F : ℝ → ℂ) (a : ℝ) : ℂ :=
  ∑ j : Fin m, (w (eventClass (r₀ + j)) : ℂ) *
    (F (a + rPrimeGapLogRatio (r₀ + j)) - 2 * F a + F (a - rPrimeGapLogRatio (r₀ + j)))

/-- Symbole de courbure de `𝓛_G` à l'exposant `d` : `Σ_r w(a_r) · 2(cosh(d L_r) − 1)`. -/
noncomputable def curvatureSymbol (w : ℕ → ℝ) (r₀ m : ℕ) (d : ℝ) : ℝ :=
  ∑ j : Fin m, w (eventClass (r₀ + j)) * (2 * (Real.cosh (d * rPrimeGapLogRatio (r₀ + j)) - 1))

/-- `𝓛_G` sur la paire : multiplication par le symbole de courbure. -/
theorem classWeightedCurvature_pair (w : ℕ → ℝ) (r₀ m : ℕ) (d L a : ℝ) :
    classWeightedCurvature w r₀ m (fun a => pairAmplitudeWindow d a L) a =
      curvatureSymbol w r₀ m d * pairAmplitudeWindow d a L := by
  unfold classWeightedCurvature curvatureSymbol
  rw [Finset.sum_mul]
  congr 1; funext j
  rw [pairAmplitudeWindow_secondDifference]; ring

theorem curvatureSymbol_even (w : ℕ → ℝ) (r₀ m : ℕ) (d : ℝ) :
    curvatureSymbol w r₀ m (-d) = curvatureSymbol w r₀ m d := by
  unfold curvatureSymbol
  congr 1; funext j
  rw [neg_mul, Real.cosh_neg]

/-- **Le symbole est nul en ligne** : `𝓛_G` annule la paire ON. -/
theorem curvatureSymbol_zero (w : ℕ → ℝ) (r₀ m : ℕ) : curvatureSymbol w r₀ m 0 = 0 := by
  simp [curvatureSymbol]

theorem classWeightedCurvature_onLine (w : ℕ → ℝ) (r₀ m : ℕ) (L a : ℝ) :
    classWeightedCurvature w r₀ m (fun a => pairAmplitudeWindow 0 a L) a = 0 := by
  rw [classWeightedCurvature_pair, curvatureSymbol_zero, zero_mul]

/-! ## §3 Signe et planchers grammaticaux du symbole -/

theorem curvatureSymbol_nonneg (w : ℕ → ℝ) (hw : ∀ c, 0 ≤ w c) (r₀ m : ℕ) (d : ℝ) :
    0 ≤ curvatureSymbol w r₀ m d := by
  unfold curvatureSymbol
  apply Finset.sum_nonneg
  intro j _
  have := Real.one_le_cosh (d * rPrimeGapLogRatio (r₀ + j))
  exact mul_nonneg (hw _) (by linarith)

/-- Dès qu'un écart de la fenêtre porte un poids actif et que `d ≠ 0`, le symbole est strictement positif. -/
theorem curvatureSymbol_pos (w : ℕ → ℝ) (hw : ∀ c, 0 ≤ w c) (r₀ m : ℕ) (hact : ∃ j : Fin m, 0 < w (eventClass (r₀ + j)))
    {d : ℝ} (hd : d ≠ 0) : 0 < curvatureSymbol w r₀ m d := by
  obtain ⟨j₀, hj₀⟩ := hact
  unfold curvatureSymbol
  apply Finset.sum_pos'
  · intro j _
    have := Real.one_le_cosh (d * rPrimeGapLogRatio (r₀ + j))
    exact mul_nonneg (hw _) (by linarith)
  · refine ⟨j₀, Finset.mem_univ _, ?_⟩
    have h1 : 1 < Real.cosh (d * rPrimeGapLogRatio (r₀ + j₀)) :=
      Real.one_lt_cosh.mpr (mul_ne_zero hd (thm_primeGapLogRatio_pos _).ne')
    exact mul_pos hj₀ (by linarith)

/-- **Plancher grammatical du symbole** : `Σ_r w(a_r) (d log(1 + plancher(a_r)/p_r))² ≤ σ_G(d)` (premiers `> 3`,
poids `≥ 0`). La classe de transition mod 6 entre ici dans la borne inférieure de la réponse de `𝓛_G`. -/
theorem curvatureSymbol_ge_classFloor (w : ℕ → ℝ) (hw : ∀ c, 0 ≤ w c) (r₀ m : ℕ)
    (h3 : ∀ j : Fin m, 3 < fnPrimeAtRank (r₀ + j)) (d : ℝ) :
    ∑ j : Fin m, w (eventClass (r₀ + j)) *
      (d * Real.log (1 + (classFloor (eventClass (r₀ + j)) : ℝ) / (fnPrimeAtRank (r₀ + j) : ℝ))) ^ 2 ≤
      curvatureSymbol w r₀ m d := by
  unfold curvatureSymbol
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (pair_curvature_gap_floor d (r₀ + j) (h3 j)) (hw _)

/-! ## §4 OFF ⟹ ¬B_G sur la paire du zéro atteint -/

/-- `𝓛_G` sur la projection (réelle positive) de la paire d'un vrai zéro à sa fréquence. -/
theorem classWeightedCurvature_zeroPair (w : ℕ → ℝ) (r₀ m : ℕ) (z : TrueZero) {L : ℝ} (hL : 0 < L) (a : ℝ) :
    classWeightedCurvature w r₀ m (fun a => ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖) a =
      curvatureSymbol w r₀ m (rZeroRadialPosition z.1 - 1 / 2) *
        pairAmplitudeWindow (rZeroRadialPosition z.1 - 1 / 2) a L := by
  have hn : (fun a => ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖) =
      fun a => pairAmplitudeWindow (rZeroRadialPosition z.1 - 1 / 2) a L := by
    funext a
    rw [zeroPairMode_windowProjection, Complex.norm_real, Real.norm_of_nonneg (pairAmplitudeWindow_pos _ a hL).le]
  rw [hn, classWeightedCurvature_pair]

/-- **OFF ⟹ ¬B_G (démontré)** : sous un demi, avec des poids `≥ 0` dont l'un est actif sur la fenêtre grammaticale,
`𝓛_G(paire)` dépasse toute constante le long des translations. -/
theorem off_classWeightedCurvature_unbounded (w : ℕ → ℝ) (hw : ∀ c, 0 ≤ w c) (r₀ m : ℕ)
    (hact : ∃ j : Fin m, 0 < w (eventClass (r₀ + j))) (z : TrueZero) (hz : rZeroRadialPosition z.1 < 1 / 2)
    {L : ℝ} (hL : 0 < L) (K : ℝ) :
    ∃ a : ℝ, K < classWeightedCurvature w r₀ m
      (fun a => ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖) a := by
  set d := rZeroRadialPosition z.1 - 1 / 2 with hd
  have hdneg : d < 0 := by rw [hd]; linarith
  have hδ : 0 < -d := by linarith
  set c := curvatureSymbol w r₀ m d with hc
  have hcpos : 0 < c := curvatureSymbol_pos w hw r₀ m hact hdneg.ne
  set v := windowAmplitude (-d) 0 L with hv
  have hvpos : 0 < v := windowAmplitude_pos (-d) 0 hL
  obtain ⟨a, ha⟩ : ∃ a : ℝ, K / (c * v) < Real.exp ((-d) * a) := by
    refine ⟨(Real.log (max (K / (c * v)) 1) + 1) / (-d), ?_⟩
    rw [mul_div_cancel₀ _ hδ.ne']
    calc K / (c * v) ≤ max (K / (c * v)) 1 := le_max_left _ _
      _ = Real.exp (Real.log (max (K / (c * v)) 1)) := (Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))).symm
      _ < Real.exp (Real.log (max (K / (c * v)) 1) + 1) := Real.exp_lt_exp.mpr (by linarith)
  refine ⟨a, ?_⟩
  rw [classWeightedCurvature_zeroPair w r₀ m z hL a]
  have hmul : K < c * (Real.exp ((-d) * a) * v) := by
    have := (div_lt_iff₀ (mul_pos hcpos hvpos)).mp ha
    linarith [mul_comm (c * v) (Real.exp ((-d) * a))]
  have hA : Real.exp ((-d) * a) * v ≤ pairAmplitudeWindow d a L := by
    unfold pairAmplitudeWindow
    rw [windowAmplitude_from_zero (-d) a L]
    linarith [windowAmplitude_pos d a hL]
  calc K < c * (Real.exp ((-d) * a) * v) := hmul
    _ ≤ c * pairAmplitudeWindow d a L := mul_le_mul_of_nonneg_left hA hcpos.le

/-- **Composition sur la paire** : toute borne `B_G` de `𝓛_G(paire)` le long des translations ferme sous un demi. -/
theorem class_operator_bound_closes (w : ℕ → ℝ) (hw : ∀ c, 0 ≤ w c) (r₀ m : ℕ)
    (hact : ∃ j : Fin m, 0 < w (eventClass (r₀ + j))) (z : TrueZero) (hz : rZeroRadialPosition z.1 < 1 / 2)
    {L : ℝ} (hL : 0 < L)
    (hBound : ∃ K : ℝ, ∀ a : ℝ, classWeightedCurvature w r₀ m
      (fun a => ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖) a ≤ K) : False := by
  obtain ⟨K, hK⟩ := hBound
  obtain ⟨a, ha⟩ := off_classWeightedCurvature_unbounded w hw r₀ m hact z hz hL K
  exact absurd (hK a) (not_le.mpr ha)

/-! ## §5 Observable collective `D_G = 𝓛_G(Q)` et schéma « deux lemmes » -/

/-- **`D_G`** : l'opérateur grammatical appliqué à l'observable collective des premiers (aucun zéro dans l'énoncé). -/
noncomputable def grammarObservable (w : ℕ → ℝ) (r₀ m : ℕ) (L T : ℝ) (a : ℝ) : ℂ :=
  classWeightedCurvatureC w r₀ m (fun a => collectiveProjection a L T) a

theorem grammarObservable_eq_sum (w : ℕ → ℝ) (r₀ m : ℕ) (L T a : ℝ) :
    grammarObservable w r₀ m L T a =
      ∑ j : Fin m, (w (eventClass (r₀ + j)) : ℂ) * collectiveCurvature a L (rPrimeGapLogRatio (r₀ + j)) T := rfl

open Classical in
/-- **Découpage exact** `D_G = 𝓛_G(paire) + 𝓛_G(complément)` (somme finie, sous intégrabilité du signal filtré). -/
theorem grammarObservable_split_pair (w : ℕ → ℝ) (r₀ m : ℕ) (z : TrueZero) (L T a : ℝ)
    (hInt : ∀ a : ℝ, IntervalIntegrable (fun u => (smoothedRemainder (Real.exp u) / (Real.exp (u / 2) : ℂ)) *
      Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ)))) volume a (a + L))
    (hz : mirrorMember z ≠ z) :
    grammarObservable w r₀ m L T a =
      classWeightedCurvatureC w r₀ m (fun a => windowProjection (zeroPairMode z) a L T) a +
      classWeightedCurvatureC w r₀ m (fun a => windowProjection (collectiveComplement {z, mirrorMember z}) a L T) a := by
  rw [grammarObservable_eq_sum]
  unfold classWeightedCurvatureC
  rw [← Finset.sum_add_distrib]
  congr 1; funext j
  rw [collectiveCurvature_split_pair z a L (rPrimeGapLogRatio (r₀ + j)) T hInt hz]
  ring

/-- Sur la paire du zéro, la version complexe est la version réelle (projection réelle positive). -/
theorem classWeightedCurvatureC_zeroPair (w : ℕ → ℝ) (r₀ m : ℕ) (z : TrueZero) {L : ℝ} (hL : 0 < L) (a : ℝ) :
    classWeightedCurvatureC w r₀ m (fun a => windowProjection (zeroPairMode z) a L (rZeroHeight z.1)) a =
      (classWeightedCurvature w r₀ m
        (fun a => ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖) a : ℂ) := by
  have hn : ∀ a, ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖ =
      pairAmplitudeWindow (rZeroRadialPosition z.1 - 1 / 2) a L := by
    intro a
    rw [zeroPairMode_windowProjection, Complex.norm_real, Real.norm_of_nonneg (pairAmplitudeWindow_pos _ a hL).le]
  unfold classWeightedCurvatureC classWeightedCurvature secondDifference
  simp_rw [hn, zeroPairMode_windowProjection]
  push_cast
  rfl

open Classical in
/-- **Schéma « grammaire ⟹ B_G, OFF ⟹ ¬B_G » avec l'opérateur `𝓛_G`** : si `D_G = 𝓛_G(Q)` (premiers seuls) est borné
le long des translations à la fréquence du zéro atteint (lemme `B_G`, NON démontré), si `𝓛_G` du complément de la paire
est borné (NON démontré), et si le signal filtré est intégrable, alors `False` sous un demi. Les deux bornes sont des
hypothèses explicites ; seul « OFF ⟹ ¬B_G » est démontré. -/
theorem grammar_operator_two_lemma_closes (w : ℕ → ℝ) (hw : ∀ c, 0 ≤ w c) (r₀ m : ℕ)
    (hact : ∃ j : Fin m, 0 < w (eventClass (r₀ + j))) (z : TrueZero) (hz : rZeroRadialPosition z.1 < 1 / 2)
    {L : ℝ} (hL : 0 < L)
    (hInt : ∀ a : ℝ, IntervalIntegrable (fun u => (smoothedRemainder (Real.exp u) / (Real.exp (u / 2) : ℂ)) *
      Complex.exp (-((rZeroHeight z.1 : ℂ) * Complex.I * (u : ℂ)))) volume a (a + L))
    (hCollective : ∃ K : ℝ, ∀ a : ℝ, ‖grammarObservable w r₀ m L (rZeroHeight z.1) a‖ ≤ K)
    (hRest : ∃ K : ℝ, ∀ a : ℝ, ‖classWeightedCurvatureC w r₀ m
      (fun a => windowProjection (collectiveComplement {z, mirrorMember z}) a L (rZeroHeight z.1)) a‖ ≤ K) :
    False := by
  obtain ⟨K₁, hK₁⟩ := hCollective
  obtain ⟨K₂, hK₂⟩ := hRest
  refine class_operator_bound_closes w hw r₀ m hact z hz hL ⟨K₁ + K₂, fun a => ?_⟩
  have hsplit := grammarObservable_split_pair w r₀ m z L (rZeroHeight z.1) a hInt (mirrorMember_ne hz)
  rw [classWeightedCurvatureC_zeroPair w r₀ m z hL a] at hsplit
  have hpair : (classWeightedCurvature w r₀ m
      (fun a => ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖) a : ℂ) =
      grammarObservable w r₀ m L (rZeroHeight z.1) a -
        classWeightedCurvatureC w r₀ m
          (fun a => windowProjection (collectiveComplement {z, mirrorMember z}) a L (rZeroHeight z.1)) a := by
    rw [hsplit]; ring
  set X : ℂ := (classWeightedCurvature w r₀ m
      (fun a => ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖) a : ℂ) with hX
  have hle : X.re ≤ ‖X‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  calc classWeightedCurvature w r₀ m
        (fun a => ‖windowProjection (zeroPairMode z) a L (rZeroHeight z.1)‖) a
      = X.re := by rw [hX, Complex.ofReal_re]
    _ ≤ ‖X‖ := hle
    _ = ‖grammarObservable w r₀ m L (rZeroHeight z.1) a -
        classWeightedCurvatureC w r₀ m
          (fun a => windowProjection (collectiveComplement {z, mirrorMember z}) a L (rZeroHeight z.1)) a‖ := by
        rw [hpair]
    _ ≤ ‖grammarObservable w r₀ m L (rZeroHeight z.1) a‖ +
        ‖classWeightedCurvatureC w r₀ m
          (fun a => windowProjection (collectiveComplement {z, mirrorMember z}) a L (rZeroHeight z.1)) a‖ :=
        norm_sub_le _ _
    _ ≤ K₁ + K₂ := add_le_add (hK₁ a) (hK₂ a)

/-! ## §6 Ce que la grammaire donne sur le complément : les zéros EN LIGNE sont bornés, à toute fréquence -/

/-- La projection du mode d'un zéro en ligne, à TOUTE fréquence, est bornée par la largeur de fenêtre, uniformément
en `a` (le mode est de module `1`). -/
theorem onLine_mode_projection_norm_le (z : TrueZero) (hz : rZeroRadialPosition z.1 = 1 / 2) (a : ℝ) {L : ℝ}
    (hL : 0 ≤ L) (T : ℝ) : ‖windowProjection (zeroMode z) a L T‖ ≤ L := by
  unfold windowProjection
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + L) (C := 1)
    (f := fun u => zeroMode z u * Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ)))) (by
      intro u _
      rw [norm_mul]
      unfold zeroMode
      rw [complexMode_norm, hz, sub_self, zero_mul, Real.exp_zero, one_mul]
      have : -((T : ℂ) * Complex.I * (u : ℂ)) = ((-(T * u) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I])
  rw [add_sub_cancel_left, abs_of_nonneg hL, one_mul] at h
  exact h

/-- Une famille FINIE de zéros en ligne contribue au complément une quantité bornée : `‖Σ_{z ∈ s} P(mode z)‖ ≤ |s| L`,
uniformément en `a` et pour toute fréquence. -/
theorem onLine_finset_projection_norm_le (s : Finset TrueZero) (hs : ∀ z ∈ s, rZeroRadialPosition z.1 = 1 / 2)
    (a : ℝ) {L : ℝ} (hL : 0 ≤ L) (T : ℝ) :
    ‖∑ z ∈ s, windowProjection (zeroMode z) a L T‖ ≤ s.card * L := by
  calc ‖∑ z ∈ s, windowProjection (zeroMode z) a L T‖ ≤ ∑ z ∈ s, ‖windowProjection (zeroMode z) a L T‖ :=
        norm_sum_le _ _
    _ ≤ ∑ z ∈ s, L := Finset.sum_le_sum fun z hz => onLine_mode_projection_norm_le z (hs z hz) a hL T
    _ = s.card * L := by rw [Finset.sum_const, nsmul_eq_mul]

/-- `𝓛_G` d'une fonction bornée est bornée : `‖𝓛_G F‖ ≤ 4M Σ_r |w(a_r)|`. La borne du complément se ramène donc à la
partie du complément qui n'est pas une famille finie de zéros en ligne. -/
theorem classWeightedCurvatureC_norm_le (w : ℕ → ℝ) (r₀ m : ℕ) (F : ℝ → ℂ) {M : ℝ} (hF : ∀ a, ‖F a‖ ≤ M) (a : ℝ) :
    ‖classWeightedCurvatureC w r₀ m F a‖ ≤ (∑ j : Fin m, |w (eventClass (r₀ + j))|) * (4 * M) := by
  unfold classWeightedCurvatureC
  rw [Finset.sum_mul]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc ‖F (a + rPrimeGapLogRatio (r₀ + j)) - 2 * F a + F (a - rPrimeGapLogRatio (r₀ + j))‖
      ≤ ‖F (a + rPrimeGapLogRatio (r₀ + j)) - 2 * F a‖ + ‖F (a - rPrimeGapLogRatio (r₀ + j))‖ := norm_add_le _ _
    _ ≤ (‖F (a + rPrimeGapLogRatio (r₀ + j))‖ + ‖2 * F a‖) + ‖F (a - rPrimeGapLogRatio (r₀ + j))‖ :=
        by have := norm_sub_le (F (a + rPrimeGapLogRatio (r₀ + j))) (2 * F a); linarith
    _ ≤ (M + 2 * M) + M := by
        have h2 : ‖(2 : ℂ) * F a‖ = 2 * ‖F a‖ := by rw [norm_mul, Complex.norm_ofNat]
        rw [h2]
        linarith [hF (a + rPrimeGapLogRatio (r₀ + j)), hF a, hF (a - rPrimeGapLogRatio (r₀ + j))]
    _ = 4 * M := by ring

end RHV6Fresh
