/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FixedGapRaccords
import RHV6Fresh.Terminal.EscapeFinancing
import RHV6Fresh.Terminal.FirstGainPremise

/-!
# Signature OFF complète et signal de tous les écarts premiers : identifiabilité conditionnelle, PAS l'étude demandée
(auteur, 2026-10-15 ; correction du même jour, §100)

Texte collé de l'auteur : « L'étude des fréquences et amplitudes attendues sur TOUT l'horizon manque : aucun théorème compilé
ne contraint conjointement la fréquence du prochain zéro et son amplitude. C'est cette étude qu'il faut mener, en confrontant
la signature OFF complète au signal de tous les écarts premiers, sans dissocier `T` et `β` ni réutiliser la seule rigidité
spectrale. » Correction collée ensuite : « le code suppose l'égalité qu'il prétend exploiter ; il compare deux signatures entre
elles ; il ne démontre pas que le signal arithmétique impose une signature ON ; résultat conditionnel d'identifiabilité, pas
l'étude demandée ». Cette correction est exacte et ce module est reclassé en conséquence.

## Ce que ce module démontre (portée exacte, sans surinterprétation)

1. IDENTIFIABILITÉ CONDITIONNELLE : `joint_frequency_amplitude_from_all_gaps` prend EN HYPOTHÈSE l'égalité des contributions
   de deux signatures sur tous les écarts au-delà d'un rang et conclut qu'elles ont même fréquence et même amplitude. Il
   compare deux signatures ; il ne lit pas le signal des premiers ; il ne produit aucune contrainte sur `(T, β)`.
   De même `frequency_displacement_changes_gaps`, `offSignature_determined_by_all_gaps`.
2. CONSÉQUENCES D'UNE SIGNATURE OFF SUPPOSÉE sur la croissance du signal (`off_signature_forces_prime_signal_growth`,
   `off_signature_lifts_remainderExponent`, `low_amplitude_tendsto_zero`, `mirror_amplitude_exceeds_beyond`) : la direction
   est « OFF supposé ⟹ le reste croît », jamais « le reste ⟹ ON ». Elles ne constituent pas un mécanisme d'exclusion.
3. CARACTÉRISATIONS : l'exclusion d'une signature OFF ⟺ un exposant `θ < 1 − β` du signal (`off_signature_excluded_of_prime_signal_exponent`),
   toutes exclues ⟺ `θ* = 1/2` (`all_off_signatures_excluded_iff_remainderExponent_half`), ⟺ RH. Forme du but, pas sa dérivation.
4. CE QUE LE SIGNAL DES PREMIERS SEUL DONNE, sans aucune hypothèse sur une signature (`prime_signal_alone_joint_constraint`) :
   la bande `0 ≤ β ≤ 1` pour tout zéro (exposant `1` acquis de `Λ(n)` et Chebyshev, `radial_strip_of_remainder_growth`), et
   AUCUNE contrainte sur la fréquence. C'est la seule contrainte conjointe compilée depuis les premiers seuls ; elle n'exclut
   aucune signature (`acquired_exponent_admits_any_off_signature`).

L'étude demandée (signal exact de tous les écarts ⟶ contraintes conjointes sur `(T, β)` excluant OFF) N'EST PAS réalisée par ce
module ; ses théorèmes ne valident aucun mécanisme d'exclusion OFF. Aucune définition modifiée, aucune prémisse ; ce module n'est
pas composé dans la chaîne.
-/

namespace RHV6Fresh

open RHV3Lean Complex Filter Topology

/-! ## 1. La signature OFF complète -/

/-- **Signature OFF complète** d'un vrai zéro : son point et celui de son miroir (même fréquence `T`, amplitudes `β` et
`1 − β`). -/
noncomputable def offSignature (w : TrueZero) : ℂ × ℂ := (zeroPoint w, zeroPoint (mirrorMember w))

theorem offSignature_same_frequency (w : TrueZero) : (offSignature w).2.im = (offSignature w).1.im := by
  simp [offSignature, zeroPoint_im, mirrorMember_ordinate]

theorem offSignature_mirror_amplitude (w : TrueZero) : (offSignature w).2.re = 1 - (offSignature w).1.re := by
  simp [offSignature, zeroPoint_re, mirrorMember_radial]

/-! ## 2. Identifiabilité CONDITIONNELLE (comparaison de deux signatures ; ne lit pas le signal des premiers) -/

/-- **Identifiabilité conditionnelle** : SOUS L'HYPOTHÈSE `h` (égalité des contributions de `ρ'` et de `w` sur tous les écarts
au-delà d'un rang), `ρ'` a l'amplitude et la fréquence de `w`. Comparaison de deux signatures ; aucune contrainte sur `(T, β)`
n'est produite depuis les premiers. -/
theorem joint_frequency_amplitude_from_all_gaps (w : TrueZero) {ρ' : ℂ} (hβ' : 0 < ρ'.re) (hT' : 0 < ρ'.im)
    (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → primeGapContribution ρ' n = primeGapContribution (zeroPoint w) n) :
    ρ'.re = rZeroRadialPosition w.1 ∧ ρ'.im = rZeroHeight w.1 := by
  have hpt := prime_gap_contributions_determine_point hβ' (zeroPoint_re_pos w) hT' w.2 n₀ h
  rw [hpt]
  exact ⟨zeroPoint_re w, zeroPoint_im w⟩

/-- **Non dissociable, côté fréquence** : à amplitude fixée, un changement de fréquence est lu sur un écart au-delà de
tout rang. -/
theorem frequency_displacement_changes_gaps {β T T' : ℝ} (hβ : 0 < β) (hT : 0 < T) (hT' : 0 < T')
    (hne : T ≠ T') (n₀ : ℕ) : ∃ n, n₀ ≤ n ∧
      primeGapContribution ((β : ℂ) + T * I) n ≠ primeGapContribution ((β : ℂ) + T' * I) n := by
  refine distinct_points_differ_beyond_any_rank (by simpa using hβ) (by simpa using hβ)
    (by simpa using hT) (by simpa using hT') ?_ n₀
  intro h
  exact hne (by simpa using congrArg Complex.im h)

/-- **La signature complète est déterminée par tous les écarts** : même contributions au-delà d'un rang ⟹ même membre,
même miroir. -/
theorem offSignature_determined_by_all_gaps (w w' : TrueZero) (n₀ : ℕ)
    (h : ∀ n, n₀ ≤ n → primeGapContribution (zeroPoint w) n = primeGapContribution (zeroPoint w') n) :
    offSignature w = offSignature w' := by
  rw [trueZero_determined_by_prime_gaps w w' n₀ h]

/-! ## 3. Conséquences d'une signature OFF SUPPOSÉE sur la croissance du signal (direction OFF ⟹ reste, jamais l'inverse) -/

/-- Une signature OFF SUPPOSÉE (`β < 1/2`) impose au signal de tous les écarts premiers de dépasser `C·x^θ` en un point
`x > 1`, pour tout `θ < 1 − β` et tout `C` (lecture du pôle sur le miroir). Direction « OFF ⟹ croissance » ; ce n'est pas une
exclusion. -/
theorem off_signature_forces_prime_signal_growth (w : TrueZero) (hLow : rZeroRadialPosition w.1 < 1 / 2)
    {θ : ℝ} (hθ : θ < 1 - rZeroRadialPosition w.1) (C : ℝ) :
    ∃ x : ℝ, 1 < x ∧ C * x ^ θ < ‖smoothedRemainder x‖ := by
  have _ := hLow
  refine escape_must_be_financed (mirrorMember w) ?_ C
  rw [mirrorMember_radial]; exact hθ

/-- **L'exposant du reste est relevé** par toute signature OFF : `1 − β ≤ θ*`, donc `1/2 < θ*`. -/
theorem off_signature_lifts_remainderExponent (w : TrueZero) (hLow : rZeroRadialPosition w.1 < 1 / 2) :
    1 - rZeroRadialPosition w.1 ≤ remainderExponent ∧ 1 / 2 < remainderExponent := by
  have h := mirror_pair_exponent_le_remainderExponent w
  have hmax : 1 - rZeroRadialPosition w.1 ≤ max (rZeroRadialPosition w.1) (1 - rZeroRadialPosition w.1) :=
    le_max_right _ _
  exact ⟨hmax.trans h, by linarith⟩

/-- **Le membre bas s'éteint** : son amplitude normalisée tend vers `0` le long de l'axe. -/
theorem low_amplitude_tendsto_zero (w : TrueZero) (hLow : rZeroRadialPosition w.1 < 1 / 2) :
    Tendsto (pairAmplitude w) atTop (𝓝 0) := by
  have hneg : rZeroRadialPosition w.1 - 1 / 2 < 0 := by linarith
  have hs : 0 < Real.sqrt (rZeroRadialPosition w.1 ^ 2 + rZeroHeight w.1 ^ 2) := by
    apply Real.sqrt_pos.mpr
    have := w.2
    positivity
  have hlim : Tendsto (fun x : ℝ => 2 * x ^ (rZeroRadialPosition w.1 - 1 / 2) /
      Real.sqrt (rZeroRadialPosition w.1 ^ 2 + rZeroHeight w.1 ^ 2)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by linarith : 0 < -(rZeroRadialPosition w.1 - 1 / 2))).const_mul 2
    simp only [neg_neg, mul_zero] at this
    simpa using this.div_const _
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [pairAmplitude_eq w hx]

/-- **Le miroir déborde** : son amplitude normalisée dépasse tout seuil au-delà d'un horizon. -/
theorem mirror_amplitude_exceeds_beyond (w : TrueZero) (hLow : rZeroRadialPosition w.1 < 1 / 2) (K : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → K < pairAmplitude (mirrorMember w) x := by
  have hpos : 0 < rZeroRadialPosition (mirrorMember w).1 - 1 / 2 := by
    rw [mirrorMember_radial]; linarith
  have hs : 0 < Real.sqrt (rZeroRadialPosition (mirrorMember w).1 ^ 2 + rZeroHeight (mirrorMember w).1 ^ 2) := by
    apply Real.sqrt_pos.mpr
    have := (mirrorMember w).2
    positivity
  have hlim : Tendsto (fun x : ℝ => 2 * x ^ (rZeroRadialPosition (mirrorMember w).1 - 1 / 2) /
      Real.sqrt (rZeroRadialPosition (mirrorMember w).1 ^ 2 + rZeroHeight (mirrorMember w).1 ^ 2)) atTop atTop :=
    ((tendsto_rpow_atTop hpos).const_mul_atTop (by norm_num)).atTop_div_const hs
  have hev : ∀ᶠ x in atTop, K < pairAmplitude (mirrorMember w) x := by
    filter_upwards [hlim.eventually_gt_atTop K, eventually_gt_atTop 0] with x hx hx0
    rwa [pairAmplitude_eq _ hx0]
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  exact ⟨X, hX⟩

/-! ## 4. Caractérisations (forme du but) et ce que le signal des premiers seul donne -/

/-- **Exclusion par le signal** : une signature OFF est incompatible avec le signal de tous les écarts dès qu'un exposant
`θ < 1 − β` de ce signal est acquis. -/
theorem off_signature_excluded_of_prime_signal_exponent (w : TrueZero)
    (h : ∃ θ C : ℝ, θ < 1 - rZeroRadialPosition w.1 ∧ ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ θ) :
    False := by
  obtain ⟨θ, C, hθ, hC⟩ := h
  obtain ⟨x, hx, hlt⟩ := escape_must_be_financed (mirrorMember w) (by rw [mirrorMember_radial]; exact hθ) C
  exact absurd (hC x hx) (not_le.mpr hlt)

/-- **Toutes les signatures OFF exclues ⟺ `θ* = 1/2`** : la confrontation sur tout l'horizon, quantifiée, est la valeur
de l'exposant du signal de tous les écarts. -/
theorem all_off_signatures_excluded_iff_remainderExponent_half :
    (∀ w : TrueZero, rZeroRadialPosition w.1 < 1 / 2 → False) ↔ remainderExponent = 1 / 2 := by
  rw [← riemannHypothesis_iff_remainderExponent_eq_half, riemannHypothesis_iff_noLowerSide]

/-- **L'exposant acquis admet toute signature OFF** : l'échelle `x` démontrée depuis les seuls poids `Λ(n)` n'est sous
`1 − β` pour aucun `β ∈ ]0, 1/2[`. -/
theorem acquired_exponent_admits_any_off_signature (w : TrueZero) (hLow : rZeroRadialPosition w.1 < 1 / 2) :
    (1 : ℝ) ∈ remainderExponents ∧ ¬ ((1 : ℝ) < 1 - rZeroRadialPosition w.1) := by
  have _ := hLow
  refine ⟨one_mem_remainderExponents, ?_⟩
  have := thm_zeroRadialPosition_positive w.1
  linarith

/-- **Ce que le signal des premiers seul donne, sans supposer aucune signature** : la bande `0 ≤ β ≤ 1` pour tout zéro, par
l'exposant `1` démontré depuis `Λ(n)` et Chebyshev ; aucune contrainte sur la fréquence. Seule contrainte conjointe compilée
depuis les premiers seuls ; elle n'exclut aucune signature. -/
theorem prime_signal_alone_joint_constraint :
    ∀ z : TrueZero, 1 - (1 : ℝ) ≤ rZeroRadialPosition z.1 ∧ rZeroRadialPosition z.1 ≤ (1 : ℝ) := by
  obtain ⟨C, hC⟩ := smoothedRemainder_linear_growth
  exact fun z => radial_strip_of_remainder_growth hC z

#print axioms prime_signal_alone_joint_constraint
#print axioms joint_frequency_amplitude_from_all_gaps
#print axioms frequency_displacement_changes_gaps
#print axioms offSignature_determined_by_all_gaps
#print axioms off_signature_forces_prime_signal_growth
#print axioms off_signature_lifts_remainderExponent
#print axioms low_amplitude_tendsto_zero
#print axioms mirror_amplitude_exceeds_beyond
#print axioms off_signature_excluded_of_prime_signal_exponent
#print axioms all_off_signatures_excluded_iff_remainderExponent_half
#print axioms acquired_exponent_admits_any_off_signature

end RHV6Fresh
