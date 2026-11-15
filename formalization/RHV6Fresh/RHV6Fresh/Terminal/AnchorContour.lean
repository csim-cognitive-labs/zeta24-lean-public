/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.AnchorStructure
import RHV3Lean.Objects.ZetaZeroCountingCrude

/-!
# Contour admissible pour le comptage de l'ancre (auteur, 2026-10-08, correction du contour)

Le rectangle `[0,1] × [0,T]` proposé dans la première tentative TDD rencontre le **pôle** de `ζ` en `s = 1`, sur sa
frontière : ce contour n'est pas admissible. Ce module formalise un contour admissible, avec traitement explicite des
pôles, par une fonction **entière** :

`ξ₁(s) := s (1 − s) Λ₀(s) − 1 = s (1 − s) Λ(s)`  (`completedEntire`),

où `Λ₀` est la zêta complétée modifiée de Mathlib (`completedRiemannZeta₀`, entière) et `Λ = Λ₀ − 1/s − 1/(1 − s)`
(`completedRiemannZeta_eq`). Propriétés démontrées ici :

1. `ξ₁` est entière (`differentiable_completedEntire`) : aucun pôle, donc tout rectangle est admissible ;
2. `ξ₁(s) = s (1 − s) Λ(s)` hors de `{0, 1}`, et `ξ₁(0) = ξ₁(1) = −1` ;
3. équation fonctionnelle `ξ₁(1 − s) = ξ₁(s)` ;
4. hors de l'axe réel, `ξ₁(s) = ζ(s) · s (1 − s) Γℝ(s)` avec un facteur analytique **non nul** ; donc `ξ₁(s) = 0 ⟺ ζ(s) = 0`
   (`completedEntire_eq_zero_iff`) et les **multiplicités coïncident** (`completedEntire_multiplicity`, par
   additivité de l'ordre analytique) ;
5. **raccord exact au comptage supérieur** : les zéros de `ξ₁` dans le rectangle ouvert `(−1, 2) × (0, T)` sont
   exactement les points de la fenêtre supérieure ouverte (`completedEntire_zero_openRect_iff`), et les zéros de `ζ`
   de hauteur strictement positive sont non triviaux (`nontrivial_of_zero_im_pos`, bande fermée de Backlund + non
   annulation sur `Re = 1` et, par symétrie, sur `Re = 0`) ;
6. **frontière** : `ξ₁` ne s'annule sur aucun point réel hors de `(0, 1)` (`completedEntire_real_ne_zero_of_not_Ioo` :
   `σ > 1` par positivité de `ζ`, `σ < 0` par l'équation fonctionnelle, `σ ∈ {0, 1}` par la valeur `−1`) ; sur les côtés
   verticaux `Re = −1` et `Re = 2`, aucun zéro (`completedEntire_ne_zero_of_re_out`) ; la non-annulation sur le segment
   réel `(0, 1)` se ramène à `ζ(σ) ≠ 0` pour `0 < σ < 1` (`completedEntire_real_ne_zero_of_zeta_ne_zero`), énoncé
   fourni par `RHV3Lean.thm_noRealZetaZeroInOpenUnitSegment` et instancié dans `Terminal/ZetaRealSegment.lean` ;
7. l'intégrale de bord du rectangle, dans la forme de Mathlib (`rectBoundaryIntegral`), est nulle pour `ξ₁` elle-même
   (contrôle de Cauchy, `rectBoundaryIntegral_completedEntire_eq_zero`).

Ce qui n'est PAS ici : le principe de l'argument (démontré dans `Terminal/ArgumentPrinciple.lean`) et l'évaluation
certifiée de l'intégrale de `ξ₁'/ξ₁` sur le contour (E185, Arb : certificat externe ; obligation (a) ouverte de la chaîne
unique `Terminal/DemonstrationChain.lean`). Aucun `sorry`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean Complex Filter Topology Set

/-! ## 1. La fonction entière `ξ₁` -/

/-- `ξ₁(s) := s (1 − s) Λ₀(s) − 1` : fonction entière égale à `s (1 − s) Λ(s)` hors de `{0, 1}`. -/
noncomputable def completedEntire (s : ℂ) : ℂ := s * (1 - s) * completedRiemannZeta₀ s - 1

/-- **Aucun pôle** : `ξ₁` est entière. -/
theorem differentiable_completedEntire : Differentiable ℂ completedEntire :=
  ((differentiable_id.mul ((differentiable_const (1 : ℂ)).sub differentiable_id)).mul
    differentiable_completedZeta₀).sub (differentiable_const 1)

/-- Hors de `{0, 1}`, `ξ₁(s) = s (1 − s) Λ(s)`. -/
theorem completedEntire_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedEntire s = s * (1 - s) * completedRiemannZeta s := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [completedRiemannZeta_eq]
  unfold completedEntire
  field_simp
  ring

theorem completedEntire_zero : completedEntire 0 = -1 := by
  unfold completedEntire; ring

theorem completedEntire_one : completedEntire 1 = -1 := by
  unfold completedEntire; ring

/-- **Équation fonctionnelle** de `ξ₁`. -/
theorem completedEntire_one_sub (s : ℂ) : completedEntire (1 - s) = completedEntire s := by
  unfold completedEntire
  rw [completedRiemannZeta₀_one_sub]
  ring

/-! ## 2. Facteur gamma : non nul et analytique hors de l'axe réel -/

theorem Gammaℝ_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff]
  rintro ⟨n, hn⟩
  apply hs
  rw [hn]
  simp

/-- Sous `Γℝ(s) ≠ 0` et `s ∉ {0, 1}` : `ξ₁(s) = ζ(s) · s (1 − s) Γℝ(s)`. -/
theorem completedEntire_eq_zeta_mul' {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hG : Gammaℝ s ≠ 0) :
    completedEntire s = riemannZeta s * (s * (1 - s) * Gammaℝ s) := by
  rw [completedEntire_eq hs0 hs1, riemannZeta_def_of_ne_zero hs0]
  field_simp

theorem im_ne_zero_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 0 := fun h => hs (by rw [h, zero_im])

theorem im_ne_zero_ne_one {s : ℂ} (hs : s.im ≠ 0) : s ≠ 1 := fun h => hs (by rw [h, one_im])

/-- Hors de l'axe réel : `ξ₁(s) = ζ(s) · s (1 − s) Γℝ(s)`. -/
theorem completedEntire_eq_zeta_mul {s : ℂ} (hs : s.im ≠ 0) :
    completedEntire s = riemannZeta s * (s * (1 - s) * Gammaℝ s) :=
  completedEntire_eq_zeta_mul' (im_ne_zero_ne_zero hs) (im_ne_zero_ne_one hs)
    (Gammaℝ_ne_zero_of_im_ne_zero hs)

/-- Le facteur `s (1 − s) Γℝ(s)` ne s'annule pas hors de l'axe réel. -/
theorem gammaFactor_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s * (1 - s) * Gammaℝ s ≠ 0 :=
  mul_ne_zero (mul_ne_zero (im_ne_zero_ne_zero hs) (sub_ne_zero.mpr (Ne.symm (im_ne_zero_ne_one hs))))
    (Gammaℝ_ne_zero_of_im_ne_zero hs)

/-- **Zéros de `ξ₁` hors de l'axe réel = zéros de `ζ`.** -/
theorem completedEntire_eq_zero_iff {s : ℂ} (hs : s.im ≠ 0) :
    completedEntire s = 0 ↔ riemannZeta s = 0 := by
  rw [completedEntire_eq_zeta_mul hs, mul_eq_zero]
  have h := gammaFactor_ne_zero hs
  exact ⟨fun h' => h'.resolve_right h, fun h' => Or.inl h'⟩

theorem isOpen_im_ne_zero : IsOpen {z : ℂ | z.im ≠ 0} :=
  isOpen_ne_fun continuous_im continuous_const

/-- `Γℝ` est analytique hors de l'axe réel (par son inverse entier, non nul). -/
theorem analyticAt_Gammaℝ_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : AnalyticAt ℂ Gammaℝ s := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_im_ne_zero.mem_nhds (show s ∈ {z : ℂ | z.im ≠ 0} from hs)] with z hz
  have hG : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_im_ne_zero hz
  have h : DifferentiableAt ℂ (fun w => ((Gammaℝ w)⁻¹)⁻¹) z :=
    (differentiable_Gammaℝ_inv z).inv (inv_ne_zero hG)
  simpa only [inv_inv] using h

theorem gammaFactor_analyticAt {s : ℂ} (hs : s.im ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ => z * (1 - z) * Gammaℝ z) s :=
  (analyticAt_id.mul (analyticAt_const.sub analyticAt_id)).mul (analyticAt_Gammaℝ_of_im_ne_zero hs)

/-- Au voisinage d'un point hors de l'axe réel, `ξ₁ = ζ · (facteur gamma)` comme fonctions. -/
theorem completedEntire_eventuallyEq {s : ℂ} (hs : s.im ≠ 0) :
    completedEntire =ᶠ[𝓝 s] (riemannZeta * fun z : ℂ => z * (1 - z) * Gammaℝ z) := by
  filter_upwards [isOpen_im_ne_zero.mem_nhds (show s ∈ {z : ℂ | z.im ≠ 0} from hs)] with z hz
  show completedEntire z = riemannZeta z * (z * (1 - z) * Gammaℝ z)
  exact completedEntire_eq_zeta_mul hz

/-- **Les multiplicités coïncident** : l'ordre analytique de `ξ₁` en un zéro de `ζ` hors de l'axe réel est la
multiplicité analytique de ce zéro (`zetaZeroMultiplicity`), le facteur gamma étant analytique et non nul. -/
theorem completedEntire_multiplicity {ρ : ℂ} (hρ : riemannZeta ρ = 0) (him : ρ.im ≠ 0) :
    analyticOrderNatAt completedEntire ρ = zetaZeroMultiplicity ρ := by
  have hζ := analyticAt_riemannZeta_of_zero hρ
  have hg := gammaFactor_analyticAt him
  have hg0 : analyticOrderAt (fun z : ℂ => z * (1 - z) * Gammaℝ z) ρ = 0 :=
    hg.analyticOrderAt_eq_zero.mpr (gammaFactor_ne_zero him)
  unfold zetaZeroMultiplicity analyticOrderNatAt
  rw [analyticOrderAt_congr (completedEntire_eventuallyEq him), analyticOrderAt_mul hζ hg, hg0, add_zero]

/-! ## 3. Raccord exact au comptage supérieur -/

/-- Un zéro de `ζ` de hauteur strictement positive est non trivial : bande fermée `0 ≤ Re ≤ 1` (Backlund, port
`rhv3_lean`), `Re ≠ 1` (non annulation de Mathlib) et `Re ≠ 0` (équation fonctionnelle de `ξ₁`, ramenée à `Re = 1`). -/
theorem nontrivial_of_zero_im_pos {s : ℂ} (hζ : riemannZeta s = 0) (him : 0 < s.im) :
    PIsNonTrivialZetaZero s := by
  obtain ⟨h0, h1⟩ := zeta_zero_re_mem_of_im_pos hζ him
  refine ⟨hζ, ?_, lt_of_le_of_ne h1 fun h => riemannZeta_ne_zero_of_one_le_re h.ge hζ⟩
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    have hs : s.im ≠ 0 := him.ne'
    have h1s : (1 - s).im ≠ 0 := by rw [sub_im, one_im]; intro h'; apply hs; linarith
    have hξ : completedEntire (1 - s) = 0 := by
      rw [completedEntire_one_sub]; exact (completedEntire_eq_zero_iff hs).mpr hζ
    have hζ' := (completedEntire_eq_zero_iff h1s).mp hξ
    exact riemannZeta_ne_zero_of_one_le_re (by rw [sub_re, one_re, ← h]; norm_num) hζ'

/-- **Raccord exact** : les zéros de `ξ₁` de hauteur dans `(0, T)` sont exactement les points de la fenêtre
supérieure ouverte. -/
theorem completedEntire_zero_iff_mem_upperWindowOpen {T : ℝ} {s : ℂ} :
    (completedEntire s = 0 ∧ 0 < s.im ∧ s.im < T) ↔ s ∈ upperWindowOpen T := by
  rw [mem_upperWindowOpen]
  constructor
  · rintro ⟨h, him, hT⟩
    exact ⟨nontrivial_of_zero_im_pos ((completedEntire_eq_zero_iff him.ne').mp h) him, him, hT⟩
  · rintro ⟨h, him, hT⟩
    exact ⟨(completedEntire_eq_zero_iff him.ne').mpr h.1, him, hT⟩

/-- Les zéros de `ξ₁` du rectangle OUVERT `(−1, 2) × (0, T)` sont exactement la fenêtre supérieure ouverte : les
bornes réelles `−1 < Re < 2` ne retirent aucun zéro (ils vérifient `0 < Re < 1`). -/
theorem completedEntire_zero_openRect_iff {T : ℝ} {s : ℂ} :
    (completedEntire s = 0 ∧ -1 < s.re ∧ s.re < 2 ∧ 0 < s.im ∧ s.im < T) ↔ s ∈ upperWindowOpen T := by
  constructor
  · rintro ⟨h, -, -, him, hT⟩
    exact completedEntire_zero_iff_mem_upperWindowOpen.mp ⟨h, him, hT⟩
  · intro hmem
    obtain ⟨h, him, hT⟩ := completedEntire_zero_iff_mem_upperWindowOpen.mpr hmem
    have hnt := (mem_upperWindowOpen.mp hmem).1
    exact ⟨h, by linarith [hnt.2.1], by linarith [hnt.2.2], him, hT⟩

/-- Sur les côtés verticaux (`Re ∉ [0, 1]`), hors de l'axe réel, `ξ₁` ne s'annule pas. -/
theorem completedEntire_ne_zero_of_re_out {s : ℂ} (hs : s.im ≠ 0) (hre : s.re < 0 ∨ 1 < s.re) :
    completedEntire s ≠ 0 := by
  intro h
  have hζ := (completedEntire_eq_zero_iff hs).mp h
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · -- hauteur négative : le conjugué est un zéro de hauteur positive, même partie réelle
    have hc : riemannZeta (starRingEnd ℂ s) = 0 := by
      rw [_root_.riemannZeta_conj, hζ, map_zero]
    obtain ⟨h0, h1⟩ := zeta_zero_re_mem_of_im_pos hc (by rw [conj_im]; linarith)
    rw [conj_re] at h0 h1
    rcases hre with hre | hre <;> linarith
  · obtain ⟨h0, h1⟩ := zeta_zero_re_mem_of_im_pos hζ hpos
    rcases hre with hre | hre <;> linarith

/-! ## 4. Le segment réel du contour -/

/-- `σ > 1` : `ζ(σ) ≠ 0`, `Γℝ(σ) ≠ 0`, donc `ξ₁(σ) ≠ 0`. -/
theorem completedEntire_real_ne_zero_of_one_lt {σ : ℝ} (h : 1 < σ) : completedEntire σ ≠ 0 := by
  have hs0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (show σ ≠ 0 by linarith)
  have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast (show σ ≠ 1 by linarith)
  have hG : Gammaℝ σ ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [ofReal_re]; linarith)
  have hζ : riemannZeta σ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [ofReal_re]; exact h)
  rw [completedEntire_eq_zeta_mul' hs0 hs1 hG]
  exact mul_ne_zero hζ (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr (Ne.symm hs1))) hG)

/-- `σ < 0` : par l'équation fonctionnelle, `ξ₁(σ) = ξ₁(1 − σ)` avec `1 − σ > 1`. -/
theorem completedEntire_real_ne_zero_of_neg {σ : ℝ} (h : σ < 0) : completedEntire σ ≠ 0 := by
  rw [← completedEntire_one_sub]
  have := completedEntire_real_ne_zero_of_one_lt (σ := 1 - σ) (by linarith)
  push_cast at this
  exact this

/-- **Segment réel hors de `(0, 1)`** : `ξ₁(σ) ≠ 0`. -/
theorem completedEntire_real_ne_zero_of_not_Ioo {σ : ℝ} (h : σ ∉ Ioo (0 : ℝ) 1) : completedEntire σ ≠ 0 := by
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at h
  rcases h with h | h
  · rcases h.lt_or_eq with h | h
    · exact completedEntire_real_ne_zero_of_neg h
    · rw [h]; push_cast; rw [completedEntire_zero]; norm_num
  · rcases h.lt_or_eq with h | h
    · exact completedEntire_real_ne_zero_of_one_lt h
    · rw [← h]; push_cast; rw [completedEntire_one]; norm_num

/-- **Segment réel `(0, 1)`, ramené à `ζ`** : si `ζ(σ) ≠ 0` pour `0 < σ < 1`, alors `ξ₁(σ) ≠ 0` sur tout l'axe réel.
L'hypothèse `hζ` est déchargée dans `Terminal/ZetaRealSegment.lean` (`completedEntire_real_ne_zero`). -/
theorem completedEntire_real_ne_zero_of_zeta_ne_zero
    (hζ : ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta σ ≠ 0) (σ : ℝ) : completedEntire σ ≠ 0 := by
  by_cases h : σ ∈ Ioo (0 : ℝ) 1
  · obtain ⟨h0, h1⟩ := h
    have hs0 : (σ : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast h1.ne
    have hG : Gammaℝ σ ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [ofReal_re]; exact h0)
    rw [completedEntire_eq_zeta_mul' hs0 hs1 hG]
    exact mul_ne_zero (hζ σ h0 h1) (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr (Ne.symm hs1))) hG)
  · exact completedEntire_real_ne_zero_of_not_Ioo h

/-! ## 5. Le bord du rectangle et l'intégrale de contour (forme de Mathlib) -/

/-- Bord du rectangle de sommets opposés `z` et `w` (côtés horizontaux et verticaux). -/
def rectBoundary (z w : ℂ) : Set ℂ :=
  {s | (s.im = z.im ∨ s.im = w.im) ∧ s.re ∈ Icc z.re w.re} ∪
    {s | (s.re = z.re ∨ s.re = w.re) ∧ s.im ∈ Icc z.im w.im}

/-- Intégrale de `f` sur le bord orienté du rectangle, dans la forme exacte des théorèmes de Cauchy de Mathlib
(`integral_boundary_rect_eq_zero_of_differentiableOn`). -/
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- **Contrôle de Cauchy** : `ξ₁` étant entière, son intégrale de bord sur tout rectangle est nulle (aucun pôle à
traiter sur le contour). -/
theorem rectBoundaryIntegral_completedEntire_eq_zero (z w : ℂ) :
    rectBoundaryIntegral completedEntire z w = 0 := by
  have h := integral_boundary_rect_eq_zero_of_differentiableOn completedEntire z w
    differentiable_completedEntire.differentiableOn
  simpa only [rectBoundaryIntegral, smul_eq_mul] using h

/-- Sur le bord du rectangle `[−1, 2] × [0, T]`, un point est : sur le segment réel, ou de hauteur `T`, ou sur un
côté vertical de partie réelle `−1` ou `2`. -/
theorem mem_rectBoundary_cases {T : ℝ} {s : ℂ} (hs : s ∈ rectBoundary (-1 : ℂ) (2 + T * I)) :
    s.im = 0 ∨ s.im = T ∨ ((s.re = -1 ∨ s.re = 2) ∧ 0 ≤ s.im ∧ s.im ≤ T) := by
  rcases hs with ⟨h, -⟩ | ⟨h, h'⟩
  · simp only [neg_im, one_im, neg_zero, add_im, im_ofNat, mul_im, ofReal_re, I_im, mul_one,
      ofReal_im, I_re, mul_zero, add_zero, zero_add] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · right; right
    simp only [neg_re, one_re, add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_zero, add_zero, neg_im, one_im, neg_zero, add_im, im_ofNat, mul_im, zero_add,
      mem_Icc] at h h'
    exact ⟨h, h'⟩

end RHV6Fresh

#print axioms RHV6Fresh.differentiable_completedEntire
#print axioms RHV6Fresh.completedEntire_eq
#print axioms RHV6Fresh.completedEntire_one_sub
#print axioms RHV6Fresh.completedEntire_eq_zero_iff
#print axioms RHV6Fresh.completedEntire_multiplicity
#print axioms RHV6Fresh.nontrivial_of_zero_im_pos
#print axioms RHV6Fresh.completedEntire_zero_openRect_iff
#print axioms RHV6Fresh.completedEntire_ne_zero_of_re_out
#print axioms RHV6Fresh.completedEntire_real_ne_zero_of_not_Ioo
#print axioms RHV6Fresh.completedEntire_real_ne_zero_of_zeta_ne_zero
#print axioms RHV6Fresh.rectBoundaryIntegral_completedEntire_eq_zero
#print axioms RHV6Fresh.mem_rectBoundary_cases
