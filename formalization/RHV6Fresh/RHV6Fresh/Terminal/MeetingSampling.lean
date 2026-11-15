/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.DominantExponent

/-!
# Le polynôme de fréquences le long des rencontres (module isolé, non importé par la chaîne)

Suite de `DominantExponent.lean`. Là, une famille finie à dominant STRICT avait une amplitude relative
non bornée aux rencontres. Ici, le cas d'égalité : plusieurs membres à la même position radiale
maximale. Deux indices distincts de même position radiale ont des hauteurs distinctes (ce sont des
nombres complexes distincts) ; leur somme est la puissance dominante multipliée par un polynôme
trigonométrique à fréquences distinctes, lu en `log x`.

Le compilé `trig_poly_not_tendsto_zero` (`FiniteRadialRigidity.lean`) dit qu'un tel polynôme ne tend
pas vers zéro quand la variable CONTINUE tend vers l'infini. La demande des premiers n'est lue qu'aux
rencontres. Ce qu'il faut est donc la même propriété LE LONG DES RENCONTRES : c'est l'hypothèse
nommée `MeetingsSampleFrequencies`. Elle n'est pas posée comme un fait : c'est une propriété de
répartition des premiers en échelle logarithmique (les rencontres échantillonnent assez finement les
battements), que ni la grammaire compilée des écarts (classes, alternance, bornes inférieures) ni le
postulat de Bertrand ne fournissent. E397 la mesure.

Faits compilés sous cette hypothèse nommée (et sous la demande bornée aux rencontres, nommée) :

* toute famille finie non vide dont la position radiale maximale dépasse un demi a une amplitude
  relative non bornée aux rencontres (`familyRelativeAmplitude_unbounded_of_sampling`) ;
* elle laisse hors d'elle un zéro strictement à droite de un demi
  (`exists_right_of_family_of_sampling`) ;
* **un zéro hors ligne n'est jamais en nombre fini** : s'il existe un zéro strictement à droite de un
  demi, il en existe une infinité (`infinite_right_of_sampling`) ; une arrivée basse en fournit un par
  son miroir (`infinite_right_of_low_of_sampling`).

Ce que cela n'établit pas : la contradiction. Une infinité de zéros à droite n'est pas exclue par ces
modules ; le reste d'une famille infinie n'est plus majoré par une somme finie de poids affaiblis.
C'est la frontière, nommée exactement : le prix d'un zéro hors ligne ne peut être payé que par une
infinité d'autres zéros hors ligne, et ce que paie une infinité n'est pas compilé.

Aucun axiome, aucun `sorry`.
-/

namespace RHV6Fresh

open Complex RHV3Lean Filter

/-! ## 1. La part d'un indice comme puissance fois coefficient fois caractère -/

/-- Coefficient d'un indice : son poids signé et son calage. -/
noncomputable def memberCoefficient (σ : ExplicitIndex) : ℂ :=
  -(zetaZeroMultiplicity (σ : ℂ) : ℂ) / ((‖(σ : ℂ)‖ * ‖(σ : ℂ) + 1‖ : ℝ) : ℂ) *
    Complex.exp (-(smoothingPhase σ : ℂ) * I)

/-- La part d'un indice : puissance de la position radiale, coefficient, caractère de la fréquence. -/
theorem residueTerm_decomp (σ : ExplicitIndex) {x : ℝ} (hx : 0 < x) :
    nontrivialZeroResidueTerm x σ =
      ((x ^ (σ : ℂ).re : ℝ) : ℂ) * memberCoefficient σ *
        Complex.exp (((σ : ℂ).im : ℂ) * I * (Real.log x : ℂ)) := by
  rw [residueTerm_eq_memberJoint σ hx]
  unfold memberJoint jointTerm memberCoefficient
  have h : Complex.exp ((((σ : ℂ).im * Real.log x - smoothingPhase σ : ℝ) : ℂ) * I) =
      Complex.exp (-(smoothingPhase σ : ℂ) * I) *
        Complex.exp (((σ : ℂ).im : ℂ) * I * (Real.log x : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h]
  push_cast
  ring

/-- Le polynôme de fréquences d'une famille : coefficients et caractères, sans la puissance. -/
noncomputable def topPolynomial (A : Finset ExplicitIndex) (x : ℝ) : ℂ :=
  ∑ σ ∈ A, memberCoefficient σ * Complex.exp (((σ : ℂ).im : ℂ) * I * (Real.log x : ℂ))

/-- Sur une famille de même position radiale `b`, la somme des parts est `x^b` fois le polynôme. -/
theorem top_sum_eq (A : Finset ExplicitIndex) (b : ℝ) (hA : ∀ σ ∈ A, (σ : ℂ).re = b) {x : ℝ}
    (hx : 0 < x) :
    ∑ σ ∈ A, nontrivialZeroResidueTerm x σ = ((x ^ b : ℝ) : ℂ) * topPolynomial A x := by
  unfold topPolynomial
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ hσ => ?_)
  rw [residueTerm_decomp σ hx, hA σ hσ, mul_assoc]

/-! ## 2. L'hypothèse nommée : les rencontres échantillonnent les fréquences -/

/-- **Hypothèse NOMMÉE** (jamais posée comme un fait) : pour toute famille finie non vide d'indices de
même position radiale, le polynôme de fréquences reste, le long des rencontres, au-dessus d'un seuil
positif infiniment souvent. Version « aux rencontres » du compilé `trig_poly_not_tendsto_zero`. -/
def MeetingsSampleFrequencies : Prop :=
  ∀ (A : Finset ExplicitIndex) (b : ℝ), A.Nonempty → (∀ σ ∈ A, (σ : ℂ).re = b) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧ ε ≤ ‖topPolynomial A (meetingPoint ⟨n⟩)‖

/-! ## 3. Minoration d'une famille par son sommet -/

open Classical in
/-- Minoration : la puissance maximale fois (le polynôme du sommet moins les autres poids affaiblis). -/
theorem familyRelative_ge_top (F : Finset ExplicitIndex) (b : ℝ) {x : ℝ} (hx : 0 < x) :
    x ^ (b - 1 / 2) *
        (‖topPolynomial (F.filter (fun σ : ExplicitIndex => (σ : ℂ).re = b)) x‖ -
          ∑ σ ∈ F.filter (fun σ : ExplicitIndex => ¬ (σ : ℂ).re = b), indexWeight σ * x ^ ((σ : ℂ).re - b)) ≤
      familyRelativeAmplitude F x := by
  set A := F.filter (fun σ : ExplicitIndex => (σ : ℂ).re = b) with hAdef
  set B := F.filter (fun σ : ExplicitIndex => ¬ (σ : ℂ).re = b) with hBdef
  have hsplit : familySum F x =
      ∑ σ ∈ A, nontrivialZeroResidueTerm x σ + ∑ σ ∈ B, nontrivialZeroResidueTerm x σ := by
    unfold familySum
    exact (Finset.sum_filter_add_sum_filter_not F _ _).symm
  have hA : ∑ σ ∈ A, nontrivialZeroResidueTerm x σ = ((x ^ b : ℝ) : ℂ) * topPolynomial A x :=
    top_sum_eq A b (fun σ hσ => (Finset.mem_filter.mp hσ).2) hx
  have hnA : ‖∑ σ ∈ A, nontrivialZeroResidueTerm x σ‖ = x ^ b * ‖topPolynomial A x‖ := by
    rw [hA, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)]
  have hnB : ‖∑ σ ∈ B, nontrivialZeroResidueTerm x σ‖ ≤ ∑ σ ∈ B, indexWeight σ * x ^ (σ : ℂ).re := by
    refine (norm_sum_le _ _).trans_eq ?_
    exact Finset.sum_congr rfl (fun σ _ => norm_residueTerm_eq σ hx)
  have hkey : x ^ b * ‖topPolynomial A x‖ - ∑ σ ∈ B, indexWeight σ * x ^ (σ : ℂ).re ≤
      ‖familySum F x‖ := by
    rw [hsplit]
    have := norm_sub_le (∑ σ ∈ A, nontrivialZeroResidueTerm x σ +
      ∑ σ ∈ B, nontrivialZeroResidueTerm x σ) (∑ σ ∈ B, nontrivialZeroResidueTerm x σ)
    rw [add_sub_cancel_right] at this
    linarith
  unfold familyRelativeAmplitude
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hx _)]
  refine le_trans (le_of_eq ?_) hkey
  have e1 : x ^ (b - 1 / 2) * x ^ (1 / 2 : ℝ) = x ^ b := by
    rw [← Real.rpow_add hx]; congr 1; ring
  calc x ^ (b - 1 / 2) * (‖topPolynomial A x‖ -
          ∑ σ ∈ B, indexWeight σ * x ^ ((σ : ℂ).re - b)) * x ^ (1 / 2 : ℝ)
      = x ^ b * (‖topPolynomial A x‖ - ∑ σ ∈ B, indexWeight σ * x ^ ((σ : ℂ).re - b)) := by
        rw [mul_comm _ (x ^ (1 / 2 : ℝ)), ← mul_assoc, mul_comm (x ^ (1 / 2 : ℝ)), e1]
    _ = x ^ b * ‖topPolynomial A x‖ - ∑ σ ∈ B, indexWeight σ * x ^ (σ : ℂ).re := by
        rw [mul_sub, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [mul_left_comm, ← Real.rpow_add hx]
        congr 2
        ring

/-! ## 4. Sous l'hypothèse nommée, toute famille au-dessus de un demi est non bornée -/

/-- **Sous l'hypothèse nommée** : une famille finie non vide dont la position radiale maximale dépasse
un demi a une amplitude relative non bornée aux rencontres. -/
theorem familyRelativeAmplitude_unbounded_of_sampling (hS : MeetingsSampleFrequencies)
    (F : Finset ExplicitIndex) (hF : F.Nonempty)
    (hβ : 1 / 2 < F.sup' hF (fun σ : ExplicitIndex => (σ : ℂ).re)) (c : ℝ) :
    ∃ I : PrimeGapInterval, c < familyRelativeAmplitude F (meetingPoint I) := by
  classical
  set b := F.sup' hF (fun σ : ExplicitIndex => (σ : ℂ).re) with hb
  set A := F.filter (fun σ : ExplicitIndex => (σ : ℂ).re = b) with hAdef
  set B := F.filter (fun σ : ExplicitIndex => ¬ (σ : ℂ).re = b) with hBdef
  -- le sommet est non vide
  obtain ⟨σ₁, hσ₁, hσ₁b⟩ := Finset.exists_mem_eq_sup' hF (fun σ : ExplicitIndex => (σ : ℂ).re)
  have hAne : A.Nonempty := ⟨σ₁, Finset.mem_filter.mpr ⟨hσ₁, hσ₁b.symm⟩⟩
  obtain ⟨ε, hε, hinf⟩ := hS A b hAne (fun σ hσ => (Finset.mem_filter.mp hσ).2)
  -- les rencontres tendent vers l'infini
  have hP : Tendsto (fun n : ℕ => meetingPoint ⟨n⟩) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp thm_primeAtRank_strictMono.tendsto_atTop).comp
      (tendsto_add_atTop_nat 1)
  -- les autres poids, affaiblis, tendent vers zéro
  have hsum : Tendsto (fun x : ℝ => ∑ σ ∈ B, indexWeight σ * x ^ ((σ : ℂ).re - b)) atTop (nhds 0) := by
    have h0 : Tendsto (fun x : ℝ => ∑ σ ∈ B, indexWeight σ * x ^ ((σ : ℂ).re - b)) atTop
        (nhds (∑ σ ∈ B, indexWeight σ * 0)) := by
      refine tendsto_finsetSum _ (fun σ hσ => ?_)
      have hmem := Finset.mem_filter.mp hσ
      have hle : (σ : ℂ).re ≤ b := Finset.le_sup' (fun σ : ExplicitIndex => (σ : ℂ).re) hmem.1
      have hlt : (σ : ℂ).re < b := lt_of_le_of_ne hle hmem.2
      have h := (tendsto_rpow_neg_atTop (y := b - (σ : ℂ).re) (by linarith)).const_mul (indexWeight σ)
      refine h.congr (fun x => ?_)
      congr 2
      ring
    simpa using h0
  have hpow : Tendsto (fun x : ℝ => x ^ (b - 1 / 2)) atTop atTop := tendsto_rpow_atTop (by linarith)
  have hev1 : ∀ᶠ n : ℕ in atTop,
      ∑ σ ∈ B, indexWeight σ * (meetingPoint ⟨n⟩) ^ ((σ : ℂ).re - b) ≤ ε / 2 :=
    (hsum.comp hP).eventually (Iic_mem_nhds (half_pos hε))
  have hev2 : ∀ᶠ n : ℕ in atTop, c < (meetingPoint ⟨n⟩) ^ (b - 1 / 2) * (ε / 2) :=
    ((hpow.comp hP).atTop_mul_const (half_pos hε)).eventually_gt_atTop c
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hev1.and hev2)
  obtain ⟨n, hn, hPn⟩ := hinf n₀
  obtain ⟨h1, h2⟩ := hn₀ n hn
  refine ⟨⟨n⟩, ?_⟩
  have hx : 0 < meetingPoint ⟨n⟩ := by linarith [one_lt_meetingPoint ⟨n⟩]
  have hlow := familyRelative_ge_top F b hx
  have hpos : 0 ≤ (meetingPoint ⟨n⟩) ^ (b - 1 / 2) := Real.rpow_nonneg hx.le _
  have h3 : (meetingPoint ⟨n⟩) ^ (b - 1 / 2) * (ε / 2) ≤
      (meetingPoint ⟨n⟩) ^ (b - 1 / 2) *
        (‖topPolynomial A (meetingPoint ⟨n⟩)‖ -
          ∑ σ ∈ B, indexWeight σ * (meetingPoint ⟨n⟩) ^ ((σ : ℂ).re - b)) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos
  linarith

/-- **Propagation sous l'hypothèse nommée** : avec la demande bornée aux rencontres (nommée), toute
famille finie non vide dont la position radiale maximale dépasse un demi laisse hors d'elle un zéro
strictement à droite de un demi. -/
theorem exists_right_of_family_of_sampling (hS : MeetingsSampleFrequencies)
    (hdem : ∃ C : ℝ, ∀ I : PrimeGapInterval, demandRelativeLevel (meetingPoint I) ≤ C)
    (F : Finset ExplicitIndex) (hF : F.Nonempty) (hβ : 1 / 2 < F.sup' hF (fun σ : ExplicitIndex => (σ : ℂ).re)) :
    ∃ ρ : ExplicitIndex, ρ ∉ F ∧ 1 / 2 < (ρ : ℂ).re := by
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hC⟩ := hdem
  obtain ⟨I, hI⟩ := familyRelativeAmplitude_unbounded_of_sampling hS F hF hβ (C + totalLineWeight)
  have h1 := restFamilyRelative_ge F (one_lt_meetingPoint I)
  have h2 := restFamilyRelative_le_total F (fun ρ hρ => hcon ρ hρ) (one_lt_meetingPoint I)
  have h3 := hC I
  linarith

/-- **Jamais en nombre fini** : sous les deux hypothèses nommées, s'il existe un zéro strictement à
droite de un demi, il en existe une infinité. -/
theorem infinite_right_of_sampling (hS : MeetingsSampleFrequencies)
    (hdem : ∃ C : ℝ, ∀ I : PrimeGapInterval, demandRelativeLevel (meetingPoint I) ≤ C)
    (hex : ∃ ρ : ExplicitIndex, 1 / 2 < (ρ : ℂ).re) :
    Set.Infinite {ρ : ExplicitIndex | 1 / 2 < (ρ : ℂ).re} := by
  classical
  intro hfin
  obtain ⟨ρ₀, hρ₀⟩ := hex
  set F := hfin.toFinset with hFdef
  have hρ₀F : ρ₀ ∈ F := hfin.mem_toFinset.mpr hρ₀
  have hF : F.Nonempty := ⟨ρ₀, hρ₀F⟩
  have hβ : 1 / 2 < F.sup' hF (fun σ : ExplicitIndex => (σ : ℂ).re) :=
    lt_of_lt_of_le hρ₀ (Finset.le_sup' (fun σ : ExplicitIndex => (σ : ℂ).re) hρ₀F)
  obtain ⟨ρ, hρF, hρ⟩ := exists_right_of_family_of_sampling hS hdem F hF hβ
  exact hρF (hfin.mem_toFinset.mpr hρ)

/-- Une arrivée basse fournit, par son miroir, un zéro strictement à droite : sous les deux
hypothèses nommées, elle n'est jamais accompagnée d'un nombre fini de zéros à droite. -/
theorem infinite_right_of_low_of_sampling (hS : MeetingsSampleFrequencies)
    (hdem : ∃ C : ℝ, ∀ I : PrimeGapInterval, demandRelativeLevel (meetingPoint I) ≤ C)
    (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2) :
    Set.Infinite {ρ : ExplicitIndex | 1 / 2 < (ρ : ℂ).re} := by
  refine infinite_right_of_sampling hS hdem ⟨memberIndex (mirrorMember l), ?_⟩
  change 1 / 2 < (zeroPoint (mirrorMember l)).re
  rw [zeroPoint_re, mirrorMember_radial]
  linarith

end RHV6Fresh
