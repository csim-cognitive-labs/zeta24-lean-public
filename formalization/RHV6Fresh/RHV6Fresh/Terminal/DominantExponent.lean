/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RemainderRegime

/-!
# L'exposant dominant d'une famille finie (module isolé, non importé par la chaîne)

Suite de `TotalityPays.lean` (le prix d'un couple) et de `RemainderRegime.lean` (ce que la ligne peut
payer). Ici, le couple est remplacé par une famille finie quelconque d'indices qui possède un membre
STRICTEMENT dominant, c'est-à-dire strictement à droite de tous les autres membres de la famille et
strictement à droite de un demi.

Faits compilés, sans prémisse :

* la demande est la famille plus son reste (`remainder_eq_family_add_rest`) ;
* l'amplitude relative de la famille vaut au moins celle du dominant moins celles des autres
  (`familyRelative_ge_dominant`) ;
* **exposant dominant** : l'amplitude relative d'une famille à dominant strict n'est bornée à aucune
  rencontre (`familyRelativeAmplitude_unbounded_of_dominant`) ;
* le reste de la famille, s'il ne contient aucun zéro strictement à droite de un demi, est borné par
  la somme totale des poids (`restFamilyRelative_le_total`) ;
* **propagation par famille** : sous demande bornée aux rencontres (hypothèse nommée), toute famille
  finie à dominant strict laisse hors d'elle un zéro strictement à droite de un demi
  (`exists_right_of_dominant_of_bounded_demand`).

Ce que ce module n'établit pas, et pourquoi : le cas d'ÉGALITÉ, deux membres ou plus de la famille
partageant la position radiale maximale à des fréquences distinctes. L'amplitude relative de la
famille est alors la puissance dominante multipliée par le module d'un polynôme exponentiel à
fréquences distinctes, lu aux seules rencontres ; dire qu'il ne tend pas vers zéro le long des
rencontres demande une propriété de répartition des premiers en échelle logarithmique (densité des
rencontres devant la période de battement), que ni la grammaire compilée des écarts (bornes
inférieures et classes) ni le postulat de Bertrand (rapport de deux premiers consécutifs au plus
deux) ne fournissent. Ce point n'est pas posé en hypothèse ici ; il est nommé comme la frontière.

Aucun axiome, aucun `sorry`.
-/

namespace RHV6Fresh

open Complex RHV3Lean

/-! ## 1. Famille, reste de la famille, bilan -/

/-- Le reste d'une famille finie : la somme des parts de tous les indices hors de la famille. -/
noncomputable def restOfFamily (F : Finset ExplicitIndex) (x : ℝ) : ℂ :=
  ∑' ρ : ((F : Set ExplicitIndex)ᶜ : Set ExplicitIndex), nontrivialZeroResidueTerm x ρ

/-- Bilan : au-delà de un, la demande est la famille plus son reste. -/
theorem remainder_eq_family_add_rest (F : Finset ExplicitIndex) {x : ℝ} (hx : 1 < x) :
    smoothedRemainder x = familySum F x + restOfFamily F x := by
  rw [smoothedRemainder_eq_tsum_residueTerm hx,
    ← (nontrivial_zero_residue_series_summable hx).sum_add_tsum_compl (s := F)]
  rfl

/-- Amplitude relative d'une famille finie. -/
noncomputable def familyRelativeAmplitude (F : Finset ExplicitIndex) (x : ℝ) : ℝ :=
  ‖familySum F x‖ / x ^ (1 / 2 : ℝ)

/-- Amplitude relative du reste d'une famille finie. -/
noncomputable def restFamilyRelative (F : Finset ExplicitIndex) (x : ℝ) : ℝ :=
  ‖restOfFamily F x‖ / x ^ (1 / 2 : ℝ)

/-- Le reste d'une famille paie au moins la famille moins la demande, en amplitude relative. -/
theorem restFamilyRelative_ge (F : Finset ExplicitIndex) {x : ℝ} (hx : 1 < x) :
    familyRelativeAmplitude F x - demandRelativeLevel x ≤ restFamilyRelative F x := by
  have h1 : ‖familySum F x‖ - ‖smoothedRemainder x‖ ≤ ‖restOfFamily F x‖ := by
    have hb := remainder_eq_family_add_rest F hx
    have h2 : restOfFamily F x = smoothedRemainder x - familySum F x := by rw [hb]; ring
    rw [h2]
    have := norm_sub_norm_le (familySum F x) (smoothedRemainder x)
    rw [norm_sub_rev] at this
    exact this
  unfold familyRelativeAmplitude demandRelativeLevel restFamilyRelative
  rw [← sub_div]
  exact div_le_div_of_nonneg_right h1 (Real.rpow_pos_of_pos (by linarith) _).le

/-! ## 2. Dominance stricte -/

/-- Un membre `σ₀` de `F` est strictement dominant : strictement à droite de tout autre membre. -/
def StrictlyDominant (F : Finset ExplicitIndex) (σ₀ : ExplicitIndex) : Prop :=
  σ₀ ∈ F ∧ ∀ σ ∈ F, σ ≠ σ₀ → (σ : ℂ).re < (σ₀ : ℂ).re

open Classical in
/-- L'amplitude relative de la famille vaut au moins celle du dominant moins la somme de celles des
autres membres. -/
theorem familyRelative_ge_dominant (F : Finset ExplicitIndex) (σ₀ : ExplicitIndex) (h0 : σ₀ ∈ F)
    {x : ℝ} (hx : 0 < x) :
    indexWeight σ₀ * x ^ ((σ₀ : ℂ).re - 1 / 2) -
        ∑ σ ∈ F.erase σ₀, indexWeight σ * x ^ ((σ : ℂ).re - 1 / 2) ≤
      familyRelativeAmplitude F x := by
  have hsplit : familySum F x =
      nontrivialZeroResidueTerm x σ₀ + ∑ σ ∈ F.erase σ₀, nontrivialZeroResidueTerm x σ := by
    unfold familySum
    exact (Finset.add_sum_erase F _ h0).symm
  have hA : ‖nontrivialZeroResidueTerm x σ₀‖ - ‖∑ σ ∈ F.erase σ₀, nontrivialZeroResidueTerm x σ‖ ≤
      ‖familySum F x‖ := by
    rw [hsplit]
    have := norm_sub_le (nontrivialZeroResidueTerm x σ₀ +
      ∑ σ ∈ F.erase σ₀, nontrivialZeroResidueTerm x σ) (∑ σ ∈ F.erase σ₀, nontrivialZeroResidueTerm x σ)
    rw [add_sub_cancel_right] at this
    linarith
  have hB : ‖∑ σ ∈ F.erase σ₀, nontrivialZeroResidueTerm x σ‖ ≤
      ∑ σ ∈ F.erase σ₀, indexWeight σ * x ^ (σ : ℂ).re := by
    refine (norm_sum_le _ _).trans_eq ?_
    exact Finset.sum_congr rfl (fun σ _ => norm_residueTerm_eq σ hx)
  have hC : indexWeight σ₀ * x ^ (σ₀ : ℂ).re - ∑ σ ∈ F.erase σ₀, indexWeight σ * x ^ (σ : ℂ).re ≤
      ‖familySum F x‖ := by
    rw [← norm_residueTerm_eq σ₀ hx]; linarith
  unfold familyRelativeAmplitude
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hx _)]
  refine le_trans (le_of_eq ?_) hC
  rw [sub_mul, Finset.sum_mul]
  congr 1
  · rw [mul_assoc, ← Real.rpow_add hx, sub_add_cancel]
  · exact Finset.sum_congr rfl (fun σ _ => by rw [mul_assoc, ← Real.rpow_add hx, sub_add_cancel])

/-- Forme produit de la minoration : la puissance dominante multipliée par le poids dominant moins
les autres poids affaiblis par des puissances d'exposant strictement négatif. -/
theorem dominant_lower_eq (F : Finset ExplicitIndex) (σ₀ : ExplicitIndex) {x : ℝ} (hx : 0 < x) :
    indexWeight σ₀ * x ^ ((σ₀ : ℂ).re - 1 / 2) -
        ∑ σ ∈ F.erase σ₀, indexWeight σ * x ^ ((σ : ℂ).re - 1 / 2) =
      x ^ ((σ₀ : ℂ).re - 1 / 2) *
        (indexWeight σ₀ - ∑ σ ∈ F.erase σ₀, indexWeight σ * x ^ ((σ : ℂ).re - (σ₀ : ℂ).re)) := by
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [mul_left_comm, ← Real.rpow_add hx]
    congr 2
    ring

/-- **Exposant dominant** : l'amplitude relative d'une famille à dominant strict, strictement à droite
de un demi, n'est bornée à aucune rencontre. -/
theorem familyRelativeAmplitude_unbounded_of_dominant (F : Finset ExplicitIndex) (σ₀ : ExplicitIndex)
    (hdom : StrictlyDominant F σ₀) (hβ : 1 / 2 < (σ₀ : ℂ).re) (c : ℝ) :
    ∃ I : PrimeGapInterval, c < familyRelativeAmplitude F (meetingPoint I) := by
  classical
  have hK0 : 0 < indexWeight σ₀ := div_pos (by exact_mod_cast zetaZeroMultiplicity_pos σ₀.property.1)
    (indexDenominator_pos σ₀)
  -- la parenthèse tend vers le poids dominant
  have hbr : Filter.Tendsto
      (fun x : ℝ => indexWeight σ₀ -
        ∑ σ ∈ F.erase σ₀, indexWeight σ * x ^ ((σ : ℂ).re - (σ₀ : ℂ).re))
      Filter.atTop (nhds (indexWeight σ₀)) := by
    have hsum : Filter.Tendsto
        (fun x : ℝ => ∑ σ ∈ F.erase σ₀, indexWeight σ * x ^ ((σ : ℂ).re - (σ₀ : ℂ).re))
        Filter.atTop (nhds (∑ σ ∈ F.erase σ₀, indexWeight σ * 0)) := by
      refine tendsto_finsetSum _ (fun σ hσ => ?_)
      have hlt : (σ : ℂ).re < (σ₀ : ℂ).re :=
        hdom.2 σ (Finset.mem_of_mem_erase hσ) (Finset.ne_of_mem_erase hσ)
      have h := (tendsto_rpow_neg_atTop (y := (σ₀ : ℂ).re - (σ : ℂ).re) (by linarith)).const_mul
        (indexWeight σ)
      refine h.congr (fun x => ?_)
      congr 2
      ring
    simp only [mul_zero, Finset.sum_const_zero] at hsum
    simpa using hsum.const_sub (indexWeight σ₀)
  have hpow : Filter.Tendsto (fun x : ℝ => x ^ ((σ₀ : ℂ).re - 1 / 2)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by linarith)
  have hprod := hpow.atTop_mul_pos hK0 hbr
  -- les rencontres tendent vers l'infini
  have hP : Filter.Tendsto (fun n : ℕ => (fnPrimeAtRank (n + 1) : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop.comp thm_primeAtRank_strictMono.tendsto_atTop).comp
      (Filter.tendsto_add_atTop_nat 1)
  obtain ⟨n, hn⟩ := ((hprod.comp hP).eventually_gt_atTop c).exists
  refine ⟨⟨n⟩, ?_⟩
  have hx : 0 < meetingPoint ⟨n⟩ := by linarith [one_lt_meetingPoint ⟨n⟩]
  have hmeet : meetingPoint ⟨n⟩ = (fnPrimeAtRank (n + 1) : ℝ) := rfl
  have h1 := familyRelative_ge_dominant F σ₀ hdom.1 hx
  rw [dominant_lower_eq F σ₀ hx] at h1
  have h2 : c < meetingPoint ⟨n⟩ ^ ((σ₀ : ℂ).re - 1 / 2) *
      (indexWeight σ₀ - ∑ σ ∈ F.erase σ₀,
        indexWeight σ * meetingPoint ⟨n⟩ ^ ((σ : ℂ).re - (σ₀ : ℂ).re)) := by
    rw [hmeet]; exact hn
  linarith

/-! ## 3. Le reste d'une famille, s'il n'est pas à droite, est borné -/

/-- Si aucun indice hors de la famille n'est strictement à droite de un demi, le reste de la famille
est borné par la somme totale des poids. -/
theorem restFamilyRelative_le_total (F : Finset ExplicitIndex)
    (h : ∀ ρ : ExplicitIndex, ρ ∉ F → (ρ : ℂ).re ≤ 1 / 2) {x : ℝ} (hx : 1 < x) :
    restFamilyRelative F x ≤ totalLineWeight := by
  have hx0 : (0 : ℝ) < x := by linarith
  unfold restFamilyRelative restOfFamily
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)]
  have hs := (summable_norm_iff.mpr (nontrivial_zero_residue_series_summable hx)).subtype
    (· ∈ ((F : Set ExplicitIndex)ᶜ : Set ExplicitIndex))
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  have hle : ∀ ρ : ((F : Set ExplicitIndex)ᶜ : Set ExplicitIndex),
      ‖nontrivialZeroResidueTerm x ρ‖ ≤ indexWeight ρ * x ^ (1 / 2 : ℝ) := by
    intro ρ
    rw [norm_residueTerm_eq ρ hx0]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx.le (h ρ (fun hρ => ρ.2 (Finset.mem_coe.mpr hρ))))
      (indexWeight_nonneg ρ)
  calc ∑' ρ : ((F : Set ExplicitIndex)ᶜ : Set ExplicitIndex), ‖nontrivialZeroResidueTerm x ρ‖
      ≤ ∑' ρ : ((F : Set ExplicitIndex)ᶜ : Set ExplicitIndex), indexWeight ρ * x ^ (1 / 2 : ℝ) :=
        Summable.tsum_le_tsum hle hs ((indexWeight_summable.subtype _).mul_right _)
    _ = (∑' ρ : ((F : Set ExplicitIndex)ᶜ : Set ExplicitIndex), indexWeight ρ) * x ^ (1 / 2 : ℝ) :=
        tsum_mul_right
    _ ≤ totalLineWeight * x ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (tsum_indexWeight_subset_le _) (Real.rpow_nonneg hx0.le _)

/-! ## 4. Propagation par famille -/

/-- **Propagation par famille** : sous demande bornée aux rencontres (hypothèse nommée), toute famille
finie à dominant strict, strictement à droite de un demi, laisse hors d'elle un zéro strictement à
droite de un demi. -/
theorem exists_right_of_dominant_of_bounded_demand (F : Finset ExplicitIndex) (σ₀ : ExplicitIndex)
    (hdom : StrictlyDominant F σ₀) (hβ : 1 / 2 < (σ₀ : ℂ).re)
    (hdem : ∃ C : ℝ, ∀ I : PrimeGapInterval, demandRelativeLevel (meetingPoint I) ≤ C) :
    ∃ ρ : ExplicitIndex, ρ ∉ F ∧ 1 / 2 < (ρ : ℂ).re := by
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hC⟩ := hdem
  obtain ⟨I, hI⟩ := familyRelativeAmplitude_unbounded_of_dominant F σ₀ hdom hβ (C + totalLineWeight)
  have h1 := restFamilyRelative_ge F (one_lt_meetingPoint I)
  have h2 := restFamilyRelative_le_total F (fun ρ hρ => hcon ρ hρ) (one_lt_meetingPoint I)
  have h3 := hC I
  linarith

end RHV6Fresh
