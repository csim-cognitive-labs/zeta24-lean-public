/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MeetingSampling
import RHV6Fresh.Terminal.DemandLevelPremise
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Le sommet atteint : test de fermeture directe sur la frontière du Reste 1 (module isolé)

Solution 4 du maître §16.7 (libre, validée par l'auteur le 2026-10-29). Atouts utilisés : la somme totale
des poids est finie (`RemainderRegime.lean`), une famille finie au sommet est non bornée aux rencontres
sous l'hypothèse nommée d'échantillonnage (`MeetingSampling.lean`).

**Découverte en écrivant le module** : la « marge d'isolement » annoncée au maître §16.7 n'est pas
nécessaire. Si le sommet `b` des positions radiales est atteint par une famille finie `A` et que tout
autre indice est strictement en dessous de `b`, alors le reste de `A`, rapporté à `x^(b − 1/2)`, est une
somme de poids affaiblis `w_ρ · x^(re ρ − b)` dont chaque terme tend vers zéro et qui est dominée par la
somme finie des poids ; par convergence dominée (Tannery, `tendsto_tsum_of_dominated_convergence`) elle
tend vers zéro, sans marge uniforme. L'hypothèse structurelle nommée se réduit donc à :

* **Sommet atteint** (`SummitAttained`) : s'il existe un indice strictement à droite de un demi, la
  position radiale maximale est atteinte, par un nombre fini d'indices, tout autre indice étant
  strictement en dessous.

Résultat compilé : sous l'hypothèse de clôture (demande bornée aux rencontres), sous l'échantillonnage,
et sous « sommet atteint », aucun indice n'est strictement à droite de un demi, donc, par le miroir, tout
zéro est sur la ligne (`riemannHypothesis_of_summitAttained`), et la prémisse unique de la chaîne en
découle (`expectedFrequencyRises_of_summitAttained`).

**Test de fermeture directe (résultat, dit avant d'écrire et confirmé).** « Sommet atteint » n'est pas
dérivable des faits compilés : la base compilée ne sait des positions radiales que (i) qu'elles sont dans
la bande ouverte entre zéro et un, et (ii) que les indices de hauteur bornée sont en nombre fini
(`explicitIndex_locallyFinite`). Ni l'une ni l'autre n'interdit une suite d'indices, de hauteurs
croissantes, dont les positions montent vers un sommet jamais atteint, ni un nombre infini d'indices sur
une même verticale. C'est l'obstruction de Landau notée le 2026-10-27 : rien de compilé ne parle de
l'ENSEMBLE des positions radiales, seulement de chaque zéro et de chaque famille finie. Les deux faits
partiels compilables sont écrits ici (`positions_bddAbove`, `topLine_finite_in_band`) ; le pas manquant
est exactement « le supremum est atteint par un nombre fini d'indices ».

Ce que le module ferme : la frontière du Reste 1 est réduite à une seule hypothèse structurelle nommée,
plus faible que celle annoncée (sans marge), vraie sous RH (`summitAttained_of_riemannHypothesis`, par
vacuité), jamais posée comme démontrée. Aucun axiome, aucun `sorry`. La chaîne est intacte.
-/

namespace RHV6Fresh

open Complex RHV3Lean Filter Topology

/-! ## 1. L'hypothèse structurelle nommée -/

/-- **Sommet atteint (hypothèse nommée, jamais posée)** : s'il existe un indice strictement à droite de un
demi, alors il existe une famille finie non vide `A`, toute à la même position radiale `b`, telle que tout
indice hors de `A` est strictement en dessous de `b`. -/
def SummitAttained : Prop :=
  (∃ ρ : ExplicitIndex, 1 / 2 < (ρ : ℂ).re) →
    ∃ (A : Finset ExplicitIndex) (b : ℝ), A.Nonempty ∧ (∀ σ ∈ A, (σ : ℂ).re = b) ∧
      ∀ ρ : ExplicitIndex, ρ ∉ A → (ρ : ℂ).re < b

/-- Version avec marge, annoncée au maître §16.7 : elle entraîne la version sans marge. -/
def SummitAttainedIsolated : Prop :=
  (∃ ρ : ExplicitIndex, 1 / 2 < (ρ : ℂ).re) →
    ∃ (A : Finset ExplicitIndex) (b θ : ℝ), A.Nonempty ∧ (∀ σ ∈ A, (σ : ℂ).re = b) ∧
      1 / 2 ≤ θ ∧ θ < b ∧ ∀ ρ : ExplicitIndex, ρ ∉ A → (ρ : ℂ).re ≤ θ

theorem summitAttained_of_isolated (h : SummitAttainedIsolated) : SummitAttained := by
  intro hex
  obtain ⟨A, b, θ, hA, hAb, _, hθb, hrest⟩ := h hex
  exact ⟨A, b, hA, hAb, fun ρ hρ => lt_of_le_of_lt (hrest ρ hρ) hθb⟩

/-- Sous RH, aucun indice n'est à droite : l'hypothèse est vraie par vacuité. Elle n'est donc pas plus
forte que la cible. -/
theorem summitAttained_of_riemannHypothesis (h : RiemannHypothesis) : SummitAttained := by
  rintro ⟨ρ, hρ⟩
  have hre : (ρ : ℂ).re = 1 / 2 := h (ρ : ℂ) ρ.property.1 ρ.property.2.1 ρ.property.2.2
  exact ((ne_of_gt hρ) hre).elim

/-! ## 2. Le reste du sommet, rapporté au sommet, tend vers zéro (convergence dominée) -/

/-- Rapport du reste au sommet : somme, hors de la famille, des poids affaiblis par `x^(re ρ − b)`. -/
noncomputable def restRatio (A : Finset ExplicitIndex) (b : ℝ) (x : ℝ) : ℝ :=
  ∑' ρ : ((A : Set ExplicitIndex)ᶜ : Set ExplicitIndex), indexWeight ρ * x ^ ((ρ : ℂ).re - b)

/-- Hors de la famille et sous le sommet, chaque poids affaibli est au plus le poids, pour `x ≥ 1`. -/
theorem weakened_le_weight (A : Finset ExplicitIndex) (b : ℝ)
    (hrest : ∀ ρ : ExplicitIndex, ρ ∉ A → (ρ : ℂ).re ≤ b) {x : ℝ} (hx : 1 ≤ x)
    (ρ : ((A : Set ExplicitIndex)ᶜ : Set ExplicitIndex)) :
    indexWeight ρ * x ^ ((ρ : ℂ).re - b) ≤ indexWeight ρ := by
  have hle : (ρ : ℂ).re - b ≤ 0 := by
    have := hrest ρ (fun hρ => ρ.2 (Finset.mem_coe.mpr hρ))
    linarith
  exact mul_le_of_le_one_right (indexWeight_nonneg ρ) (Real.rpow_le_one_of_one_le_of_nonpos hx hle)

theorem weakened_summable (A : Finset ExplicitIndex) (b : ℝ)
    (hrest : ∀ ρ : ExplicitIndex, ρ ∉ A → (ρ : ℂ).re ≤ b) {x : ℝ} (hx : 1 ≤ x) :
    Summable fun ρ : ((A : Set ExplicitIndex)ᶜ : Set ExplicitIndex) =>
      indexWeight ρ * x ^ ((ρ : ℂ).re - b) :=
  Summable.of_nonneg_of_le
    (fun ρ => mul_nonneg (indexWeight_nonneg ρ) (Real.rpow_nonneg (by linarith) _))
    (weakened_le_weight A b hrest hx) (indexWeight_summable.subtype _)

/-- Le reste de la famille, en amplitude relative, est au plus `x^(b − 1/2)` fois le rapport. -/
theorem restFamilyRelative_le_ratio (A : Finset ExplicitIndex) (b : ℝ)
    (hrest : ∀ ρ : ExplicitIndex, ρ ∉ A → (ρ : ℂ).re ≤ b) {x : ℝ} (hx : 1 < x) :
    restFamilyRelative A x ≤ x ^ (b - 1 / 2) * restRatio A b x := by
  have hx0 : (0 : ℝ) < x := by linarith
  unfold restFamilyRelative restOfFamily restRatio
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)]
  have hs := (summable_norm_iff.mpr (nontrivial_zero_residue_series_summable hx)).subtype
    (· ∈ ((A : Set ExplicitIndex)ᶜ : Set ExplicitIndex))
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  have heq : ∀ ρ : ((A : Set ExplicitIndex)ᶜ : Set ExplicitIndex),
      ‖nontrivialZeroResidueTerm x ρ‖ = x ^ b * (indexWeight ρ * x ^ ((ρ : ℂ).re - b)) := by
    intro ρ
    rw [norm_residueTerm_eq ρ hx0, mul_left_comm, ← Real.rpow_add hx0]
    congr 2
    ring
  rw [tsum_congr heq, tsum_mul_left]
  have e1 : x ^ (b - 1 / 2) * x ^ (1 / 2 : ℝ) = x ^ b := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  rw [mul_comm (x ^ (b - 1 / 2)), mul_assoc, e1, mul_comm]

/-- **Convergence dominée** : sous le sommet, le rapport du reste tend vers zéro quand `x` tend vers
l'infini — sans marge uniforme. -/
theorem restRatio_tendsto_zero (A : Finset ExplicitIndex) (b : ℝ)
    (hrest : ∀ ρ : ExplicitIndex, ρ ∉ A → (ρ : ℂ).re < b) :
    Tendsto (fun x : ℝ => restRatio A b x) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (x : ℝ) (ρ : ((A : Set ExplicitIndex)ᶜ : Set ExplicitIndex)) =>
      indexWeight ρ * x ^ ((ρ : ℂ).re - b))
    (g := fun _ => (0 : ℝ))
    (bound := fun ρ : ((A : Set ExplicitIndex)ᶜ : Set ExplicitIndex) => indexWeight ρ)
    (indexWeight_summable.subtype _)
    (fun ρ => by
      have hlt : (ρ : ℂ).re < b := hrest ρ (fun hρ => ρ.2 (Finset.mem_coe.mpr hρ))
      have h := (tendsto_rpow_neg_atTop (y := b - (ρ : ℂ).re) (by linarith)).const_mul (indexWeight ρ)
      rw [mul_zero] at h
      refine h.congr (fun x => ?_)
      congr 2
      ring)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx ρ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (indexWeight_nonneg ρ)
        (Real.rpow_nonneg (by linarith) _))]
      exact weakened_le_weight A b (fun ρ hρ => (hrest ρ hρ).le) hx ρ)
  simpa [restRatio] using h

/-! ## 3. Sous le sommet atteint, la demande n'est pas bornée aux rencontres -/

/-- **Théorème** : sous l'échantillonnage (nommé), une famille finie au sommet `b > 1/2`, tout autre
indice strictement en dessous, rend le niveau de la demande non borné aux rencontres. -/
theorem demand_unbounded_of_summit (hS : MeetingsSampleFrequencies) (A : Finset ExplicitIndex)
    (b : ℝ) (hA : A.Nonempty) (hAb : ∀ σ ∈ A, (σ : ℂ).re = b) (hb : 1 / 2 < b)
    (hrest : ∀ ρ : ExplicitIndex, ρ ∉ A → (ρ : ℂ).re < b) (c : ℝ) :
    ∃ I : PrimeGapInterval, c < demandRelativeLevel (meetingPoint I) := by
  classical
  obtain ⟨ε, hε, hinf⟩ := hS A b hA hAb
  have hP : Tendsto (fun n : ℕ => meetingPoint ⟨n⟩) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp thm_primeAtRank_strictMono.tendsto_atTop).comp
      (tendsto_add_atTop_nat 1)
  have hev1 : ∀ᶠ n : ℕ in atTop, restRatio A b (meetingPoint ⟨n⟩) ≤ ε / 2 :=
    ((restRatio_tendsto_zero A b hrest).comp hP).eventually (Iic_mem_nhds (half_pos hε))
  have hpow : Tendsto (fun x : ℝ => x ^ (b - 1 / 2)) atTop atTop := tendsto_rpow_atTop (by linarith)
  have hev2 : ∀ᶠ n : ℕ in atTop, c < (meetingPoint ⟨n⟩) ^ (b - 1 / 2) * (ε / 2) :=
    ((hpow.comp hP).atTop_mul_const (half_pos hε)).eventually_gt_atTop c
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hev1.and hev2)
  obtain ⟨n, hn, hPn⟩ := hinf n₀
  obtain ⟨h1, h2⟩ := hn₀ n hn
  refine ⟨⟨n⟩, ?_⟩
  have hx1 : 1 < meetingPoint ⟨n⟩ := one_lt_meetingPoint ⟨n⟩
  have hx : 0 < meetingPoint ⟨n⟩ := by linarith
  have hfam : (meetingPoint ⟨n⟩) ^ (b - 1 / 2) * ‖topPolynomial A (meetingPoint ⟨n⟩)‖ ≤
      familyRelativeAmplitude A (meetingPoint ⟨n⟩) := by
    have h := familyRelative_ge_top A b hx
    have hfilt : A.filter (fun σ : ExplicitIndex => (σ : ℂ).re = b) = A :=
      Finset.filter_true_of_mem hAb
    have hfilt' : A.filter (fun σ : ExplicitIndex => ¬ (σ : ℂ).re = b) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun σ hσ h' => h' (hAb σ hσ))
    rw [hfilt, hfilt', Finset.sum_empty, sub_zero] at h
    exact h
  have h3 := restFamilyRelative_ge A hx1
  have h4 := restFamilyRelative_le_ratio A b (fun ρ hρ => (hrest ρ hρ).le) hx1
  have hpos : 0 ≤ (meetingPoint ⟨n⟩) ^ (b - 1 / 2) := Real.rpow_nonneg hx.le _
  have h5 : (meetingPoint ⟨n⟩) ^ (b - 1 / 2) * (ε / 2) ≤
      (meetingPoint ⟨n⟩) ^ (b - 1 / 2) *
        (‖topPolynomial A (meetingPoint ⟨n⟩)‖ - restRatio A b (meetingPoint ⟨n⟩)) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos
  rw [mul_sub] at h5
  linarith

/-- **Aucun indice à droite** : sous l'hypothèse de clôture, l'échantillonnage et le sommet atteint. -/
theorem no_right_of_summitAttained (hS : MeetingsSampleFrequencies) (hdem : DemandBoundedAtMeetings)
    (hsum : SummitAttained) : ∀ ρ : ExplicitIndex, (ρ : ℂ).re ≤ 1 / 2 := by
  intro ρ
  by_contra hlt
  push Not at hlt
  obtain ⟨A, b, hA, hAb, hrest⟩ := hsum ⟨ρ, hlt⟩
  have hb : 1 / 2 < b := by
    by_cases hρA : ρ ∈ A
    · exact (hAb ρ hρA) ▸ hlt
    · exact hlt.trans (hrest ρ hρA)
  obtain ⟨C, hC⟩ := hdem
  obtain ⟨I, hI⟩ := demand_unbounded_of_summit hS A b hA hAb hb hrest C
  linarith [hC I]

/-- **Tout zéro est sur la ligne** : par le miroir, un membre sous un demi aurait son miroir à droite. -/
theorem riemannHypothesis_of_summitAttained (hS : MeetingsSampleFrequencies)
    (hdem : DemandBoundedAtMeetings) (hsum : SummitAttained) : RiemannHypothesis := by
  refine riemannHypothesis_of_noLowerSide fun l hlow => ?_
  have h := no_right_of_summitAttained hS hdem hsum (memberIndex (mirrorMember l))
  change (zeroPoint (mirrorMember l)).re ≤ 1 / 2 at h
  rw [zeroPoint_re, mirrorMember_radial] at h
  linarith

/-- La prémisse unique de la chaîne, sous les trois hypothèses nommées. -/
theorem expectedFrequencyRises_of_summitAttained (hS : MeetingsSampleFrequencies)
    (hdem : DemandBoundedAtMeetings) (hsum : SummitAttained) : ExpectedFrequencyRises :=
  expectedFrequencyRises_iff_riemannHypothesis.mpr (riemannHypothesis_of_summitAttained hS hdem hsum)

/-- **Le Reste 1 réduit au sommet** : sous l'échantillonnage et le sommet atteint, « le reste n'est jamais
à droite » (Reste 1) découle de l'hypothèse de clôture seule. -/
theorem restNeverRight_of_summitAttained (hS : MeetingsSampleFrequencies)
    (hdem : DemandBoundedAtMeetings) (hsum : SummitAttained) : RestNeverRight :=
  fun l ρ _ => no_right_of_summitAttained hS hdem hsum ρ

/-! ## 4. Test de fermeture directe : les deux faits partiels compilables, et le pas manquant -/

/-- Les positions radiales sont majorées (par un) : le supremum existe. -/
theorem positions_bddAbove : BddAbove (Set.range fun ρ : ExplicitIndex => (ρ : ℂ).re) :=
  ⟨1, by rintro _ ⟨ρ, rfl⟩; exact explicitIndex_re_le_one ρ⟩

/-- Sur toute verticale, les indices de hauteur bornée sont en nombre fini. -/
theorem topLine_finite_in_band (b R : ℝ) :
    {ρ : ExplicitIndex | (ρ : ℂ).re = b ∧ ‖(ρ : ℂ)‖ ≤ R}.Finite :=
  (explicitIndex_locallyFinite R).subset fun _ h => h.2

/-- **Le pas manquant, écrit** : « sommet atteint » équivaut à la conjonction de deux énoncés sur
l'ENSEMBLE des positions radiales — le supremum des positions à droite est atteint, et la verticale du
supremum ne porte qu'un nombre fini d'indices. Aucun des deux n'est dérivable de `positions_bddAbove` ni
de `topLine_finite_in_band` : ils parlent de toutes les hauteurs à la fois. -/
theorem summitAttained_iff :
    SummitAttained ↔
      ((∃ ρ : ExplicitIndex, 1 / 2 < (ρ : ℂ).re) →
        ∃ b : ℝ, (∃ ρ : ExplicitIndex, (ρ : ℂ).re = b) ∧ (∀ ρ : ExplicitIndex, (ρ : ℂ).re ≤ b) ∧
          {ρ : ExplicitIndex | (ρ : ℂ).re = b}.Finite) := by
  classical
  constructor
  · intro h hex
    obtain ⟨A, b, hA, hAb, hrest⟩ := h hex
    obtain ⟨σ, hσ⟩ := hA
    refine ⟨b, ⟨σ, hAb σ hσ⟩, fun ρ => ?_, (A.finite_toSet.subset fun ρ hρ => ?_)⟩
    · by_cases hρA : ρ ∈ A
      · exact (hAb ρ hρA).le
      · exact (hrest ρ hρA).le
    · by_contra hρA
      exact (ne_of_lt (hrest ρ hρA)) hρ
  · intro h hex
    obtain ⟨b, ⟨σ, hσ⟩, hle, hfin⟩ := h hex
    refine ⟨hfin.toFinset, b, ⟨σ, hfin.mem_toFinset.mpr hσ⟩,
      fun ρ hρ => hfin.mem_toFinset.mp hρ, fun ρ hρ => ?_⟩
    exact lt_of_le_of_ne (hle ρ) (fun h' => hρ (hfin.mem_toFinset.mpr h'))

end RHV6Fresh
