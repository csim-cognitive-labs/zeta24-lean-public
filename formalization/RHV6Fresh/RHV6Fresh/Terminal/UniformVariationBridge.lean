/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MeetingsBridge

/-!
# Le pont des rencontres sous sa forme la plus faible : la variation uniforme dans les écarts
# (module isolé)

Élément intégré depuis l'audit de causalité remis par l'auteur le 2026-10-29 (flèche 11) : « la véritable
obligation de la solution 1 est la borne uniforme, sur tous les écarts, de la variation du niveau de la
demande entre un point de l'écart et la rencontre ; cette formulation est plus précise que “pente bornée”
car elle tient compte de la longueur réelle des écarts ».

**Ce que fait ce module.** Il nomme cette obligation (`UniformVariationAtGaps`) et établit :

* elle suffit au pont : demande bornée aux rencontres et variation uniforme donnent la demande bornée en
  tout point, donc RH (`demandBoundedEverywhere_of_meetings_of_variation`) ;
* elle est NÉCESSAIRE : la demande bornée partout l'entraîne (`uniformVariation_of_demandBoundedEverywhere`),
  d'où l'équivalence `DemandBoundedEverywhere ↔ DemandBoundedAtMeetings ∧ UniformVariationAtGaps`, et la
  prémisse unique de la chaîne équivaut à la même conjonction. C'est l'équivalence que le maître §17.1
  disait absente pour `GapsRootOrder` ; elle existe pour la forme faible ;
* elle est entraînée par les écarts de l'ordre de la racine (`uniformVariation_of_gaps`), par la pente de
  Tchebychev de `MeetingsBridge.lean` ET la croissance linéaire du reste : la forme faible est bien plus
  faible que `GapsRootOrder`, et elle est vraie sous RH.

**Ce qu'il ne fait pas.** Il ne dérive pas la variation uniforme des premiers : c'est, sous sa forme la
plus faible, le point de blocage unique du maître §17.4, inchangé. Aucun axiome, aucun `sorry`, aucune
hypothèse posée comme démontrée. La chaîne est intacte.
-/

namespace RHV6Fresh

open Complex RHV3Lean

/-! ## 1. L'obligation nommée -/

/-- **Variation uniforme dans les écarts (hypothèse nommée, jamais posée)** : il existe `C` tel que, pour
tout écart entre deux rencontres consécutives, le niveau de la demande en tout point de l'écart diffère
du niveau à la rencontre qui ouvre l'écart d'au plus `C`. -/
def UniformVariationAtGaps : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, ∀ x : ℝ, meetingPoint ⟨n⟩ ≤ x → x ≤ meetingPoint ⟨n + 1⟩ →
    |demandRelativeLevel x - demandRelativeLevel (meetingPoint ⟨n⟩)| ≤ C

theorem demandRelativeLevel_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ demandRelativeLevel x :=
  div_nonneg (norm_nonneg _) (Real.rpow_nonneg hx _)

/-! ## 2. Suffisance : le pont sous variation uniforme -/

/-- **Le pont** : demande bornée aux rencontres et variation uniforme donnent la demande bornée partout. -/
theorem demandBoundedEverywhere_of_meetings_of_variation (hdem : DemandBoundedAtMeetings)
    (hvar : UniformVariationAtGaps) : DemandBoundedEverywhere := by
  obtain ⟨C, hC⟩ := hdem
  obtain ⟨V, hV⟩ := hvar
  obtain ⟨C₁, hC₁⟩ := smoothedRemainder_linear_growth
  refine ⟨max (|C₁| * (fnPrimeAtRank 1 : ℝ) ^ (1 / 2 : ℝ)) (C + V), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  by_cases hxp : x < (fnPrimeAtRank 1 : ℝ)
  · refine le_trans ?_ (le_max_left _ _)
    unfold demandRelativeLevel
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)]
    calc ‖smoothedRemainder x‖ ≤ C₁ * x ^ (1 : ℝ) := hC₁ x hx
      _ ≤ |C₁| * x := by
          rw [Real.rpow_one]
          exact mul_le_mul_of_nonneg_right (le_abs_self C₁) hx0.le
      _ = |C₁| * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by
          rw [← Real.rpow_add hx0]; norm_num
      _ ≤ |C₁| * ((fnPrimeAtRank 1 : ℝ) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx0.le hxp.le (by norm_num))
            (Real.rpow_nonneg hx0.le _)
      _ = |C₁| * (fnPrimeAtRank 1 : ℝ) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by ring
  · push Not at hxp
    have h0 : (fnPrimeAtRank 0 : ℝ) ≤ x := by
      have h01 : fnPrimeAtRank 0 < fnPrimeAtRank 1 := thm_primeAtRank_strictMono (by norm_num)
      have h01' : (fnPrimeAtRank 0 : ℝ) < fnPrimeAtRank 1 := by exact_mod_cast h01
      linarith
    obtain ⟨n, hn1, hn2⟩ := exists_rank_le_lt h0
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      rcases n with _ | m
      · exact absurd (lt_of_le_of_lt hxp hn2) (lt_irrefl _)
      · exact ⟨m, rfl⟩
    refine le_trans ?_ (le_max_right _ _)
    have hvx := hV m x hn1 hn2.le
    have hCm : demandRelativeLevel (meetingPoint ⟨m⟩) ≤ C := hC ⟨m⟩
    have := (abs_sub_le_iff.mp hvx).1
    linarith

/-- Sous variation uniforme, le pont nommé de `DemandLevelPremise.lean` est vrai. -/
theorem meetingsBridge_of_variation (hvar : UniformVariationAtGaps) : MeetingsBridge :=
  fun hdem => demandBoundedEverywhere_of_meetings_of_variation hdem hvar

/-- Demande bornée aux rencontres et variation uniforme donnent RH. -/
theorem riemannHypothesis_of_meetings_of_variation (hdem : DemandBoundedAtMeetings)
    (hvar : UniformVariationAtGaps) : RiemannHypothesis :=
  riemannHypothesis_of_demandBoundedEverywhere
    (demandBoundedEverywhere_of_meetings_of_variation hdem hvar)

/-! ## 3. Nécessité : la variation uniforme est vraie dès que la demande est bornée partout -/

/-- Si la demande est bornée partout, la variation dans chaque écart est bornée par le double de la borne. -/
theorem uniformVariation_of_demandBoundedEverywhere (h : DemandBoundedEverywhere) :
    UniformVariationAtGaps := by
  obtain ⟨C, hC⟩ := h
  refine ⟨2 * C, fun n x hx1 _ => ?_⟩
  have hm : 1 < meetingPoint ⟨n⟩ := one_lt_meetingPoint ⟨n⟩
  have hx : 1 < x := lt_of_lt_of_le hm hx1
  have h1 := hC x hx
  have h2 := hC _ hm
  have h3 := demandRelativeLevel_nonneg (by linarith : (0:ℝ) ≤ x)
  have h4 := demandRelativeLevel_nonneg (by linarith : (0:ℝ) ≤ meetingPoint ⟨n⟩)
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Sous RH, la variation est uniforme. -/
theorem uniformVariation_of_riemannHypothesis (h : RiemannHypothesis) : UniformVariationAtGaps :=
  uniformVariation_of_demandBoundedEverywhere (demandBoundedEverywhere_of_riemannHypothesis h)

/-- **Équivalence** : la demande bornée partout, c'est exactement la demande bornée aux rencontres et la
variation uniforme dans les écarts. -/
theorem demandBoundedEverywhere_iff_meetings_and_variation :
    DemandBoundedEverywhere ↔ (DemandBoundedAtMeetings ∧ UniformVariationAtGaps) :=
  ⟨fun h => ⟨demandBoundedAtMeetings_of_everywhere h, uniformVariation_of_demandBoundedEverywhere h⟩,
    fun ⟨hdem, hvar⟩ => demandBoundedEverywhere_of_meetings_of_variation hdem hvar⟩

/-- **La prémisse unique de la chaîne, lue aux rencontres et dans les écarts.** -/
theorem expectedFrequencyRises_iff_meetings_and_variation :
    ExpectedFrequencyRises ↔ (DemandBoundedAtMeetings ∧ UniformVariationAtGaps) :=
  expectedFrequencyRises_iff_demandBoundedEverywhere.trans
    demandBoundedEverywhere_iff_meetings_and_variation

/-- Sous demande bornée aux rencontres, RH équivaut à la variation uniforme dans les écarts. -/
theorem riemannHypothesis_iff_variation_of_meetings (hdem : DemandBoundedAtMeetings) :
    RiemannHypothesis ↔ UniformVariationAtGaps :=
  ⟨uniformVariation_of_riemannHypothesis, fun hvar => riemannHypothesis_of_meetings_of_variation hdem hvar⟩

/-! ## 4. La forme faible est entraînée par les écarts de l'ordre de la racine -/

/-- Inégalité réelle : pour `0 < s ≤ t` et `0 ≤ R ≤ K t²`, `R/s − R/t ≤ K (t² − s²)/s`. -/
theorem div_sub_div_le_of_le_sq {s t R K : ℝ} (hs : 0 < s) (hst : s ≤ t) (hR : 0 ≤ R)
    (hK : 0 ≤ K) (hRt : R ≤ K * t ^ 2) :
    R / s - R / t ≤ K * (t ^ 2 - s ^ 2) / s := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  rw [div_sub_div _ _ hs.ne' ht.ne', div_le_div_iff₀ (mul_pos hs ht) hs]
  have h1 : 0 ≤ s * (t - s) * (K * t ^ 2 - R) :=
    mul_nonneg (mul_nonneg hs.le (by linarith)) (by linarith)
  have h2 : 0 ≤ s * (t - s) * (K * t * s) :=
    mul_nonneg (mul_nonneg hs.le (by linarith)) (mul_nonneg (mul_nonneg hK ht.le) hs.le)
  nlinarith [h1, h2]

/-- **Théorème** : les écarts de l'ordre de la racine entraînent la variation uniforme dans les écarts. -/
theorem uniformVariation_of_gaps (hgap : GapsRootOrder) : UniformVariationAtGaps := by
  obtain ⟨G, hG⟩ := hgap
  obtain ⟨C₁, hC₁⟩ := smoothedRemainder_linear_growth
  -- `G` est positif : l'écart de rang zéro est strictement positif
  have hG0 : 0 ≤ G := by
    have h := hG 0
    have h01 : (fnPrimeAtRank 0 : ℝ) < fnPrimeAtRank 1 := by
      exact_mod_cast thm_primeAtRank_strictMono (by norm_num : 0 < 1)
    have hs : 0 < (fnPrimeAtRank 0 : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast thm_primeAtRank_pos 0) _
    by_contra hneg
    push Not at hneg
    have : G * (fnPrimeAtRank 0 : ℝ) ^ (1 / 2 : ℝ) < 0 := mul_neg_of_neg_of_pos hneg hs
    linarith
  refine ⟨bridgeSlope * G + bridgeOffset + |C₁| * G, fun n x hx1 hx2 => ?_⟩
  have hp1 : 1 < meetingPoint ⟨n⟩ := one_lt_meetingPoint ⟨n⟩
  have hp0 : 0 < meetingPoint ⟨n⟩ := by linarith
  have hx0 : 0 < x := by linarith
  have hx1' : 1 < x := lt_of_lt_of_le hp1 hx1
  -- l'écart est de l'ordre de la racine
  have hgap' : x - meetingPoint ⟨n⟩ ≤ G * (meetingPoint ⟨n⟩) ^ (1 / 2 : ℝ) := by
    have h := hG (n + 1)
    change x ≤ (fnPrimeAtRank (n + 1 + 1) : ℝ) at hx2
    change (fnPrimeAtRank (n + 1) : ℝ) ≤ x at hx1
    change x - (fnPrimeAtRank (n + 1) : ℝ) ≤ G * (fnPrimeAtRank (n + 1) : ℝ) ^ (1 / 2 : ℝ)
    linarith
  have hsp : 0 < (meetingPoint ⟨n⟩) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hp0 _
  have h1sp : 1 ≤ (meetingPoint ⟨n⟩) ^ (1 / 2 : ℝ) := Real.one_le_rpow hp1.le (by norm_num)
  have hS0 := bridgeSlope_nonneg
  have hO0 := bridgeOffset_nonneg
  -- sens montant : le théorème du pont
  have hup : demandRelativeLevel x - demandRelativeLevel (meetingPoint ⟨n⟩) ≤
      bridgeSlope * G + bridgeOffset := by
    have key := demandRelativeLevel_le_of_mem_gap hp1 hx1 hgap'
    have hdiv : G * (meetingPoint ⟨n⟩) ^ (1 / 2 : ℝ) / (meetingPoint ⟨n⟩) ^ (1 / 2 : ℝ) = G :=
      mul_div_cancel_right₀ _ hsp.ne'
    rw [hdiv] at key
    linarith
  -- sens descendant : la pente de Tchebychev et la croissance linéaire du reste
  have hdown : demandRelativeLevel (meetingPoint ⟨n⟩) - demandRelativeLevel x ≤
      bridgeSlope * G + bridgeOffset + |C₁| * G := by
    have hsub := smoothedRemainder_sub_le hp1 hx1
    have htri := norm_sub_norm_le (smoothedRemainder (meetingPoint ⟨n⟩)) (smoothedRemainder x)
    rw [norm_sub_rev] at htri
    have hRp : ‖smoothedRemainder (meetingPoint ⟨n⟩)‖ ≤
        ‖smoothedRemainder x‖ + (bridgeSlope * (x - meetingPoint ⟨n⟩) + bridgeOffset) := by linarith
    have hRx : ‖smoothedRemainder x‖ ≤ |C₁| * (x ^ (1 / 2 : ℝ)) ^ 2 := by
      calc ‖smoothedRemainder x‖ ≤ C₁ * x ^ (1 : ℝ) := hC₁ x hx1'
        _ ≤ |C₁| * x := by
            rw [Real.rpow_one]
            exact mul_le_mul_of_nonneg_right (le_abs_self C₁) hx0.le
        _ = |C₁| * (x ^ (1 / 2 : ℝ)) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    have hsps : (meetingPoint ⟨n⟩) ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hp0.le hx1 (by norm_num)
    have hsq : (x ^ (1 / 2 : ℝ)) ^ 2 - ((meetingPoint ⟨n⟩) ^ (1 / 2 : ℝ)) ^ 2 = x - meetingPoint ⟨n⟩ := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_mul hp0.le]
      norm_num
    have hdd := div_sub_div_le_of_le_sq hsp hsps (norm_nonneg _) (abs_nonneg _) hRx
    rw [hsq] at hdd
    -- assemblage
    unfold demandRelativeLevel
    have e1 : ‖smoothedRemainder (meetingPoint ⟨n⟩)‖ / (meetingPoint ⟨n⟩) ^ (1 / 2 : ℝ) ≤
        ‖smoothedRemainder x‖ / (meetingPoint ⟨n⟩) ^ (1 / 2 : ℝ) +
          (bridgeSlope * (x - meetingPoint ⟨n⟩) + bridgeOffset) / (meetingPoint ⟨n⟩) ^ (1 / 2 : ℝ) := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hRp hsp.le
    have e2 : (bridgeSlope * (x - meetingPoint ⟨n⟩) + bridgeOffset) / (meetingPoint ⟨n⟩) ^ (1 / 2 : ℝ) ≤
        bridgeSlope * G + bridgeOffset := by
      rw [div_le_iff₀ hsp]
      have hg' : bridgeSlope * (x - meetingPoint ⟨n⟩) ≤
          bridgeSlope * G * (meetingPoint ⟨n⟩) ^ (1 / 2 : ℝ) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hgap' hS0
      have ho' : bridgeOffset ≤ bridgeOffset * (meetingPoint ⟨n⟩) ^ (1 / 2 : ℝ) :=
        le_mul_of_one_le_right hO0 h1sp
      linarith
    have e3 : |C₁| * (x - meetingPoint ⟨n⟩) / (meetingPoint ⟨n⟩) ^ (1 / 2 : ℝ) ≤ |C₁| * G := by
      rw [div_le_iff₀ hsp, mul_assoc]
      exact mul_le_mul_of_nonneg_left hgap' (abs_nonneg _)
    linarith
  have hCG : 0 ≤ |C₁| * G := mul_nonneg (abs_nonneg _) hG0
  rw [abs_sub_le_iff]
  exact ⟨by linarith, hdown⟩

/-- Sous écarts de l'ordre de la racine, le théorème du pont de `MeetingsBridge.lean` est un cas particulier
du pont par variation uniforme. -/
theorem demandBoundedEverywhere_of_meetings_of_gaps' (hdem : DemandBoundedAtMeetings)
    (hgap : GapsRootOrder) : DemandBoundedEverywhere :=
  demandBoundedEverywhere_of_meetings_of_variation hdem (uniformVariation_of_gaps hgap)

end RHV6Fresh
