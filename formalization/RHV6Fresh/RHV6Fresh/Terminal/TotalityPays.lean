/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.MeetingPoint

/-!
# Ce que la totalité doit payer (module isolé, non importé par la chaîne)

Relie deux faits compilés, sans prémisse :

* la part d'un membre, lue en amplitude relative aux rencontres (`MeetingPoint.lean`, section 9) :
  pour un couple à fréquence partagée (arrivée basse et miroir), l'amplitude relative du couple n'est
  bornée à aucune rencontre (`pairRelativeAmplitude_unbounded`) ;
* l'obligation de totalité : à chaque point, la demande des premiers est la somme de toutes les parts
  (`smoothedRemainder_eq_tsum_residueTerm`).

Objet : écrire ce que les zéros restants (tous sauf le couple) doivent fournir pour que la totalité
accomplisse une demande de niveau relatif borné. Réponse compilée : une annulation elle-même non
bornée, rencontre après rencontre. Ce n'est pas une exclusion : rien ici ne touche la position radiale
d'aucun zéro, et aucune hypothèse sur la demande n'est posée comme démontrée. La chaîne est intacte.

Aucun axiome, aucun `sorry`.
-/

namespace RHV6Fresh

open Complex RHV3Lean

/-! ## 1. Le couple et le reste -/

open Classical in
/-- Les deux indices du couple : l'arrivée basse et son miroir. -/
noncomputable def pairIndices (l : TrueZero) : Finset ExplicitIndex :=
  {memberIndex l, memberIndex (mirrorMember l)}

/-- Le reste : la somme des parts de tous les zéros sauf le couple, au point `x`. -/
noncomputable def restOfPair (l : TrueZero) (x : ℝ) : ℂ :=
  ∑' ρ : ((pairIndices l : Set ExplicitIndex)ᶜ : Set ExplicitIndex), nontrivialZeroResidueTerm x ρ

/-- Hors ligne, les deux indices du couple sont distincts. -/
theorem pair_indices_ne (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2) :
    memberIndex l ≠ memberIndex (mirrorMember l) := by
  intro h
  have h1 : l = mirrorMember l := memberIndex_injective h
  have h2 := mirrorMember_radial l
  rw [← h1] at h2
  linarith

/-- **Totalité = couple + reste** : au-delà de un, la demande des premiers est la part conjointe du couple
plus la somme de toutes les autres parts. -/
theorem remainder_eq_pair_add_rest (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2) {x : ℝ}
    (hx : 1 < x) : smoothedRemainder x = pairJoint l x + restOfPair l x := by
  classical
  rw [smoothedRemainder_eq_tsum_residueTerm hx,
    ← (nontrivial_zero_residue_series_summable hx).sum_add_tsum_compl (s := pairIndices l)]
  have hs : ∑ ρ ∈ pairIndices l, nontrivialZeroResidueTerm x ρ = pairJoint l x := by
    unfold pairIndices
    rw [Finset.sum_pair (pair_indices_ne l hlow)]
    unfold pairJoint
    rw [residueTerm_eq_memberJoint _ (by linarith), residueTerm_eq_memberJoint _ (by linarith)]
  rw [hs]
  rfl

/-- Le reste est la demande moins le couple. -/
theorem restOfPair_eq (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2) {x : ℝ} (hx : 1 < x) :
    restOfPair l x = smoothedRemainder x - pairJoint l x := by
  rw [remainder_eq_pair_add_rest l hlow hx]; ring

/-- Le module du reste domine le module du couple moins le module de la demande. -/
theorem norm_rest_ge (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2) {x : ℝ} (hx : 1 < x) :
    ‖pairJoint l x‖ - ‖smoothedRemainder x‖ ≤ ‖restOfPair l x‖ := by
  rw [restOfPair_eq l hlow hx]
  have := norm_sub_le (smoothedRemainder x) (pairJoint l x)
  have h2 := norm_sub_norm_le (pairJoint l x) (smoothedRemainder x)
  rw [← norm_neg (pairJoint l x - smoothedRemainder x), neg_sub] at h2
  exact h2

/-! ## 2. Lecture en amplitude relative -/

/-- Niveau relatif de la demande au point `x` : le module du reste des premiers rapporté à `x^(1/2)`. -/
noncomputable def demandRelativeLevel (x : ℝ) : ℝ := ‖smoothedRemainder x‖ / x ^ (1 / 2 : ℝ)

/-- Amplitude relative du reste (tous les zéros sauf le couple) au point `x`. -/
noncomputable def restRelativeAmplitude (l : TrueZero) (x : ℝ) : ℝ := ‖restOfPair l x‖ / x ^ (1 / 2 : ℝ)

/-- **Ce que le reste doit payer en un point** : au moins l'amplitude relative du couple moins le niveau
relatif de la demande. -/
theorem restRelative_ge (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2) {x : ℝ} (hx : 1 < x) :
    pairRelativeAmplitude l x - demandRelativeLevel x ≤ restRelativeAmplitude l x := by
  unfold pairRelativeAmplitude demandRelativeLevel restRelativeAmplitude
  rw [← sub_div]
  exact div_le_div_of_nonneg_right (norm_rest_ge l hlow hx) (Real.rpow_pos_of_pos (by linarith) _).le

/-- Forme quantitative : le reste paie au moins l'amplitude relative du miroir, moins celle de l'arrivée
basse, moins le niveau relatif de la demande. La première croît strictement de rencontre en rencontre
(`relativeAmplitude_strictMono_of_high`), la seconde décroît (`relativeAmplitude_strictAnti_of_low`). -/
theorem restRelative_ge_members (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2) {x : ℝ}
    (hx : 1 < x) :
    relativeAmplitude (mirrorMember l) x - relativeAmplitude l x - demandRelativeLevel x ≤
      restRelativeAmplitude l x := by
  have h1 := pairRelativeAmplitude_ge l (show 0 < x by linarith)
  have h2 := restRelative_ge l hlow hx
  linarith

/-! ## 3. Aux rencontres, jusqu'à l'infini -/

/-- **Théorème (inconditionnel)** : pour un couple à fréquence partagée, à toute borne correspond une
rencontre où le reste et la demande, en amplitude relative, dépassent ensemble cette borne. Autrement dit :
ou bien le niveau relatif de la demande n'est pas borné aux rencontres, ou bien l'amplitude relative du reste
(la somme des autres parts, identité du complément) ne l'est pas. -/
theorem totality_pays_or_demand_unbounded (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2)
    (c : ℝ) :
    ∃ I : PrimeGapInterval,
      c < restRelativeAmplitude l (meetingPoint I) + demandRelativeLevel (meetingPoint I) := by
  obtain ⟨I, hI⟩ := pairRelativeAmplitude_unbounded l hlow c
  refine ⟨I, ?_⟩
  have := restRelative_ge l hlow (one_lt_meetingPoint I)
  linarith

/-- **Théorème (sous demande bornée)** : si le niveau relatif de la demande est borné aux rencontres,
alors l'amplitude relative du reste n'est bornée par aucune constante aux rencontres : annulation exigée sous
hypothèse nommée, jamais valuée (§19.21). L'hypothèse de bornage est une hypothèse, pas un fait
compilé. -/
theorem rest_unbounded_of_bounded_demand (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2)
    {C : ℝ} (hC : ∀ I : PrimeGapInterval, demandRelativeLevel (meetingPoint I) ≤ C) (c : ℝ) :
    ∃ I : PrimeGapInterval, c < restRelativeAmplitude l (meetingPoint I) := by
  obtain ⟨I, hI⟩ := totality_pays_or_demand_unbounded l hlow (c + C)
  exact ⟨I, by linarith [hC I]⟩

/-- **Contraposée** : si la demande et le reste ont tous deux un niveau relatif borné aux rencontres, le
membre n'est pas une arrivée basse. Lecture : un couple hors ligne exige des autres zéros une annulation
sans borne ; là où cette annulation est bornée et la demande aussi, il n'y a pas de couple hors ligne. -/
theorem not_low_of_bounded_demand_and_rest (l : TrueZero)
    (hdem : ∃ C : ℝ, ∀ I : PrimeGapInterval, demandRelativeLevel (meetingPoint I) ≤ C)
    (hrest : ∃ C' : ℝ, ∀ I : PrimeGapInterval, restRelativeAmplitude l (meetingPoint I) ≤ C') :
    ¬ rZeroRadialPosition l.1 < 1 / 2 := by
  intro hlow
  obtain ⟨C, hC⟩ := hdem
  obtain ⟨C', hC'⟩ := hrest
  obtain ⟨I, hI⟩ := rest_unbounded_of_bounded_demand l hlow hC C'
  linarith [hC' I]

/-- Le paiement croît sans borne rencontre après rencontre, sous demande bornée : pour tout rang, une
rencontre de rang supérieur exige du reste une amplitude relative plus grande que toute borne donnée. -/
theorem rest_unbounded_beyond_rank (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2)
    {C : ℝ} (hC : ∀ I : PrimeGapInterval, demandRelativeLevel (meetingPoint I) ≤ C) (c : ℝ) (n : ℕ) :
    ∃ I : PrimeGapInterval, n ≤ I.rank ∧ c < restRelativeAmplitude l (meetingPoint I) := by
  obtain ⟨B, hB⟩ := ((Set.finite_Iio n).image
    (fun k : ℕ => restRelativeAmplitude l (meetingPoint ⟨k⟩))).bddAbove
  obtain ⟨I, hI⟩ := rest_unbounded_of_bounded_demand l hlow hC (max c B)
  refine ⟨I, ?_, lt_of_le_of_lt (le_max_left _ _) hI⟩
  by_contra hn
  push_neg at hn
  have hle : restRelativeAmplitude l (meetingPoint I) ≤ B :=
    hB ⟨I.rank, Set.mem_Iio.mpr hn, rfl⟩
  linarith [le_max_right c B]

end RHV6Fresh
