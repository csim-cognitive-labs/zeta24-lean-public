/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RayCapture
import RHV6Fresh.Terminal.RegimeTower
import RHV6Fresh.Terminal.DoubleRigidity
import RHV6Fresh.Terminal.ArrivalFiberHypotheses
import RHV6Fresh.Terminal.EngagedAllConstraints

/-!
# La prémisse Astra réexaminée avec les théorèmes actuels (auteur, 2026-10-19 : « reprends cette piste et élabore
avec l'état actuel des théorèmes »)

Historique retrouvé dans `git` (commits `66162218`, `624a0c53`, `5a4c5efc` ; bases RHV4/RHV5Fresh, hors périmètre
d'import, définitions relues et transcrites ici mot pour mot dans le vocabulaire RHV6Fresh) :

* `interMemberLogSeparation z w = |logIncidence_w(0) − logIncidence_z(0)|` : séparation logarithmique des deux Tours
  au stade commun `0`, c'est-à-dire `|log C₀(w) − log C₀(z)|` avec `C₀ = contactMinusAt · 0` ;
* `TowerSatisfiesNext z w` : l'événement premier de `w` est le successeur de celui de `z` ; c'est un THÉORÈME sur tout
  passage (M9, `thm_authenticPair_mustSatisfyNext`), il n'ajoute rien à la consécutivité ;
* prémisse Astra (`66162218`, `624a0c53`, axiome `PENDING_ExperimentalInterMemberPiOverT`) : pour tout passage
  consécutif, `interMemberLogSeparation z w = π / T_z`, SANS hypothèse de hauteur ;
* transformation `5a4c5efc` (phases 1–4, `sorry` en phase 3) : remplacer `=` par `π / T_z ≤ …` depuis la géométrie
  des anneaux (`thm_trueTower_ringJump_logWidth`, identité INTRA-Tour `(k₁ − k₀)·π/T`) et le pas de rang `≥ 1` ;
* fermeture historique : à même hauteur la séparation est `< π/(2T)` (théorème, bande de phase), donc la prémisse
  interdit le passage de même hauteur, donc le miroir, donc RH (`riemannHypothesis_rhv4`, axiomes avec `sorryAx`).

Ce que les théorèmes actuels établissent (axiomes standard) :

1. l'identité `π/T` est INTRA-Tour : `log C_{k₁} − log C_{k₀} = (k₁ − k₀)·π/T` (`ringJump_logWidth`,
   `towerPitch_eq_contacts`) ; elle ne dit rien de deux Tours distinctes ;
2. la séparation INTER-Tours au stade `0` vaut `|arctan(T_w/β_w)/T_w − arctan(T_z/β_z)/T_z|` ; chaque terme est dans
   `]0, π/(2T)[` ; dès que la hauteur ne recule pas (`passage_height_le`, tout passage), la séparation est
   `< π/(2T_z)` (`interMemberLogSeparation_lt_half_pitch`) : la prémisse Astra, égalité ou inégalité, est FAUSSE sur
   TOUT passage de hauteurs positives (`astra_equality_premise_false`, `astra_inequality_premise_false`), et en
   particulier sur le premier passage authentique (`first_passage_separation_lt`) ; sa forme quantifiée implique
   `False` (`astra_premise_refuted`) : la fermeture historique était ex falso ;
3. la forme restreinte à même hauteur (`thm_preOff_progression_necessary` de `5a4c5efc`) est exactement « aucun
   passage de même hauteur » (`astra_sameHeight_premise_iff_no_sameHeight`) ⟺ RH
   (`astra_sameHeight_premise_iff_riemannHypothesis`) : ce n'est pas une prémisse plus locale que RH ;
4. le théorème laissé en `sorry` par Astra (`thm_offInterlacing_grammarRankSucc_incompatible`) a toutes ses hypothèses
   satisfaites sur tout passage de même hauteur (`astra_open_hypotheses_satisfied`) : il est le but `False` du cas bas ;
5. T2/R-PASS (RHV2) : « même hauteur ⟹ passage premier nul » est RÉFUTÉ : sur tout passage de même hauteur le rang
   avance d'une unité et l'occurrence de l'arrivée est le minimum attendu du départ (`sameHeight_prime_passage_nonnull`,
   `rpass_transport_refuted`) ; la nullité en hauteur ne se transporte jamais en nullité première ;
6. profil du cas bas : le passage sortant de même hauteur a une séparation strictement positive et `< π/(2T_l)`, rang
   `+ 1` (`low_arrival_astra_profile`).

Aucun contre-exemple n'est à chercher : la borne `< π/(2T)` est un théorème sur toute paire de Tours de hauteurs
ordonnées, ON ou OFF ; aucun théorème de transport ne peut produire `≥ π/T`. Aucun `sorry`, aucun `admit`, aucun
axiome, aucune prémisse.
-/

set_option linter.style.longLine false

namespace RHV6Fresh

open RHV3Lean

/-! ## §1 Les objets d'Astra dans le vocabulaire actuel -/

/-- Séparation inter-membres d'Astra : écart logarithmique des deux Tours au stade commun `0`. -/
noncomputable def interMemberLogSeparation (z w : TrueZero) : ℝ :=
  |Real.log (contactMinusAt w 0) - Real.log (contactMinusAt z 0)|

/-- Progression inter-membres requise par Astra : le pas `π/T` du membre de départ. -/
noncomputable def requiredInterMemberProgression (z : TrueZero) : ℝ := towerPitch z

theorem requiredInterMemberProgression_eq (z : TrueZero) :
    requiredInterMemberProgression z = Real.pi / rZeroHeight z.1 := rfl

/-- Le logarithme du contact de stade `k` : `(arctan(T/β) + kπ)/T`. -/
theorem log_contactMinusAt (z : TrueZero) (k : ℤ) :
    Real.log (contactMinusAt z k) =
      (Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) + (k : ℝ) * Real.pi) / rZeroHeight z.1 := by
  rw [contactMinusAt_eq_exp, Real.log_exp]

theorem log_contactMinusAt_zero (z : TrueZero) :
    Real.log (contactMinusAt z 0) = Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) / rZeroHeight z.1 := by
  rw [log_contactMinusAt]; simp

/-- **L'identité `π/T` d'Astra est intra-Tour** : d'un anneau à l'autre de la MÊME Tour, `(k₁ − k₀)·π/T`
(`thm_trueTower_ringJump_logWidth`, phase 2 de `5a4c5efc`). -/
theorem ringJump_logWidth (z : TrueZero) (k₀ k₁ : ℤ) :
    Real.log (contactMinusAt z k₁) - Real.log (contactMinusAt z k₀) = ((k₁ : ℝ) - k₀) * towerPitch z := by
  rw [log_contactMinusAt, log_contactMinusAt]
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  unfold towerPitch
  field_simp
  ring

/-! ## §2 La séparation inter-Tours est toujours sous un demi-pas -/

/-- Le logarithme du contact de stade `0` est dans `]0, π/(2T)[`, pour toute position radiale. -/
theorem log_contactMinusAt_zero_bounds (z : TrueZero) :
    0 < Real.log (contactMinusAt z 0) ∧ Real.log (contactMinusAt z 0) < Real.pi / (2 * rZeroHeight z.1) := by
  rw [log_contactMinusAt_zero]
  have hT : 0 < rZeroHeight z.1 := z.2
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hpos : 0 < Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) :=
    Real.arctan_pos.mpr (div_pos hT hβ)
  have hlt : Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  refine ⟨div_pos hpos hT, ?_⟩
  rw [div_lt_div_iff₀ hT (by positivity)]
  nlinarith

/-- **Séparation inter-Tours sous un demi-pas** : dès que la hauteur ne recule pas, `sep z w < π/(2T_z)`, pour
toutes positions radiales (ON ou OFF). C'est le contre-modèle demandé : aucune paire de Tours de hauteurs ordonnées
n'atteint `π/T_z`. -/
theorem interMemberLogSeparation_lt_half_pitch (z w : TrueZero) (hT : rZeroHeight z.1 ≤ rZeroHeight w.1) :
    interMemberLogSeparation z w < towerPitch z / 2 := by
  obtain ⟨hz0, hz1⟩ := log_contactMinusAt_zero_bounds z
  obtain ⟨hw0, hw1⟩ := log_contactMinusAt_zero_bounds w
  have hTz : 0 < rZeroHeight z.1 := z.2
  have hw1' : Real.log (contactMinusAt w 0) < Real.pi / (2 * rZeroHeight z.1) := by
    refine hw1.trans_le ?_
    exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith)
  have hhalf : towerPitch z / 2 = Real.pi / (2 * rZeroHeight z.1) := by
    unfold towerPitch; field_simp
  unfold interMemberLogSeparation
  rw [hhalf, abs_lt]
  constructor <;> linarith

theorem interMemberLogSeparation_lt_pitch (z w : TrueZero) (hT : rZeroHeight z.1 ≤ rZeroHeight w.1) :
    interMemberLogSeparation z w < towerPitch z :=
  (interMemberLogSeparation_lt_half_pitch z w hT).trans_le (by linarith [towerPitch_pos z])

/-- Sur tout passage (hauteurs positives), la séparation d'Astra est sous un demi-pas du départ. -/
theorem passage_interMemberLogSeparation_lt (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    interMemberLogSeparation ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ < towerPitch ⟨p.zEarlierMember, hE⟩ / 2 :=
  interMemberLogSeparation_lt_half_pitch _ _ (passage_height_le p)

/-! ## §3 La prémisse Astra est fausse sur tout passage -/

/-- **La prémisse d'égalité d'Astra (`66162218`, `624a0c53`) est fausse sur tout passage.** -/
theorem astra_equality_premise_false (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    interMemberLogSeparation ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ ≠
      requiredInterMemberProgression ⟨p.zEarlierMember, hE⟩ :=
  ne_of_lt (interMemberLogSeparation_lt_pitch _ _ (passage_height_le p))

/-- **La prémisse d'inégalité visée par `5a4c5efc` est fausse sur tout passage.** -/
theorem astra_inequality_premise_false (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    ¬ requiredInterMemberProgression ⟨p.zEarlierMember, hE⟩ ≤
        interMemberLogSeparation ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ :=
  not_le.mpr (interMemberLogSeparation_lt_pitch _ _ (passage_height_le p))

/-- Le premier passage authentique (premier et deuxième membres canoniques) : séparation sous un demi-pas. -/
theorem first_passage_separation_lt :
    interMemberLogSeparation (canonicalZero 1) (canonicalZero 2) < towerPitch (canonicalZero 1) / 2 :=
  interMemberLogSeparation_lt_half_pitch _ _
    (passage_height_le ⟨(canonicalZero 1).1, (canonicalZero 2).1, canonicalZero_consecutive le_rfl⟩)

/-- **La prémisse Astra quantifiée implique `False`** : la fermeture historique `riemannHypothesis_rhv4` était ex
falso. -/
theorem astra_premise_refuted
    (hP : ∀ p : TZeroPassage, ∀ hE : 0 < rZeroHeight p.zEarlierMember, ∀ hL : 0 < rZeroHeight p.zLaterMember,
      requiredInterMemberProgression ⟨p.zEarlierMember, hE⟩ ≤
        interMemberLogSeparation ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩) : False :=
  astra_inequality_premise_false ⟨(canonicalZero 1).1, (canonicalZero 2).1, canonicalZero_consecutive le_rfl⟩
    (canonicalZero 1).2 (canonicalZero 2).2 (hP _ _ _)

/-! ## §4 À même hauteur : séparation exacte, invariance de stade, nullité ⟺ même position radiale -/

/-- À même hauteur, la séparation vaut `|Δ arctan(T/β)| / T`. -/
theorem sameHeight_interMemberLogSeparation_eq (z w : TrueZero) (hT : rZeroHeight w.1 = rZeroHeight z.1) :
    interMemberLogSeparation z w =
      |Real.arctan (rZeroHeight z.1 / rZeroRadialPosition w.1) -
        Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1)| / rZeroHeight z.1 := by
  have hTz : (0 : ℝ) < rZeroHeight z.1 := z.2
  unfold interMemberLogSeparation
  rw [log_contactMinusAt_zero, log_contactMinusAt_zero, hT, ← sub_div, abs_div, abs_of_pos hTz]

/-- À même hauteur, la séparation est la même à tout stade commun (Astra : « at common height any common stage has
this same separation »). -/
theorem sameHeight_interMemberLogSeparation_stage_invariant (z w : TrueZero)
    (hT : rZeroHeight w.1 = rZeroHeight z.1) (k : ℤ) :
    |Real.log (contactMinusAt w k) - Real.log (contactMinusAt z k)| = interMemberLogSeparation z w := by
  unfold interMemberLogSeparation
  rw [log_contactMinusAt, log_contactMinusAt, log_contactMinusAt_zero, log_contactMinusAt_zero, hT]
  congr 1
  field_simp
  ring

/-- À même hauteur, séparation nulle ⟺ même position radiale : la séparation d'Astra lit le déplacement radial. -/
theorem sameHeight_interMemberLogSeparation_eq_zero_iff (z w : TrueZero)
    (hT : rZeroHeight w.1 = rZeroHeight z.1) :
    interMemberLogSeparation z w = 0 ↔ rZeroRadialPosition z.1 = rZeroRadialPosition w.1 := by
  rw [sameHeight_interMemberLogSeparation_eq z w hT, div_eq_zero_iff, abs_eq_zero, sub_eq_zero]
  have hTz : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  have hβz : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hβw : 0 < rZeroRadialPosition w.1 := thm_zeroRadialPosition_positive w.1
  constructor
  · rintro (h | h)
    · have := Real.arctan_injective h
      rw [div_eq_div_iff (ne_of_gt hβw) (ne_of_gt hβz)] at this
      exact mul_left_cancel₀ hTz this
    · exact absurd h hTz
  · intro h; left; rw [h]

/-- À même hauteur avec positions radiales distinctes, la séparation est strictement positive. -/
theorem sameHeight_interMemberLogSeparation_pos (z w : TrueZero) (hT : rZeroHeight w.1 = rZeroHeight z.1)
    (hβ : rZeroRadialPosition z.1 ≠ rZeroRadialPosition w.1) : 0 < interMemberLogSeparation z w :=
  lt_of_le_of_ne (abs_nonneg _) fun h => hβ ((sameHeight_interMemberLogSeparation_eq_zero_iff z w hT).mp h.symm)

/-! ## §5 La forme à même hauteur de la prémisse est « aucun passage de même hauteur » ⟺ RH -/

/-- **Forme à même hauteur de la prémisse Astra ⟺ aucun passage de même hauteur** : d'un côté elle est vide, de
l'autre elle contredit `sep < π/(2T)` sur tout passage de même hauteur. -/
theorem astra_sameHeight_premise_iff_no_sameHeight :
    (∀ p : TZeroPassage, ∀ hE : 0 < rZeroHeight p.zEarlierMember, HorizontalPassage p →
      requiredInterMemberProgression ⟨p.zEarlierMember, hE⟩ ≤
        interMemberLogSeparation ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hE.trans_le (passage_height_le p)⟩) ↔
    (∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → ¬ HorizontalPassage p) := by
  constructor
  · intro h p hE hH
    exact astra_inequality_premise_false p hE (hE.trans_le (passage_height_le p)) (h p hE hH)
  · intro h p hE hH
    exact absurd hH (h p hE)

/-- **La forme à même hauteur de la prémisse Astra ⟺ RH.** -/
theorem astra_sameHeight_premise_iff_riemannHypothesis :
    (∀ p : TZeroPassage, ∀ hE : 0 < rZeroHeight p.zEarlierMember, HorizontalPassage p →
      requiredInterMemberProgression ⟨p.zEarlierMember, hE⟩ ≤
        interMemberLogSeparation ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hE.trans_le (passage_height_le p)⟩) ↔
    RiemannHypothesis :=
  astra_sameHeight_premise_iff_no_sameHeight.trans no_sameHeight_iff_riemannHypothesis

/-- **Le théorème laissé en `sorry` par Astra** (`thm_offInterlacing_grammarRankSucc_incompatible`) a toutes ses
hypothèses satisfaites sur tout passage de même hauteur : consécutivité, rang `+ 1`, même hauteur, positions radiales
distinctes, séparation `< π/T`. Il est donc exactement « aucun passage de même hauteur », le but `False` du cas bas. -/
theorem astra_open_hypotheses_satisfied (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hH : HorizontalPassage p) :
    PZeroMembersConsecutive p.zEarlierMember p.zLaterMember ∧
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
    rZeroHeight p.zLaterMember = rZeroHeight p.zEarlierMember ∧
    rZeroRadialPosition p.zLaterMember ≠ rZeroRadialPosition p.zEarlierMember ∧
    interMemberLogSeparation ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hE.trans_le (passage_height_le p)⟩ <
      Real.pi / rZeroHeight p.zEarlierMember := by
  have hL : 0 < rZeroHeight p.zLaterMember := hE.trans_le (passage_height_le p)
  refine ⟨p.hConsecutive, eventIndex_succ_of_passage p hE, hH.symm, ?_, ?_⟩
  · exact ne_of_gt (sameHeight_passage_profile p hE hL hH).1
  · exact interMemberLogSeparation_lt_pitch _ _ (passage_height_le p)

/-! ## §6 T2/R-PASS : la nullité en hauteur ne se transporte pas en nullité première -/

/-- **Sur tout passage de même hauteur, le passage premier n'est pas nul** : rang `+ 1`, occurrence de l'arrivée =
minimum attendu du départ. Le transport R-PASS « passage de hauteur nulle ⟹ passage premier nul » est réfuté. -/
theorem sameHeight_prime_passage_nonnull (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (_hH : HorizontalPassage p) :
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
    occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ :=
  ⟨eventIndex_succ_of_passage p hE, (grammar_step_regime_blind p hE hL).2⟩

theorem rpass_transport_refuted (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (_hH : HorizontalPassage p) : nZeroSourceIndex p.zLaterMember ≠ nZeroSourceIndex p.zEarlierMember := by
  rw [eventIndex_succ_of_passage p hE]; omega

/-! ## §7 Profil Astra du cas bas -/

/-- **Profil Astra du passage sortant d'une arrivée basse** : il existe un successeur consécutif à la même hauteur,
séparation strictement positive et sous un demi-pas, rang `+ 1`. Tout ce qu'Astra exigeait du passage de même hauteur
est réalisé ; rien n'y contredit `β_l < 1/2`. -/
theorem low_arrival_astra_profile (l : TrueZero) (hβ : rZeroRadialPosition l.1 < 1 / 2) :
    ∃ s : TrueZero, ∃ hC : PZeroMembersConsecutive l.1 s.1,
      HorizontalPassage (⟨l.1, s.1, hC⟩ : TZeroPassage) ∧
      0 < interMemberLogSeparation l s ∧
      interMemberLogSeparation l s < towerPitch l / 2 ∧
      nZeroSourceIndex s.1 = nZeroSourceIndex l.1 + 1 := by
  obtain ⟨s, hC, hT, hrank, -, hH, -⟩ := rank_step_counts_members_not_heights l hβ
  refine ⟨s, hC, hH, ?_, interMemberLogSeparation_lt_half_pitch l s hT.ge, hrank⟩
  refine sameHeight_interMemberLogSeparation_pos l s hT ?_
  exact ne_of_lt (sameHeight_passage_profile ⟨l.1, s.1, hC⟩ l.2 s.2 hH).1

/-! ## §8 Les deux fermetures candidates du second message (auteur, 2026-10-19) -/

/-- **Fermeture A, prémisse Astra restreinte au passage engagé** : départ ON, historique ON, passage qui monte,
arrivée basse. Même sous ces quatre hypothèses, la séparation d'Astra reste sous un demi-pas : l'inégalité
`π/T_e ≤ sep` est fausse sur le premier passage qui quitterait le régime ON, exactement comme sur tout passage. La
restriction ne rend pas la prémisse vraie ; elle ne fournit aucune contrainte inférieure sur `β_l`. -/
theorem engaged_astra_inequality_false (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (_hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) (_hV : VerticalPassage p)
    (_hHist : ∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2)
    (hL : 0 < rZeroHeight p.zLaterMember) (_hBelow : rZeroRadialPosition p.zLaterMember < 1 / 2) :
    interMemberLogSeparation ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ < towerPitch ⟨p.zEarlierMember, hE⟩ / 2 ∧
    ¬ requiredInterMemberProgression ⟨p.zEarlierMember, hE⟩ ≤
        interMemberLogSeparation ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ :=
  ⟨passage_interMemberLogSeparation_lt p hE hL, astra_inequality_premise_false p hE hL⟩

/-- **Fermeture B, le passage miroir nul** : une arrivée basse a un miroir haut à la même hauteur ; sa fibre contient
un passage CONSÉCUTIF de même hauteur (la consécutivité du miroir lui-même n'est pas dérivée) ; ce passage est nul en
hauteur, mais son passage premier n'est pas nul : rang `+ 1`, occurrence de l'arrivée = minimum attendu du départ. La
dernière implication de la fermeture B (« passage nul ⟹ ⊥ ») ne peut donc pas venir d'un transport de nullité : la
nullité de hauteur ne se transporte pas aux premiers. -/
theorem mirror_pair_null_passage_profile (l : TrueZero) (hβ : rZeroRadialPosition l.1 < 1 / 2) :
    rZeroHeight (mirrorMember l).1 = rZeroHeight l.1 ∧ 1 / 2 < rZeroRadialPosition (mirrorMember l).1 ∧
    ∃ s : TrueZero, ∃ hC : PZeroMembersConsecutive l.1 s.1,
      HorizontalPassage (⟨l.1, s.1, hC⟩ : TZeroPassage) ∧
      nZeroSourceIndex s.1 = nZeroSourceIndex l.1 + 1 ∧
      expectedMinimumPrime l = occurrence s ∧
      0 < interMemberLogSeparation l s := by
  obtain ⟨s, hC, hT, hrank, hocc, hH, -⟩ := rank_step_counts_members_not_heights l hβ
  refine ⟨mirrorMember_ordinate l, by rw [mirrorMember_radial]; linarith, s, hC, hH, hrank, hocc, ?_⟩
  exact sameHeight_interMemberLogSeparation_pos l s hT
    (ne_of_lt (sameHeight_passage_profile ⟨l.1, s.1, hC⟩ l.2 s.2 hH).1)

/-- **Les deux fermetures A et B, prises ensemble, sont exactement la forme à même hauteur de la prémisse Astra** :
« tout passage de même hauteur viole la borne `sep < π/(2T)` » ; l'une et l'autre reviennent à « aucun passage de même
hauteur », ⟺ RH. Aucune contrainte inférieure sur `β_l` n'en sort indépendamment. -/
theorem closures_A_B_iff_riemannHypothesis :
    (∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → ¬ HorizontalPassage p) ↔ RiemannHypothesis :=
  no_sameHeight_iff_riemannHypothesis

/-! ## §10 Le certificat d'Astra, affûté puis réduit (auteur, 2026-10-19 : « une paire de zéros distincts de même
hauteur ⟹ une séparation de contacts inférieure à un demi-pas ; ce qui échoue, c'est de lui opposer le pas complet
`π/T`, intra-Tour »)

Le certificat est compilé (§5). Trois faits le situent :
1. il n'est PAS une signature de la même hauteur : tout passage, vertical compris, a une séparation `< π/(2T_e)`
   (`passage_interMemberLogSeparation_lt`) ; sa réciproque est fausse ;
2. affûté, il est de l'ordre `1/T²`, pas `π/(2T)` : à même hauteur, `sep < 1/T²` pour toute paire de vrais zéros
   (`sameHeight_interMemberLogSeparation_lt_inv_sq`, par `0 < β < 1`) ;
3. la seule prémisse qui l'utilise pour exclure est un PLANCHER `1/T² ≤ sep` sur le passage sortant de l'arrivée.
   Elle ferme le cas bas (`sep_floor_closes_low_arrival`) ; restreinte aux passages de même hauteur elle est ⟺ RH
   (`sep_floor_sameHeight_iff_riemannHypothesis`) ; sur les passages verticaux ON → ON serrés (écart de hauteur
   `≤ 1/2`) elle est FAUSSE (`close_onLine_pair_separation_lt_inv_sq`) : ce n'est pas un plancher de zêta (paires de
   Lehmer, littérature, non compilé). Sa réduction maximale est donc le but lui-même. -/

/-- Pour tout vrai zéro, `arctan(T/β) ∈ ]arctan T, π/2[`, puisque `0 < β < 1`. -/
theorem arctan_height_over_radial_bounds (z : TrueZero) :
    Real.arctan (rZeroHeight z.1) < Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) ∧
    Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) < Real.pi / 2 := by
  have hT : (0 : ℝ) < rZeroHeight z.1 := z.2
  have hβ := thm_zeroRadialPosition_positive z.1
  have hβ1 := thm_zeroRadialPosition_lt_one z.1
  refine ⟨Real.arctan_lt_arctan_iff.mpr ?_, Real.arctan_lt_pi_div_two _⟩
  rw [lt_div_iff₀ hβ]
  nlinarith

/-- `π/2 − arctan T < 1/T` pour `T > 0`. -/
theorem pi_div_two_sub_arctan_lt (T : ℝ) (hT : 0 < T) : Real.pi / 2 - Real.arctan T < 1 / T := by
  rw [← Real.arctan_inv_of_pos hT, one_div]
  exact arctan_lt_self_of_pos (inv_pos.mpr hT)

/-- **Le certificat affûté** : deux vrais zéros de même hauteur ont une séparation de contacts `< 1/T²`, quelle que
soit la paire de positions radiales (`0 < β < 1`). Le demi-pas `π/(2T)` du certificat historique est lâche d'un
facteur `≈ πT/2`. -/
theorem sameHeight_interMemberLogSeparation_lt_inv_sq (z w : TrueZero)
    (hT : rZeroHeight w.1 = rZeroHeight z.1) :
    interMemberLogSeparation z w < 1 / rZeroHeight z.1 ^ 2 := by
  have hTz : (0 : ℝ) < rZeroHeight z.1 := z.2
  rw [sameHeight_interMemberLogSeparation_eq z w hT]
  obtain ⟨hz1, hz2⟩ := arctan_height_over_radial_bounds z
  obtain ⟨hw1, hw2⟩ := arctan_height_over_radial_bounds w
  rw [hT] at hw1 hw2
  have hinv := pi_div_two_sub_arctan_lt _ hTz
  have habs : |Real.arctan (rZeroHeight z.1 / rZeroRadialPosition w.1) -
      Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1)| < 1 / rZeroHeight z.1 := by
    rw [abs_sub_lt_iff]; constructor <;> linarith
  rw [div_lt_iff₀ hTz]
  have hsq : 1 / rZeroHeight z.1 ^ 2 * rZeroHeight z.1 = 1 / rZeroHeight z.1 := by
    rw [pow_two, one_div, one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hTz.ne', mul_one]
  rw [hsq]; exact habs

/-- Instance sur la paire miroir d'une arrivée basse : `sep(l, l*) < 1/T_l²`. -/
theorem mirror_pair_separation_lt_inv_sq (l : TrueZero) :
    interMemberLogSeparation l (mirrorMember l) < 1 / rZeroHeight l.1 ^ 2 :=
  sameHeight_interMemberLogSeparation_lt_inv_sq l (mirrorMember l) (mirrorMember_ordinate l)

/-- **Prémisse de test (plancher de séparation)** : `1/T_e² ≤ sep` sur un passage de même hauteur est FAUX. -/
theorem sep_floor_sameHeight_false (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hH : HorizontalPassage p) :
    ¬ (1 / rZeroHeight p.zEarlierMember ^ 2 ≤
        interMemberLogSeparation ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩) :=
  not_le.mpr (sameHeight_interMemberLogSeparation_lt_inv_sq ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hH.symm)

/-- **La prémisse de plancher ferme le cas bas** : si le passage qui quitte l'arrivée basse avait une séparation
`≥ 1/T_l²`, contradiction (le passage sortant est de même hauteur, `rank_step_counts_members_not_heights`). -/
theorem sep_floor_closes_low_arrival (l : TrueZero) (hβ : rZeroRadialPosition l.1 < 1 / 2)
    (hFloor : ∀ s : TrueZero, ∀ hC : PZeroMembersConsecutive l.1 s.1,
      HorizontalPassage (⟨l.1, s.1, hC⟩ : TZeroPassage) →
      1 / rZeroHeight l.1 ^ 2 ≤ interMemberLogSeparation l s) : False := by
  obtain ⟨s, hC, hH, -, -, -⟩ := low_arrival_astra_profile l hβ
  exact sep_floor_sameHeight_false ⟨l.1, s.1, hC⟩ l.2 s.2 hH (hFloor s hC hH)

/-- **Réduction de la prémisse, côté même hauteur** : le plancher quantifié sur les passages de même hauteur n'est
rien d'autre que « aucun passage de même hauteur », c'est-à-dire RH. -/
theorem sep_floor_sameHeight_iff_riemannHypothesis :
    (∀ p : TZeroPassage, ∀ hE : 0 < rZeroHeight p.zEarlierMember, HorizontalPassage p →
      1 / rZeroHeight p.zEarlierMember ^ 2 ≤
        interMemberLogSeparation ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hE.trans_le (passage_height_le p)⟩) ↔
    RiemannHypothesis := by
  refine Iff.trans ?_ no_sameHeight_iff_riemannHypothesis
  constructor
  · intro h p hE hH
    exact sep_floor_sameHeight_false p hE (hE.trans_le (passage_height_le p)) hH (h p hE hH)
  · intro h p hE hH
    exact absurd hH (h p hE)

/-- **Réduction de la prémisse, côté vertical** : deux zéros ON de hauteurs `T_e < T_l ≤ T_e + 1/2` ont aussi une
séparation `< 1/T_e²`. Le plancher n'est donc pas une propriété des passages verticaux de zêta : il tomberait sur toute
paire ON serrée (paires de Lehmer, littérature, non compilé). Il ne peut être ni dérivé ni posé ; sa seule partie
utile au but est sa restriction au passage sortant de l'arrivée, qui est le but. -/
theorem close_onLine_pair_separation_lt_inv_sq (e l : TrueZero)
    (hOnE : rZeroRadialPosition e.1 = 1 / 2) (hOnL : rZeroRadialPosition l.1 = 1 / 2)
    (hlt : rZeroHeight e.1 < rZeroHeight l.1) (hClose : rZeroHeight l.1 ≤ rZeroHeight e.1 + 1 / 2) :
    interMemberLogSeparation e l < 1 / rZeroHeight e.1 ^ 2 := by
  have hTe : (0 : ℝ) < rZeroHeight e.1 := e.2
  have hTl : (0 : ℝ) < rZeroHeight l.1 := l.2
  unfold interMemberLogSeparation
  rw [log_contactMinusAt_zero, log_contactMinusAt_zero, hOnE, hOnL]
  have h2e : rZeroHeight e.1 / (1 / 2) = 2 * rZeroHeight e.1 := by ring
  have h2l : rZeroHeight l.1 / (1 / 2) = 2 * rZeroHeight l.1 := by ring
  rw [h2e, h2l]
  set ae := Real.arctan (2 * rZeroHeight e.1) with hae
  set al := Real.arctan (2 * rZeroHeight l.1) with hal
  have hmono : ae ≤ al := Real.arctan_strictMono.monotone (by linarith)
  have hae0 : 0 < ae := Real.arctan_pos.mpr (by linarith)
  have hal_lt : al < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hgap : al - ae < 1 / (2 * rZeroHeight e.1) := by
    have := pi_div_two_sub_arctan_lt (2 * rZeroHeight e.1) (by linarith)
    linarith
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  rw [abs_sub_lt_iff]
  constructor
  · -- al/T_l − ae/T_e ≤ (al − ae)/T_l < 1/(2 T_e T_l) < 1/T_e²
    have h1 : al / rZeroHeight l.1 - ae / rZeroHeight e.1 ≤ (al - ae) / rZeroHeight l.1 := by
      rw [sub_div]
      have : ae / rZeroHeight l.1 ≤ ae / rZeroHeight e.1 :=
        div_le_div_of_nonneg_left hae0.le hTe hlt.le
      linarith
    have h2 : (al - ae) / rZeroHeight l.1 < 1 / rZeroHeight e.1 ^ 2 := by
      rw [div_lt_iff₀ hTl]
      have hTl2 : 1 / rZeroHeight e.1 ^ 2 * rZeroHeight l.1 > 1 / rZeroHeight e.1 ^ 2 * rZeroHeight e.1 :=
        mul_lt_mul_of_pos_left hlt (by positivity)
      have hsq : 1 / rZeroHeight e.1 ^ 2 * rZeroHeight e.1 = 1 / rZeroHeight e.1 := by
        rw [pow_two, one_div, one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hTe.ne', mul_one]
      have hhalf : 1 / (2 * rZeroHeight e.1) ≤ 1 / rZeroHeight e.1 :=
        one_div_le_one_div_of_le hTe (by linarith)
      linarith
    linarith
  · -- ae/T_e − al/T_l ≤ al·(T_l − T_e)/(T_e T_l) ≤ (π/2)(1/2)/(T_e T_l) < 1/T_e²
    have h1 : ae / rZeroHeight e.1 - al / rZeroHeight l.1 ≤
        al / rZeroHeight e.1 - al / rZeroHeight l.1 := by
      have : ae / rZeroHeight e.1 ≤ al / rZeroHeight e.1 := div_le_div_of_nonneg_right hmono hTe.le
      linarith
    have h2 : al / rZeroHeight e.1 - al / rZeroHeight l.1 =
        al * (rZeroHeight l.1 - rZeroHeight e.1) / (rZeroHeight e.1 * rZeroHeight l.1) := by
      field_simp
    have h3 : al * (rZeroHeight l.1 - rZeroHeight e.1) / (rZeroHeight e.1 * rZeroHeight l.1) <
        1 / rZeroHeight e.1 ^ 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have hd : 0 ≤ rZeroHeight l.1 - rZeroHeight e.1 := by linarith
      have hal_le : al * (rZeroHeight l.1 - rZeroHeight e.1) ≤ 2 * (1 / 2) := by
        have := mul_le_mul hal_lt.le (show rZeroHeight l.1 - rZeroHeight e.1 ≤ 1 / 2 by linarith)
          hd (by linarith)
        nlinarith
      nlinarith [mul_pos hTe hTl, mul_pos hTe hTe]
    linarith

/-- **Bilan des réductions** : la prémisse de plancher ferme le cas bas, sa forme à même hauteur est RH, sa forme
verticale est fausse sur les paires ON serrées. Reste, comme seule forme vraie et utile, le but. -/
theorem sep_floor_premise_reduction (l : TrueZero) (hβ : rZeroRadialPosition l.1 < 1 / 2) :
    (∀ s : TrueZero, ∀ hC : PZeroMembersConsecutive l.1 s.1,
      HorizontalPassage (⟨l.1, s.1, hC⟩ : TZeroPassage) →
      1 / rZeroHeight l.1 ^ 2 ≤ interMemberLogSeparation l s) ↔ False :=
  ⟨sep_floor_closes_low_arrival l hβ, False.elim⟩

end RHV6Fresh

#print axioms RHV6Fresh.astra_premise_refuted
#print axioms RHV6Fresh.astra_sameHeight_premise_iff_riemannHypothesis
#print axioms RHV6Fresh.low_arrival_astra_profile
#print axioms RHV6Fresh.engaged_astra_inequality_false
#print axioms RHV6Fresh.mirror_pair_null_passage_profile
#print axioms RHV6Fresh.sameHeight_interMemberLogSeparation_lt_inv_sq
#print axioms RHV6Fresh.sep_floor_closes_low_arrival
#print axioms RHV6Fresh.sep_floor_sameHeight_iff_riemannHypothesis
#print axioms RHV6Fresh.close_onLine_pair_separation_lt_inv_sq
