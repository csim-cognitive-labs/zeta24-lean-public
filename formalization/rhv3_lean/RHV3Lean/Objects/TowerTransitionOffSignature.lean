/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TowerTransition
import RHV3Lean.Objects.SamePrimeCollision
import RHV3Lean.Objects.OffMirrorDifferenceBands

/-!
# RHV3Lean — la signature de transition de la paire miroir OFF

    TRACE_ID              : RHV3-TOWER-TRANSITION-OFF-SIGNATURE
    SEMANTIC_OBJECT       : la paire miroir hors ligne, relue comme un passage
                            entre deux Tours propres au sens de
                            `TowerTransition.lean`, sans aucune hypothèse
                            supplémentaire (ni `PMirrorSameStageLogGap`, ni
                            aucune autre `Prop` nommée non prouvée).
    SEMANTIC_STATEMENT    : le passage construit depuis le membre original et
                            son miroir fonctionnel a un écart de hauteur nul et,
                            par la rigidité de largeur déjà prouvée, un écart de
                            largeur nul aussi — automatiquement, sans hypothèse
                            de même étage.  Sa variation radiale et sa variation
                            de phase sont, elles, non nulles : c'est la
                            signature qui distingue structurellement ce passage
                            de tout passage entre deux membres réellement
                            consécutifs et de hauteurs distinctes.
    MATHEMATICAL_STATEMENT: heightGap = 0 ; widthGap = 0 (conséquence directe de
                            `thm_widthGap_eq_heightGap_reciprocal`) ;
                            radialGap != 0 ; phaseGap != 0.  De plus,
                            criticalDefect(original) + criticalDefect(mirror) =
                            pi*(2*beta-1)^2 / (beta*(1-beta)), strictement
                            positif hors ligne, et nul ssi beta=1/2.
    MATHEMATICAL_PARENT   : `TowerTransition.lean`, `TowerCriticalDefect.lean`,
                            `FunctionalMirror.lean` (`thm_mirror_sameHeight`,
                            `thm_mirror_radialPosition`), et les deux faits
                            déjà inconditionnels de `OffMirrorDifferenceBands.lean`
                            (`thm_offRadialPosition_ne`, `thm_offPhase_ne`).
    PROOF_STRATEGY        : instancier `TTowerMemberTransition` sur le couple
                            (original, miroir) pour un porteur quelconque ;
                            `heightGap=0` et `widthGap=0` viennent directement
                            de `thm_mirror_sameHeight` composée avec
                            `thm_widthGap_eq_heightGap_reciprocal` — aucune
                            hypothèse de même étage n'est nécessaire, contraire
                            à la route `PMirrorSameStageLogGap` antérieure ;
                            `radialGap != 0` et `phaseGap != 0` sont exactement
                            les deux faits déjà produits sans hypothèse ; la
                            somme des défauts critiques est une réécriture
                            algébrique directe de `thm_towerCriticalDefect_eq_radial`
                            aux deux positions radiales `beta` et `1-beta`.
    REQUIRED_LEMMAS       : thm_mirror_sameHeight, thm_mirror_radialPosition,
                            thm_offRadialPosition_ne, thm_offPhase_ne,
                            thm_widthGap_eq_heightGap_reciprocal,
                            thm_towerCriticalDefect_eq_radial
    WHY_EACH_LEMMA_EXISTS : les deux premiers donnent les deux coordonnées
                            exactes du miroir ; les deux suivants distinguent
                            structurellement le couple sans jamais supposer RH
                            ni sa négation ; les deux derniers transportent la
                            rigidité de largeur et le défaut critique déjà
                            produits sur ce couple précis.
    LEAN_DEFINITION       : tOffTransition (namespace TTrueTowerCarrier)
    LEAN_THEOREM          : thm_offTransition_heightGap_zero,
                            thm_offTransition_widthGap_zero,
                            thm_offTransition_radialGap_ne_zero,
                            thm_offTransition_phaseGap_ne_zero,
                            thm_offCriticalDefectSum_eq,
                            thm_offCriticalDefectSum_pos,
                            thm_criticalDefectSum_eq_zero_iff
    SAME_MEMBER_CHECK     : les deux états du passage sont ceux du porteur
                            appliqué aux deux vrais membres du couple OFF,
                            jamais un état synthétique.
    SAME_PASSAGE_CHECK    : toutes les clauses portent sur LE MÊME passage
                            `tCarrier.tOffTransition zOff`.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre dans ce module.
    FORBIDDEN_PREMISES    : `PMirrorSameStageLogGap` ou toute autre hypothèse
                            de même étage ; T1, T2, R-PASS, `PUniqueCenterRegime`,
                            `PCanonicalSuccession`, `PNullPassageForcesNullPlace` ;
                            l'hypothèse de Riemann ou sa négation.
    NEXT_CONSUMER         : le morphisme grammatical (`TowerGrammarTransition.lean`),
                            qui doit placer ce passage hors du domaine où une
                            transition première canonique `p_n -> p_(n+1)`
                            peut légitimement s'appliquer.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED — sans aucune `Prop` nommée non
                            prouvée, contrairement à `OffMirrorDifferenceBands.lean`.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

open TTrueHarmonicTowerState TTowerMemberTransition

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-! ## 1. Le passage OFF, comme instance de `TTowerMemberTransition` -/

/-- **Le passage de la paire miroir OFF**, sous un porteur quelconque. -/
noncomputable def tOffTransition (zOff : TOffCriticalLineUpperZero) :
    TTowerMemberTransition where
  zLeft := offOriginalUpperMember zOff
  zRight := offMirrorUpperMember zOff
  SLeft := tCarrier.fnState (offOriginalUpperMember zOff)
  SRight := tCarrier.fnState (offMirrorUpperMember zOff)

/-! ## 2. La signature : hauteur et largeur nulles, radial et phase non nuls -/

/-- **L'écart de hauteur du passage OFF est nul.** -/
theorem thm_offTransition_heightGap_zero (zOff : TOffCriticalLineUpperZero) :
    (tCarrier.tOffTransition zOff).heightGap = 0 := by
  unfold tOffTransition TTowerMemberTransition.heightGap
  have := thm_offMirror_sameHeight zOff
  linarith

/-- **L'écart de largeur du passage OFF est nul, SANS aucune hypothèse de même
étage.**  Conséquence directe de la rigidité de largeur générique appliquée à
un écart de hauteur nul. -/
theorem thm_offTransition_widthGap_zero (zOff : TOffCriticalLineUpperZero) :
    (tCarrier.tOffTransition zOff).widthGap = 0 := by
  rw [thm_widthGap_eq_heightGap_reciprocal]
  have hHeightEq : rZeroHeight (tCarrier.tOffTransition zOff).zRight.1 =
      rZeroHeight (tCarrier.tOffTransition zOff).zLeft.1 := by
    have hGap := tCarrier.thm_offTransition_heightGap_zero zOff
    unfold TTowerMemberTransition.heightGap at hGap
    linarith
  rw [hHeightEq]
  ring

/-- **L'écart de position radiale du passage OFF n'est jamais nul.** -/
theorem thm_offTransition_radialGap_ne_zero (zOff : TOffCriticalLineUpperZero) :
    (tCarrier.tOffTransition zOff).radialGap ≠ 0 := by
  unfold tOffTransition TTowerMemberTransition.radialGap
  intro hEq
  apply thm_offRadialPosition_ne zOff
  unfold rTowerRadialPosition
  linarith

/-- **L'écart de phase du passage OFF n'est jamais nul.** -/
theorem thm_offTransition_phaseGap_ne_zero (zOff : TOffCriticalLineUpperZero) :
    (tCarrier.tOffTransition zOff).phaseGap ≠ 0 := by
  unfold tOffTransition TTowerMemberTransition.phaseGap
  intro hEq
  apply thm_offPhase_ne zOff
  linarith

/-- **LA SIGNATURE OFF COMPLÈTE, sur le même passage.** -/
theorem thm_offTransition_signature (zOff : TOffCriticalLineUpperZero) :
    (tCarrier.tOffTransition zOff).heightGap = 0 ∧
      (tCarrier.tOffTransition zOff).widthGap = 0 ∧
        (tCarrier.tOffTransition zOff).radialGap ≠ 0 ∧
          (tCarrier.tOffTransition zOff).phaseGap ≠ 0 :=
  ⟨tCarrier.thm_offTransition_heightGap_zero zOff,
    tCarrier.thm_offTransition_widthGap_zero zOff,
    tCarrier.thm_offTransition_radialGap_ne_zero zOff,
    tCarrier.thm_offTransition_phaseGap_ne_zero zOff⟩

end TTrueTowerCarrier

/-! ## 3. La somme des défauts critiques du couple miroir -/

/-- **La somme des deux défauts critiques du couple miroir est exactement
`pi*(2*beta-1)^2/(beta*(1-beta))`.**  Redémontrée dans RHV3 à partir de
`thm_towerCriticalDefect_eq_radial`, sur les deux positions radiales exactes
`beta` et `1-beta` du couple. -/
theorem thm_offCriticalDefectSum_eq
    {z : TUpperNonTrivialZetaZero} (S : TTrueHarmonicTowerState z)
    {zMirror : TUpperNonTrivialZetaZero} (SMirror : TTrueHarmonicTowerState zMirror)
    (hMirror : rZeroRadialPosition zMirror.1 = 1 - rZeroRadialPosition z.1) :
    rTowerCriticalDefect S + rTowerCriticalDefect SMirror =
      Real.pi * (2 * rZeroRadialPosition z.1 - 1) ^ 2 /
        (rZeroRadialPosition z.1 * (1 - rZeroRadialPosition z.1)) := by
  have hBetaPos : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hBetaLtOne : rZeroRadialPosition z.1 < 1 := thm_zeroRadialPosition_lt_one z.1
  have hLeft := thm_towerCriticalDefect_eq_radial S
  have hRight := thm_towerCriticalDefect_eq_radial SMirror
  rw [hLeft, hRight, hMirror]
  have hBetaNe : rZeroRadialPosition z.1 ≠ 0 := ne_of_gt hBetaPos
  have hOneMinusNe : (1 : ℝ) - rZeroRadialPosition z.1 ≠ 0 := by linarith
  field_simp
  ring

/-- **La somme des défauts critiques est strictement positive hors ligne.** -/
theorem thm_offCriticalDefectSum_pos
    {z : TUpperNonTrivialZetaZero} (S : TTrueHarmonicTowerState z)
    {zMirror : TUpperNonTrivialZetaZero} (SMirror : TTrueHarmonicTowerState zMirror)
    (hMirror : rZeroRadialPosition zMirror.1 = 1 - rZeroRadialPosition z.1)
    (hOff : rZeroRadialPosition z.1 ≠ 1 / 2) :
    0 < rTowerCriticalDefect S + rTowerCriticalDefect SMirror := by
  rw [thm_offCriticalDefectSum_eq S SMirror hMirror]
  have hBetaPos : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hBetaLtOne : rZeroRadialPosition z.1 < 1 := thm_zeroRadialPosition_lt_one z.1
  have hDenomPos : 0 < rZeroRadialPosition z.1 * (1 - rZeroRadialPosition z.1) := by
    apply mul_pos hBetaPos; linarith
  have hNumPos : 0 < (2 * rZeroRadialPosition z.1 - 1) ^ 2 := by
    apply sq_pos_of_ne_zero
    intro hEq
    apply hOff
    linarith
  positivity

/-- **La somme des défauts critiques s'annule exactement quand `beta=1/2`.**
Équivalence algébrique pure, valide même sur la ligne critique (auquel cas la
somme vaut `0`). -/
theorem thm_criticalDefectSum_eq_zero_iff
    {z : TUpperNonTrivialZetaZero} (S : TTrueHarmonicTowerState z)
    {zMirror : TUpperNonTrivialZetaZero} (SMirror : TTrueHarmonicTowerState zMirror)
    (hMirror : rZeroRadialPosition zMirror.1 = 1 - rZeroRadialPosition z.1) :
    rTowerCriticalDefect S + rTowerCriticalDefect SMirror = 0 ↔
      rZeroRadialPosition z.1 = 1 / 2 := by
  rw [thm_offCriticalDefectSum_eq S SMirror hMirror]
  have hBetaPos : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hBetaLtOne : rZeroRadialPosition z.1 < 1 := thm_zeroRadialPosition_lt_one z.1
  have hDenomNe : rZeroRadialPosition z.1 * (1 - rZeroRadialPosition z.1) ≠ 0 := by
    apply ne_of_gt; apply mul_pos hBetaPos; linarith
  rw [div_eq_zero_iff]
  constructor
  · rintro (hNum | hDenom)
    · rcases mul_eq_zero.mp hNum with hPi | hSq
      · exact absurd hPi Real.pi_ne_zero
      · have := sq_eq_zero_iff.mp hSq
        linarith
    · exact absurd hDenom hDenomNe
  · intro hEq
    left
    rw [hEq]; norm_num

/-! Surface audit. -/

#check TTrueTowerCarrier.tOffTransition
#check TTrueTowerCarrier.thm_offTransition_signature
#check thm_offCriticalDefectSum_eq
#check thm_offCriticalDefectSum_pos
#check thm_criticalDefectSum_eq_zero_iff

end RHV3Lean
