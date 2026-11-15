/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.SamePrimeCollision
import RHV3Lean.Objects.VonMangoldtChebyshev

/-!
# RHV3Lean — Piste C : les bandes de différence de la paire miroir OFF

    TRACE_ID              : RHV3-OFF-MIRROR-DIFFERENCE-BANDS
    SEMANTIC_OBJECT       : la collision miroir OFF (§13.1/§13.2/§35.2 du
                            maître Lean), réduite à un fait arithmétique fini.
    SEMANTIC_STATEMENT    : les deux membres de la paire miroir OFF partagent
                            exactement la même hauteur, donc la même largeur
                            logarithmique de cellule. Leur décalage de contact
                            (issu uniquement de l'écart de phase tangentielle)
                            est borné, sans aucune hypothèse de croissance,
                            strictement en dessous de cette largeur. Les deux
                            cellules se recouvrent donc nécessairement ; leur
                            différence symétrique se réduit à deux bandes
                            étroites. Si ces deux bandes ne contiennent aucun
                            premier — un fait que le comptage fini de Von
                            Mangoldt/Chebyshev peut trancher, sans intégrale ni
                            somme sur les zéros — alors les deux cellules
                            partagent le même rang central, donc le même
                            premier canonique.
    MATHEMATICAL_STATEMENT: |phi(beta)-phi(1-beta)| < pi/2 (bornes arctan
                            inconditionnelles) ; sous l'hypothèse nommée du
                            même étage de transport, le décalage logarithmique
                            de contact vaut exactement cet écart de phase
                            divisé par T, donc < pi/(2T) < pi/T = largeur de
                            cellule (identité exacte de l'état propre S4).
    MATHEMATICAL_PARENT   : maître sémantique §13.1/§13.2 ; maître Lean §34.2,
                            §35.2, §35.3 (Piste C) ; TrueTowerState.lean (les
                            deux équations exactes de l'état propre) ;
                            VonMangoldtChebyshev.lean (comptage fini).
    PROOF_STRATEGY        : borner la phase par les deux inégalités arctan
                            déjà produites ; transporter cette borne au
                            décalage logarithmique via l'hypothèse nommée du
                            même étage ; comparer à la largeur exacte de
                            cellule ; construire les deux bandes comme
                            intervalles algébriques ; réduire leur non-
                            appartenance première à une égalité de rangs de
                            comptage, elle-même conséquence directe d'un
                            cardinal nul (thm_cellFoundCount_eq_edgeRankDifference).
    REQUIRED_LEMMAS       : Real.arctan_pos, Real.arctan_lt_pi_div_two,
                            Real.arctan_inj, thm_offMirror_sameHeight,
                            thm_mirror_radialPosition,
                            thm_cellFoundCount_eq_edgeRankDifference
    WHY_EACH_LEMMA_EXISTS : les deux premières bornent la phase ; la troisième
                            exclut le décalage nul (position radiale
                            distincte) ; les deux suivantes donnent la même
                            hauteur et la position radiale reflétée du
                            miroir ; la dernière réduit "bande sans premier" à
                            une égalité de rangs, jamais une recherche.
    LEAN_DEFINITION       : PMirrorSameStageLogGap, POffDifferenceBandsPrimeFree
    LEAN_THEOREM          : thm_carrierCell_logWidth,
                            thm_offRadialPosition_ne, thm_offPhase_ne,
                            thm_mirrorPhaseGap_abs_lt_piDivTwo,
                            thm_mirrorLogGap_abs_lt_width,
                            thm_mirrorCollision_of_stageAndBandsPrimeFree
    SAME_MEMBER_CHECK     : toutes les lectures restent fonctions du seul
                            membre (rCarrierContactMinus/Plus, rTowerPhase).
    SAME_PASSAGE_CHECK    : sans objet — aucun passage n'est construit ici.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : le comptage utilisé est celui de O10
                            (VonMangoldtChebyshev.lean), sur l'unique histoire
                            première.
    FORBIDDEN_PREMISES    : choisir une adresse kappa explicite ; supposer une
                            relation entre T et l'ordre de grandeur absolu des
                            contacts ; re-dériver la formule explicite ou toute
                            somme sur les zéros (leçon de §31.2).
    NEXT_CONSUMER         : la route miroir (`PMirrorCollision`,
                            SamePrimeCollision.lean), en remplacement de la
                            réception libre par ces deux faits plus primitifs.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS            : BODY_PRODUCED pour la borne et la réduction ;
                             `PMirrorSameStageLogGap` et
                             `POffDifferenceBandsPrimeFree` restent des `Prop`
                             nommées, non prouvées ici — exactement au même
                             statut que `PUniqueCenterRegime`/
                             `PCanonicalSuccession`. `POffDifferenceBandsPrimeFree`
                             est désormais réduite à un fait arithmétique fini
                             (cardinal de bande nul), jamais analytique.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

/-! ## 1. Le rang de comptage est monotone au bord -/

theorem thm_nEdgePrimeRank_mono {rPoint1 rPoint2 : ℝ} (hLe : rPoint1 ≤ rPoint2) :
    nEdgePrimeRank rPoint1 ≤ nEdgePrimeRank rPoint2 := by
  unfold nEdgePrimeRank
  exact Nat.count_monotone Nat.Prime (Nat.add_le_add_right (Nat.floor_le_floor hLe) 1)

/-- **Fait arithmétique pur, découplé de tout porteur.** Si le cardinal
trouvé de la bande `(min a b, max a b]` est nul, les deux points `a` et `b`
ont le même rang de comptage. C'est la seule chose qu'une bande sans premier
donne : une égalité de rangs, jamais plus. -/
theorem thm_bandFoundCount_zero_imp_edgeRank_eq {a b : ℝ}
    (I : TAlgebraicInterval) (hLeft : I.rLeftEndpoint = min a b)
    (hRight : I.rRightEndpoint = max a b) (hCount : nCellFoundCount I = 0) :
    nEdgePrimeRank a = nEdgePrimeRank b := by
  have hDiff := thm_cellFoundCount_eq_edgeRankDifference I
  have hMono : nEdgePrimeRank (min a b) ≤ nEdgePrimeRank (max a b) :=
    thm_nEdgePrimeRank_mono (min_le_max (a := a) (b := b))
  unfold nCellLeftEdgeRank nCellRightEdgeRank at hDiff
  rw [hLeft, hRight, hCount] at hDiff
  have hEq : nEdgePrimeRank (min a b) = nEdgePrimeRank (max a b) := by omega
  rcases le_total a b with hle | hle
  · rwa [min_eq_left hle, max_eq_right hle] at hEq
  · rw [min_eq_right hle, max_eq_left hle] at hEq
    exact hEq.symm

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-! ## 2. La largeur logarithmique exacte de la cellule -/

/-- La largeur logarithmique de la cellule d'un membre, sous ce porteur, est
exactement `pi/T` -- une identité de l'état propre, pas une approximation. -/
theorem thm_carrierCell_logWidth (zUpperZero : TUpperNonTrivialZetaZero) :
    Real.log (tCarrier.rCarrierContactPlus zUpperZero) -
        Real.log (tCarrier.rCarrierContactMinus zUpperZero) =
      Real.pi / rTowerHeight zUpperZero :=
  (tCarrier.fnState zUpperZero).consecutive_width

/-! ## 3. Le fait du même étage (maître sémantique §13.1), nommé -/

/-- **Le même étage de transport.** Le décalage logarithmique entre les deux
contacts inférieurs de la paire miroir vaut exactement l'écart de phase
tangentielle divisé par la hauteur commune. C'est l'hypothèse que kappa est le
même pour les deux membres (§13.1) : elle s'annule dans la différence, mais
n'est pas encore produite pour un porteur générique quelconque. Reçue comme
fait à établir, jamais une hypothèse silencieuse, au même titre que
`PUniqueCenterRegime`/`PCanonicalSuccession`. -/
def PMirrorSameStageLogGap : Prop :=
  ∀ zOff : TOffCriticalLineUpperZero,
    Real.log (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff)) -
        Real.log (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff)) =
      (rTowerPhase (offMirrorUpperMember zOff) -
          rTowerPhase (offOriginalUpperMember zOff)) /
        rTowerHeight (offOriginalUpperMember zOff)

/-- Le même décalage vaut aussi entre les deux contacts supérieurs : la
largeur de cellule est la même pour les deux membres (même hauteur), donc le
décalage se transporte identiquement au bord droit. -/
theorem thm_mirrorSameStage_contactPlus (hStage : tCarrier.PMirrorSameStageLogGap)
    (zOff : TOffCriticalLineUpperZero) :
    Real.log (tCarrier.rCarrierContactPlus (offMirrorUpperMember zOff)) -
        Real.log (tCarrier.rCarrierContactPlus (offOriginalUpperMember zOff)) =
      (rTowerPhase (offMirrorUpperMember zOff) -
          rTowerPhase (offOriginalUpperMember zOff)) /
        rTowerHeight (offOriginalUpperMember zOff) := by
  have hWidthOrig := tCarrier.thm_carrierCell_logWidth (offOriginalUpperMember zOff)
  have hWidthMirror := tCarrier.thm_carrierCell_logWidth (offMirrorUpperMember zOff)
  have hHeightEq : rTowerHeight (offMirrorUpperMember zOff) =
      rTowerHeight (offOriginalUpperMember zOff) := thm_offMirror_sameHeight zOff
  rw [hHeightEq] at hWidthMirror
  have hMinus := hStage zOff
  linarith

end TTrueTowerCarrier

/-! ## 4. Les deux membres OFF ont des positions radiales et des phases
distinctes -/

theorem thm_offRadialPosition_ne (zOff : TOffCriticalLineUpperZero) :
    rTowerRadialPosition (offOriginalUpperMember zOff) ≠
      rTowerRadialPosition (offMirrorUpperMember zOff) := by
  have hMirror : rTowerRadialPosition (offMirrorUpperMember zOff) =
      1 - rTowerRadialPosition (offOriginalUpperMember zOff) :=
    thm_mirror_radialPosition (offOriginalUpperMember zOff).1
  have hOff : rTowerRadialPosition (offOriginalUpperMember zOff) ≠ 1 / 2 := zOff.2
  intro hEq
  apply hOff
  rw [hMirror] at hEq
  linarith

theorem thm_offPhase_ne (zOff : TOffCriticalLineUpperZero) :
    rTowerPhase (offOriginalUpperMember zOff) ≠ rTowerPhase (offMirrorUpperMember zOff) := by
  intro hEq
  unfold rTowerPhase at hEq
  have hInj := Real.arctan_inj.mp hEq
  have hHeightPos := thm_rTowerHeight_positive (offOriginalUpperMember zOff)
  have hRadPosOrig := thm_rTowerRadialPosition_positive (offOriginalUpperMember zOff)
  have hRadPosMirror := thm_rTowerRadialPosition_positive (offMirrorUpperMember zOff)
  have hMirrorHeight : rTowerHeight (offMirrorUpperMember zOff) =
      rTowerHeight (offOriginalUpperMember zOff) := thm_offMirror_sameHeight zOff
  rw [hMirrorHeight] at hInj
  have hCross :
      rTowerHeight (offOriginalUpperMember zOff) *
          rTowerRadialPosition (offMirrorUpperMember zOff) =
        rTowerHeight (offOriginalUpperMember zOff) *
          rTowerRadialPosition (offOriginalUpperMember zOff) :=
    (div_eq_div_iff hRadPosOrig.ne' hRadPosMirror.ne').mp hInj
  exact thm_offRadialPosition_ne zOff
    (mul_left_cancel₀ hHeightPos.ne' hCross).symm

/-! ## 5. La borne exacte sur l'écart de phase, et sur le décalage -/

theorem thm_mirrorPhaseGap_abs_lt_piDivTwo (zOff : TOffCriticalLineUpperZero) :
    |rTowerPhase (offMirrorUpperMember zOff) -
        rTowerPhase (offOriginalUpperMember zOff)| < Real.pi / 2 := by
  have hMirrorPos := thm_rTowerPhase_positive (offMirrorUpperMember zOff)
  have hMirrorLt := thm_rTowerPhase_lt_piDivTwo (offMirrorUpperMember zOff)
  have hOrigPos := thm_rTowerPhase_positive (offOriginalUpperMember zOff)
  have hOrigLt := thm_rTowerPhase_lt_piDivTwo (offOriginalUpperMember zOff)
  rw [abs_sub_lt_iff]
  constructor <;> linarith

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-- **La borne finale, sans aucune hypothèse de croissance.** Le décalage
logarithmique entre les deux contacts miroir est strictement inférieur à la
largeur exacte de la cellule -- pour toute hauteur, sans seuil, sans relation
entre T et l'ordre de grandeur absolu des contacts. -/
theorem thm_mirrorLogGap_abs_lt_width (hStage : tCarrier.PMirrorSameStageLogGap)
    (zOff : TOffCriticalLineUpperZero) :
    |Real.log (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff)) -
        Real.log (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff))| <
      Real.pi / rTowerHeight (offOriginalUpperMember zOff) := by
  have hHeightPos := thm_rTowerHeight_positive (offOriginalUpperMember zOff)
  have hPhase := thm_mirrorPhaseGap_abs_lt_piDivTwo zOff
  rw [hStage zOff, abs_div, abs_of_pos hHeightPos]
  rw [div_lt_div_iff_of_pos_right hHeightPos]
  linarith [Real.pi_pos]

/-- Le décalage n'est jamais nul : les deux contacts miroir sont distincts. -/
theorem thm_mirrorLogGap_ne_zero (hStage : tCarrier.PMirrorSameStageLogGap)
    (zOff : TOffCriticalLineUpperZero) :
    Real.log (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff)) -
        Real.log (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff)) ≠ 0 := by
  rw [hStage zOff]
  have hHeightPos := thm_rTowerHeight_positive (offOriginalUpperMember zOff)
  have hPhaseNe := thm_offPhase_ne zOff
  exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hPhaseNe)) hHeightPos.ne'

/-- Les deux contacts inférieurs miroir sont distincts. -/
theorem thm_mirrorContactMinus_ne (hStage : tCarrier.PMirrorSameStageLogGap)
    (zOff : TOffCriticalLineUpperZero) :
    tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff) ≠
      tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff) := by
  intro hEq
  apply tCarrier.thm_mirrorLogGap_ne_zero hStage zOff
  rw [hEq]; ring

/-- Les deux contacts supérieurs miroir sont distincts. -/
theorem thm_mirrorContactPlus_ne (hStage : tCarrier.PMirrorSameStageLogGap)
    (zOff : TOffCriticalLineUpperZero) :
    tCarrier.rCarrierContactPlus (offOriginalUpperMember zOff) ≠
      tCarrier.rCarrierContactPlus (offMirrorUpperMember zOff) := by
  intro hEq
  have hGapPlus := tCarrier.thm_mirrorSameStage_contactPlus hStage zOff
  have hGapMinus := hStage zOff
  apply tCarrier.thm_mirrorLogGap_ne_zero hStage zOff
  rw [hGapMinus, ← hGapPlus, hEq]; ring

/-! ## 6. Les deux bandes de différence, comme intervalles algébriques -/

/-- **La bande gauche** : la différence symétrique des deux cellules miroir au
bord inférieur. Un intervalle algébrique bien formé, sans jamais choisir un
premier ni une adresse. -/
noncomputable def tLeftDifferenceBand (hStage : tCarrier.PMirrorSameStageLogGap)
    (zOff : TOffCriticalLineUpperZero) : TAlgebraicInterval where
  rLeftEndpoint :=
    min (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff))
      (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff))
  rRightEndpoint :=
    max (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff))
      (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff))
  hLeftPositive :=
    lt_min ((tCarrier.fnState (offOriginalUpperMember zOff)).contactMinus_pos)
      ((tCarrier.fnState (offMirrorUpperMember zOff)).contactMinus_pos)
  hOrdered := min_lt_max.mpr (tCarrier.thm_mirrorContactMinus_ne hStage zOff)

/-- **La bande droite** : la différence symétrique des deux cellules miroir au
bord supérieur. -/
noncomputable def tRightDifferenceBand (hStage : tCarrier.PMirrorSameStageLogGap)
    (zOff : TOffCriticalLineUpperZero) : TAlgebraicInterval where
  rLeftEndpoint :=
    min (tCarrier.rCarrierContactPlus (offOriginalUpperMember zOff))
      (tCarrier.rCarrierContactPlus (offMirrorUpperMember zOff))
  rRightEndpoint :=
    max (tCarrier.rCarrierContactPlus (offOriginalUpperMember zOff))
      (tCarrier.rCarrierContactPlus (offMirrorUpperMember zOff))
  hLeftPositive :=
    lt_min ((tCarrier.fnState (offOriginalUpperMember zOff)).contactPlus_pos)
      ((tCarrier.fnState (offMirrorUpperMember zOff)).contactPlus_pos)
  hOrdered := min_lt_max.mpr (tCarrier.thm_mirrorContactPlus_ne hStage zOff)

/-! ## 7. Le fait arithmétique fini restant, nommé -/

/-- **Les deux bandes ne contiennent aucun premier.** Un fait arithmétique
fini, tranché par le comptage de Von Mangoldt/Chebyshev déjà produit
(`thm_vonMangoldtChebyshev_reads_same_interval`, `nCellFoundCount`), jamais
une hypothèse analytique sur la croissance de T. C'est le contenu réel
restant de la Piste C (maître Lean §35.3). Reçu comme fait à établir, jamais
une hypothèse silencieuse. -/
def POffDifferenceBandsPrimeFree (hStage : tCarrier.PMirrorSameStageLogGap) : Prop :=
  ∀ zOff : TOffCriticalLineUpperZero,
    nCellFoundCount (tCarrier.tLeftDifferenceBand hStage zOff) = 0 ∧
      nCellFoundCount (tCarrier.tRightDifferenceBand hStage zOff) = 0

/-! ## 8. La collision miroir, produite depuis ces deux faits plus primitifs -/

/-- **Théorème.** Si les deux membres miroir partagent le même étage de
transport, et si leurs deux bandes de différence sont vides de premier, alors
ils partagent le même rang de comptage aux deux bords -- donc le même rang
central, donc le même premier canonique. Aucune borne analytique, aucune
relation T-vs-x : seulement une égalité de rangs de comptage entiers. -/
theorem thm_mirrorCollision_of_stageAndBandsPrimeFree
    (hStage : tCarrier.PMirrorSameStageLogGap)
    (hBandsFree : tCarrier.POffDifferenceBandsPrimeFree hStage) :
    tCarrier.PMirrorCollision := by
  intro zOff
  set cOrig := tCarrier.tCarrierCell (offOriginalUpperMember zOff)
  set cMirror := tCarrier.tCarrierCell (offMirrorUpperMember zOff)
  have hLeftEq : nCellLeftEdgeRank cOrig = nCellLeftEdgeRank cMirror :=
    thm_bandFoundCount_zero_imp_edgeRank_eq
      (tCarrier.tLeftDifferenceBand hStage zOff) rfl rfl (hBandsFree zOff).1
  have hRightEq : nCellRightEdgeRank cOrig = nCellRightEdgeRank cMirror :=
    thm_bandFoundCount_zero_imp_edgeRank_eq
      (tCarrier.tRightDifferenceBand hStage zOff) rfl rfl (hBandsFree zOff).2
  have hCentralRankEq : nCellCentralRank cOrig = nCellCentralRank cMirror := by
    unfold nCellCentralRank
    rw [thm_cellFoundCount_eq_edgeRankDifference,
      thm_cellFoundCount_eq_edgeRankDifference, hLeftEq, hRightEq]
  show nCarrierCentralPrime tCarrier (offOriginalUpperMember zOff) =
    nCarrierCentralPrime tCarrier (offMirrorUpperMember zOff)
  unfold nCarrierCentralPrime nCellCentralPrime
  rw [hCentralRankEq]

end TTrueTowerCarrier

end RHV3Lean
