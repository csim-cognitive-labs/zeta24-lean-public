/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.OffMirrorOverlapReduction
import Mathlib.NumberTheory.Chebyshev

/-!
# RHV3Lean — le canal pondéré Chebyshev sur les deux bandes de la paire miroir

    TRACE_ID              : RHV3-OFF-MIRROR-CHEBYSHEV-CHANNEL
    SEMANTIC_OBJECT       : Piste C, resserrement demandé par l'utilisateur --
                            après OffMirrorOverlapReduction (qui réduit la
                            collision à un seul bit de comptage non pondéré),
                            ce module construit le second canal, pondéré par
                            le logarithme du premier trouvé (Chebyshev theta),
                            sur les deux mêmes bandes, et prouve la seule
                            relation qui est un fait arithmétique fini pur,
                            sans aucune formule explicite ni intégration de
                            contour (leçon de §31.2 du maître Lean).
    SEMANTIC_STATEMENT    : sous T1 (un seul premier par cellule), la bande
                            gauche et la bande droite ont toujours le même
                            cardinal non pondéré, et ce cardinal commun vaut 0
                            ou 1 -- jamais plus, parce que chaque bande est
                            structurellement contenue dans une cellule qui n'a
                            elle-même qu'un seul premier. Si ce cardinal vaut
                            0, le poids Chebyshev des deux bandes vaut aussi 0
                            (fait arithmétique pur, sans T1). Si ce cardinal
                            vaut 1, les deux bandes sont géométriquement
                            disjointes et ordonnées -- fait déjà contenu dans
                            l'écart de phase borné, sans T1 non plus -- donc
                            le premier unique de la bande gauche est
                            strictement inférieur au premier unique de la
                            bande droite, et le poids Chebyshev gauche est
                            strictement inférieur au poids Chebyshev droit.
    MATHEMATICAL_STATEMENT: D_pi,L = D_pi,R ∈ {0,1} (sous T1) ;
                            D_pi = 0 ⇒ D_theta = 0 (fait pur, sans T1) ;
                            D_pi = 1 ⇒ D_theta,L < D_theta,R (sous T1 + stage).
    MATHEMATICAL_PARENT   : OffMirrorDifferenceBands.lean (les deux bandes,
                            la borne de largeur exacte) ; OffMirrorOverlapReduction.lean
                            (l'égalité des deux cardinaux sous T1) ;
                            VonMangoldtChebyshev.lean (le rang de comptage) ;
                            Mathlib.NumberTheory.Chebyshev (`Chebyshev.theta`).
    PROOF_STRATEGY        : (1) une bande est nichée dans l'une des deux
                            cellules miroir -- conséquence directe de la borne
                            de décalage déjà prouvée (`thm_mirrorLogGap_abs_lt_width`)
                            combinée à la largeur exacte de cellule
                            (`thm_carrierCell_logWidth`), jamais une nouvelle
                            hypothèse analytique ; (2) le cardinal d'une bande
                            nichée est borné par le cardinal de la cellule qui
                            la contient (monotonie du rang de comptage) ; (3)
                            le poids Chebyshev d'un intervalle sans premier
                            trouvé est nul (égalité des ensembles `primesLE`
                            aux deux bords) ; (4) le poids Chebyshev d'un
                            intervalle à un seul premier trouvé est exactement
                            le logarithme de ce premier (le même argument,
                            avec `insert` au lieu de l'égalité).
    REQUIRED_LEMMAS       : thm_nEdgePrimeRank_mono, thm_mirrorLogGap_abs_lt_width,
                            thm_carrierCell_logWidth, thm_mirrorSameStage_contactPlus,
                            thm_cellFoundCount_eq_edgeRankDifference,
                            thm_cellFoundCount_eq_one_iff_existsUniquePrime,
                            Nat.le_floor_iff, Nat.floor_lt,
                            Nat.primesLE_mono, Nat.primesLE_card_eq_primeCounting,
                            Finset.eq_of_subset_of_card_le, Finset.sum_insert,
                            Real.log_lt_log_iff
    WHY_EACH_LEMMA_EXISTS : les deux premières et la troisième donnent
                            l'imbrication géométrique d'une bande dans une
                            cellule ; la quatrième borne son cardinal ; les
                            suivantes convertissent une égalité (ou une
                            adjonction) de rang de comptage en une égalité (ou
                            un incrément d'un seul terme) du poids Chebyshev.
    LEAN_DEFINITION       : rCellThetaWeight
    LEAN_THEOREM          : thm_cellFoundCount_mono_of_nested,
                            thm_leftBand_nested_in_cell_of_stage,
                            thm_rightBand_nested_in_cell_of_stage,
                            thm_leftBand_count_le_one_of_T1,
                            thm_rightBand_count_le_one_of_T1,
                            thm_mirrorBand_count_mem_zeroOne_of_T1,
                            thm_cellThetaWeight_eq_zero_of_countZero,
                            thm_cellThetaWeight_eq_log_centralPrime_of_countOne,
                            thm_leftBand_lt_rightBand_of_stage,
                            thm_mirrorBand_Dpi_one_imp_Dtheta_strict_of_T1
    SAME_MEMBER_CHECK     : chaque quantité de comptage ou de poids reste
                            fonction des seuls contacts propres des deux
                            membres miroir déjà produits ailleurs.
    SAME_PASSAGE_CHECK    : sans objet -- aucun passage n'est construit ici.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : le canal Chebyshev lit la même histoire première
                            unique que O10 -- `Chebyshev.theta` de Mathlib,
                            jamais une seconde reconstruction.
    FORBIDDEN_PREMISES    : re-dériver `Chebyshev.theta` par la formule
                            explicite ou l'intégration de contour (leçon de
                            §31.2) ; recevoir la relation demi-tour comme
                            hypothèse nommée avant identification d'un
                            théorème classique exact (refus explicite de
                            l'utilisateur) ; choisir une adresse kappa.
    NEXT_CONSUMER         : la suite de la Piste C -- ce module ne clôt PAS
                            la relation analytique demi-tour ; il fournit
                            seulement le second canal et les deux faits
                            arithmétiques purs qui en dérivent, exactement
                            comme demandé.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS            : BODY_PRODUCED. Aucune nouvelle `Prop` nommée :
                             ce module compose uniquement des faits déjà
                             acquis (T1, l'étage commun) avec le comptage
                             pondéré de Mathlib.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

open scoped Nat.Prime

/-! ## 1. Monotonie du cardinal trouvé sous imbrication -/

/-- **Un intervalle niché dans un autre a un cardinal trouvé au plus égal.**
Fait purement arithmétique, conséquence directe de la monotonie du rang de
comptage aux deux bords. -/
theorem thm_cellFoundCount_mono_of_nested
    {I0 I1 : TAlgebraicInterval}
    (hL : I0.rLeftEndpoint ≤ I1.rLeftEndpoint)
    (hR : I1.rRightEndpoint ≤ I0.rRightEndpoint) :
    nCellFoundCount I1 ≤ nCellFoundCount I0 := by
  have hOrdered1 : nEdgePrimeRank I1.rLeftEndpoint ≤ nEdgePrimeRank I1.rRightEndpoint :=
    thm_nEdgePrimeRank_mono (le_of_lt I1.hOrdered)
  have hA : nEdgePrimeRank I0.rLeftEndpoint ≤ nEdgePrimeRank I1.rLeftEndpoint :=
    thm_nEdgePrimeRank_mono hL
  have hB : nEdgePrimeRank I1.rRightEndpoint ≤ nEdgePrimeRank I0.rRightEndpoint :=
    thm_nEdgePrimeRank_mono hR
  have h0 := thm_cellFoundCount_eq_edgeRankDifference I0
  have h1 := thm_cellFoundCount_eq_edgeRankDifference I1
  unfold nCellLeftEdgeRank nCellRightEdgeRank at h0 h1
  omega

/-! ## 2. Le poids Chebyshev d'un intervalle algébrique -/

/-- **Le poids Chebyshev d'un intervalle algébrique** : `theta(C+) - theta(C-)`,
le pendant pondéré exact de `nCellFoundCount`. -/
noncomputable def rCellThetaWeight (I : TAlgebraicInterval) : ℝ :=
  Chebyshev.theta I.rRightEndpoint - Chebyshev.theta I.rLeftEndpoint

/-- **Le poids Chebyshev d'un intervalle sans premier trouvé est nul.** Fait
arithmétique pur : cardinal nul donne l'égalité des deux ensembles `primesLE`
aux deux bords, donc l'égalité des deux sommes pondérées. -/
theorem thm_cellThetaWeight_eq_zero_of_countZero
    (I : TAlgebraicInterval) (h0 : nCellFoundCount I = 0) :
    rCellThetaWeight I = 0 := by
  have hLeftNonneg : (0 : ℝ) ≤ I.rLeftEndpoint := le_of_lt I.hLeftPositive
  have hRightNonneg : (0 : ℝ) ≤ I.rRightEndpoint := le_of_lt I.rightPositive
  have hMono : nEdgePrimeRank I.rLeftEndpoint ≤ nEdgePrimeRank I.rRightEndpoint :=
    thm_nEdgePrimeRank_mono (le_of_lt I.hOrdered)
  have hDiff := thm_cellFoundCount_eq_edgeRankDifference I
  unfold nCellLeftEdgeRank nCellRightEdgeRank at hDiff
  rw [h0] at hDiff
  have hRankEq : nEdgePrimeRank I.rLeftEndpoint = nEdgePrimeRank I.rRightEndpoint := by omega
  have hCardEq :
      (Nat.primesLE ⌊I.rLeftEndpoint⌋₊).card = (Nat.primesLE ⌊I.rRightEndpoint⌋₊).card := by
    rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
    unfold nEdgePrimeRank at hRankEq
    unfold Nat.primeCounting Nat.primeCounting'
    exact hRankEq
  have hSub : Nat.primesLE ⌊I.rLeftEndpoint⌋₊ ⊆ Nat.primesLE ⌊I.rRightEndpoint⌋₊ :=
    Nat.primesLE_mono (Nat.floor_le_floor (le_of_lt I.hOrdered))
  have hSetEq :
      Nat.primesLE ⌊I.rLeftEndpoint⌋₊ = Nat.primesLE ⌊I.rRightEndpoint⌋₊ :=
    Finset.eq_of_subset_of_card_le hSub (le_of_eq hCardEq.symm)
  unfold rCellThetaWeight
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE, hSetEq, sub_self]

/-- **Le poids Chebyshev d'un intervalle à un seul premier trouvé est
exactement le logarithme de ce premier**, qui est aussi son premier central.
Même argument que le cas nul, avec `insert` au lieu de l'égalité des deux
ensembles. -/
theorem thm_cellThetaWeight_eq_log_centralPrime_of_countOne
    (I : TAlgebraicInterval) (h1 : nCellFoundCount I = 1) :
    rCellThetaWeight I = Real.log (nCellCentralPrime I) := by
  have hLeftNonneg : (0 : ℝ) ≤ I.rLeftEndpoint := le_of_lt I.hLeftPositive
  have hRightNonneg : (0 : ℝ) ≤ I.rRightEndpoint := le_of_lt I.rightPositive
  obtain ⟨p, ⟨hpPrime, hpLeft, hpRight⟩, hUniq⟩ :=
    (thm_cellFoundCount_eq_one_iff_existsUniquePrime I).mp h1
  have hCentralEqP : nCellCentralPrime I = p := by
    have hFoundNonempty : 0 < nCellFoundCount I := by omega
    exact hUniq (nCellCentralPrime I)
      ⟨thm_cellCentralPrime_isPrime I, thm_cellCentralPrime_in_interval I hFoundNonempty⟩
  have hNotInLeft : p ∉ Nat.primesLE ⌊I.rLeftEndpoint⌋₊ := by
    intro hMem
    have hpLe : (p : ℝ) ≤ I.rLeftEndpoint :=
      (Nat.le_floor_iff hLeftNonneg).mp (Nat.mem_primesLE.mp hMem).1
    exact absurd hpLe (not_le.mpr hpLeft)
  have hInsert :
      Nat.primesLE ⌊I.rRightEndpoint⌋₊ = insert p (Nat.primesLE ⌊I.rLeftEndpoint⌋₊) := by
    ext q
    simp only [Finset.mem_insert, Nat.mem_primesLE]
    constructor
    · rintro ⟨hqRight, hqPrime⟩
      by_cases hqLeft : (q : ℝ) ≤ I.rLeftEndpoint
      · exact Or.inr ⟨(Nat.le_floor_iff hLeftNonneg).mpr hqLeft, hqPrime⟩
      · have hqLeftLt : I.rLeftEndpoint < (q : ℝ) := not_le.mp hqLeft
        have hqRightLe : (q : ℝ) ≤ I.rRightEndpoint :=
          (Nat.le_floor_iff hRightNonneg).mp hqRight
        exact Or.inl (hUniq q ⟨hqPrime, hqLeftLt, hqRightLe⟩)
    · rintro (rfl | ⟨hqLeft, hqPrime⟩)
      · exact ⟨(Nat.le_floor_iff hRightNonneg).mpr hpRight, hpPrime⟩
      · exact ⟨le_trans hqLeft (Nat.floor_le_floor (le_of_lt I.hOrdered)), hqPrime⟩
  unfold rCellThetaWeight
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE, hInsert,
    Finset.sum_insert hNotInLeft, hCentralEqP]
  ring

/-! ## 3. Chaque bande est nichée dans l'une des deux cellules miroir -/

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-- **La bande gauche est toujours nichée dans l'une des deux cellules
miroir.** Conséquence directe et sans nouvelle hypothèse de la borne de
décalage déjà prouvée : le décalage logarithmique entre les deux contacts
inférieurs est strictement en dessous de la largeur exacte de n'importe
laquelle des deux cellules, donc chaque contact inférieur reste strictement
en-deçà du contact supérieur de l'autre membre. -/
theorem thm_crossContactMinus_lt_contactPlus_of_stage
    (hStage : tCarrier.PMirrorSameStageLogGap) (zOff : TOffCriticalLineUpperZero) :
    tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff) <
        tCarrier.rCarrierContactPlus (offOriginalUpperMember zOff) ∧
      tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff) <
        tCarrier.rCarrierContactPlus (offMirrorUpperMember zOff) := by
  have hWidthOrig := tCarrier.thm_carrierCell_logWidth (offOriginalUpperMember zOff)
  have hWidthMirror := tCarrier.thm_carrierCell_logWidth (offMirrorUpperMember zOff)
  have hHeightEq : rTowerHeight (offMirrorUpperMember zOff) =
      rTowerHeight (offOriginalUpperMember zOff) := thm_offMirror_sameHeight zOff
  rw [hHeightEq] at hWidthMirror
  have hGap := tCarrier.thm_mirrorLogGap_abs_lt_width hStage zOff
  rw [abs_lt] at hGap
  have hMinusOrigPos := (tCarrier.tCarrierCell (offOriginalUpperMember zOff)).hLeftPositive
  have hMinusMirrorPos := (tCarrier.tCarrierCell (offMirrorUpperMember zOff)).hLeftPositive
  have hPlusOrigPos := (tCarrier.tCarrierCell (offOriginalUpperMember zOff)).rightPositive
  have hPlusMirrorPos := (tCarrier.tCarrierCell (offMirrorUpperMember zOff)).rightPositive
  constructor
  · have hLog : Real.log (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff)) <
        Real.log (tCarrier.rCarrierContactPlus (offOriginalUpperMember zOff)) := by
      linarith [hGap.2, hWidthOrig]
    exact (thm_algebraicAxis_log_lt_log_iff hMinusMirrorPos hPlusOrigPos).mp hLog
  · have hLog : Real.log (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff)) <
        Real.log (tCarrier.rCarrierContactPlus (offMirrorUpperMember zOff)) := by
      linarith [hGap.1, hWidthMirror]
    exact (thm_algebraicAxis_log_lt_log_iff hMinusOrigPos hPlusMirrorPos).mp hLog

/-- **La bande gauche est nichée dans la cellule originale, ou dans la
cellule miroir** -- selon lequel des deux contacts inférieurs est le plus
petit. -/
theorem thm_leftBand_nested_in_cell_of_stage
    (hStage : tCarrier.PMirrorSameStageLogGap) (zOff : TOffCriticalLineUpperZero) :
    nCellFoundCount (tCarrier.tLeftDifferenceBand hStage zOff) ≤
        nCellFoundCount (tCarrier.tCarrierCell (offOriginalUpperMember zOff)) ∨
      nCellFoundCount (tCarrier.tLeftDifferenceBand hStage zOff) ≤
        nCellFoundCount (tCarrier.tCarrierCell (offMirrorUpperMember zOff)) := by
  have hCross := tCarrier.thm_crossContactMinus_lt_contactPlus_of_stage hStage zOff
  rcases le_total (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff))
      (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff)) with hle | hle
  · left
    exact thm_cellFoundCount_mono_of_nested
      (le_min (le_refl (tCarrier.rCarrierContactMinus (offOriginalUpperMember zOff))) hle)
      (max_le (le_of_lt (tCarrier.tCarrierCell (offOriginalUpperMember zOff)).hOrdered)
        (le_of_lt hCross.1))
  · right
    exact thm_cellFoundCount_mono_of_nested
      (le_min hle (le_refl (tCarrier.rCarrierContactMinus (offMirrorUpperMember zOff))))
      (max_le (le_of_lt hCross.2)
        (le_of_lt (tCarrier.tCarrierCell (offMirrorUpperMember zOff)).hOrdered))

/-- **La bande droite est nichée dans la cellule miroir, ou dans la cellule
originale** -- symétrique de la précédente, sur les contacts supérieurs. -/
theorem thm_rightBand_nested_in_cell_of_stage
    (hStage : tCarrier.PMirrorSameStageLogGap) (zOff : TOffCriticalLineUpperZero) :
    nCellFoundCount (tCarrier.tRightDifferenceBand hStage zOff) ≤
        nCellFoundCount (tCarrier.tCarrierCell (offMirrorUpperMember zOff)) ∨
      nCellFoundCount (tCarrier.tRightDifferenceBand hStage zOff) ≤
        nCellFoundCount (tCarrier.tCarrierCell (offOriginalUpperMember zOff)) := by
  have hCross := tCarrier.thm_crossContactMinus_lt_contactPlus_of_stage hStage zOff
  rcases le_total (tCarrier.rCarrierContactPlus (offOriginalUpperMember zOff))
      (tCarrier.rCarrierContactPlus (offMirrorUpperMember zOff)) with hle | hle
  · left
    exact thm_cellFoundCount_mono_of_nested
      (le_min (le_of_lt hCross.1)
        (le_of_lt (tCarrier.tCarrierCell (offMirrorUpperMember zOff)).hOrdered))
      (max_le hle (le_refl (tCarrier.rCarrierContactPlus (offMirrorUpperMember zOff))))
  · right
    exact thm_cellFoundCount_mono_of_nested
      (le_min (le_of_lt (tCarrier.tCarrierCell (offOriginalUpperMember zOff)).hOrdered)
        (le_of_lt hCross.2))
      (max_le (le_refl (tCarrier.rCarrierContactPlus (offOriginalUpperMember zOff))) hle)

/-! ## 4. Sous T1, chaque bande vaut au plus un -/

/-- **La bande gauche vaut au plus un, sous T1.** Conséquence immédiate de
son imbrication géométrique dans l'une des deux cellules miroir, chacune à
un seul premier. -/
theorem thm_leftBand_count_le_one_of_T1
    (hStage : tCarrier.PMirrorSameStageLogGap) (hT1 : tCarrier.PUniqueCenterRegime)
    (zOff : TOffCriticalLineUpperZero) :
    nCellFoundCount (tCarrier.tLeftDifferenceBand hStage zOff) ≤ 1 := by
  rcases tCarrier.thm_leftBand_nested_in_cell_of_stage hStage zOff with h | h
  · rw [hT1 (offOriginalUpperMember zOff)] at h; exact h
  · rw [hT1 (offMirrorUpperMember zOff)] at h; exact h

/-- **La bande droite vaut au plus un, sous T1.** -/
theorem thm_rightBand_count_le_one_of_T1
    (hStage : tCarrier.PMirrorSameStageLogGap) (hT1 : tCarrier.PUniqueCenterRegime)
    (zOff : TOffCriticalLineUpperZero) :
    nCellFoundCount (tCarrier.tRightDifferenceBand hStage zOff) ≤ 1 := by
  rcases tCarrier.thm_rightBand_nested_in_cell_of_stage hStage zOff with h | h
  · rw [hT1 (offMirrorUpperMember zOff)] at h; exact h
  · rw [hT1 (offOriginalUpperMember zOff)] at h; exact h

/-- **Théorème demandé : `D_pi,L = D_pi,R ∈ {0,1}`, sous T1.** Les deux
bandes ont toujours le même cardinal non pondéré (déjà acquis,
`thm_mirrorBands_sameCount_of_T1`), et ce cardinal commun vaut au plus un --
jamais davantage -- parce que chaque bande est structurellement contenue dans
une cellule qui n'a elle-même qu'un seul premier. -/
theorem thm_mirrorBand_count_mem_zeroOne_of_T1
    (hStage : tCarrier.PMirrorSameStageLogGap) (hT1 : tCarrier.PUniqueCenterRegime)
    (zOff : TOffCriticalLineUpperZero) :
    nCellFoundCount (tCarrier.tLeftDifferenceBand hStage zOff) =
        nCellFoundCount (tCarrier.tRightDifferenceBand hStage zOff) ∧
      (nCellFoundCount (tCarrier.tLeftDifferenceBand hStage zOff) = 0 ∨
        nCellFoundCount (tCarrier.tLeftDifferenceBand hStage zOff) = 1) := by
  have hSame := tCarrier.thm_mirrorBands_sameCount_of_T1 hStage hT1 zOff
  have hLe := tCarrier.thm_leftBand_count_le_one_of_T1 hStage hT1 zOff
  exact ⟨hSame, by omega⟩

/-! ## 5. Les deux bandes sont géométriquement disjointes et ordonnées -/

/-- **La bande gauche se termine strictement avant que la bande droite ne
commence.** Fait pur, conséquence directe de la borne de décalage -- sans
T1, sans aucune hypothèse supplémentaire. -/
theorem thm_leftBand_lt_rightBand_of_stage
    (hStage : tCarrier.PMirrorSameStageLogGap) (zOff : TOffCriticalLineUpperZero) :
    (tCarrier.tLeftDifferenceBand hStage zOff).rRightEndpoint <
      (tCarrier.tRightDifferenceBand hStage zOff).rLeftEndpoint := by
  have hCross := tCarrier.thm_crossContactMinus_lt_contactPlus_of_stage hStage zOff
  have hOrdOrig := (tCarrier.tCarrierCell (offOriginalUpperMember zOff)).hOrdered
  have hOrdMirror := (tCarrier.tCarrierCell (offMirrorUpperMember zOff)).hOrdered
  exact lt_min (max_lt hOrdOrig hCross.1) (max_lt hCross.2 hOrdMirror)

/-! ## 6. Le theorem final : `D_pi = 1 ⇒ D_theta,L < D_theta,R` -/

/-- **Théorème demandé.** Si la bande gauche contient exactement un premier
(donc, par le théorème précédent, la bande droite aussi), alors le poids
Chebyshev de la bande gauche est strictement inférieur à celui de la bande
droite -- parce que les deux bandes sont disjointes et ordonnées, donc le
premier unique de la bande gauche est strictement inférieur au premier
unique de la bande droite. Aucune formule explicite, aucune intégration de
contour : uniquement la composition des faits déjà acquis. -/
theorem thm_mirrorBand_Dpi_one_imp_Dtheta_strict_of_T1
    (hStage : tCarrier.PMirrorSameStageLogGap) (hT1 : tCarrier.PUniqueCenterRegime)
    (zOff : TOffCriticalLineUpperZero)
    (hCountOne : nCellFoundCount (tCarrier.tLeftDifferenceBand hStage zOff) = 1) :
    rCellThetaWeight (tCarrier.tLeftDifferenceBand hStage zOff) <
      rCellThetaWeight (tCarrier.tRightDifferenceBand hStage zOff) := by
  have hSame := tCarrier.thm_mirrorBands_sameCount_of_T1 hStage hT1 zOff
  have hCountOneRight : nCellFoundCount (tCarrier.tRightDifferenceBand hStage zOff) = 1 := by
    rw [← hSame]; exact hCountOne
  have hWeightLeft := thm_cellThetaWeight_eq_log_centralPrime_of_countOne
    (tCarrier.tLeftDifferenceBand hStage zOff) hCountOne
  have hWeightRight := thm_cellThetaWeight_eq_log_centralPrime_of_countOne
    (tCarrier.tRightDifferenceBand hStage zOff) hCountOneRight
  have hMemLeft := thm_cellCentralPrime_in_interval
    (tCarrier.tLeftDifferenceBand hStage zOff) (by omega)
  have hMemRight := thm_cellCentralPrime_in_interval
    (tCarrier.tRightDifferenceBand hStage zOff) (by omega)
  have hSeparation := tCarrier.thm_leftBand_lt_rightBand_of_stage hStage zOff
  have hPrimeLt :
      (nCellCentralPrime (tCarrier.tLeftDifferenceBand hStage zOff) : ℝ) <
        (nCellCentralPrime (tCarrier.tRightDifferenceBand hStage zOff) : ℝ) := by
    calc (nCellCentralPrime (tCarrier.tLeftDifferenceBand hStage zOff) : ℝ)
        ≤ (tCarrier.tLeftDifferenceBand hStage zOff).rRightEndpoint := hMemLeft.2
      _ < (tCarrier.tRightDifferenceBand hStage zOff).rLeftEndpoint := hSeparation
      _ < (nCellCentralPrime (tCarrier.tRightDifferenceBand hStage zOff) : ℝ) := hMemRight.1
  rw [hWeightLeft, hWeightRight]
  have hPosLeft : 0 < nCellCentralPrime (tCarrier.tLeftDifferenceBand hStage zOff) :=
    (thm_cellCentralPrime_isPrime (tCarrier.tLeftDifferenceBand hStage zOff)).pos
  exact Real.log_lt_log (by exact_mod_cast hPosLeft) hPrimeLt

end TTrueTowerCarrier

end RHV3Lean
