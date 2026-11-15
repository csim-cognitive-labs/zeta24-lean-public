/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TowerCriticalDefect

/-!
# RHV3Lean — le passage entre deux états propres, et sa rigidité de largeur

    TRACE_ID              : RHV3-TOWER-TRANSITION
    SEMANTIC_OBJECT       : le passage entre deux Tours propres, comme objet
                            causal remplaçant la cellule ré-initialisée près de
                            deux pour chaque zéro pris isolément.
    SEMANTIC_STATEMENT    : deux états propres réellement fournis, l'un du
                            membre d'entrée, l'autre du membre de sortie,
                            portent chacun leur hauteur, leur position radiale
                            et leur phase propres.  Leur transition conserve
                            ces trois écarts, ainsi que le décalage du contact
                            d'entrée, la largeur de chaque cellule et son écart,
                            et le centre logarithmique de chaque cellule.  Rien
                            de tout cela n'est choisi : chaque quantité est
                            dérivée des deux seuls états reçus.
    MATHEMATICAL_STATEMENT: heightGap = T_right - T_left ;
                            radialGap = beta_right - beta_left ;
                            phaseGap = phi_right - phi_left ;
                            leftLogShift = log L_right - log L_left ;
                            widthLeft = log R_left - log L_left = pi/T_left ;
                            widthRight = log R_right - log L_right = pi/T_right ;
                            widthGap = widthRight - widthLeft
                                     = pi*(1/T_right - 1/T_left) ;
                            log R_right - log R_left = leftLogShift + widthGap ;
                            centerLog(S) = (log L + log R)/2 ;
                            centerShift = leftLogShift + widthGap/2.
    MATHEMATICAL_PARENT   : O3 — la Tour harmonique ; O4 — les contacts et la
                            cellule (`TrueTowerState.lean`) ; §33/§34 du maître
                            Lean (correction de la succession universelle).
    PROOF_STRATEGY        : chaque identité est une combinaison linéaire directe
                            des deux équations `consecutive_width` des deux
                            états, ou de leur différence ; `widthGap` utilise en
                            outre la positivité stricte des deux hauteurs pour
                            l'inversion `1/T`.  Aucune borne, aucune analyse,
                            aucune hypothèse de croissance.
    REQUIRED_LEMMAS       : TTrueHarmonicTowerState.consecutive_width (x2),
                            thm_rTowerHeight_positive (x2)
    WHY_EACH_LEMMA_EXISTS : la première donne la largeur exacte de chaque
                            cellule ; la seconde permet l'inversion `1/T` sans
                            perte, aux deux membres.
    LEAN_DEFINITION       : TTowerMemberTransition, heightGap, radialGap,
                            phaseGap, leftLogShift, widthLeft, widthRight,
                            widthGap, centerLog, centerShift
    LEAN_THEOREM          : thm_widthGap_eq_heightGap_reciprocal,
                            thm_widthRight_lt_widthLeft_of_heightGap_pos,
                            thm_contactPlusLogGap_eq_shift_plus_widthGap,
                            thm_centerShift_eq_shift_plus_halfWidthGap
    SAME_MEMBER_CHECK     : chaque quantité dérivée lit exclusivement les deux
                            états `SLeft`/`SRight` reçus par la structure ;
                            aucune substitution n'est exprimable.
    SAME_PASSAGE_CHECK    : toutes les identités de ce module portent sur LA
                            MÊME transition `T : TTowerMemberTransition`.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau — la composition à trois
                            membres est un consommateur ultérieur.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre dans ce module.
    FORBIDDEN_PREMISES    : premier, rang, comptage, C3, T1, T2, R-PASS,
                            hypothèse de Riemann ; toute conclusion stockée
                            comme champ de `TTowerMemberTransition`.
    NEXT_CONSUMER         : la signature OFF de la paire miroir
                            (`TowerTransitionOffSignature.lean`), et la lecture
                            quantitative du gap premier par la Tour
                            (`TowerPrimeGapSpan.lean`).
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

open TTrueHarmonicTowerState

/-! ## 1. Le passage entre deux états propres -/

/-- **Le passage entre deux Tours propres.**  Deux membres, et un état propre
réellement fourni pour chacun.  Aucun champ ne stocke une conclusion : toutes
les quantités dérivées ci-dessous sont des fonctions de ces quatre données. -/
structure TTowerMemberTransition where
  /-- Le membre d'entrée. -/
  zLeft : TUpperNonTrivialZetaZero
  /-- Le membre de sortie. -/
  zRight : TUpperNonTrivialZetaZero
  /-- L'état propre réel du membre d'entrée. -/
  SLeft : TTrueHarmonicTowerState zLeft
  /-- L'état propre réel du membre de sortie. -/
  SRight : TTrueHarmonicTowerState zRight

namespace TTowerMemberTransition

variable (Tr : TTowerMemberTransition)

/-! ## 2. Les trois écarts propres -/

/-- **L'écart de hauteur.** -/
def heightGap : ℝ := rZeroHeight Tr.zRight.1 - rZeroHeight Tr.zLeft.1

/-- **L'écart de position radiale.** -/
def radialGap : ℝ := rZeroRadialPosition Tr.zRight.1 - rZeroRadialPosition Tr.zLeft.1

/-- **L'écart de phase.** -/
noncomputable def phaseGap : ℝ := rTowerPhase Tr.zRight - rTowerPhase Tr.zLeft

/-! ## 3. Le décalage de contact, et les deux largeurs -/

/-- **Le décalage logarithmique du contact d'entrée.** -/
noncomputable def leftLogShift : ℝ :=
  Real.log Tr.SRight.contactMinus - Real.log Tr.SLeft.contactMinus

/-- **La largeur logarithmique de la cellule d'entrée.** -/
noncomputable def widthLeft : ℝ :=
  Real.log Tr.SLeft.contactPlus - Real.log Tr.SLeft.contactMinus

/-- **La largeur logarithmique de la cellule de sortie.** -/
noncomputable def widthRight : ℝ :=
  Real.log Tr.SRight.contactPlus - Real.log Tr.SRight.contactMinus

/-- **L'écart des deux largeurs.** -/
noncomputable def widthGap : ℝ := Tr.widthRight - Tr.widthLeft

/-! ## 4. Le centre logarithmique de chaque cellule -/

/-- **Le centre logarithmique d'un état propre quelconque.** -/
noncomputable def centerLog {z : TUpperNonTrivialZetaZero}
    (S : TTrueHarmonicTowerState z) : ℝ :=
  (Real.log S.contactMinus + Real.log S.contactPlus) / 2

/-- **Le décalage du centre logarithmique.** -/
noncomputable def centerShift : ℝ :=
  centerLog Tr.SRight - centerLog Tr.SLeft

/-! ## 5. Rigidité de largeur — la conservation exacte -/

/-- **Les deux largeurs sont exactement `pi/T`.**  Relecture directe de
`consecutive_width` des deux états. -/
theorem thm_widthLeft_eq (Tr : TTowerMemberTransition) :
    Tr.widthLeft = Real.pi / rZeroHeight Tr.zLeft.1 :=
  Tr.SLeft.consecutive_width

theorem thm_widthRight_eq (Tr : TTowerMemberTransition) :
    Tr.widthRight = Real.pi / rZeroHeight Tr.zRight.1 :=
  Tr.SRight.consecutive_width

/-- **L'ÉCART DE LARGEUR EST EXACTEMENT `pi*(1/T_right - 1/T_left)`.**
Conservation exacte de la Tour propre entre deux membres, sans aucune borne
ni approximation. -/
theorem thm_widthGap_eq_heightGap_reciprocal (Tr : TTowerMemberTransition) :
    Tr.widthGap =
      Real.pi * (1 / rZeroHeight Tr.zRight.1 - 1 / rZeroHeight Tr.zLeft.1) := by
  unfold widthGap
  rw [Tr.thm_widthRight_eq, Tr.thm_widthLeft_eq]
  ring

/-- **Si la hauteur croît, la largeur de la cellule de sortie est strictement
plus petite que celle de la cellule d'entrée.**  Conséquence directe de la
décroissance stricte de `x -> 1/x` sur les réels strictement positifs. -/
theorem thm_widthRight_lt_widthLeft_of_heightGap_pos (Tr : TTowerMemberTransition)
    (hPos : 0 < Tr.heightGap) : Tr.widthRight < Tr.widthLeft := by
  have hLeftPos : 0 < rZeroHeight Tr.zLeft.1 := Tr.zLeft.2
  have hRightPos : 0 < rZeroHeight Tr.zRight.1 := Tr.zRight.2
  have hOrder : rZeroHeight Tr.zLeft.1 < rZeroHeight Tr.zRight.1 := by
    unfold TTowerMemberTransition.heightGap at hPos; linarith
  have hReciprocal :
      1 / rZeroHeight Tr.zRight.1 < 1 / rZeroHeight Tr.zLeft.1 :=
    one_div_lt_one_div_of_lt hLeftPos hOrder
  have hGap : Tr.widthGap < 0 := by
    rw [thm_widthGap_eq_heightGap_reciprocal]
    have : Real.pi * (1 / rZeroHeight Tr.zRight.1 - 1 / rZeroHeight Tr.zLeft.1) < 0 :=
      mul_neg_of_pos_of_neg Real.pi_pos (by linarith)
    linarith
  unfold TTowerMemberTransition.widthGap at hGap
  linarith

/-! ## 6. Le contact terminal, et le centre, sont conservés composante par
composante -/

/-- **Le décalage du contact terminal se décompose exactement en décalage
d'entrée plus écart de largeur.** -/
theorem thm_contactPlusLogGap_eq_shift_plus_widthGap (Tr : TTowerMemberTransition) :
    Real.log Tr.SRight.contactPlus - Real.log Tr.SLeft.contactPlus =
      Tr.leftLogShift + Tr.widthGap := by
  unfold TTowerMemberTransition.leftLogShift TTowerMemberTransition.widthGap
    TTowerMemberTransition.widthLeft TTowerMemberTransition.widthRight
  ring

/-- **Le décalage du centre logarithmique se décompose exactement en décalage
d'entrée plus la moitié de l'écart de largeur.** -/
theorem thm_centerShift_eq_shift_plus_halfWidthGap (Tr : TTowerMemberTransition) :
    Tr.centerShift = Tr.leftLogShift + Tr.widthGap / 2 := by
  unfold TTowerMemberTransition.centerShift TTowerMemberTransition.centerLog
    TTowerMemberTransition.leftLogShift TTowerMemberTransition.widthGap
    TTowerMemberTransition.widthLeft TTowerMemberTransition.widthRight
  ring

end TTowerMemberTransition

/-! Surface audit. -/

#check TTowerMemberTransition
#check TTowerMemberTransition.thm_widthGap_eq_heightGap_reciprocal
#check TTowerMemberTransition.thm_widthRight_lt_widthLeft_of_heightGap_pos
#check TTowerMemberTransition.thm_contactPlusLogGap_eq_shift_plus_widthGap
#check TTowerMemberTransition.thm_centerShift_eq_shift_plus_halfWidthGap

end RHV3Lean
