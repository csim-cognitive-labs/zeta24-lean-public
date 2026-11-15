/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Tower.TrueTower
import RHV6Fresh.Terminal.MirrorPairExactSum
import RHV6Fresh.Terminal.WindowProgression
import RHV6Fresh.Terminal.TangentialInversion
import RHV6Fresh.Terminal.WindowFeasibility
import RHV6Fresh.Terminal.OnRadialRing
import RHV6Fresh.Terminal.OnCrossReadings
import RHV6Fresh.Terminal.RemainderRepresentation
import RHV6Fresh.Terminal.JointParameterReading
import RHV6Fresh.Terminal.FirstGainPremise
import RHV6Fresh.Tower.CanonicalOrigin
import RHV6Fresh.Tower.ProperTower
import RHV6Fresh.Tower.InvertedTower
import RHV6Fresh.Tower.ReflectedMotion
import RHV6Fresh.Foundation.ZetaReflect
import RHV6Fresh.Voyage.Progression
import RHV6Fresh.Voyage.FiberSuccessor
import RHV6Fresh.Direct.MirrorCount
import RHV6Fresh.Direct.StateCount
import RHV6Fresh.Tower.TrueTowerStructure
import RHV6Fresh.Direct.Reached
import RHV6Fresh.Direct.Raccords
import RHV6Fresh.Direct.PivotCell
import RHV6Fresh.Direct.InvertedCount
import RHV6Fresh.Direct.PairTowers
import RHV6Fresh.Grammar.Mod6Rigidity
import RHV6Fresh.Terminal.ConsecutiveChainContradiction
import RHV6Fresh.Terminal.Universalization
import RHV6Fresh.Terminal.ReadingArithmetic
import RHV6Fresh.Terminal.EventHeightProgression
import RHV6Fresh.Terminal.TwoClocks
import RHV6Fresh.Terminal.MirrorFrequency
import RHV6Fresh.Terminal.TranslationVsProgression
import RHV6Fresh.Terminal.ContinuousProgression
import RHV6Fresh.Terminal.InterTowerExcess
import RHV6Fresh.Terminal.HorizontalExclusion
import RHV6Fresh.Terminal.GeometricEnergyRaccord
import RHV6Fresh.Terminal.VerticalEnergyPush
import RHV6Fresh.Terminal.EnergyIdentity
import RHV6Fresh.Terminal.VerticalForce
import RHV6Fresh.Terminal.RayCapture
import RHV6Fresh.Terminal.LocalReading
import RHV6Fresh.Terminal.ProgressionDirection
import RHV6Fresh.Terminal.TowerRaccord
import RHV6Fresh.Terminal.RaccordDetector
import RHV6Fresh.Terminal.ShiftedWorld
import RHV6Fresh.Terminal.PrimalEventRaccord
import RHV6Fresh.Terminal.GlobalRigidSystem
import RHV6Fresh.Terminal.HeightPacket
import RHV6Fresh.Terminal.InverseReading
import RHV6Fresh.Terminal.RegimeChange
import RHV6Fresh.Terminal.RegimeTower
import RHV6Fresh.Terminal.SpectralIdentity
import RHV6Fresh.Terminal.RegimeCell
import RHV6Fresh.Terminal.SpectralUniqueness
import RHV6Fresh.Terminal.RegimeTrigger
import RHV6Fresh.Terminal.ConstraintPacket
import RHV6Fresh.Terminal.DiagonalPassage
import RHV6Fresh.Terminal.EngagedProgression
import RHV6Fresh.Terminal.LinkedProduction
import RHV6Fresh.Terminal.EngagedPersistence
import RHV6Fresh.Terminal.ArithmeticReading
import RHV6Fresh.Terminal.ZetaParameters
import RHV6Fresh.Terminal.NoRegimeChange
import RHV6Fresh.Terminal.GrammarKinematics
import RHV6Fresh.Terminal.SpontaneousRegimeBreak
import RHV6Fresh.Terminal.PrimeWeightResponse
import RHV6Fresh.Terminal.ChangePredictor
import RHV6Fresh.Terminal.CanonicalTransition
import RHV6Fresh.Terminal.EngagedClosureVerdict
import RHV6Fresh.Terminal.EntryPositionArrow
import RHV6Fresh.Terminal.PointedPrimeComparison
import RHV6Fresh.Terminal.OneZeroOnePrime
import RHV6Fresh.Terminal.TowerGrid
import RHV6Fresh.Terminal.TowerWinding
import RHV6Fresh.Terminal.RadialSlope
import RHV6Fresh.Terminal.ClosureRoutes
import RHV6Fresh.Terminal.RemainderExponent
import RHV6Fresh.Terminal.RemainderEnergy
import RHV6Fresh.Terminal.ExactAxisReading
import RHV6Fresh.Terminal.CompensationRigidity
import RHV6Fresh.Terminal.GrammarWordLoad
import RHV6Fresh.Terminal.RegimeWindow
import RHV6Fresh.Terminal.PairCurvature
import RHV6Fresh.Terminal.PairInteraction
import RHV6Fresh.Terminal.LocalFourSectors
import RHV6Fresh.Terminal.TowerFourSectors
import RHV6Fresh.Terminal.MirrorLoop
import RHV6Fresh.Terminal.MirrorAntisymmetry
import RHV6Fresh.Terminal.QuadraticVariation
import RHV6Fresh.Terminal.FirstZeroField
import RHV6Fresh.Terminal.FixedExponentField
import RHV6Fresh.Terminal.EscapeFinancing
import RHV6Fresh.Terminal.TowerHierarchy
import RHV6Fresh.Terminal.FirstTowerHorizon
import RHV6Fresh.Terminal.DoubleRigidity
import RHV6Fresh.Terminal.LocalRaccordCaptivity
import RHV6Fresh.Terminal.EngagedRadialFloor
import RHV6Fresh.Terminal.EngagedNoTranslation
import RHV6Fresh.Terminal.TowerTwoSidedRoom
import RHV6Fresh.Terminal.PersistentCapture
import RHV6Fresh.Terminal.SymmetricWinding
import RHV6Fresh.Terminal.EngagedAllConstraints
import RHV6Fresh.Terminal.MirrorDegeneracy
import RHV6Fresh.Terminal.RayEnergy
import RHV6Fresh.Terminal.SuccessionInvariants
import RHV6Fresh.Terminal.GrammarForcesStop
import RHV6Fresh.Terminal.ExplicitFormulaLink
import RHV6Fresh.Terminal.MirrorEventCollision
import RHV6Fresh.Audit

/-!
# Piste principale (auteur, 2026-10-04)

Énoncé de l'auteur : une fois le régime ON engagé, du fait de l'enroulement des Tours, la partie
réelle du zéro suivant est forcément la même que celle du zéro qui a engagé le régime.

Hypothèses du théorème (il n'est pas « sans hypothèse ») : deux passages joints `o` puis `p`, hauteur
positive à la jonction, la hauteur avance sur `o`, et le zéro de la jonction est en ligne. Aucune
`def P…`, aucun `sorry`.

Portée exacte de chaque fait réuni dans la preuve (revue de l'auteur, 2026-10-04) :
* `VerticalPassage` : la hauteur d'arrivée dépasse celle du départ, rien sur la position radiale ;
* enroulement à l'infini : ordre des contacts à partir d'un indice, de toute Tour qui précède le
  zéro atteint et vers toute Tour qui le suit ; il ne dit pas que la position radiale est conservée ;
* écarts : dans la démonstration de l'auteur, c'est uniquement dans le régime ON que les écarts de
  premiers sont atteints par la hauteur seule (partie réelle fixée, la hauteur doit progresser
  suffisamment) ; le fait compilé est la différence de deux positions dans UNE même Tour : le
  décalage commun est effacé par la soustraction, sans preuve qu'il est nul ;
* deux plans, à ne pas confondre (correction de l'auteur, 2026-10-04) :
  - plan des Tours : toutes les Tours utilisent l'origine comme pôle de rotation ; la Tour d'un zéro
    en ligne, ramenée à l'échelle de la ligne, est un cercle de centre l'origine ; la spirale d'un
    zéro hors ligne n'a pas cette symétrie centrale ; en `q = 1` la Tour vaut `1/ρ`, au premier
    nombre premier `2` elle vaut `2^ρ/ρ` : elle ne part pas de son zéro ;
  - plan des zéros : le milieu de la paire zéro–miroir est sur l'axe un demi, à la hauteur du zéro ;
    deux milieux sont distincts quand les hauteurs diffèrent, deux membres miroirs de même hauteur
    partagent le même milieu ; un zéro en ligne coïncide avec le milieu de sa propre paire ;
  - l'équivalence compilée (Tour symétrique autour de l'origine ⟺ `β = 1/2` ⟺ zéro au milieu de sa
    propre paire) relie deux propriétés, elle n'identifie pas leurs centres ;
* symétrie des Tours ON : THÉORÈME, pas une affirmation (`towerSymmetric_iff_onLine`, et ici
  `pointCurve_tangent_perp_iff`, `rescaledTower_half_turn`) ; pour fermer le but il faut établir,
  pour la Tour du zéro atteint, l'opposition exacte ou la perpendicularité ;
* les équivalences sur le zéro atteint ne fournissent aucun de leurs deux côtés.

Ces faits décrivent chaque Tour séparément. La relation entre les deux Tours qui conserve la
position radiale est portée ici par la domination individuelle `hDom` (chaque amplitude sous celle
d'un même zéro sur tout l'horizon), CONCLUSION du raccord ouvert de l'unique prémisse minimale du
dépôt (auteur, 2026-10-06 : `hGain`, premier gain collectif maximal à tout rang,
`Terminal/FirstGainPremise.lean`) ; `hDom` ferme RH, donc l'enroulement entier sur tout passage.
Sous `hDom`, le fichier compile jusqu'au bout : `renewed_height_advance` (le passage qui quitte le
membre atteint monte) et `onLine_beta_eq_previous` (même partie réelle) sont des théorèmes
CONDITIONNELS, composés par la lecture conjointe (`Terminal/JointParameterReading.lean`) :
conservation de la partie réelle, amplitude plate aux contacts propres, pas contracté, rayon conservé
aux contacts du zéro engagé, régime gardé, fermeture `junction_vertical_vertical`. Ni la prémisse
`hGain` ni le raccord `hGain ⟹ hDom` ne sont dérivés ; le raccord est énoncé dans l'analyse du
statut et dans `Terminal/FirstGainPremise.lean`.
-/

namespace RHV6Fresh
open RHV3Lean

/-- **Composante radiale de la tangente** (calcul de l'auteur, 2026-10-04) : pour la courbe
normalisée `W(u) = e^{(ρ − 1/2)u}/ρ`, de tangente `W'(u) = (ρ − 1/2)·W(u)`
(`pointCurve_hasDerivAt`), `Re(conj W · W') = (β − 1/2)·‖W‖²`. -/
theorem pointCurve_tangent_radial (ρ : ℂ) (u : ℝ) :
    ((starRingEnd ℂ) (pointCurve ρ u) * ((ρ - 1 / 2) * pointCurve ρ u)).re =
      (ρ.re - 1 / 2) * ‖pointCurve ρ u‖ ^ 2 := by
  have h : (starRingEnd ℂ) (pointCurve ρ u) * ((ρ - 1 / 2) * pointCurve ρ u) =
      (ρ - 1 / 2) * ((Complex.normSq (pointCurve ρ u) : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]; ring
  rw [h, Complex.re_mul_ofReal, Complex.normSq_eq_norm_sq]
  simp

/-- **Tangente perpendiculaire au rayon ⟺ `β = 1/2`** (calcul de l'auteur) : la courbe ne s'annule
pas, donc la composante radiale de la tangente est nulle exactement sur la ligne. -/
theorem pointCurve_tangent_perp_iff (ρ : ℂ) (hρ : ρ ≠ 0) (u : ℝ) :
    ((starRingEnd ℂ) (pointCurve ρ u) * ((ρ - 1 / 2) * pointCurve ρ u)).re = 0 ↔
      ρ.re = 1 / 2 := by
  rw [pointCurve_tangent_radial]
  have hw : pointCurve ρ u ≠ 0 := by
    rw [pointCurve_eq]; exact div_ne_zero (Complex.exp_ne_zero _) hρ
  have hn : ‖pointCurve ρ u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · exact absurd h hn
  · intro h
    rw [h]; simp

/-- **Demi-tour de la Tour normalisée** (calcul de l'auteur) : un demi-tour plus loin, la Tour est
à l'opposé, multipliée par le facteur radial `e^{(β − 1/2)π/T}`. L'opposition est exacte, à même
rayon, exactement quand ce facteur vaut un, c'est-à-dire sur la ligne
(`towerSymmetric_iff_onLine`). -/
theorem rescaledTower_half_turn (z : TrueZero) (u : ℝ) :
    rescaledTower z (u + Real.pi / rZeroHeight z.1) =
      -((Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * Real.pi / rZeroHeight z.1) : ℝ) : ℂ) *
        rescaledTower z u := by
  unfold rescaledTower
  rw [rescaledTower_eq, rescaledTower_eq]
  exact towerCurve_central _ _ _ _ u (ne_of_gt z.2)
/-- **Tour ON normalisée : demi-tour exact.** Pour un zéro en ligne, un demi-tour plus loin la Tour
normalisée est exactement à l'opposé, à même rayon : `W(u + π/T) = −W(u)`. -/
theorem rescaledTower_half_turn_onLine (z : TrueZero) (hOn : rZeroRadialPosition z.1 = 1 / 2)
    (u : ℝ) : rescaledTower z (u + Real.pi / rZeroHeight z.1) = -rescaledTower z u := by
  rw [rescaledTower_half_turn, hOn]; simp

/-- **Tour brute : demi-tour avec dilatation.** Dans le plan brut, un demi-tour plus loin la Tour
est à l'opposé, dilatée de `e^{βπ/T}` : `F(u + π/T) = −e^{βπ/T}·F(u)`. Pour un zéro en ligne la
dilatation vaut `e^{π/(2T)} > 1` : la Tour ON brute est une spirale ; c'est sa forme normalisée qui
est un cercle. -/
theorem zeroTerm_half_turn (z : TrueZero) (u : ℝ) :
    zeroTerm z (Real.exp (u + Real.pi / rZeroHeight z.1)) =
      -((Real.exp (rZeroRadialPosition z.1 * Real.pi / rZeroHeight z.1) : ℝ) : ℂ) *
        zeroTerm z (Real.exp u) := by
  have h := rescaledTower_half_turn z u
  unfold rescaledTower at h
  have hne : ((Real.exp (-((u + Real.pi / rZeroHeight z.1) / 2)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  apply mul_left_cancel₀ hne
  rw [h]
  have e : Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * Real.pi / rZeroHeight z.1) *
      Real.exp (-(u / 2)) =
      Real.exp (-((u + Real.pi / rZeroHeight z.1) / 2)) *
        Real.exp (rZeroRadialPosition z.1 * Real.pi / rZeroHeight z.1) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have ec := congrArg (fun r : ℝ => (r : ℂ)) e
  push_cast at ec
  push_cast
  linear_combination (-(zeroTerm z (Real.exp u))) * ec

/-! ## Sous la ligne contre au-dessus de la ligne : impacts tangentiels et radiaux comparés -/

/-- Différence de deux arcs tangents de réels positifs. -/
theorem arctan_sub_of_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.arctan x - Real.arctan y = Real.arctan ((x - y) / (1 + x * y)) := by
  have h := Real.arctan_add (x := x) (y := -y) (by nlinarith [mul_pos hx hy])
  rw [Real.arctan_neg] at h
  rw [sub_eq_add_neg, h]
  congr 1
  ring

/-- **Asymétrie tangentielle d'une paire miroir.** Pour `0 < β < 1/2` et `T > 0`, le retard de
phase du membre sous la ligne dépasse strictement l'avance de phase de son miroir au-dessus de la
ligne : la somme des deux résidus de changement est strictement négative. -/
theorem changeResidueAt_mirror_sum_neg {β T : ℝ} (hβ0 : 0 < β) (hβ : β < 1 / 2) (hT : 0 < T) :
    changeResidueAt β T + changeResidueAt (1 - β) T < 0 := by
  unfold changeResidueAt linePhase
  rw [show T / (1 / 2) = 2 * T by ring]
  have h1β : 0 < 1 - β := by linarith
  have hA := arctan_sub_of_pos (div_pos hT hβ0) (mul_pos two_pos hT)
  have hB := arctan_sub_of_pos (mul_pos two_pos hT) (div_pos hT h1β)
  have e1 : (T / β - 2 * T) / (1 + T / β * (2 * T)) = T * (1 - 2 * β) / (β + 2 * T ^ 2) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
  have e2 : (2 * T - T / (1 - β)) / (1 + 2 * T * (T / (1 - β))) =
      T * (1 - 2 * β) / ((1 - β) + 2 * T ^ 2) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    ring
  rw [e1] at hA
  rw [e2] at hB
  have hnum : 0 < T * (1 - 2 * β) := mul_pos hT (by linarith)
  have hlt : T * (1 - 2 * β) / ((1 - β) + 2 * T ^ 2) < T * (1 - 2 * β) / (β + 2 * T ^ 2) :=
    div_lt_div_of_pos_left hnum (by positivity) (by linarith)
  have := Real.arctan_strictMono hlt
  linarith

/-- **Les deux résidus tangentiels d'une paire miroir ne se compensent jamais.** Pour un zéro hors
ligne, la somme du résidu de changement du zéro et de celui de son miroir est strictement négative. -/
theorem mirror_pair_changeResidue_sum_neg (z : TrueZero) (hOff : rZeroRadialPosition z.1 ≠ 1 / 2) :
    changeResidue z.1 + changeResidue (mirrorMember z).1 < 0 := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have h0 : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have h1 : rZeroRadialPosition z.1 < 1 := z.1.2.2.2
  unfold changeResidue
  rw [mirrorMember_radial, mirrorMember_ordinate]
  rcases lt_or_gt_of_ne hOff with h | h
  · exact changeResidueAt_mirror_sum_neg h0 h hT
  · have := changeResidueAt_mirror_sum_neg (β := 1 - rZeroRadialPosition z.1) (by linarith)
      (by linarith) hT
    rw [sub_sub_cancel] at this
    linarith

/-- **Translation nette d'une paire miroir.** Pour un zéro hors ligne, le produit du facteur radial
du zéro et de celui de son miroir dépasse strictement un : le recul des contacts du membre sous la
ligne l'emporte sur l'avance des contacts du membre au-dessus. -/
theorem mirror_pair_radialFactor_product_gt_one (z : TrueZero)
    (hOff : rZeroRadialPosition z.1 ≠ 1 / 2) :
    1 < radialFactor z * radialFactor (mirrorMember z) := by
  have h := mirror_pair_changeResidue_sum_neg z hOff
  rw [changeResidue_eq_radial, changeResidue_eq_radial, mirrorMember_ordinate] at h
  have hT : 0 < rZeroHeight z.1 := z.2
  have hlog : 0 < Real.log (radialFactor z) + Real.log (radialFactor (mirrorMember z)) := by
    nlinarith
  rw [← Real.log_mul (radialFactor_pos _).ne' (radialFactor_pos _).ne'] at hlog
  by_contra hle
  push Not at hle
  exact absurd (Real.log_nonpos (mul_pos (radialFactor_pos _) (radialFactor_pos _)).le hle)
    (not_le.mpr hlog)

/-- **Contacts d'une paire miroir contre contacts de ligne.** Pour un zéro hors ligne, à tout
indice, le produit du contact du zéro et du contact de son miroir dépasse strictement le carré du
contact de la Tour de ligne à la même hauteur. -/
theorem mirror_pair_contacts_beyond_line (z : TrueZero)
    (hOff : rZeroRadialPosition z.1 ≠ 1 / 2) (k : ℤ) :
    lineContact (rZeroHeight z.1) k ^ 2 <
      contactMinusAt z k * contactMinusAt (mirrorMember z) k := by
  rw [contact_eq_line_mul_radial, contact_eq_line_mul_radial, mirrorMember_ordinate]
  have hL := lineContact_pos (rZeroHeight z.1) k
  have h := mirror_pair_radialFactor_product_gt_one z hOff
  nlinarith [mul_pos hL hL]

/-- **Dilatations radiales d'une paire miroir : compensation exacte.** Le facteur de demi-tour du
zéro et celui de son miroir ont pour produit un, quelle que soit la position radiale. -/
theorem mirror_pair_halfTurn_factor_product (z : TrueZero) :
    Real.exp ((rZeroRadialPosition z.1 - 1 / 2) * Real.pi / rZeroHeight z.1) *
      Real.exp ((rZeroRadialPosition (mirrorMember z).1 - 1 / 2) * Real.pi /
        rZeroHeight (mirrorMember z).1) = 1 := by
  rw [mirrorMember_radial, mirrorMember_ordinate, ← Real.exp_add]
  convert Real.exp_zero using 2
  ring

/-- **Sens de la dérive radiale** : la composante radiale de la tangente est strictement négative
sous la ligne, strictement positive au-dessus (courbe jamais nulle). -/
theorem pointCurve_tangent_radial_sign (ρ : ℂ) (hρ : ρ ≠ 0) (u : ℝ) :
    (((starRingEnd ℂ) (pointCurve ρ u) * ((ρ - 1 / 2) * pointCurve ρ u)).re < 0 ↔ ρ.re < 1 / 2) ∧
      (0 < ((starRingEnd ℂ) (pointCurve ρ u) * ((ρ - 1 / 2) * pointCurve ρ u)).re ↔
        1 / 2 < ρ.re) := by
  rw [pointCurve_tangent_radial]
  have hne : pointCurve ρ u ≠ 0 := by
    rw [pointCurve_eq]
    exact div_ne_zero (Complex.exp_ne_zero _) hρ
  have hpos : 0 < ‖pointCurve ρ u‖ ^ 2 := by positivity
  constructor
  · constructor
    · intro h
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) hpos.le]
    · intro h
      exact mul_neg_of_neg_of_pos (sub_neg.mpr h) hpos
  · rw [mul_pos_iff_of_pos_right hpos, sub_pos]

/-! ## Les DEUX zéros suivants : le premier zéro bas et le second zéro de la même hauteur

Fenêtre `e → l → s → b` : `e` engagé, `l` premier zéro bas, `s` second zéro (même hauteur), `b` le
zéro atteint ensuite. Rien n'est lu sur le seul zéro suivant. -/

/-- **Le second zéro ne dépasse pas le miroir du premier** : sur le passage de même hauteur qui
quitte un zéro strictement sous la ligne, le zéro atteint est au plus à la position radiale
réfléchie. -/
theorem second_zero_radial_le_mirror (q : TZeroPassage) (hH : HorizontalPassage q)
    (hLow : rZeroRadialPosition q.zEarlierMember < 1 / 2) :
    rZeroRadialPosition q.zLaterMember ≤ 1 - rZeroRadialPosition q.zEarlierMember := by
  by_contra hlt
  have hlt' := not_le.mp hlt
  apply q.hConsecutive.2
  refine ⟨zMirrorZero q.zEarlierMember, ?_, ?_⟩
  · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    refine ⟨by rw [thm_mirror_sameHeight], ?_⟩
    rw [thm_mirror_radialPosition]
    linarith
  · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    refine ⟨by rw [thm_mirror_sameHeight]; exact hH, ?_⟩
    rw [thm_mirror_radialPosition]
    exact hlt'

/-- **Le rayon normalisé des deux zéros d'une même hauteur est lu en sens inverse** : celui d'un
zéro sous la ligne décroît le long de l'axe, celui d'un zéro au-dessus de la ligne croît. -/
theorem pair_radius_senses_inverted (z s : TrueZero) (hz : rZeroRadialPosition z.1 < 1 / 2)
    (hs : 1 / 2 < rZeroRadialPosition s.1) {u v : ℝ} (h : u < v) :
    ‖pointCurve (zeroPoint z) v‖ < ‖pointCurve (zeroPoint z) u‖ ∧
      ‖pointCurve (zeroPoint s) u‖ < ‖pointCurve (zeroPoint s) v‖ :=
  ⟨(pointCurve_norm_gt_iff _ (zeroPoint_ne_zero z) h).mpr (by rw [zeroPoint_re]; exact hz),
    (pointCurve_norm_lt_iff _ (zeroPoint_ne_zero s) h).mpr (by rw [zeroPoint_re]; exact hs)⟩

/-- **Fenêtre des deux zéros suivants.** Passage `p` où la hauteur avance vers un zéro strictement
sous la ligne, passage `q` qui le quitte : `q` garde la hauteur ; le second zéro est strictement à
droite du premier et au plus à sa position réfléchie (il n'est pas démontré qu'il est le miroir, ni
qu'il est au-dessus de la ligne) ; sa Tour est une Tour DISTINCTE de même intervalle logarithmique,
tous ses contacts translatés strictement en deçà ; elle dépasse celle du premier en des
premiers arbitrairement grands ; et si le passage `r` qui quitte le second zéro avance en hauteur,
le second zéro est strictement au-dessus de la ligne, son rayon normalisé est lu en sens inverse de
celui du premier, et le zéro atteint ensuite ne dépasse pas la ligne. -/
theorem second_zero_window {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hp : VerticalPassage p) (hLow : rZeroRadialPosition p.zLaterMember < 1 / 2)
    (hEq : 0 < rZeroHeight q.zEarlierMember) (hLq : 0 < rZeroHeight q.zLaterMember) :
    HorizontalPassage q ∧
      rZeroRadialPosition q.zEarlierMember < rZeroRadialPosition q.zLaterMember ∧
      rZeroRadialPosition q.zLaterMember ≤ 1 - rZeroRadialPosition q.zEarlierMember ∧
      towerPitch ⟨q.zLaterMember, hLq⟩ = towerPitch ⟨q.zEarlierMember, hEq⟩ ∧
      (∀ k : ℤ, contactMinusAt ⟨q.zLaterMember, hLq⟩ k < contactMinusAt ⟨q.zEarlierMember, hEq⟩ k) ∧
      (∀ N : ℝ, ∃ M : ℕ, M.Prime ∧ N ≤ (M : ℝ) ∧
        ‖zeroTerm ⟨q.zEarlierMember, hEq⟩ (M : ℝ)‖ < ‖zeroTerm ⟨q.zLaterMember, hLq⟩ (M : ℝ)‖) ∧
      (∀ r : TZeroPassage, q.zLaterMember = r.zEarlierMember → VerticalPassage r →
        1 / 2 < rZeroRadialPosition q.zLaterMember ∧
          rZeroRadialPosition r.zLaterMember ≤ 1 / 2 ∧
          ∀ u v : ℝ, u < v →
            ‖pointCurve (zeroPoint ⟨q.zEarlierMember, hEq⟩) v‖ <
                ‖pointCurve (zeroPoint ⟨q.zEarlierMember, hEq⟩) u‖ ∧
              ‖pointCurve (zeroPoint ⟨q.zLaterMember, hLq⟩) u‖ <
                ‖pointCurve (zeroPoint ⟨q.zLaterMember, hLq⟩) v‖) := by
  have hH : HorizontalPassage q := (vertical_arrival_characterizes hJ hp).2.mpr hLow
  have hLowQ : rZeroRadialPosition q.zEarlierMember < 1 / 2 := by rw [← hJ]; exact hLow
  have hIn := sameHeight_successor_translates_inward q hEq hLq hH
  refine ⟨hH, horizontalPassage_radial_lt hH, second_zero_radial_le_mirror q hH hLowQ, hIn.1,
    hIn.2.1, fun N => horizontal_escape_at_prime hEq hLq hH N, fun r hJr hr => ?_⟩
  have hHigh : 1 / 2 < rZeroRadialPosition q.zLaterMember := junction_horizontal_vertical hJr hH hr
  exact ⟨hHigh, passage_entry_radial_le_half r hr, fun u v huv =>
    pair_radius_senses_inverted ⟨q.zEarlierMember, hEq⟩ ⟨q.zLaterMember, hLq⟩ hLowQ hHigh huv⟩

#print axioms second_zero_window

#print axioms mirror_pair_changeResidue_sum_neg
#print axioms mirror_pair_contacts_beyond_line

/-! ## Le passage sortant `q` : renouvellement de la progression de hauteur

Trois passages consécutifs : `o` atteint `e` en ligne et monte ; `p` quitte `e` et atteint `l` ; `q` quitte
`l` et atteint `s`. ACQUIS (pas le verrou) : `p` monte (`engaged_regime_kept`) ; `β_l ≤ 1/2`
(`passage_entry_radial_le_half`). Flèche de référence (auteur, 2026-10-05), mot pour mot : « Depuis un zéro
ON engagé, dériver des contraintes acquises de succession, de raccord et d'enroulement que le passage
quittant le membre atteint doit lui aussi monter — sans supposer ce membre ON. » Fermeture disponible
ensuite : `junction_vertical_vertical` (un membre atteint par un passage qui monte et quitté par un passage
qui monte est en ligne). -/

/-- **Le second membre d'une même hauteur est au plus sur la ligne, ou il est exactement le miroir du
premier.** Composition de la consécutivité et de la réflexion : si `β_s > 1/2` et `β_s < 1 − β_l`, le miroir
de `s` (même hauteur, partie réelle `1 − β_s`) s'intercalerait strictement entre `l` et `s`. -/
theorem second_zero_mirror_or_le_half (q : TZeroPassage) (hH : HorizontalPassage q)
    (hLow : rZeroRadialPosition q.zEarlierMember < 1 / 2) :
    rZeroRadialPosition q.zLaterMember ≤ 1 / 2 ∨ q.zLaterMember = zMirrorZero q.zEarlierMember := by
  have hH' : rZeroHeight q.zEarlierMember = rZeroHeight q.zLaterMember := hH
  by_cases hs : rZeroRadialPosition q.zLaterMember ≤ 1 / 2
  · exact Or.inl hs
  right
  have hs' := not_le.mp hs
  have hle := second_zero_radial_le_mirror q hH hLow
  have hEq : rZeroRadialPosition q.zLaterMember = 1 - rZeroRadialPosition q.zEarlierMember := by
    by_contra hne
    have hlt := lt_of_le_of_ne hle hne
    apply q.hConsecutive.2
    refine ⟨zMirrorZero q.zLaterMember, ?_, ?_⟩
    · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
      right
      refine ⟨by rw [thm_mirror_sameHeight]; exact hH', ?_⟩
      rw [thm_mirror_radialPosition]
      linarith
    · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
      right
      refine ⟨by rw [thm_mirror_sameHeight], ?_⟩
      rw [thm_mirror_radialPosition]
      linarith
  apply thm_zeroOrderKey_injective
  unfold fnZeroOrderKey
  rw [thm_mirror_sameHeight, thm_mirror_radialPosition, hEq, hH']

/-- **Flèche de référence (auteur, 2026-10-05), réécrite au sens de la prémisse du 2026-10-06** :
depuis le zéro ON engagé `e` atteint par `o` qui monte, `p : e → l` monte (acquis,
`engaged_regime_kept`) ; si chaque amplitude individuelle reste sous celle d'un même zéro `z₁` sur
tout l'horizon (CONCLUSION du raccord ouvert « premier gain collectif maximal à tout rang ⟹
domination individuelle », jamais la prémisse elle-même), alors l'enroulement entier tient sur tout
passage (`whole_winding_all_passages_of_individual_domination`, par RH), la lecture conjointe
conserve la partie réelle et `q : l → s` monte. L'unique prémisse (`∀ n ≥ 1, D_n ≤ D_1`,
`Terminal/FirstGainPremise.lean`) n'entre pas ici : le raccord qui la relie à la domination
individuelle n'est pas démontré. -/
theorem renewed_height_advance {o p q : TZeroPassage}
    (hJ : o.zLaterMember = p.zEarlierMember) (hJq : p.zLaterMember = q.zEarlierMember)
    (hE : 0 < rZeroHeight o.zLaterMember) (ho : VerticalPassage o)
    (hOn : rZeroRadialPosition o.zLaterMember = 1 / 2) {z₁ : TrueZero}
    (hDom : ∀ w : TrueZero, ∀ x : ℝ, 0 < x → pairAmplitude w x ≤ pairAmplitude z₁ x) :
    VerticalPassage q :=
  renewed_height_advance_of_whole_winding hJ hJq hE ho hOn
    (whole_winding_all_passages_of_individual_domination hDom p)

#print axioms second_zero_mirror_or_le_half

/-- Une fois le régime ON engagé, du fait de l'enroulement des Tours, la partie réelle du zéro
suivant est forcément la même que celle du zéro qui a engagé le régime. Théorème CONDITIONNEL à la
domination individuelle de toute amplitude par celle d'un même zéro sur tout l'horizon (conclusion
du raccord ouvert de `Terminal/FirstGainPremise.lean` ; elle ferme RH,
`riemannHypothesis_of_individual_domination`). Composition : réduction au cas bas
(`passage_entry_radial_le_half`), existence du passage `q` qui quitte le membre atteint
(`exists_fiberSuccessor`), renouvellement de la progression de hauteur (`renewed_height_advance`),
fermeture (`junction_vertical_vertical`). -/
theorem onLine_beta_eq_previous {o p : TZeroPassage}
    (hJ : o.zLaterMember = p.zEarlierMember)
    (hE : 0 < rZeroHeight o.zLaterMember) (ho : VerticalPassage o)
    (hOn : rZeroRadialPosition o.zLaterMember = 1 / 2) {z₁ : TrueZero}
    (hDom : ∀ w : TrueZero, ∀ x : ℝ, 0 < x → pairAmplitude w x ≤ pairAmplitude z₁ x) :
    rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember := by
  have hHeightAdvances : VerticalPassage p := (engaged_regime_kept hJ ho hOn).1
  have hOnE : rZeroRadialPosition p.zEarlierMember = 1 / 2 := by rw [← hJ]; exact hOn
  have hPE : 0 < rZeroHeight p.zEarlierMember := by rw [← hJ]; exact hE
  have hPL : 0 < rZeroHeight p.zLaterMember := lt_of_lt_of_le hPE (passage_height_le p)
  have hLe : rZeroRadialPosition p.zLaterMember ≤ 1 / 2 :=
    passage_entry_radial_le_half p hHeightAdvances
  rw [hOnE]
  apply le_antisymm hLe
  by_contra h
  have hBelow : rZeroRadialPosition p.zLaterMember < 1 / 2 := lt_of_not_ge h
  -- le passage `q` qui quitte le membre atteint existe (successeur consécutif)
  obtain ⟨s, _, hCons⟩ := exists_fiberSuccessor (z := ⟨p.zLaterMember, hPL⟩) hBelow
  have hq : VerticalPassage ⟨p.zLaterMember, s.1, hCons⟩ :=
    renewed_height_advance hJ rfl hE ho hOn hDom
  exact absurd (junction_vertical_vertical rfl hHeightAdvances hq) (ne_of_lt hBelow)

#print axioms renewed_height_advance
#print axioms onLine_beta_eq_previous

end RHV6Fresh
