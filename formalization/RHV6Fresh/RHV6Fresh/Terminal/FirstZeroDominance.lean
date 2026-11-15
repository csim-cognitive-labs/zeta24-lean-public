/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.AuthenticPassageProfile
import RHV6Fresh.Terminal.EngagedAllConstraints
import RHV6Fresh.Terminal.TowerTwoSidedRoom

/-!
# Dominance du premier zéro et étages de captivité

Directive de l'auteur (2026-10-10) : « dès que l'ancre ON est prouvée, le premier zéro est le plus puissant pour les
restes et les écarts de tous les autres zéros sur la ligne ; il apporte la plus grande contribution, il est dominant.
Définir cette dominance et l'utiliser : captivité plus prononcée des zéros à venir, symétrie de la Tour autour de son
origine `(0, 0)`, contacts insérés à l'intérieur des contacts du précédent, intervalles réduits, fréquence et vitesse de
rotation accrues, rayons diminués. Le raisonnement a des étapes qui se renforcent les unes les autres. »

`DominanceStage z w` réunit, pour un zéro `w` sous un zéro `z`, toutes ces propriétés à la fois :
* Tour normalisée de `w` symétrique autour de l'origine (`TowerSymmetric`) ;
* hauteur, donc fréquence et vitesse de rotation par unité de `log x`, au moins celle de `z` ;
* intervalle logarithmique entre contacts (`towerPitch = π/T`) au plus celui de `z` ;
* rayon normalisé (amplitude ramenée à `√x`) sous celui de `z` sur TOUT l'axe positif ;
* contacts de `w` à l'intérieur de ceux de `z` à tout indice `k ≥ 1` dès que la hauteur avance (`WindingNested`).

Portée exacte (compilée ci-dessous) : entre deux zéros ON l'étage est un THÉORÈME, et les étages se composent
(renforcement) ; sous l'ancre, le premier zéro domine tout zéro ON (`firstZero_dominates`). Réciproquement l'étage FORCE
la ligne (`onLine_of_dominanceStage`) : il caractérise l'arrivée ON, il ne la produit pas. Sur un pas parti d'un zéro ON,
la partie cinématique de l'étage (hauteur, fréquence, intervalle, emboîtement à l'infini) est acquise pour toute position
radiale (`passage_stage_kinematics`) ; seuls la symétrie et le rayon sur tout l'axe lisent la position radiale, et une
arrivée basse les viole (`low_arrival_breaks_stage`). L'étage de l'arrivée n'est pas dérivé ici.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **Étage de dominance de `w` sous `z`** (définition de l'auteur, 2026-10-10). -/
structure DominanceStage (z w : TrueZero) : Prop where
  /-- Tour normalisée de `w` symétrique autour de l'origine. -/
  symmetric : TowerSymmetric w
  /-- Hauteur (fréquence, vitesse de rotation par unité de `log x`) au moins celle de `z`. -/
  height : rZeroHeight z.1 ≤ rZeroHeight w.1
  /-- Intervalle logarithmique entre contacts réduit. -/
  pitch : towerPitch w ≤ towerPitch z
  /-- Rayon normalisé sous celui de `z` sur tout l'axe positif. -/
  radius : ∀ x : ℝ, 0 < x → normalizedRadius w x ≤ normalizedRadius z x
  /-- Contacts de `w` à l'intérieur de ceux de `z` à tout indice `k ≥ 1` dès que la hauteur avance. -/
  nested : rZeroHeight z.1 < rZeroHeight w.1 → WindingNested z w

/-- L'étage force la ligne : la symétrie de la Tour autour de l'origine ⟺ `β = 1/2`. -/
theorem onLine_of_dominanceStage {z w : TrueZero} (h : DominanceStage z w) :
    rZeroRadialPosition w.1 = 1 / 2 :=
  (towerSymmetric_iff_onLine w).mp h.symmetric

/-- **Entre deux zéros ON, l'étage est un théorème.** -/
theorem dominanceStage_of_onLine {z w : TrueZero} (hz : rZeroRadialPosition z.1 = 1 / 2)
    (hw : rZeroRadialPosition w.1 = 1 / 2) (hT : rZeroHeight z.1 ≤ rZeroHeight w.1) : DominanceStage z w where
  symmetric := (towerSymmetric_iff_onLine w).mpr hw
  height := hT
  pitch := by
    unfold towerPitch
    exact div_le_div_of_nonneg_left Real.pi_pos.le z.2 hT
  radius := fun x hx => by
    rw [normalizedRadius_onLine z hz hx, normalizedRadius_onLine w hw hx]
    exact onRadius_anti z.2.le hT
  nested := fun hlt => windingNested_of_onLine z w hz hw hlt

/-- Sous un zéro `z` ON et à hauteur au moins la sienne, l'étage ⟺ ON. -/
theorem dominanceStage_iff_onLine {z w : TrueZero} (hz : rZeroRadialPosition z.1 = 1 / 2)
    (hT : rZeroHeight z.1 ≤ rZeroHeight w.1) : DominanceStage z w ↔ rZeroRadialPosition w.1 = 1 / 2 :=
  ⟨onLine_of_dominanceStage, fun hw => dominanceStage_of_onLine hz hw hT⟩

/-- Amplitude de paire dominée sur tout l'axe. -/
theorem DominanceStage.amplitude {z w : TrueZero} (h : DominanceStage z w) {x : ℝ} (hx : 0 < x) :
    pairAmplitude w x ≤ pairAmplitude z x := by
  unfold pairAmplitude
  exact mul_le_mul_of_nonneg_left (h.radius x hx) (by norm_num)

/-- Captivité : `w` est dans le champ de `z`. -/
theorem DominanceStage.insideField {z w : TrueZero} (h : DominanceStage z w) : InsideField z w :=
  (insideField_iff_pairAmplitude z w).mpr fun x hx => h.amplitude (by linarith)

/-- Contacts de `w` à l'intérieur de ceux de `z` à l'infini (dès que la hauteur avance). -/
theorem DominanceStage.nestedAtInfinity {z w : TrueZero} (_h : DominanceStage z w)
    (hT : rZeroHeight z.1 < rZeroHeight w.1) : WindingNestedAtInfinity z w :=
  windingNestedAtInfinity_of_precedes z w
    ((thm_zeroMemberPrecedes_iff_height_radial_lex z.1 w.1).mpr (Or.inl hT))

/-- **Renforcement strict** : sous `z` ON, dès que la hauteur avance, intervalle strictement réduit, rayon et amplitude
strictement diminués sur tout l'axe. -/
theorem DominanceStage.strict {z w : TrueZero} (hz : rZeroRadialPosition z.1 = 1 / 2) (h : DominanceStage z w)
    (hT : rZeroHeight z.1 < rZeroHeight w.1) :
    towerPitch w < towerPitch z ∧
    (∀ x : ℝ, 0 < x → normalizedRadius w x < normalizedRadius z x) ∧
    (∀ x : ℝ, 0 < x → pairAmplitude w x < pairAmplitude z x) := by
  have hw := onLine_of_dominanceStage h
  refine ⟨(towerPitch_lt_iff z w).mpr hT, fun x hx => ?_, fun x hx => pairAmplitude_onLine_lt_of_height hz hw hT hx⟩
  rw [normalizedRadius_onLine z hz hx, normalizedRadius_onLine w hw hx]
  exact onRadius_strictAnti z.2.le hT

/-- **Les étages se composent** (renforcement le long d'une chaîne). -/
theorem dominanceStage_trans {z e l : TrueZero} (hz : rZeroRadialPosition z.1 = 1 / 2)
    (h₁ : DominanceStage z e) (h₂ : DominanceStage e l) : DominanceStage z l :=
  dominanceStage_of_onLine hz (onLine_of_dominanceStage h₂) (h₁.height.trans h₂.height)

/-- Un étage de `w` sous un zéro ON est aussi un étage sous tout zéro ON plus bas. -/
theorem dominanceStage_lower {z z' w : TrueZero} (hz' : rZeroRadialPosition z'.1 = 1 / 2)
    (hT : rZeroHeight z'.1 ≤ rZeroHeight z.1) (h : DominanceStage z w) : DominanceStage z' w :=
  dominanceStage_of_onLine hz' (onLine_of_dominanceStage h) (hT.trans h.height)

/-! ## Le premier zéro dominant -/

/-- Le premier membre canonique est le plus bas. -/
theorem firstZero_height_le (w : TrueZero) : rZeroHeight (canonicalZero 1).1 ≤ rZeroHeight w.1 := by
  obtain ⟨n, hn, rfl⟩ := canonicalZero_surjective w
  exact canonicalZero_height_mono hn

/-- **Dominance du premier zéro (sous l'ancre)** : tout zéro ON est à un étage sous le premier ; captif de son champ,
contacts à l'intérieur des siens, intervalle réduit, fréquence accrue, rayon diminué. -/
theorem firstZero_dominates (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) (w : TrueZero)
    (hw : rZeroRadialPosition w.1 = 1 / 2) : DominanceStage (canonicalZero 1) w :=
  dominanceStage_of_onLine h₁ hw (firstZero_height_le w)

/-- Sous l'ancre : étage sous le premier ⟺ ON. -/
theorem firstZero_dominates_iff (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) (w : TrueZero) :
    DominanceStage (canonicalZero 1) w ↔ rZeroRadialPosition w.1 = 1 / 2 :=
  dominanceStage_iff_onLine h₁ (firstZero_height_le w)

/-- **Étages consécutifs le long de l'énumération canonique** : si tous les membres jusqu'au rang `m + 1` sont ON, chaque
membre est à un étage sous son prédécesseur et sous le premier. -/
theorem canonical_stages {m : ℕ} (hOn : ∀ j ≤ m + 1, rZeroRadialPosition (canonicalMember j).1 = 1 / 2) :
    DominanceStage (canonicalMember m) (canonicalMember (m + 1)) ∧
    DominanceStage (canonicalZero 1) (canonicalMember (m + 1)) := by
  have h1 : canonicalZero 1 = canonicalMember 0 := rfl
  refine ⟨dominanceStage_of_onLine (hOn m (by omega)) (hOn (m + 1) le_rfl)
      (canonicalMember_height_mono (by omega)), ?_⟩
  rw [h1]
  exact dominanceStage_of_onLine (hOn 0 (by omega)) (hOn (m + 1) le_rfl) (canonicalMember_height_mono (by omega))

/-- **Domination des contributions totales ON** : le rapport des amplitudes ON au premier est `‖ρ₁‖/‖ρ_w‖ ≤ 1`, constant
sur tout l'axe. -/
theorem firstZero_amplitude_ratio (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) (w : TrueZero)
    (hw : rZeroRadialPosition w.1 = 1 / 2) {x : ℝ} (hx : 0 < x) :
    normalizedRadius w x = onRadius (rZeroHeight w.1) ∧
    normalizedRadius (canonicalZero 1) x = onRadius (rZeroHeight (canonicalZero 1).1) ∧
    onRadius (rZeroHeight w.1) ≤ onRadius (rZeroHeight (canonicalZero 1).1) :=
  ⟨normalizedRadius_onLine w hw hx, normalizedRadius_onLine _ h₁ hx,
    onRadius_anti (canonicalZero 1).2.le (firstZero_height_le w)⟩

/-! ## Sur un pas parti d'un zéro ON -/

/-- **Partie cinématique de l'étage, acquise pour toute position radiale** : sur un pas qui monte depuis `e`, hauteur et
fréquence accrues, intervalle strictement réduit, contacts de l'arrivée à l'intérieur de ceux du départ à l'infini ; et
sous l'ancre, au-dessus du premier. -/
theorem passage_stage_kinematics (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hV : VerticalPassage p) :
    rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
    towerPitch ⟨p.zLaterMember, hL⟩ < towerPitch ⟨p.zEarlierMember, hE⟩ ∧
    WindingNestedAtInfinity ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ ∧
    rZeroHeight (canonicalZero 1).1 ≤ rZeroHeight p.zLaterMember ∧
    towerPitch ⟨p.zLaterMember, hL⟩ ≤ towerPitch (canonicalZero 1) := by
  have hT : rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember := hV
  have h1 := firstZero_height_le ⟨p.zLaterMember, hL⟩
  refine ⟨hT, (towerPitch_lt_iff _ _).mpr hT,
    windingNestedAtInfinity_of_precedes _ _
      ((thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mpr (Or.inl hT)), h1, ?_⟩
  unfold towerPitch
  exact div_le_div_of_nonneg_left Real.pi_pos.le (canonicalZero 1).2 h1

/-- **Une arrivée basse viole l'étage** : sa Tour n'est pas symétrique, son rayon dépasse celui du départ ON près de
l'origine, et son miroir (haut, même hauteur) sort du champ du premier. -/
theorem low_arrival_breaks_stage (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) {e l : TrueZero}
    (he : rZeroRadialPosition e.1 = 1 / 2) (hl : rZeroRadialPosition l.1 < 1 / 2) :
    ¬ TowerSymmetric l ∧
    (∃ x : ℝ, 0 < x ∧ x < 1 ∧ normalizedRadius e x < normalizedRadius l x) ∧
    ¬ InsideField (canonicalZero 1) (mirrorMember l) ∧
    ¬ DominanceStage e l ∧ ¬ DominanceStage (canonicalZero 1) (mirrorMember l) := by
  have hNS : ¬ TowerSymmetric l := fun h => absurd ((towerSymmetric_iff_onLine l).mp h) (ne_of_lt hl)
  obtain ⟨x, hx0, hx1, hx⟩ := low_member_not_dominated_on_axis l hl (onRadius (rZeroHeight e.1))
  have hmup : 1 / 2 < rZeroRadialPosition (mirrorMember l).1 := by rw [mirrorMember_radial]; linarith
  have hOut := upper_not_insideField (w := mirrorMember l) h₁ hmup
  refine ⟨hNS, ⟨x, hx0, hx1, by rwa [normalizedRadius_onLine e he hx0]⟩, hOut,
    fun h => hNS h.symmetric, fun h => hOut h.insideField⟩

/-- **Fermeture du pas par l'étage** : depuis un zéro ON, l'étage de l'arrivée sous le départ, ou sous le premier, ou la
seule captivité du MIROIR de l'arrivée dans le champ du premier, donne une arrivée ON (avec `β_l ≤ 1/2` acquis). -/
theorem stage_closes_passage (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) {e l : TrueZero}
    (hLe : rZeroRadialPosition l.1 ≤ 1 / 2) :
    (DominanceStage e l → rZeroRadialPosition l.1 = 1 / 2) ∧
    (DominanceStage (canonicalZero 1) l → rZeroRadialPosition l.1 = 1 / 2) ∧
    (InsideField (canonicalZero 1) (mirrorMember l) → rZeroRadialPosition l.1 = 1 / 2) := by
  refine ⟨onLine_of_dominanceStage, onLine_of_dominanceStage, fun hIn => ?_⟩
  by_contra hne
  have hl : rZeroRadialPosition l.1 < 1 / 2 := lt_of_le_of_ne hLe hne
  exact (low_arrival_breaks_stage h₁ (e := canonicalZero 1) h₁ hl).2.2.1 hIn

#print axioms firstZero_dominates
#print axioms passage_stage_kinematics
#print axioms low_arrival_breaks_stage
#print axioms stage_closes_passage

end RHV6Fresh
