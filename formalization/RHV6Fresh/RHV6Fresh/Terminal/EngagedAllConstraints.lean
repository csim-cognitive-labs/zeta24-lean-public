/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.SymmetricWinding
import RHV6Fresh.Terminal.FirstZeroField
import RHV6Fresh.Terminal.TowerFourSectors
import RHV6Fresh.Terminal.TowerTwoSidedRoom
import RHV6Fresh.Terminal.EngagedNoTranslation

/-!
# Toutes les contraintes de l'auteur sur un pas engagé, réunies (auteur, 2026-10-04)

« Les Tours des zéros de la ligne sont centrées sur un seul point d'origine, symétriques, divisées
en quatre par les deux axes ; elles ne peuvent sortir ni par le haut ni par le bas ni se translater ;
tous les écarts sont atteints uniquement par la hauteur ; les Tours imbriquent leurs contacts,
réduisent les intervalles entre contacts et laissent la place à la suivante jusqu'à l'infini. »

Ce fichier écrit la symétrie au niveau du zéro lui-même (et non plus de paramètres abstraits), puis
réunit sur un même pas engagé : symétrie de la Tour de départ, hauteur qui avance, intervalles
réduits, emboîtement à l'infini, écarts lus par la hauteur seule, translation de la grille d'arrivée.
-/

namespace RHV6Fresh

open RHV3Lean

/-- La Tour d'un zéro ramenée à l'échelle de la ligne : centrée à l'origine. -/
noncomputable def rescaledTower (z : TrueZero) (u : ℝ) : ℂ :=
  ((Real.exp (-(u / 2)) : ℝ) : ℂ) * zeroTerm z (Real.exp u)

/-- **Tour symétrique par rapport à son centre** : l'opposé de tout point de la Tour est un point
de la Tour. -/
def TowerSymmetric (z : TrueZero) : Prop :=
  ∀ u : ℝ, ∃ u' : ℝ, rescaledTower z u' = -rescaledTower z u

/-- **La Tour d'un zéro est symétrique par rapport à son centre ⟺ le zéro est en ligne.** -/
theorem towerSymmetric_iff_onLine (z : TrueZero) :
    TowerSymmetric z ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  unfold TowerSymmetric rescaledTower
  simp_rw [rescaledTower_eq]
  exact (tower_central_invariant_iff (rZeroRadialPosition z.1 - 1 / 2) (rZeroHeight z.1)
    (Complex.arg (zeroPoint z)) (1 / ‖zeroPoint z‖) (one_div_pos.mpr (norm_zeroPoint_pos z))
    (ne_of_gt z.2)).trans sub_eq_zero

/-- **Tour symétrique ⟺ grille non translatée.** -/
theorem towerSymmetric_iff_no_translation (z : TrueZero) :
    TowerSymmetric z ↔ radialFactor z = 1 :=
  (towerSymmetric_iff_onLine z).trans (radialFactor_eq_one_iff z).symm

/-- **Toutes les contraintes sur un pas engagé, ensemble.** Départ en ligne, la hauteur avance :
la Tour de départ est symétrique ; la hauteur avance ; l'arrivée est au plus à un demi ; les
intervalles entre contacts sont réduits ; la grille d'arrivée est la grille de ligne translatée par
un facteur unique au moins égal à un ; la Tour d'arrivée s'emboîte dans la Tour de départ à
l'infini ; tous ses écarts sont lus par la hauteur seule ; et sa symétrie équivaut à l'absence de
translation. -/
theorem engaged_step_all_constraints (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hV : VerticalPassage p) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hT2 : 2 ≤ rZeroHeight p.zLaterMember) :
    TowerSymmetric ⟨p.zEarlierMember, hE⟩ ∧
      rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
      rZeroRadialPosition p.zLaterMember ≤ 1 / 2 ∧
      towerPitch ⟨p.zLaterMember, hL⟩ < towerPitch ⟨p.zEarlierMember, hE⟩ ∧
      1 ≤ radialFactor ⟨p.zLaterMember, hL⟩ ∧
      (∀ k : ℤ, contactMinusAt ⟨p.zLaterMember, hL⟩ k =
        lineContact (rZeroHeight p.zLaterMember) k * radialFactor ⟨p.zLaterMember, hL⟩) ∧
      WindingNestedAtInfinity ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ ∧
      (∀ q q' : ℝ, towerPosition ⟨p.zLaterMember, hL⟩ q' - towerPosition ⟨p.zLaterMember, hL⟩ q =
        rZeroHeight p.zLaterMember * (Real.log q' - Real.log q) / Real.pi) ∧
      (TowerSymmetric ⟨p.zLaterMember, hL⟩ ↔ radialFactor ⟨p.zLaterMember, hL⟩ = 1) := by
  have h := engaged_step_combined p hE hL hV hOn hT2
  refine ⟨(towerSymmetric_iff_onLine _).mpr hOn, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, ?_, fun q q' => gap_reading_height_only _ q q',
    towerSymmetric_iff_no_translation _⟩
  exact windingNestedAtInfinity_of_precedes _ _
    ((thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mpr (Or.inl hV))

/-- **Fermeture du pas par la symétrie** : depuis un zéro en ligne, si la Tour du zéro atteint est
symétrique par rapport à son centre, ce zéro est en ligne. -/
theorem engaged_step_closes_of_symmetric_arrival (p : TZeroPassage)
    (hL : 0 < rZeroHeight p.zLaterMember) (hS : TowerSymmetric ⟨p.zLaterMember, hL⟩) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 :=
  (towerSymmetric_iff_onLine ⟨p.zLaterMember, hL⟩).mp hS

/-- **Toutes les Tours symétriques ⟺ RH.** Équivalence, non dérivée. -/
theorem towerSymmetric_all_iff_riemannHypothesis :
    (∀ z : TrueZero, TowerSymmetric z) ↔ RiemannHypothesis := by
  constructor
  · intro h
    refine riemannHypothesis_iff_passage_whole_winding.mp fun p hE hL => ?_
    exact (whole_winding_iff_onLine p hE hL ((towerSymmetric_iff_onLine ⟨_, hE⟩).mp (h _))).mpr
      ((towerSymmetric_iff_onLine ⟨_, hL⟩).mp (h _))
  · intro hRH z
    exact (towerSymmetric_iff_onLine z).mpr (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _)

/-! ## Deux symétries distinctes (auteur, 2026-10-04, E163)

Haut / bas, par l'axe algébrique : vraie pour toute Tour, en ligne ou non. Gauche / droite, centre
sur l'axe un demi : la paire d'un zéro et de son miroir est toujours centrée sur cet axe, le zéro
lui-même n'est à ce centre que s'il est en ligne. -/

/-- **Symétrie haut / bas de toute Tour** : l'image de la Tour par l'axe algébrique est la Tour du
point conjugué, pour toute position radiale. -/
theorem tower_topBottom_symmetric (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    (starRingEnd ℂ) (zeroTerm z x) =
      (x : ℂ) ^ (starRingEnd ℂ) (zeroPoint z) / (starRingEnd ℂ) (zeroPoint z) := by
  unfold zeroTerm
  rw [map_div₀, Complex.cpow_conj _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne), Complex.conj_ofReal]

/-- **Centre gauche / droite de la paire miroir** : le milieu d'un zéro et de son miroir est sur
l'axe un demi, à la hauteur du zéro, pour toute position radiale. -/
theorem mirror_pair_center (z : TrueZero) :
    (zeroPoint z + zeroPoint (mirrorMember z)) / 2 =
      (1 / 2 : ℂ) + (rZeroHeight z.1 : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [zeroPoint_re, mirrorMember_radial]
  · simp [zeroPoint_im, mirrorMember_ordinate]

/-- **Seul un zéro en ligne est lui-même au centre** : le zéro est au centre de sa paire miroir ⟺
il est en ligne. -/
theorem zero_at_center_iff_onLine (z : TrueZero) :
    zeroPoint z = (1 / 2 : ℂ) + (rZeroHeight z.1 : ℂ) * Complex.I ↔
      rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    simpa [zeroPoint_re] using this
  · intro h
    apply Complex.ext
    · simp [zeroPoint_re, h]
    · simp [zeroPoint_im]

/-- **Les deux symétries ensemble, pour toute Tour** : haut / bas toujours, centre de la paire sur
l'axe un demi toujours ; la symétrie centrale de la Tour seule ⟺ le zéro est à ce centre. -/
theorem tower_two_symmetries (z : TrueZero) :
    (∀ x : ℝ, 0 < x → (starRingEnd ℂ) (zeroTerm z x) =
        (x : ℂ) ^ (starRingEnd ℂ) (zeroPoint z) / (starRingEnd ℂ) (zeroPoint z)) ∧
      (zeroPoint z + zeroPoint (mirrorMember z)) / 2 =
        (1 / 2 : ℂ) + (rZeroHeight z.1 : ℂ) * Complex.I ∧
      (TowerSymmetric z ↔ zeroPoint z = (1 / 2 : ℂ) + (rZeroHeight z.1 : ℂ) * Complex.I) :=
  ⟨fun _ hx => tower_topBottom_symmetric z hx, mirror_pair_center z,
    (towerSymmetric_iff_onLine z).trans (zero_at_center_iff_onLine z).symm⟩

#print axioms tower_two_symmetries
/-! ## Prison à l'infini par la Tour du premier zéro en ligne, lue avec la symétrie miroir
(auteur, 2026-10-04 : « la symétrie et le centre nécessaire d'un zéro en ligne ; le premier zéro en
ligne emprisonne tous les autres jusqu'à l'infini ; réduis le verrou »)

La symétrie gauche / droite donne à chaque zéro un miroir qui est aussi un zéro. Il suffit donc que
chaque Tour reste sous la Tour du premier zéro À L'INFINI (au-delà d'un horizon propre à chaque Tour,
à un multiple fixe près) : appliquée au zéro et à son miroir, cette prison place le zéro au centre. -/

/-- Comparaison d'exposants à l'infini : il suffit que l'inégalité tienne au-delà d'un horizon. -/
theorem exponent_le_of_eventually_inside {β γ A B X : ℝ} (hA : 0 < A) (hB : 0 < B) (hX : 1 ≤ X)
    (h : ∀ x : ℝ, X ≤ x → x ^ β / A ≤ x ^ γ / B) : β ≤ γ := by
  have hX0 : 0 < X := by linarith
  have hXβ := Real.rpow_pos_of_pos hX0 β
  have hXγ := Real.rpow_pos_of_pos hX0 γ
  refine exponent_le_of_inside (A := A / X ^ β) (B := B / X ^ γ) (div_pos hA hXβ)
    (div_pos hB hXγ) (fun y hy => ?_)
  have hy0 : 0 ≤ y := by linarith
  have key := h (X * y) (by nlinarith)
  rw [Real.mul_rpow hX0.le hy0, Real.mul_rpow hX0.le hy0] at key
  have e1 : y ^ β / (A / X ^ β) = X ^ β * y ^ β / A := by field_simp
  have e2 : y ^ γ / (B / X ^ γ) = X ^ γ * y ^ γ / B := by field_simp
  rw [e1, e2]
  exact key

/-- **Prison à l'infini** : au-delà d'un horizon, à un multiple fixe près, la Tour de `w` reste sous
la Tour de `z₁`. -/
def PrisonAtInfinity (z₁ w : TrueZero) : Prop :=
  ∃ K X : ℝ, 0 < K ∧ 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → ‖zeroTerm w x‖ ≤ K * firstField z₁ x

/-- La prison à l'infini borne la partie réelle par celle du zéro qui emprisonne. -/
theorem prisonAtInfinity_exponent_le {z₁ w : TrueZero} (h : PrisonAtInfinity z₁ w) :
    rZeroRadialPosition w.1 ≤ rZeroRadialPosition z₁.1 := by
  obtain ⟨K, X, hK, hX, hle⟩ := h
  refine exponent_le_of_eventually_inside (norm_zeroPoint_pos w)
    (div_pos (norm_zeroPoint_pos z₁) hK) hX (fun x hx => ?_)
  have hx0 : 0 < x := by linarith
  have := hle x hx
  unfold firstField at this
  rw [norm_zeroTerm_eq w hx0, norm_zeroTerm_eq z₁ hx0] at this
  have e : x ^ rZeroRadialPosition z₁.1 / (‖zeroPoint z₁‖ / K) =
      K * (x ^ rZeroRadialPosition z₁.1 / ‖zeroPoint z₁‖) := by
    have := (norm_zeroPoint_pos z₁).ne'
    field_simp
  rw [e]
  exact this

/-- **Tout zéro en ligne au-dessus du premier zéro en ligne est prisonnier à l'infini** (et dès un,
sans multiple). -/
theorem prisonAtInfinity_of_onLine {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hw : rZeroRadialPosition w.1 = 1 / 2) (hT : rZeroHeight z₁.1 ≤ rZeroHeight w.1) :
    PrisonAtInfinity z₁ w :=
  ⟨1, 1, one_pos, le_refl 1, fun x hx => by
    rw [one_mul]; exact inside_field_of_onLine h₁ hw hT x hx⟩

/-- **La symétrie miroir ferme le zéro au centre** : premier zéro en ligne ; si la Tour d'un zéro
et la Tour de son miroir sont prisonnières à l'infini, ce zéro est en ligne. -/
theorem onLine_of_prisonAtInfinity_pair {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hw : PrisonAtInfinity z₁ w) (hm : PrisonAtInfinity z₁ (mirrorMember w)) :
    rZeroRadialPosition w.1 = 1 / 2 := by
  have h1 := prisonAtInfinity_exponent_le hw
  have h2 := prisonAtInfinity_exponent_le hm
  rw [mirrorMember_radial] at h2
  rw [h₁] at h1 h2
  linarith

/-- **Verrou réduit à l'infini** : pour le premier zéro, en ligne, « toute Tour est prisonnière à
l'infini » équivaut à l'hypothèse de Riemann. Équivalence, non dérivée. -/
theorem prisonAtInfinity_iff_riemannHypothesis {z₁ : TrueZero}
    (hFirst : sUpperZerosBelow z₁.1 = ∅) (h₁ : rZeroRadialPosition z₁.1 = 1 / 2) :
    (∀ w : TrueZero, PrisonAtInfinity z₁ w) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact thm_riemannHypothesis_of_allUpperOnCriticalLine fun w =>
      onLine_of_prisonAtInfinity_pair h₁ (h w) (h (mirrorMember w))
  · intro hRH w
    exact ⟨1, 1, one_pos, le_refl 1, fun x hx => by
      rw [one_mul]
      exact (first_field_iff_riemannHypothesis hFirst h₁).mpr hRH w x hx⟩

/-! ## La symétrie importée dans le pas engagé (auteur, 2026-10-04 : « l'égalité est prouvée par
la symétrie et le centre ; le premier zéro en ligne emprisonne tous les autres et crée le centre
géométrique ; importe la symétrie, donne-moi la nouvelle erreur »)

Le zéro en ligne de départ est le centre. Le zéro atteint, au plus à un demi, est prisonnier de sa
Tour à l'infini : c'est acquis. Sur la ligne le miroir est annulé : aucun énoncé n'est posé sur la
Tour d'un miroir distinct (auteur, 2026-10-04 : faux sauf sur la ligne, à ne pas implémenter). -/

/-- **Un zéro au plus à un demi est prisonnier à l'infini de la Tour d'un zéro en ligne.** -/
theorem prisonAtInfinity_of_le_half {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hw : rZeroRadialPosition w.1 ≤ 1 / 2) : PrisonAtInfinity z₁ w := by
  refine ⟨‖zeroPoint z₁‖ / ‖zeroPoint w‖, 1,
    div_pos (norm_zeroPoint_pos z₁) (norm_zeroPoint_pos w), le_refl 1, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  unfold firstField
  rw [norm_zeroTerm_eq w hx0, norm_zeroTerm_eq z₁ hx0, h₁]
  have h1 := (norm_zeroPoint_pos z₁).ne'
  have h2 := norm_zeroPoint_pos w
  have e : ‖zeroPoint z₁‖ / ‖zeroPoint w‖ * (x ^ (1 / 2 : ℝ) / ‖zeroPoint z₁‖) =
      x ^ (1 / 2 : ℝ) / ‖zeroPoint w‖ := by field_simp
  rw [e]
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx hw) h2.le

/-- **Le miroir annulé, lu sur le pas engagé** (auteur, 2026-10-04 : « la ligne critique annule le
miroir ») : pour le zéro atteint, « son miroir est annulé » et « il est en ligne » sont un seul et
même énoncé ; le miroir du zéro de départ, en ligne, est annulé. -/
theorem engaged_step_mirror_annulled_iff (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    mirrorMember ⟨p.zEarlierMember, hE⟩ = ⟨p.zEarlierMember, hE⟩ ∧
      (mirrorMember ⟨p.zLaterMember, hL⟩ = ⟨p.zLaterMember, hL⟩ ↔
        rZeroRadialPosition p.zLaterMember = 1 / 2) :=
  ⟨(mirror_annulled_iff_onLine _).mpr hOn, mirror_annulled_iff_onLine _⟩

#print axioms engaged_step_mirror_annulled_iff

#print axioms prisonAtInfinity_iff_riemannHypothesis

/-- **Sous l'échelle de la ligne à l'infini** : au-delà d'un horizon, à un multiple fixe près,
l'amplitude de la Tour reste sous l'amplitude d'une Tour en ligne. Aucun zéro de référence. -/
def UnderLineScaleAtInfinity (w : TrueZero) : Prop :=
  ∃ K X : ℝ, 0 < K ∧ 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → ‖zeroTerm w x‖ ≤ K * x ^ (1 / 2 : ℝ)

theorem underLineScale_exponent_le {w : TrueZero} (h : UnderLineScaleAtInfinity w) :
    rZeroRadialPosition w.1 ≤ 1 / 2 := by
  obtain ⟨K, X, hK, hX, hle⟩ := h
  refine exponent_le_of_eventually_inside (norm_zeroPoint_pos w) (one_div_pos.mpr hK) hX
    (fun x hx => ?_)
  have hx0 : 0 < x := by linarith
  have := hle x hx
  rw [norm_zeroTerm_eq w hx0] at this
  have e : x ^ (1 / 2 : ℝ) / (1 / K) = K * x ^ (1 / 2 : ℝ) := by field_simp
  rw [e]
  exact this

/-- **Une seule demande, sans amorce** : toute Tour reste sous l'échelle de la ligne à l'infini ⟺
hypothèse de Riemann. La symétrie miroir fait le reste : appliquée au zéro et à son miroir, elle
place le zéro au centre. Équivalence, non dérivée. -/
theorem underLineScale_iff_riemannHypothesis :
    (∀ w : TrueZero, UnderLineScaleAtInfinity w) ↔ RiemannHypothesis := by
  constructor
  · intro h
    refine thm_riemannHypothesis_of_allUpperOnCriticalLine fun w => ?_
    have h1 := underLineScale_exponent_le (h w)
    have h2 := underLineScale_exponent_le (h (mirrorMember w))
    rw [mirrorMember_radial] at h2
    linarith
  · intro hRH w
    refine ⟨1 / ‖zeroPoint w‖, 1, one_div_pos.mpr (norm_zeroPoint_pos w), le_refl 1,
      fun x hx => ?_⟩
    rw [norm_zeroTerm_eq w (by linarith),
      thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1]
    exact le_of_eq (by ring)

#print axioms underLineScale_iff_riemannHypothesis

/-! ## L'unique configuration restante : le passage de même hauteur (auteur, 2026-10-04 : « une
seule erreur, aucune prémisse, implémentation fidèle »)

Tout ce que le code établit sur un passage de même hauteur, réuni. En particulier le fait compilé
rappelé par l'auteur : un tel passage ne part jamais d'un zéro engagé (en ligne et atteint par une
hauteur qui avance). -/

/-- **Profil complet d'un passage de même hauteur.** Le zéro d'arrivée est strictement à droite du
zéro de départ ; l'un des deux est hors ligne ; la Tour d'arrivée dépasse la Tour de départ en des
premiers aussi grands qu'on veut et n'en est pas prisonnière ; ses contacts restent emboîtés à
l'infini ; les intervalles entre contacts sont inchangés ; et le zéro de départ n'est jamais un
zéro engagé : s'il est atteint par une hauteur qui avance, il est strictement sous la ligne. -/
theorem sameHeight_passage_profile (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hH : HorizontalPassage p) :
    rZeroRadialPosition p.zEarlierMember < rZeroRadialPosition p.zLaterMember ∧
      (PIsOffCriticalLine p.zEarlierMember ∨ PIsOffCriticalLine p.zLaterMember) ∧
      (∀ N : ℝ, ∃ q : ℕ, q.Prime ∧ N ≤ (q : ℝ) ∧
        ‖zeroTerm ⟨p.zEarlierMember, hE⟩ (q : ℝ)‖ < ‖zeroTerm ⟨p.zLaterMember, hL⟩ (q : ℝ)‖) ∧
      ¬ TowerPrisoner p ∧
      WindingNestedAtInfinity ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ ∧
      towerPitch ⟨p.zLaterMember, hL⟩ = towerPitch ⟨p.zEarlierMember, hE⟩ ∧
      (∀ o : TZeroPassage, o.zLaterMember = p.zEarlierMember → VerticalPassage o →
        rZeroRadialPosition o.zLaterMember < 1 / 2) := by
  have hR := horizontal_regime p hE hL hH
  have hB := sameHeight_satisfies_both_rigidities p hE hL hH
  refine ⟨hR.1, hR.2.1, horizontal_escape_at_prime hE hL hH, hB.2.2.2.2.2.2.2, ?_, hB.2.2.2.1,
    fun o hJ ho => junction_vertical_horizontal hJ ho hH⟩
  exact windingNestedAtInfinity_of_precedes _ _ p.precedes

#print axioms sameHeight_passage_profile

#print axioms towerSymmetric_iff_onLine
#print axioms engaged_step_all_constraints
#print axioms towerSymmetric_all_iff_riemannHypothesis

end RHV6Fresh
