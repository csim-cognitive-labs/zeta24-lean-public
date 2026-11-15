/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FirstZeroField
import RHV6Fresh.Terminal.ZetaParameters
import RHV6Fresh.Terminal.GrammarKinematics

/-!
# RHV6Fresh — β fixé, amplitude constante, la Tour reste dans le champ (auteur, 2026-10-03)

Argument de l'auteur, encodé tel quel : « β est toujours le même, donc l'amplitude est constante ; la Tour ne
peut pas sortir de celle du premier zéro ; à moins de changer β, on ne peut justifier la fuite d'une Tour ; la
fonction zêta ne possède pas d'autre paramètre que la hauteur. CQFD. »

* **§1 β est fixé le long de chaque Tour** : le rapport d'une Tour au champ du premier zéro est une seule
  puissance de `x`, d'exposant `β_w − β₁` fixé pour tout `x` (`tower_field_ratio`).
* **§2 Même β que le premier zéro ⟹ dans le champ** (`inside_field_of_same_exponent`) ; même β pour tous ⟹ RH
  (`riemannHypothesis_of_same_exponent`).
* **§3 Fuite à β fixé** : un β fixé strictement plus grand que celui du premier zéro sort du champ
  (`fixed_exponent_escapes`) ; la fuite ne demande aucun changement de β le long de la Tour, seulement un β
  différent de celui du premier.
* **§4 Le témoin sans paramètre** : `regimeWitness`, fonction fixe sans aucun paramètre, avec miroir, conjugaison,
  réelle sur la ligne, premier zéro en ligne à la hauteur 1 : la Tour de son zéro `3/4 + 2i`, de β fixé, dépasse
  le champ de ce premier zéro en `x = 16` (`regimeWitness_fixed_exponent_escapes`).
* **§5 Chaque Tour prisonnière de la précédente** (auteur : « chaque Tour est prisonnière de la Tour précédente » ;
  « la contrainte de répétition de la grammaire contraint le prochain zéro à fuir en hauteur ») : prisonnière ⟹ β
  ne monte pas sur le passage (`prisoner_exponent_le`) ⟹ la hauteur avance (`prisoner_forces_height`) ; hauteur
  qui avance sur tout passage ⟹ RH (`riemannHypothesis_of_height_always_advances`) ; toutes prisonnières ⟺ RH
  (`riemannHypothesis_of_prison`, `prison_of_riemannHypothesis`, `prison_iff_riemannHypothesis`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse `def P… : Prop`.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. β fixé le long de chaque Tour -/

/-- **Le rapport d'une Tour au champ du premier zéro est une seule puissance de `x`**, d'exposant fixé
`β_w − β₁`, multipliée par une constante. -/
theorem tower_field_ratio (z₁ w : TrueZero) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm w x‖ / firstField z₁ x =
      x ^ (rZeroRadialPosition w.1 - rZeroRadialPosition z₁.1) * (‖zeroPoint z₁‖ / ‖zeroPoint w‖) := by
  unfold firstField
  rw [norm_zeroTerm_eq w hx, norm_zeroTerm_eq z₁ hx, Real.rpow_sub hx]
  have h1 := norm_zeroPoint_pos z₁
  have h2 := norm_zeroPoint_pos w
  have h3 := Real.rpow_pos_of_pos hx (rZeroRadialPosition z₁.1)
  field_simp

/-! ## 2. Même β que le premier zéro -/

/-- **Même β que `z₁`, au moins aussi haut ⟹ dans le champ de `z₁`.** -/
theorem inside_field_of_same_exponent {z₁ w : TrueZero}
    (hβ : rZeroRadialPosition w.1 = rZeroRadialPosition z₁.1) (hT : rZeroHeight z₁.1 ≤ rZeroHeight w.1) :
    InsideField z₁ w := by
  intro x hx
  have hx0 : 0 < x := by linarith
  unfold firstField
  rw [norm_zeroTerm_eq w hx0, norm_zeroTerm_eq z₁ hx0, hβ]
  have hn : ‖zeroPoint z₁‖ ≤ ‖zeroPoint w‖ := by
    have h1 := Complex.sq_norm (zeroPoint z₁)
    have h2 := Complex.sq_norm (zeroPoint w)
    rw [Complex.normSq_apply, zeroPoint_re, zeroPoint_im] at h1 h2
    have hz1 : 0 < rZeroHeight z₁.1 := z₁.2
    have hsq : ‖zeroPoint z₁‖ ^ 2 ≤ ‖zeroPoint w‖ ^ 2 := by
      rw [h1, h2, hβ]; nlinarith
    nlinarith [norm_nonneg (zeroPoint z₁), norm_nonneg (zeroPoint w)]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) (norm_zeroPoint_pos z₁) hn

/-- **Si tous les zéros ont le β du premier zéro en ligne, l'hypothèse de Riemann suit.** -/
theorem riemannHypothesis_of_same_exponent {z₁ : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hSame : ∀ w : TrueZero, rZeroRadialPosition w.1 = rZeroRadialPosition z₁.1) : RiemannHypothesis :=
  thm_riemannHypothesis_of_allUpperOnCriticalLine fun w => (hSame w).trans h₁

/-! ## 3. Fuite à β fixé -/

/-- **Un β fixé plus grand que celui du premier zéro sort du champ**, sans aucun changement de β le long
de la Tour. -/
theorem fixed_exponent_escapes {z₁ w : TrueZero}
    (hgt : rZeroRadialPosition z₁.1 < rZeroRadialPosition w.1) : ¬ InsideField z₁ w := by
  intro hw
  have := exponent_le_of_inside (norm_zeroPoint_pos w) (norm_zeroPoint_pos z₁)
    (fun x hx => by
      have := hw x hx
      unfold firstField at this
      rwa [norm_zeroTerm_eq w (by linarith), norm_zeroTerm_eq z₁ (by linarith)] at this)
  linarith

/-! ## 4. Le témoin sans paramètre -/

/-- **Fonction fixe sans paramètre, premier zéro en ligne, Tour de β fixé qui sort de son champ.**
`regimeWitness` a le miroir, la conjugaison, la réalité sur la ligne ; son premier zéro `1/2 + i` est en
ligne ; la Tour de son zéro `3/4 + 2i` (β = 3/4, fixé) dépasse en `x = 16` l'amplitude de la Tour du
premier zéro. -/
theorem regimeWitness_fixed_exponent_escapes :
    regimeWitness (1 / 2 + Complex.I) = 0 ∧ regimeWitness (3 / 4 + 2 * Complex.I) = 0 ∧
    (∀ s : ℂ, regimeWitness s = 0 → 0 < s.im → 1 ≤ s.im) ∧
    ‖(16 : ℂ) ^ ((1 / 2 : ℂ) + Complex.I) / ((1 / 2 : ℂ) + Complex.I)‖ <
      ‖(16 : ℂ) ^ ((3 / 4 : ℂ) + 2 * Complex.I) / ((3 / 4 : ℂ) + 2 * Complex.I)‖ := by
  obtain ⟨h1, -, -, -, h34⟩ := regimeWitness_regime_changes
  refine ⟨h1, h34, fun s hs hpos => ?_, ?_⟩
  · rcases (regimeWitness_zero_iff s).mp hs with (h | h) | (h | h) | (h | h) <;>
      (rw [h] at hpos ⊢; simp at hpos ⊢) <;> linarith
  · have h16 : (0 : ℝ) < 16 := by norm_num
    rw [norm_div, norm_div, show (16 : ℂ) = ((16 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos h16, Complex.norm_cpow_eq_rpow_re_of_pos h16]
    have ea : ((1 / 2 : ℂ) + Complex.I).re = 1 / 2 := by simp
    have eb : ((3 / 4 : ℂ) + 2 * Complex.I).re = 3 / 4 := by simp
    rw [ea, eb]
    have p2 : (16 : ℝ) ^ ((1 : ℝ) / 2) = 4 := by
      rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    have p4 : (16 : ℝ) ^ ((3 : ℝ) / 4) = 8 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [p2, p4]
    set a := ‖(1 / 2 : ℂ) + Complex.I‖
    set b := ‖(3 / 4 : ℂ) + 2 * Complex.I‖
    have ha2 : a ^ 2 = 5 / 4 := by
      simp only [a]; rw [Complex.sq_norm, Complex.normSq_apply]; simp; norm_num
    have hb2 : b ^ 2 = 73 / 16 := by
      simp only [b]; rw [Complex.sq_norm, Complex.normSq_apply]; simp; norm_num
    have ha : 0 < a := by nlinarith [norm_nonneg ((1 / 2 : ℂ) + Complex.I)]
    have hb : 0 < b := by nlinarith [norm_nonneg ((3 / 4 : ℂ) + 2 * Complex.I)]
    rw [div_lt_div_iff₀ ha hb]
    nlinarith

/-! ## 5. Chaque Tour prisonnière de la précédente -/

/-- **La Tour d'arrivée d'un passage est prisonnière de la Tour de départ** : elle ne dépasse jamais son
amplitude le long de l'axe des premiers. -/
def TowerPrisoner (p : TZeroPassage) : Prop :=
  ∀ (he : 0 < rZeroHeight p.zEarlierMember) (hl : 0 < rZeroHeight p.zLaterMember),
    InsideField ⟨p.zEarlierMember, he⟩ ⟨p.zLaterMember, hl⟩

/-- **Prisonnière ⟹ la position radiale ne monte pas sur le passage.** -/
theorem prisoner_exponent_le {p : TZeroPassage} (hP : TowerPrisoner p)
    (he : 0 < rZeroHeight p.zEarlierMember) (hl : 0 < rZeroHeight p.zLaterMember) :
    rZeroRadialPosition p.zLaterMember ≤ rZeroRadialPosition p.zEarlierMember := by
  by_contra h
  push Not at h
  exact fixed_exponent_escapes (z₁ := ⟨_, he⟩) (w := ⟨_, hl⟩) h (hP he hl)

/-- **Prisonnière ⟹ la hauteur avance** : un passage dont l'arrivée est prisonnière est vertical. -/
theorem prisoner_forces_height {p : TZeroPassage} (hP : TowerPrisoner p)
    (he : 0 < rZeroHeight p.zEarlierMember) (hl : 0 < rZeroHeight p.zLaterMember) :
    VerticalPassage p := by
  have hβ := prisoner_exponent_le hP he hl
  rcases (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mp p.hConsecutive.1 with h | ⟨_, h⟩
  · exact h
  · exact absurd hβ (not_le.mpr h)

/-- **Si la hauteur avance sur tout passage de la moitié supérieure, l'hypothèse de Riemann suit.** -/
theorem riemannHypothesis_of_height_always_advances
    (hV : ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p) :
    RiemannHypothesis := by
  refine thm_riemannHypothesis_of_allUpperOnCriticalLine fun z => ?_
  by_contra hOff
  obtain ⟨m, -, -, ⟨q, hq, hH⟩, -⟩ := off_forces_regime_entry (z := z) hOff
  have hV' := hV q (by rw [hq]; exact m.2)
  exact absurd hH (ne_of_lt hV')

/-- **Toutes les Tours prisonnières de la précédente ⟹ RH.** -/
theorem riemannHypothesis_of_prison (hP : ∀ p : TZeroPassage, TowerPrisoner p) : RiemannHypothesis :=
  riemannHypothesis_of_height_always_advances fun p he =>
    prisoner_forces_height (hP p) he (he.trans_le (passage_height_le p))

/-- **Sous RH, toute Tour est prisonnière de la précédente.** -/
theorem prison_of_riemannHypothesis (hRH : RiemannHypothesis) (p : TZeroPassage) : TowerPrisoner p :=
  fun he hl => inside_field_of_onLine (z₁ := ⟨_, he⟩) (w := ⟨_, hl⟩)
    (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _)
    (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _) (passage_height_le p)

/-- **« Chaque Tour est prisonnière de la précédente » équivaut à l'hypothèse de Riemann.** -/
theorem prison_iff_riemannHypothesis : (∀ p : TZeroPassage, TowerPrisoner p) ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_prison, prison_of_riemannHypothesis⟩

#print axioms tower_field_ratio
#print axioms inside_field_of_same_exponent
#print axioms riemannHypothesis_of_same_exponent
#print axioms fixed_exponent_escapes
#print axioms regimeWitness_fixed_exponent_escapes
#print axioms prisoner_exponent_le
#print axioms prisoner_forces_height
#print axioms riemannHypothesis_of_height_always_advances
#print axioms riemannHypothesis_of_prison
#print axioms prison_of_riemannHypothesis
#print axioms prison_iff_riemannHypothesis

end RHV6Fresh
