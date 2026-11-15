/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TowerTwoSidedRoom
import RHV6Fresh.Terminal.FixedExponentField

/-!
# Transport individuel des Tours et évasion à un premier

Revue de l'auteur (2026-10-04) : la persistance d'une Tour est une IDENTITÉ, pas une propriété à poser. Chaque
zéro contribue, à tout `M`, par `Z(M) = M^ρ/ρ` (`spectral_organism_member`) ; lue en deux points,
`‖Z(M₂)‖ = ‖Z(M₁)‖·(M₂/M₁)^β` (`zeroTerm_norm_transport`). La loi de persistance est donc compilée avant ce module.

- `transported_energy_ratio` : le rapport d'énergie de deux Tours successives se transporte d'un premier à un
  autre par le seul facteur `(M₂/M₁)^{β_l − β_e}` ;
- `horizontal_escapes_beyond_horizon`, `horizontal_escape_at_prime` : un passage de même hauteur (`β_l > β_e`)
  dépasse la Tour de départ au-delà d'un horizon explicite, donc en un premier futur ;
- `PersistentCapture p` : l'INÉGALITÉ « énergie de l'arrivée sous celle du départ en tout premier à partir du
  raccord ». Ce n'est pas la loi de persistance : c'est une conséquence de type RH (nécessaire sous RH, et sur tous
  les passages elle entraîne RH : `persistent_of_riemannHypothesis`, `riemannHypothesis_of_persistent`), à ne pas
  chercher à démontrer comme telle ; elle entraîne captivité locale, `β_l ≤ β_e`, hauteur qui avance, et au raccord
  suivant la non-translation (`persistent_gives_local`, `persistent_exponent_le`, `persistent_forces_height`,
  `persistent_next_forces_no_translation`).

Portée : l'évasion individuelle à un premier ne contredit pas la reconstruction collective
(`spectral_organism_reconstructs`), qui porte sur la somme de tous les zéros : sans énoncé d'anti-compensation,
les autres membres peuvent compenser. Aucun `sorry`, aucun `admit`, aucun axiome, aucune prémisse `def P… : Prop`.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **Capture persistante** : en tout `M ≥` premier du raccord, la Tour d'arrivée ne lit pas plus d'énergie que
la Tour de départ. -/
def PersistentCapture (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) : Prop :=
  ∀ M : ℝ, (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) ≤ M →
    ‖zeroTerm ⟨p.zLaterMember, hL⟩ M‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ M‖

theorem persistent_gives_local {p : TZeroPassage} {hE : 0 < rZeroHeight p.zEarlierMember}
    {hL : 0 < rZeroHeight p.zLaterMember} (h : PersistentCapture p hE hL) : LocalCaptivity p hE hL :=
  h _ le_rfl

/-- **Capture persistante ⟹ la position radiale ne monte pas.** -/
theorem persistent_exponent_le {p : TZeroPassage} {hE : 0 < rZeroHeight p.zEarlierMember}
    {hL : 0 < rZeroHeight p.zLaterMember} (h : PersistentCapture p hE hL) :
    rZeroRadialPosition p.zLaterMember ≤ rZeroRadialPosition p.zEarlierMember := by
  set e : TrueZero := ⟨p.zEarlierMember, hE⟩
  set l : TrueZero := ⟨p.zLaterMember, hL⟩
  set M0 : ℝ := (expectedMinimumPrime e : ℝ) with hM0
  have hM0pos : 0 < M0 := by have := raccordPrime_two_le e; linarith
  have key : ∀ y : ℝ, 1 ≤ y →
      y ^ rZeroRadialPosition l.1 / (‖zeroPoint l‖ / M0 ^ rZeroRadialPosition l.1) ≤
        y ^ rZeroRadialPosition e.1 / (‖zeroPoint e‖ / M0 ^ rZeroRadialPosition e.1) := by
    intro y hy
    have hy0 : 0 < y := by linarith
    have hM : M0 ≤ M0 * y := by nlinarith
    have := h (M0 * y) hM
    have hMy : 0 < M0 * y := by positivity
    rw [norm_zeroTerm_eq l hMy, norm_zeroTerm_eq e hMy, Real.mul_rpow hM0pos.le hy0.le,
      Real.mul_rpow hM0pos.le hy0.le] at this
    have h1 := norm_zeroPoint_pos l
    have h2 := norm_zeroPoint_pos e
    have h3 := Real.rpow_pos_of_pos hM0pos (rZeroRadialPosition l.1)
    have h4 := Real.rpow_pos_of_pos hM0pos (rZeroRadialPosition e.1)
    rw [div_div_eq_mul_div, div_div_eq_mul_div, mul_comm (y ^ _) (M0 ^ _), mul_comm (y ^ _) (M0 ^ _)]
    exact this
  exact exponent_le_of_inside (A := ‖zeroPoint l‖ / M0 ^ rZeroRadialPosition l.1)
    (B := ‖zeroPoint e‖ / M0 ^ rZeroRadialPosition e.1)
    (div_pos (norm_zeroPoint_pos l) (Real.rpow_pos_of_pos hM0pos _))
    (div_pos (norm_zeroPoint_pos e) (Real.rpow_pos_of_pos hM0pos _)) key

/-- **Capture persistante ⟹ la hauteur avance** : le passage est vertical. -/
theorem persistent_forces_height {p : TZeroPassage} {hE : 0 < rZeroHeight p.zEarlierMember}
    {hL : 0 < rZeroHeight p.zLaterMember} (h : PersistentCapture p hE hL) : VerticalPassage p := by
  have hβ := persistent_exponent_le h
  rcases (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mp p.hConsecutive.1 with hT | ⟨_, hr⟩
  · exact hT
  · exact absurd hβ (not_le.mpr hr)

/-- **Un passage de même hauteur sort de la capture à un horizon** : au-delà de `M_*`, l'énergie de l'arrivée
dépasse strictement celle du départ, en tout premier. -/
theorem horizontal_escapes_beyond_horizon {p : TZeroPassage} (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hH : HorizontalPassage p) :
    ∃ Ms : ℝ, ∀ M : ℝ, Ms ≤ M →
      ‖zeroTerm ⟨p.zEarlierMember, hE⟩ M‖ < ‖zeroTerm ⟨p.zLaterMember, hL⟩ M‖ := by
  set e : TrueZero := ⟨p.zEarlierMember, hE⟩
  set l : TrueZero := ⟨p.zLaterMember, hL⟩
  have hT : rZeroHeight e.1 = rZeroHeight l.1 := hH
  have hβ : rZeroRadialPosition e.1 < rZeroRadialPosition l.1 := by
    rcases (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mp p.hConsecutive.1 with h | ⟨_, hr⟩
    · exact absurd hT (ne_of_lt h)
    · exact hr
  set c := rZeroRadialPosition l.1 - rZeroRadialPosition e.1 with hc
  have hcpos : 0 < c := by linarith
  set R := ‖zeroPoint l‖ / ‖zeroPoint e‖ with hR
  have hRpos : 0 < R := div_pos (norm_zeroPoint_pos l) (norm_zeroPoint_pos e)
  refine ⟨max 1 (R ^ (1 / c)) + 1, fun M hM => ?_⟩
  have hM1 : 1 < M := by have := le_max_left 1 (R ^ (1 / c)); linarith
  have hM0 : 0 < M := by linarith
  have hgt : R ^ (1 / c) < M := by have := le_max_right 1 (R ^ (1 / c)); linarith
  have hpow : R < M ^ c := by
    have := Real.rpow_lt_rpow (Real.rpow_nonneg hRpos.le _) hgt hcpos
    rwa [← Real.rpow_mul hRpos.le, one_div, inv_mul_cancel₀ hcpos.ne', Real.rpow_one] at this
  have hratio := successive_tower_ratio e l hM0
  have hpos := (norm_zeroTerm_eq e hM0)
  have hepos : 0 < ‖zeroTerm e M‖ := by
    rw [hpos]; exact div_pos (Real.rpow_pos_of_pos hM0 _) (norm_zeroPoint_pos e)
  have h1 : 1 < ‖zeroTerm l M‖ / ‖zeroTerm e M‖ := by
    rw [hratio, ← hc]
    have : (1 : ℝ) < M ^ c * (‖zeroPoint e‖ / ‖zeroPoint l‖) := by
      have hinv : ‖zeroPoint e‖ / ‖zeroPoint l‖ = R⁻¹ := by rw [hR, inv_div]
      rw [hinv]
      have := mul_lt_mul_of_pos_right hpow (inv_pos.mpr hRpos)
      rwa [mul_inv_cancel₀ hRpos.ne'] at this
    exact this
  exact (one_lt_div hepos).mp h1

/-- **Capture persistante au raccord SUIVANT `l → b`, départ engagé ⟹ grille de `l` non translatée.** -/
theorem persistent_next_forces_no_translation {p q : TZeroPassage}
    (hJ : p.zLaterMember = q.zEarlierMember) (hp : VerticalPassage p)
    (hL : 0 < rZeroHeight p.zLaterMember) (hE' : 0 < rZeroHeight q.zEarlierMember)
    (hB : 0 < rZeroHeight q.zLaterMember) (hT2 : 2 ≤ rZeroHeight q.zEarlierMember)
    (hq : PersistentCapture q hE' hB) : radialFactor ⟨p.zLaterMember, hL⟩ = 1 :=
  (renewed_captivity_iff_no_translation hJ hp hL hE' hB hT2).mp (persistent_gives_local hq)

/-- **Sous RH, toute capture est persistante.** -/
theorem persistent_of_riemannHypothesis (hRH : RiemannHypothesis) (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    PersistentCapture p hE hL := by
  intro M hM
  have hM1 : 1 ≤ M := by have := raccordPrime_two_le ⟨p.zEarlierMember, hE⟩; linarith
  have := prison_of_riemannHypothesis hRH p hE hL M hM1
  unfold firstField at this
  exact this

/-- **Capture persistante à tout passage de la moitié supérieure ⟹ RH.** -/
theorem riemannHypothesis_of_persistent
    (hP : ∀ (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
      (hL : 0 < rZeroHeight p.zLaterMember), PersistentCapture p hE hL) : RiemannHypothesis :=
  riemannHypothesis_of_height_always_advances fun p he =>
    persistent_forces_height (hP p he (he.trans_le (passage_height_le p)))

/-- **La loi de persistance : le rapport d'énergie de deux Tours se transporte d'un premier à un autre** par le
seul facteur `(M₂/M₁)^{β_l − β_e}` (identité, `zeroTerm_norm_transport`). -/
theorem transported_energy_ratio (e l : TrueZero) {M₁ M₂ : ℝ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    ‖zeroTerm l M₂‖ / ‖zeroTerm e M₂‖ =
      ‖zeroTerm l M₁‖ / ‖zeroTerm e M₁‖ * (M₂ / M₁) ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) := by
  have hr : 0 < M₂ / M₁ := div_pos h₂ h₁
  rw [zeroTerm_norm_transport l h₁ h₂, zeroTerm_norm_transport e h₁ h₂, Real.rpow_sub hr]
  have he : 0 < ‖zeroTerm e M₁‖ := by
    rw [norm_zeroTerm_eq e h₁]; exact div_pos (Real.rpow_pos_of_pos h₁ _) (norm_zeroPoint_pos e)
  have h3 := Real.rpow_pos_of_pos hr (rZeroRadialPosition e.1)
  field_simp

/-- **Un passage de même hauteur sort de la Tour de départ en un premier futur** : au-delà de tout horizon il
existe un premier où l'énergie de l'arrivée dépasse strictement celle du départ. -/
theorem horizontal_escape_at_prime {p : TZeroPassage} (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hH : HorizontalPassage p) (N : ℝ) :
    ∃ q : ℕ, q.Prime ∧ N ≤ (q : ℝ) ∧
      ‖zeroTerm ⟨p.zEarlierMember, hE⟩ (q : ℝ)‖ < ‖zeroTerm ⟨p.zLaterMember, hL⟩ (q : ℝ)‖ := by
  obtain ⟨Ms, hMs⟩ := horizontal_escapes_beyond_horizon hE hL hH
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes ⌈max N Ms⌉₊
  have h1 : max N Ms ≤ (q : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hq)
  exact ⟨q, hqp, (le_max_left _ _).trans h1, hMs _ ((le_max_right _ _).trans h1)⟩

#print axioms transported_energy_ratio
#print axioms horizontal_escape_at_prime

#print axioms persistent_exponent_le
#print axioms horizontal_escapes_beyond_horizon
#print axioms persistent_next_forces_no_translation
#print axioms riemannHypothesis_of_persistent

end RHV6Fresh
