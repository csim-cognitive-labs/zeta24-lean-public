/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FixedGapRaccords
import RHV6Fresh.Terminal.AuthenticPassageProfile

/-!
# Rigidité radiale depuis les seuls premiers (E308, 2026-10-15)

Ce module fixe la portée exacte de la chaîne « écarts premiers exacts → signal collectif → signatures → positions →
conservation radiale » :

* §1 la séparation stricte `‖J‖ + ‖ΔL_{Sᶜ}‖ < ‖ΔL_S‖` posée comme dernier pas de la chaîne (E304) est RÉFUTÉE par
  l'identité `ΔL_S + ΔL_{Sᶜ} = J` elle-même (inégalité triangulaire) : ce n'était pas une condition suffisante de vérité
  inconnue, mais un énoncé faux dans le contexte ;
* §2 pont de rigidité : la non-déplaçabilité (E305) vaut pour toute partie réelle `> 0` ; deux points identifiés par leurs
  contributions peuvent avoir des parties réelles distinctes : l'identification n'égalise aucune partie réelle ;
* §3 exposant commun : deux profils `x^{β₁}`, `x^{β₂}` sont proportionnels sur `x > 0` ⟺ `β₁ = β₂` ; loi d'échelle
  critique `2x^{1/2}/√(1/4 + T²)` ;
* §4 la loi de conservation radiale (historique ON) est, sous l'ancre démontrée, équivalente à RH.
-/

namespace RHV6Fresh

open RHV3Lean Complex

/-! ## 1. La séparation stricte est réfutée par l'identité qui la motive -/

/-- Si `a + b = J`, jamais `‖J‖ + ‖b‖ < ‖a‖`. -/
theorem strict_separation_impossible {E : Type*} [SeminormedAddCommGroup E] {a b J : E} (h : a + b = J) :
    ¬ (‖J‖ + ‖b‖ < ‖a‖) := by
  intro hlt
  have ha : a = J - b := by rw [← h]; abel
  have : ‖a‖ ≤ ‖J‖ + ‖b‖ := by rw [ha]; exact norm_sub_le _ _
  linarith

/-- Forme soustractive : `a = J − b ⟹ ¬ (‖J‖ + ‖b‖ < ‖a‖)`. -/
theorem strict_separation_impossible_sub {E : Type*} [SeminormedAddCommGroup E] {a b J : E} (h : a = J - b) :
    ¬ (‖J‖ + ‖b‖ < ‖a‖) :=
  strict_separation_impossible (by rw [h]; abel)

/-! ## 2. Pont de rigidité : identifier n'est pas égaliser -/

/-- Deux points de parties réelles distinctes ont tous deux leurs raccords fixés : la rigidité individuelle (E305)
n'impose aucune égalité de parties réelles entre points distincts. -/
theorem rigidity_does_not_equalize_radial :
    ∃ ρ ρ' : ℂ, ρ.re ≠ ρ'.re ∧ FixedRaccords ρ ∧ FixedRaccords ρ' :=
  ⟨(1 / 2 : ℂ) + 14 * I, (1 / 4 : ℂ) + 21 * I, by norm_num,
    fixed_raccords_any_radial (by norm_num) (by norm_num),
    fixed_raccords_any_radial (by norm_num) (by norm_num)⟩

/-- Toute assignation radiale `β ∈ ]0, 1[` à toute hauteur `T > 0` donne un point aux raccords fixés. -/
theorem fixedRaccords_any_assignment {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) :
    FixedRaccords ((β : ℂ) + T * I) :=
  fixed_raccords_any_radial (by simpa using hβ) (by simpa using hT)

/-! ## 3. Exposant commun -/

/-- Deux profils radiaux sont proportionnels sur tout `x > 0` ⟺ même exposant. -/
theorem proportional_profiles_iff {β₁ β₂ : ℝ} :
    (∃ c : ℝ, ∀ x : ℝ, 0 < x → x ^ β₁ = c * x ^ β₂) ↔ β₁ = β₂ := by
  constructor
  · rintro ⟨c, hc⟩
    have h1 := hc 1 one_pos
    simp at h1
    have he := hc (Real.exp 1) (Real.exp_pos 1)
    rw [Real.exp_one_rpow, Real.exp_one_rpow, ← h1, one_mul] at he
    exact Real.exp_injective he
  · rintro rfl
    exact ⟨1, fun x _ => by ring⟩

/-- Loi d'échelle critique de l'enveloppe du canal `ψ(x) − x` : à `β = 1/2`, `2x^β/√(β² + T²) = 2√x/√(1/4 + T²)`. -/
theorem critical_envelope_law (T x : ℝ) :
    2 * x ^ ((1 : ℝ) / 2) / Real.sqrt ((1 / 2 : ℝ) ^ 2 + T ^ 2) = 2 * Real.sqrt x / Real.sqrt (1 / 4 + T ^ 2) := by
  rw [← Real.sqrt_eq_rpow]
  norm_num

/-- Le rapport de deux enveloppes d'exposant commun est indépendant de `x` (fonction des hauteurs seules). -/
theorem common_exponent_ratio {β T₁ T₂ x : ℝ} (hx : 0 < x) :
    (2 * x ^ β / Real.sqrt (β ^ 2 + T₁ ^ 2)) / (2 * x ^ β / Real.sqrt (β ^ 2 + T₂ ^ 2)) =
      Real.sqrt (β ^ 2 + T₂ ^ 2) / Real.sqrt (β ^ 2 + T₁ ^ 2) := by
  have hxβ : 0 < x ^ β := Real.rpow_pos_of_pos hx β
  field_simp

/-! ## 4. La loi de conservation radiale et RH -/

/-- Sous l'ancre, la loi de conservation radiale à historique ON équivaut à RH (aucun sens n'est démontré
inconditionnellement par ce module). -/
theorem radial_conservation_law_iff_riemannHypothesis
    (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    (∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      (∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember) ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_anchor_and_history_conservation h₁,
    fun hRH => history_conservation_of_conservation (conservation_of_riemannHypothesis hRH)⟩

end RHV6Fresh
