/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ChebyshevAsymptoticToLogGaps
import RHV6Fresh.Terminal.UniformVariationBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# La dichotomie de l'ensemble droit : la contradiction localisée (module isolé)

Éléments intégrés depuis l'audit de causalité remis par l'auteur le 2026-10-29 :

* flèche 9, §11.3 : « deux difficultés différentes : plusieurs zéros à la même position maximale (une somme
  trigonométrique à fréquences distinctes) ; une famille infinie dont le supremum n'est pas atteint » ;
* flèche 7, §9 : la dérive cumulative d'un membre hors ligne doit être DIVERGENTE, pas seulement positive ;
* §16 : la contradiction doit être cherchée du côté des premiers, et l'ensemble droit doit être vide.

**Ce que fait ce module.**

1. La première difficulté de §11.3 est levée sans hypothèse : si l'ensemble des indices strictement à
   droite de un demi est FINI, le sommet est atteint (`summitAttained_of_finite_right`) ; la somme
   trigonométrique à fréquences distinctes est déjà traitée par `SummitAttained.lean` et
   `FiniteRadialRigidity.lean`. Donc, sous l'hypothèse de clôture et l'échantillonnage, un ensemble droit
   fini est VIDE (`riemannHypothesis_of_finite_right`).
2. La dichotomie (`right_empty_or_infinite_not_summit`) : sous l'hypothèse de clôture et l'échantillonnage,
   ou bien aucun indice n'est à droite, ou bien l'ensemble droit est infini ET le sommet n'est pas atteint.
   La seconde difficulté de §11.3 est donc le SEUL monde restant, écrit en une phrase compilée : une
   infinité d'indices à droite dont les positions n'ont pas de maximum atteint sur une verticale finie.
3. La dérive cumulative (§9) est exacte et divergente, sans constante uniforme : l'amplitude relative d'un
   membre au-dessus de la ligne, lue aux rencontres, tend vers l'infini (`relativeAmplitude_meetings_tendsto_atTop_of_high`),
   parce qu'elle vaut une constante fois la rencontre élevée à la position moins un demi
   (`relativeAmplitude_eq`, complément 13), et que les rencontres tendent vers l'infini.
4. Les deux chemins vers RH, sous l'interface exacte avec le théorème des nombres premiers et sous la
   forme faible du pont (`riemannHypothesis_of_closure`).

Aucun axiome, aucun `sorry`, aucune hypothèse posée comme démontrée. La chaîne est intacte.
-/

namespace RHV6Fresh

open Complex RHV3Lean Filter Topology

/-! ## 1. Un ensemble droit fini a son sommet atteint -/

/-- **Théorème** : si les indices strictement à droite de un demi sont en nombre fini, le sommet est
atteint. La position maximale est prise sur cet ensemble fini ; la famille du sommet est sa fibre, finie ;
tout autre indice est soit dans l'ensemble fini et strictement sous le maximum, soit au plus à un demi. -/
theorem summitAttained_of_finite_right (h : {ρ : ExplicitIndex | 1 / 2 < (ρ : ℂ).re}.Finite) :
    SummitAttained := by
  classical
  intro hex
  obtain ⟨ρ₀, hρ₀⟩ := hex
  have hρ₀F : ρ₀ ∈ h.toFinset := h.mem_toFinset.mpr hρ₀
  have hF : h.toFinset.Nonempty := ⟨ρ₀, hρ₀F⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = h.toFinset.sup' hF (fun σ : ExplicitIndex => (σ : ℂ).re) :=
    ⟨_, rfl⟩
  obtain ⟨σ₀, hσ₀F, hσ₀⟩ := Finset.exists_mem_eq_sup' hF (fun σ : ExplicitIndex => (σ : ℂ).re)
  have hb : 1 / 2 < b := by
    rw [hbdef]
    exact lt_of_lt_of_le hρ₀ (Finset.le_sup' (fun σ : ExplicitIndex => (σ : ℂ).re) hρ₀F)
  refine ⟨h.toFinset.filter (fun σ : ExplicitIndex => (σ : ℂ).re = b), b, ⟨σ₀, ?_⟩, ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨hσ₀F, by rw [hbdef, hσ₀]⟩
  · intro σ hσ
    exact (Finset.mem_filter.mp hσ).2
  · intro ρ hρ
    rw [Finset.mem_filter, not_and] at hρ
    by_cases hρF : ρ ∈ h.toFinset
    · have hle : (ρ : ℂ).re ≤ b := by
        rw [hbdef]
        exact Finset.le_sup' (fun σ : ExplicitIndex => (σ : ℂ).re) hρF
      exact lt_of_le_of_ne hle (hρ hρF)
    · have h1 : ¬ (1 / 2 < (ρ : ℂ).re) := fun hc => hρF (h.mem_toFinset.mpr hc)
      push Not at h1
      linarith

/-- **Un ensemble droit fini est vide** : sous l'hypothèse de clôture et l'échantillonnage. -/
theorem no_right_of_finite_right (hS : MeetingsSampleFrequencies) (hdem : DemandBoundedAtMeetings)
    (hfin : {ρ : ExplicitIndex | 1 / 2 < (ρ : ℂ).re}.Finite) :
    ∀ ρ : ExplicitIndex, (ρ : ℂ).re ≤ 1 / 2 :=
  no_right_of_summitAttained hS hdem (summitAttained_of_finite_right hfin)

/-- RH, sous l'hypothèse de clôture, l'échantillonnage, et un ensemble droit fini. -/
theorem riemannHypothesis_of_finite_right (hS : MeetingsSampleFrequencies)
    (hdem : DemandBoundedAtMeetings) (hfin : {ρ : ExplicitIndex | 1 / 2 < (ρ : ℂ).re}.Finite) :
    RiemannHypothesis :=
  riemannHypothesis_of_summitAttained hS hdem (summitAttained_of_finite_right hfin)

/-! ## 2. La dichotomie : le seul monde restant, écrit -/

/-- **Dichotomie** : sous l'hypothèse de clôture et l'échantillonnage, ou bien aucun indice n'est à droite
de un demi, ou bien l'ensemble droit est infini et son sommet n'est pas atteint. -/
theorem right_empty_or_infinite_not_summit (hS : MeetingsSampleFrequencies)
    (hdem : DemandBoundedAtMeetings) :
    (∀ ρ : ExplicitIndex, (ρ : ℂ).re ≤ 1 / 2) ∨
      (Set.Infinite {ρ : ExplicitIndex | 1 / 2 < (ρ : ℂ).re} ∧ ¬ SummitAttained) := by
  by_cases hex : ∃ ρ : ExplicitIndex, 1 / 2 < (ρ : ℂ).re
  · right
    refine ⟨infinite_right_of_sampling hS hdem hex, fun hsum => ?_⟩
    obtain ⟨ρ, hρ⟩ := hex
    exact absurd (no_right_of_summitAttained hS hdem hsum ρ) (not_le.mpr hρ)
  · left
    intro ρ
    push Not at hex
    exact hex ρ

/-- La même dichotomie, en termes de la cible : RH, ou bien le monde « infini, sommet non atteint ». -/
theorem riemannHypothesis_or_infinite_not_summit (hS : MeetingsSampleFrequencies)
    (hdem : DemandBoundedAtMeetings) :
    RiemannHypothesis ∨
      (Set.Infinite {ρ : ExplicitIndex | 1 / 2 < (ρ : ℂ).re} ∧ ¬ SummitAttained) := by
  rcases right_empty_or_infinite_not_summit hS hdem with h | h
  · left
    refine riemannHypothesis_of_noLowerSide fun l hlow => ?_
    have h' := h (memberIndex (mirrorMember l))
    change (zeroPoint (mirrorMember l)).re ≤ 1 / 2 at h'
    rw [zeroPoint_re, mirrorMember_radial] at h'
    linarith
  · right
    exact h

/-- La dichotomie sous l'interface exacte avec le théorème des nombres premiers. -/
theorem riemannHypothesis_or_infinite_not_summit_of_chebyshev (h : ChebyshevAsymptotic)
    (hdem : DemandBoundedAtMeetings) :
    RiemannHypothesis ∨
      (Set.Infinite {ρ : ExplicitIndex | 1 / 2 < (ρ : ℂ).re} ∧ ¬ SummitAttained) :=
  riemannHypothesis_or_infinite_not_summit (meetingsSampleFrequencies_of_chebyshev h) hdem

/-! ## 3. La dérive cumulative est exacte et divergente (audit §9, proposition C) -/

/-- Les rencontres tendent vers l'infini. -/
theorem meetingPoint_tendsto_atTop : Tendsto (fun n : ℕ => meetingPoint ⟨n⟩) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  change (n : ℝ) ≤ (fnPrimeAtRank (n + 1) : ℝ)
  have h1 : n + 1 ≤ fnPrimeAtRank (n + 1) := thm_primeAtRank_strictMono.id_le (n + 1)
  exact_mod_cast (Nat.le_succ n).trans h1

/-- **Théorème** : l'amplitude relative d'un membre strictement au-dessus de la ligne, lue aux rencontres,
tend vers l'infini. La dérive n'est pas seulement positive à chaque pas : son cumul est une puissance
strictement positive de la rencontre. -/
theorem relativeAmplitude_meetings_tendsto_atTop_of_high (w : TrueZero)
    (hhigh : 1 / 2 < rZeroRadialPosition w.1) :
    Tendsto (fun n : ℕ => relativeAmplitude w (meetingPoint ⟨n⟩)) atTop atTop := by
  have hK : 0 < (zetaZeroMultiplicity (zeroPoint w) : ℝ) / (‖zeroPoint w‖ * ‖zeroPoint w + 1‖) :=
    div_pos (memberMultiplicity_pos w) (memberDenominator_pos w)
  have hc : 0 < rZeroRadialPosition w.1 - 1 / 2 := by linarith
  have hpow : Tendsto (fun n : ℕ => (meetingPoint ⟨n⟩) ^ (rZeroRadialPosition w.1 - 1 / 2))
      atTop atTop :=
    (tendsto_rpow_atTop hc).comp meetingPoint_tendsto_atTop
  have hmul := hpow.const_mul_atTop hK
  refine hmul.congr' (Eventually.of_forall fun n => ?_)
  have hx : 0 < meetingPoint ⟨n⟩ := by linarith [one_lt_meetingPoint ⟨n⟩]
  exact (relativeAmplitude_eq w hx).symm

/-- Par le miroir : une arrivée basse a un miroir dont l'amplitude relative aux rencontres diverge. -/
theorem mirror_relativeAmplitude_tendsto_atTop_of_low (l : TrueZero)
    (hlow : rZeroRadialPosition l.1 < 1 / 2) :
    Tendsto (fun n : ℕ => relativeAmplitude (mirrorMember l) (meetingPoint ⟨n⟩)) atTop atTop := by
  refine relativeAmplitude_meetings_tendsto_atTop_of_high (mirrorMember l) ?_
  rw [mirrorMember_radial]
  linarith

/-! ## 4. Les deux chemins vers RH, sous l'hypothèse de clôture -/

/-- **Chemin des zéros** (interface exacte avec le théorème des nombres premiers, sommet atteint) ou
**chemin des premiers** (variation uniforme dans les écarts) : chacun ferme, sous l'hypothèse de clôture. -/
theorem riemannHypothesis_of_closure (hdem : DemandBoundedAtMeetings)
    (hroute : (ChebyshevAsymptotic ∧ SummitAttained) ∨ UniformVariationAtGaps) : RiemannHypothesis := by
  rcases hroute with ⟨hc, hs⟩ | hv
  · exact riemannHypothesis_of_chebyshev_summit hc hdem hs
  · exact riemannHypothesis_of_meetings_of_variation hdem hv

end RHV6Fresh
