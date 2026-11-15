/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CarrierTotalWord
import RHV6Fresh.Terminal.SpectralUniqueness

/-!
# RHV6Fresh — Terminal/ArithmeticRealization : la réalisation arithmétique d'une Tour
(E462, plan Φ étape Φ6, §19.92, 2026-11-09 ; module isolé, NON importé par `RHV6Fresh.lean` ;
aucune hypothèse, aucun axiome, aucun `sorry`)

Proposition de l'auteur (§19.90–19.91) : une Tour dont la totalité des contacts a la bonne relation aux premiers est un zéro.
E461 a compilé l'existence d'un lecteur du mot total, défini PAR le poids. Ce module donne une définition SANS le poids ni
l'annulation de zêta au point de la Tour, par la recomposition collective des premiers, et la raccorde aux Tours.

* `ArithmeticRecomposition` : famille de points distincts, localement finie, avec poids, dont la série de noyaux redonne pour tout
  `x > 1` la somme lissée de von Mangoldt moins le fond lisse. Le fond est FIXE (le même pour toutes les Tours) ; il contient la série
  des zéros triviaux et deux constantes de zêta, mais ni le point de la Tour, ni son poids, ni aucun zéro non trivial.
* `ArithmeticallyRealized β T` : une recomposition porte un poids non nul au point de la Tour.
* R1 `ArithmeticRecomposition.toSpectral`, R2 `trueRecomposition`.
* R3 `arithmeticallyRealized_iff_isCarrier`, R4 `arithmeticallyRealized_iff_zeta_eq_zero` : réalisée ⟺ porteuse ⟺ zêta s'annule.
* R5 `recomposition_contains_carrier`, `recomposition_weight_eq_zero_of_not_isCarrier` : toute recomposition contient chaque porteuse,
  aucune ne porte de poids sur une non-porteuse.
* R6 `readsCarriers_arithmeticWordCarrier`, R7 `arithmeticWordCarrier_iff_totalWordCarrier` : le lecteur du mot total défini par la
  réalisation lit la sélection et coïncide avec celui d'E461.
* R8 `riemannHypothesis_iff_realized_on_line` : RH ⟺ toute Tour réalisée est sur la ligne (classement ; jamais une prémisse).

Portée : R3–R7 valent pour les porteurs de la ligne comme hors ligne ; ils n'excluent aucun zéro hors ligne. La réalisation est
collective et existentielle (elle porte sur le signal entier des premiers), pas un critère lu sur les cellules de la seule Tour.
L'analyse (unicité de la représentation) est celle de `SpectralUniqueness.lean` ; rien de neuf n'y est démontré ici.
-/

namespace RHV6Fresh

open Real RHV3Lean

/-! ## Définition : recomposition arithmétique -/

structure ArithmeticRecomposition (ι : Type*) where
  point : ι → ℂ
  weight : ι → ℂ
  injective : Function.Injective point
  re_le_one : ∀ i, (point i).re ≤ 1
  ne_zero : ∀ i, point i ≠ 0 ∧ point i + 1 ≠ 0
  locallyFinite : ∀ R : ℝ, {i | ‖point i‖ ≤ R}.Finite
  summable : Summable fun i => ‖weight i / (point i * (point i + 1))‖
  recomposes : ∀ x : ℝ, 1 < x →
    ∑' i, weight i * Perron.f x (point i) = smoothedVonMangoldtSum x - smoothedZeroBackground x

/-! ## R1–R2 : raccord au canal compilé ; existence -/

def ArithmeticRecomposition.toSpectral {ι : Type*} (Rec : ArithmeticRecomposition ι) : SpectralRepresentation ι where
  point := Rec.point
  weight := Rec.weight
  injective := Rec.injective
  re_le_one := Rec.re_le_one
  ne_zero := Rec.ne_zero
  locallyFinite := Rec.locallyFinite
  summable := Rec.summable
  represents := fun x hx => (Rec.recomposes x hx).trans (channel_eq_arithmetic hx).symm

noncomputable def trueRecomposition : ArithmeticRecomposition ExplicitIndex where
  point := trueRepresentation.point
  weight := trueRepresentation.weight
  injective := trueRepresentation.injective
  re_le_one := trueRepresentation.re_le_one
  ne_zero := trueRepresentation.ne_zero
  locallyFinite := trueRepresentation.locallyFinite
  summable := trueRepresentation.summable
  recomposes := fun x hx => (trueRepresentation.represents x hx).trans (channel_eq_arithmetic hx)

/-! ## Porteuse ⟺ zêta s'annule au point (hauteur positive) -/

theorem zeta_eq_zero_of_isCarrier {β T : ℝ} (hT : 0 < T) (h : IsCarrier β T) : riemannZeta (towerPoint β T) = 0 := by
  by_contra hne
  exact (not_isCarrier_iff hT).mpr hne h

theorem isCarrier_of_zeta_eq_zero {β T : ℝ} (hT : 0 < T) (h : riemannZeta (towerPoint β T) = 0) : IsCarrier β T := by
  by_contra hc
  exact (not_isCarrier_iff hT).mp hc h

theorem isNontrivialZetaZero_towerPoint {β T : ℝ} (hT : 0 < T) (h : riemannZeta (towerPoint β T) = 0) :
    IsNontrivialZetaZero (towerPoint β T) := by
  refine ⟨h, ?_, towerPoint_ne_one hT⟩
  rintro ⟨n, hn⟩
  have him : (towerPoint β T).im = 0 := by
    rw [hn]
    simp
  rw [towerPoint_im] at him
  linarith

/-! ## R5 : toute recomposition contient chaque porteuse, aucune ne charge une non-porteuse -/

theorem recomposition_weight_eq_zero_of_not_isCarrier {ι : Type*} (Rec : ArithmeticRecomposition ι) {β T : ℝ} (hT : 0 < T)
    (hc : ¬ IsCarrier β T) (i : ι) (hi : Rec.point i = towerPoint β T) : Rec.weight i = 0 := by
  refine Rec.toSpectral.no_intruder i ?_
  intro hz
  have hz' : IsNontrivialZetaZero (Rec.point i) := hz
  rw [hi] at hz'
  exact (not_isCarrier_iff hT).mp hc hz'.1

theorem recomposition_contains_carrier {ι : Type*} (Rec : ArithmeticRecomposition ι) {β T : ℝ} (hT : 0 < T)
    (hc : IsCarrier β T) : ∃ i, Rec.point i = towerPoint β T ∧ Rec.weight i ≠ 0 := by
  have hz := isNontrivialZetaZero_towerPoint hT (zeta_eq_zero_of_isCarrier hT hc)
  obtain ⟨i, hi, hw⟩ := Rec.toSpectral.contains_member ⟨towerPoint β T, hz⟩
  refine ⟨i, hi, ?_⟩
  have hw' : Rec.weight i = -(zetaZeroMultiplicity (towerPoint β T) : ℂ) := hw
  rw [hw', neg_ne_zero]
  exact_mod_cast (zetaZeroMultiplicity_pos hz.1).ne'

/-! ## R3–R4 : réalisée ⟺ porteuse ⟺ zêta s'annule -/

def ArithmeticallyRealized (β T : ℝ) : Prop :=
  ∃ (ι : Type) (Rec : ArithmeticRecomposition ι) (i : ι), Rec.point i = towerPoint β T ∧ Rec.weight i ≠ 0

theorem arithmeticallyRealized_iff_isCarrier {β T : ℝ} (hT : 0 < T) : ArithmeticallyRealized β T ↔ IsCarrier β T := by
  constructor
  · rintro ⟨ι, Rec, i, hi, hw⟩
    by_contra hc
    exact hw (recomposition_weight_eq_zero_of_not_isCarrier Rec hT hc i hi)
  · intro hc
    obtain ⟨i, hi, hw⟩ := recomposition_contains_carrier trueRecomposition hT hc
    exact ⟨ExplicitIndex, trueRecomposition, i, hi, hw⟩

theorem arithmeticallyRealized_iff_zeta_eq_zero {β T : ℝ} (hT : 0 < T) :
    ArithmeticallyRealized β T ↔ riemannZeta (towerPoint β T) = 0 :=
  (arithmeticallyRealized_iff_isCarrier hT).trans ⟨zeta_eq_zero_of_isCarrier hT, isCarrier_of_zeta_eq_zero hT⟩

/-! ## R6–R7 : le lecteur du mot total défini par la réalisation arithmétique -/

def arithmeticWordCarrier (w : ℕ → ℤ) : Prop :=
  ∃ β T : ℝ, 0 < β ∧ 0 < T ∧ w = towerWord β T ∧ ArithmeticallyRealized β T

theorem arithmeticWordCarrier_iff_totalWordCarrier (w : ℕ → ℤ) : arithmeticWordCarrier w ↔ totalWordCarrier w := by
  constructor
  · rintro ⟨β, T, hβ, hT, hw, hr⟩
    exact ⟨β, T, hβ, hT, hw, (arithmeticallyRealized_iff_isCarrier hT).mp hr⟩
  · rintro ⟨β, T, hβ, hT, hw, hc⟩
    exact ⟨β, T, hβ, hT, hw, (arithmeticallyRealized_iff_isCarrier hT).mpr hc⟩

theorem readsCarriers_arithmeticWordCarrier : ReadsCarriers arithmeticWordCarrier := by
  intro β T hβ hT
  exact (arithmeticWordCarrier_iff_totalWordCarrier _).trans (readsCarriers_totalWordCarrier β T hβ hT)

/-! ## R8 : classement contre RH -/

theorem riemannHypothesis_iff_realized_on_line :
    RiemannHypothesis ↔ ∀ β T : ℝ, 0 < T → ArithmeticallyRealized β T → β = 1 / 2 := by
  constructor
  · intro hRH β T hT hr
    have hz := isNontrivialZetaZero_towerPoint hT ((arithmeticallyRealized_iff_zeta_eq_zero hT).mp hr)
    have h := hRH (towerPoint β T) hz.1 hz.2.1 hz.2.2
    rwa [towerPoint_re] at h
  · intro h
    refine riemannHypothesis_of_noOff fun z hOff => hOff ?_
    exact h _ _ (zero_height_pos z)
      ((arithmeticallyRealized_iff_isCarrier (zero_height_pos z)).mpr (isCarrier_zero z))

#print axioms trueRecomposition
#print axioms recomposition_weight_eq_zero_of_not_isCarrier
#print axioms recomposition_contains_carrier
#print axioms arithmeticallyRealized_iff_isCarrier
#print axioms arithmeticallyRealized_iff_zeta_eq_zero
#print axioms arithmeticWordCarrier_iff_totalWordCarrier
#print axioms readsCarriers_arithmeticWordCarrier
#print axioms riemannHypothesis_iff_realized_on_line

end RHV6Fresh
