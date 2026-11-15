/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZeroCascadeReading
import RHV6Fresh.Terminal.AuthenticPassageProfile
import RHV6Fresh.Terminal.AstraSeparation
import RHV6Fresh.Terminal.LocalGlobalGapMatrix
import RHV6Fresh.Terminal.GeneratedFrequency
import RHV6Fresh.Terminal.TowerTwoSidedRoom
import RHV6Fresh.Terminal.RaccordDetector

/-!
# Chaîne de lecture, d'enroulement et de compensation entre zéros (auteur, 2026-10-19, vingt et unième message)

Chaîne de l'auteur : `Z_n = (β_n, T_n)` → enroulement de la Tour `n` → contacts successifs `C_{n,k}` → lecture des
événements premiers → raccord avec la Tour `n + 1` → compensation signée et nouvel enroulement ; obligations : ordre des
hauteurs, ordre des fréquences, lecture du précédent, compensation signée, transmission.

Compilé ici, axiomes standard, par composition des théorèmes existants :
* enroulement propre : `C_{n,k} = exp((arctan(T_n/β_n) + kπ)/T_n)`, `log(C_{n,k+1}/C_{n,k}) = π/T_n` (`winding_contacts`) ;
* pas qui diminue quand la hauteur monte (`winding_pitch_contracts`) ; dans une même Tour l'écart de deux contacts consécutifs
  est le pas complet, entre deux Tours la séparation des contacts d'indice zéro est inférieure au demi-pas
  (`same_tower_full_pitch_inter_tower_half`) ;
* sur tout passage, ensemble : hauteur et fréquence ordonnées, lecture du précédent, contacts des deux Tours, enroulement du
  suivant dans le précédent à l'infini, compensation signée (additivité des colonnes de comptage, contribution imposée)
  (`passage_reading_chain`), toute position radiale ;
* RÉDUCTION DE LA PRÉMISSE : depuis un départ ON sur un passage qui monte, la part radiale est positive ou nulle à toutes les
  rencontres (`radialShiftAt_nonneg_of_on_departure`) ; il suffit donc qu'à UNE rencontre le contact du suivant ne dépasse
  pas la position fixée par la seule hausse de fréquence (`noRadialShift_of_one_sided`) : une inégalité, une rencontre, sans
  tolérance ; équivalente à l'arrivée ON (`one_sided_iff_onLine`), quantifiée de la force de RH.
Portée : ces énoncés valent pour toute position radiale de l'arrivée, sauf la réduction, qui est une caractérisation ; la
transmission universelle n'est pas dérivée.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Enroulement propre d'une Tour -/

/-- **Enroulement propre** : contacts `C_k = exp((arctan(T/β) + kπ)/T)` et pas logarithmique `π/T`, toute position radiale. -/
theorem winding_contacts (z : TrueZero) (k : ℤ) :
    contactMinusAt z k =
        Real.exp ((Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) + (k : ℝ) * Real.pi) / rZeroHeight z.1) ∧
      Real.log (contactMinusAt z (k + 1) / contactMinusAt z k) = Real.pi / rZeroHeight z.1 := by
  refine ⟨(authentic_contacts z k).1, ?_⟩
  rw [Real.log_div (contactMinusAt_positive z (k + 1)).ne' (contactMinusAt_positive z k).ne']
  exact (authentic_contacts z k).2

/-- **Fréquence croissante** : quand la hauteur monte, le pas de contacts diminue strictement. -/
theorem winding_pitch_contracts (e l : TrueZero) (hT : rZeroHeight e.1 < rZeroHeight l.1) :
    Real.pi / rZeroHeight l.1 < Real.pi / rZeroHeight e.1 :=
  arrival_frequency_rises e l hT

/-- **Pas complet dans une Tour, moins d'un demi-pas entre deux Tours** : le pas `π/T` sépare deux contacts consécutifs d'une
même Tour ; il n'est pas une séparation minimale entre deux Tours (`interMemberLogSeparation_lt_half_pitch`). -/
theorem same_tower_full_pitch_inter_tower_half (z w : TrueZero) (hT : rZeroHeight z.1 ≤ rZeroHeight w.1) (k : ℤ) :
    Real.log (contactMinusAt z (k + 1) / contactMinusAt z k) = towerPitch z ∧
      interMemberLogSeparation z w < towerPitch z / 2 :=
  ⟨(winding_contacts z k).2, interMemberLogSeparation_lt_half_pitch z w hT⟩

/-! ## 2. La chaîne sur un passage, toute position radiale -/

/-- **Chaîne de lecture sur tout passage qui monte** : ordre des hauteurs, ordre des fréquences, lecture du précédent
(successeur déterminé, rang suivant, premier minimum attendu, hauteur du précédent retrouvée), enroulement propre des deux
Tours, enroulement du suivant dans le précédent à l'infini, compensation signée (colonnes de comptage additives sur des écarts
consécutifs ; contribution du suivant = reste des premiers − part fixe des autres vrais zéros). Toute position radiale. -/
theorem passage_reading_chain (p : TZeroPassage) (hV : VerticalPassage p) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
    Real.pi / rZeroHeight p.zLaterMember < Real.pi / rZeroHeight p.zEarlierMember ∧
    ((∀ p' : TZeroPassage, p'.zEarlierMember = p.zEarlierMember → p'.zLaterMember = p.zLaterMember) ∧
      nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
      occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
      (∀ k : ℤ, rZeroHeight p.zEarlierMember =
        Real.pi / (Real.pi / rZeroHeight p.zLaterMember -
          cascadeIncrement ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ k))) ∧
    (∀ k : ℤ, Real.log (contactMinusAt ⟨p.zEarlierMember, hE⟩ (k + 1) / contactMinusAt ⟨p.zEarlierMember, hE⟩ k) =
        Real.pi / rZeroHeight p.zEarlierMember) ∧
    (∀ k : ℤ, Real.log (contactMinusAt ⟨p.zLaterMember, hL⟩ (k + 1) / contactMinusAt ⟨p.zLaterMember, hL⟩ k) =
        Real.pi / rZeroHeight p.zLaterMember) ∧
    WindingNestedAtInfinity ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ ∧
    (∀ {a b c : ℝ}, 1 < a → a ≤ b → b ≤ c →
      cellModulation ⟨p.zLaterMember, hL⟩ a b + cellModulation ⟨p.zLaterMember, hL⟩ b c =
        cellModulation ⟨p.zLaterMember, hL⟩ a c) ∧
    (∀ {x : ℝ}, 1 < x → nontrivialZeroResidueTerm x (memberIndex ⟨p.zLaterMember, hL⟩) =
      smoothedRemainder x - othersSum ⟨p.zLaterMember, hL⟩ x) :=
  ⟨hV, winding_pitch_contracts ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hV, next_zero_reads_previous p hE hL,
    fun k => (winding_contacts _ k).2, fun k => (winding_contacts _ k).2,
    windingNestedAtInfinity_of_precedes _ _ p.hConsecutive.1,
    fun ha hab hbc => cellModulation_add _ ha hab hbc, fun hx => imposed_contribution_eq _ hx⟩

/-! ## 3. Réduction de la prémisse : une inégalité à une seule rencontre -/

/-- Depuis un départ ON, vers une arrivée au plus à un demi, la part radiale est positive ou nulle. -/
theorem radialShiftAt_nonneg_of_on (e l : TrueZero) (hOn : rZeroRadialPosition e.1 = 1 / 2)
    (hlow : rZeroRadialPosition l.1 ≤ 1 / 2) (k : ℤ) : 0 ≤ radialShiftAt e l k := by
  rw [radialShiftAt_eq e l k, (radialFactor_eq_one_iff e).mpr hOn, Real.log_one, sub_zero]
  apply Real.log_nonneg
  rcases hlow.lt_or_eq with hlt | heq
  · exact ((radialFactor_gt_one_iff l).mpr hlt).le
  · exact ((radialFactor_eq_one_iff l).mpr heq).ge

/-- Depuis un départ ON sur un passage qui monte, la part radiale du déplacement des rencontres est positive ou nulle
(l'arrivée est au plus à un demi, son facteur radial est au moins un). -/
theorem radialShiftAt_nonneg_of_on_departure (p : TZeroPassage) (hV : VerticalPassage p)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) (k : ℤ) :
    0 ≤ radialShiftAt ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ k :=
  radialShiftAt_nonneg_of_on ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hOn (passage_entry_radial_le_half p hV) k

/-- Forme générale de la réduction : une part radiale positive à toutes les rencontres et `≤ 0` à une seule est nulle à
toutes. -/
theorem noRadialShift_of_nonneg_of_one_sided (e l : TrueZero) (hnn : ∀ k : ℤ, 0 ≤ radialShiftAt e l k)
    (h : ∃ k : ℤ, radialShiftAt e l k ≤ 0) (k' : ℤ) : NoRadialShift e l k' := by
  obtain ⟨k, hk⟩ := h
  apply (noRadialShift_iff_radialShiftAt e l k').mpr
  rw [radialShiftAt_const e l k' k]
  exact le_antisymm hk (hnn k)

/-- **Réduction** : depuis un départ ON sur un passage qui monte, si à UNE rencontre le contact du suivant ne dépasse pas la
position fixée par la seule hausse de fréquence (part radiale `≤ 0`), alors il atteint exactement toutes les rencontres. -/
theorem noRadialShift_of_one_sided (p : TZeroPassage) (hV : VerticalPassage p)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (h : ∃ k : ℤ, radialShiftAt ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ k ≤ 0) (k' : ℤ) :
    NoRadialShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ k' :=
  noRadialShift_of_nonneg_of_one_sided _ _ (radialShiftAt_nonneg_of_on_departure p hV hE hL hOn) h k'

/-- La condition réduite, lue en contacts : à une rencontre, `C_{l,k} ≤ C_{e,k} · exp(part de hauteur)`. -/
theorem one_sided_iff_contact_le (e l : TrueZero) (k : ℤ) :
    radialShiftAt e l k ≤ 0 ↔
      contactMinusAt l k ≤ contactMinusAt e k * Real.exp (lineHeightShift (rZeroHeight e.1) (rZeroHeight l.1) k) := by
  unfold radialShiftAt
  rw [sub_nonpos, Real.log_le_iff_le_exp (div_pos (contactMinusAt_positive l k) (contactMinusAt_positive e k)),
    div_le_iff₀ (contactMinusAt_positive e k), mul_comm]

/-- **La condition réduite est une caractérisation** : depuis un départ ON sur un passage qui monte, elle équivaut à
l'arrivée ON. -/
theorem one_sided_iff_onLine (p : TZeroPassage) (hV : VerticalPassage p)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    (∃ k : ℤ, radialShiftAt ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ k ≤ 0) ↔
      rZeroRadialPosition p.zLaterMember = 1 / 2 := by
  constructor
  · intro h
    exact (noRadialShift_iff_onLine ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hOn 0).mp
      (noRadialShift_of_one_sided p hV hE hL hOn h 0)
  · intro hl
    exact ⟨0, ((noRadialShift_iff_radialShiftAt ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ 0).mp
      (noRadialShift_of_onLine ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hOn hl 0)).le⟩

end RHV6Fresh

#print axioms RHV6Fresh.winding_contacts
#print axioms RHV6Fresh.same_tower_full_pitch_inter_tower_half
#print axioms RHV6Fresh.passage_reading_chain
#print axioms RHV6Fresh.noRadialShift_of_one_sided
#print axioms RHV6Fresh.one_sided_iff_contact_le
#print axioms RHV6Fresh.one_sided_iff_onLine
