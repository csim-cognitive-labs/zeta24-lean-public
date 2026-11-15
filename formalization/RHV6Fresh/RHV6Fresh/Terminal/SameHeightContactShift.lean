/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TowerTwoSidedRoom
import RHV6Fresh.Terminal.TangentialInversion
import RHV6Fresh.Terminal.ContactsFromGapsInversion
import RHV6Fresh.Terminal.MeetingRegimeFinite

/-!
# K6 — Le décalage des contacts à même hauteur (E456, §19.79, 2026-11-08 ; module isolé, NON importé par `RHV6Fresh.lean` ;
aucune hypothèse, aucun axiome, aucun `sorry`, aucune amplitude, aucun zéro : identités de paramètres `(β, T)`)

Question de l'auteur (Q1 de §19.79) : « un zéro calculé sur la ligne et un zéro calculé hors ligne qui viseraient la même hauteur ;
affecter une valeur à β change la fréquence atteignable ; si on affecte quelque chose à β, T en souffre ». Ce que le corpus avait
déjà : la lecture d'un écart ne dépend que de la hauteur (`gap_reading_height_only`), la phase `arctan(T/β)` dépend de β, les
contacts d'une Tour de position radiale plus grande sont tous plus bas (`windingContact_lt_of_radial_lt`), le rapport des contacts
de même indice est unique (`windingContact_sameHeight`), et le mot sur tous les premiers fixe la hauteur ET β
(`tower_eq_of_same_word`). Ce module ajoute la forme littérale des deux phrases de l'auteur.

* M0 `phase_diff_abs_lt_half_pi` : deux phases de même hauteur diffèrent de moins d'un quart de tour.
* M1 `same_height_distinct_radial_no_shared_contact` : à même hauteur, deux positions radiales différentes ne partagent AUCUN
  contact, à aucun couple d'indices. Le décalage n'est jamais un nombre entier de cellules.
* M2 `off_shares_no_contact_with_line_same_height` : un OFF à hauteur `T` ne prend aucune rencontre de la Tour de ligne de hauteur `T`.
* M3 `shared_contact_forces_height_change` : si un même premier est contact de deux Tours de positions radiales différentes, leurs
  hauteurs diffèrent — « si on affecte quelque chose à β, T en souffre », au sens exact : à rencontre imposée.
* M4 `same_height_shift_within_half_cell` : à même hauteur, chaque contact est strictement à moins d'une demi-cellule (en logarithme :
  `π/(2T)`) du contact de même indice de l'autre Tour — les grilles sont décalées, jamais confondues, jamais échangées d'un indice.
* M5 `cell_ratio_radially_blind` : le rapport de deux contacts consécutifs vaut `e^{π/T}` pour toute position radiale — le pas, donc
  le pouvoir de résolution des écarts (`log_ratio_ge_cell_of_meeting`, `two_consecutive_contacts_finite`), ne dépend que de `T`.

Ce que le module NE dit PAS : qu'un OFF de hauteur `T` ait une autre hauteur que `T` ; que la grille décalée soit interdite à un zéro
(frontière, §19.78 : `NoMixedHeight` ⟸ RH) ; que les OFF soient nécessaires ou impossibles aux grandes hauteurs (Q2, §19.79.2).
-/

namespace RHV6Fresh

/-- **M0.** Deux phases de même hauteur diffèrent de moins d'un quart de tour. -/
theorem phase_diff_abs_lt_half_pi {β β' T : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (hT : 0 < T) :
    -(Real.pi / 2) < Real.arctan (T / β) - Real.arctan (T / β') ∧
      Real.arctan (T / β) - Real.arctan (T / β') < Real.pi / 2 := by
  have a1 : 0 < Real.arctan (T / β) := Real.arctan_pos.mpr (div_pos hT hβ)
  have a2 : Real.arctan (T / β) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have b1 : 0 < Real.arctan (T / β') := Real.arctan_pos.mpr (div_pos hT hβ')
  have b2 : Real.arctan (T / β') < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  constructor <;> linarith

/-- **M1.** À même hauteur, deux positions radiales différentes ne partagent aucun contact, à aucun couple d'indices. -/
theorem same_height_distinct_radial_no_shared_contact {β β' T : ℝ} (hβ : 0 < β) (hβ' : 0 < β')
    (hne : β ≠ β') (hT : 0 < T) (k j : ℤ) : windingContact β T k ≠ windingContact β' T j := by
  intro h
  unfold windingContact at h
  have h1 := Real.exp_eq_exp.mp h
  have h2 : Real.arctan (T / β) + k * Real.pi = Real.arctan (T / β') + j * Real.pi :=
    (div_left_inj' hT.ne').mp h1
  obtain ⟨l1, l2⟩ := phase_diff_abs_lt_half_pi hβ hβ' hT
  have hpi := Real.pi_pos
  rcases lt_trichotomy (j - k) 0 with hd | hd | hd
  · have hd' : ((j - k : ℤ) : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hd
    push_cast at hd'
    nlinarith
  · have hjk : j = k := by omega
    subst hjk
    have h3 : Real.arctan (T / β) = Real.arctan (T / β') := by linarith
    have h4 := Real.arctan_injective h3
    apply hne
    field_simp at h4
    nlinarith
  · have hd' : (1 : ℝ) ≤ ((j - k : ℤ) : ℝ) := by exact_mod_cast hd
    push_cast at hd'
    nlinarith

/-- **M2.** Un OFF de hauteur `T` ne prend aucune rencontre de la Tour de ligne de hauteur `T`. -/
theorem off_shares_no_contact_with_line_same_height {β T : ℝ} (hβ : 0 < β) (hne : β ≠ 1 / 2) (hT : 0 < T)
    (k j : ℤ) : windingContact β T k ≠ lineContact T j := by
  rw [← windingContact_half]
  exact same_height_distinct_radial_no_shared_contact hβ (by norm_num) hne hT k j

/-- **M3.** Une rencontre commune à deux positions radiales différentes impose des hauteurs différentes. -/
theorem shared_contact_forces_height_change {β β' T T' q : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (hT : 0 < T)
    (hne : β ≠ β') {k j : ℤ} (hk : windingContact β T k = q) (hj : windingContact β' T' j = q) : T ≠ T' := by
  intro hTT
  subst hTT
  exact same_height_distinct_radial_no_shared_contact hβ hβ' hne hT k j (hk.trans hj.symm)

/-- **M4.** À même hauteur, chaque contact est strictement à moins d'une demi-cellule du contact de même indice de l'autre Tour. -/
theorem same_height_shift_within_half_cell {β β' T : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (hT : 0 < T) (k : ℝ) :
    Real.exp (-(Real.pi / (2 * T))) * windingContact β' T k < windingContact β T k ∧
      windingContact β T k < Real.exp (Real.pi / (2 * T)) * windingContact β' T k := by
  obtain ⟨l1, l2⟩ := phase_diff_abs_lt_half_pi hβ hβ' hT
  rw [windingContact_sameHeight β' β T k]
  have hpos := windingContact_pos β' T k
  have e1 : -(Real.pi / (2 * T)) < (Real.arctan (T / β) - Real.arctan (T / β')) / T := by
    rw [show -(Real.pi / (2 * T)) = (-(Real.pi / 2)) / T by ring]
    exact div_lt_div_of_pos_right l1 hT
  have e2 : (Real.arctan (T / β) - Real.arctan (T / β')) / T < Real.pi / (2 * T) := by
    rw [show Real.pi / (2 * T) = (Real.pi / 2) / T by ring]
    exact div_lt_div_of_pos_right l2 hT
  constructor
  · rw [mul_comm (windingContact β' T k)]
    exact mul_lt_mul_of_pos_right (Real.exp_lt_exp.mpr e1) hpos
  · rw [mul_comm (windingContact β' T k)]
    exact mul_lt_mul_of_pos_right (Real.exp_lt_exp.mpr e2) hpos

/-- **M5.** Le rapport de deux contacts consécutifs vaut `e^{π/T}` quelle que soit la position radiale. -/
theorem cell_ratio_radially_blind (β T k : ℝ) (hT : 0 < T) :
    windingContact β T (k + 1) = Real.exp (Real.pi / T) * windingContact β T k := by
  unfold windingContact
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

#print axioms phase_diff_abs_lt_half_pi
#print axioms same_height_distinct_radial_no_shared_contact
#print axioms off_shares_no_contact_with_line_same_height
#print axioms shared_contact_forces_height_change
#print axioms same_height_shift_within_half_cell
#print axioms cell_ratio_radially_blind

end RHV6Fresh
