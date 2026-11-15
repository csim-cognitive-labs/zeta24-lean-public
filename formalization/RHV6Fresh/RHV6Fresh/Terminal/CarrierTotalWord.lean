/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CarrierSelection

/-!
# RHV6Fresh — Terminal/CarrierTotalWord : la sélection des porteurs lue sur le mot TOTAL
(E461, plan Φ étape Φ5, §19.90, 2026-11-09 ; module isolé, NON importé par `RHV6Fresh.lean` ;
aucune hypothèse, aucun axiome, aucun `sorry`)

Proposition de l'auteur (2026-11-09) : « totalité des contacts d'une Tour = même rythme, même phase, même fréquence, même relation
aux premiers ⟹ c'est un zéro ». Ce module fixe ce qui en est ACQUIS, sans rien poser :

* T1 `tower_eq_of_same_towerWord` : deux Tours de même mot total sont la même Tour (E449 réécrit sur `towerWord`).
* T2 `isCarrier_iff_of_same_towerWord` : deux Tours de même mot total sont porteuses ensemble ou non.
* T3 `ReadsCarriers P` : `P` lit la sélection (sur toute Tour, `P` du mot ⟺ porteuse) ; `readsCarriers_totalWordCarrier` : un tel
  lecteur EXISTE. Il est défini PAR le poids : c'est l'existence, non la définition arithmétique indépendante.
* T4 `readsCarriers_unique_on_tower_words` : deux lecteurs coïncident sur tous les mots de Tours.
* T5 `readsCarriers_zeroWord` : tout lecteur est vrai sur le mot de tout zéro vrai, sur la ligne comme hors ligne.
* T6 `readsCarriers_not_finite_window` : aucun lecteur ne dépend d'une fenêtre finie de rangs (E457) : il faut la TOTALITÉ.
* T7 `zero_data_eq_of_same_zeroWord` : deux zéros vrais de même mot ont même hauteur et même position radiale.

Portée : la « réalisation arithmétique » de la proposition (un lecteur défini sans le poids ni l'annulation de zêta) n'est PAS
fournie ici ; elle reste l'obligation ouverte, seulement nommée. « Lecteur ⟺ porteur » caractérise tous les porteurs : ce n'est pas
une reformulation de RH et cela n'exclut aucun zéro hors ligne. Aucune contradiction n'est tirée ; aucune théorie spectrale.
-/

namespace RHV6Fresh

open Real RHV3Lean

/-! ## T1–T2 : le mot total détermine la Tour, donc son statut de porteuse -/

theorem tower_eq_of_same_towerWord {β β' T T' : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (hT : 0 < T) (hT' : 0 < T')
    (hw : towerWord β T = towerWord β' T') : T = T' ∧ β = β' :=
  tower_eq_of_same_word hβ hβ' hT hT' (fun n => congrFun hw n)

theorem isCarrier_iff_of_same_towerWord {β β' T T' : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (hT : 0 < T) (hT' : 0 < T')
    (hw : towerWord β T = towerWord β' T') : IsCarrier β T ↔ IsCarrier β' T' := by
  obtain ⟨hTT, hββ⟩ := tower_eq_of_same_towerWord hβ hβ' hT hT' hw
  rw [hTT, hββ]

/-! ## T3 : un lecteur de la sélection sur le mot total existe -/

def ReadsCarriers (P : (ℕ → ℤ) → Prop) : Prop :=
  ∀ β T : ℝ, 0 < β → 0 < T → (P (towerWord β T) ↔ IsCarrier β T)

def totalWordCarrier (w : ℕ → ℤ) : Prop :=
  ∃ β T : ℝ, 0 < β ∧ 0 < T ∧ w = towerWord β T ∧ IsCarrier β T

theorem readsCarriers_totalWordCarrier : ReadsCarriers totalWordCarrier := by
  intro β T hβ hT
  constructor
  · rintro ⟨β', T', hβ', hT', hw, hc⟩
    exact (isCarrier_iff_of_same_towerWord hβ hβ' hT hT' hw).mpr hc
  · intro hc
    exact ⟨β, T, hβ, hT, rfl, hc⟩

/-! ## T4–T6 : unicité sur les mots de Tours, valeur sur les zéros vrais, jamais à fenêtre finie -/

theorem readsCarriers_unique_on_tower_words {P Q : (ℕ → ℤ) → Prop} (hP : ReadsCarriers P) (hQ : ReadsCarriers Q)
    {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) : P (towerWord β T) ↔ Q (towerWord β T) :=
  (hP β T hβ hT).trans (hQ β T hβ hT).symm

theorem readsCarriers_zeroWord {P : (ℕ → ℤ) → Prop} (hP : ReadsCarriers P) (z : TrueZero) : P (zeroWord z) :=
  (hP (rZeroRadialPosition z.1) (rZeroHeight z.1) (zero_radial_pos z) (zero_height_pos z)).mpr (isCarrier_zero z)

theorem readsCarriers_not_finite_window {P : (ℕ → ℤ) → Prop} (hP : ReadsCarriers P) (z : TrueZero) (S : Finset ℕ) :
    ¬ ∀ w w' : ℕ → ℤ, (∀ n ∈ S, w n = w' n) → (P w ↔ P w') := by
  intro hfin
  obtain ⟨β', hβ', -, hnc, hPw⟩ :=
    finite_window_predicate_not_carrier_selective P S hfin z (readsCarriers_zeroWord hP z)
  exact hnc ((hP β' (rZeroHeight z.1) hβ' (zero_height_pos z)).mp hPw)

/-! ## T7 : le mot d'un zéro vrai rend sa hauteur et sa position radiale -/

theorem zero_data_eq_of_same_zeroWord (z w : TrueZero) (h : zeroWord z = zeroWord w) :
    rZeroHeight z.1 = rZeroHeight w.1 ∧ rZeroRadialPosition z.1 = rZeroRadialPosition w.1 :=
  tower_eq_of_same_towerWord (zero_radial_pos z) (zero_radial_pos w) (zero_height_pos z) (zero_height_pos w) h

/-! ## T8–T9 (§19.91) : une Tour de même mot total que la Tour d'un zéro vrai EST ce zéro -/

theorem tower_is_zero_of_same_word_as_zero {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (z : TrueZero)
    (hw : towerWord β T = zeroWord z) :
    IsCarrier β T ∧ T = rZeroHeight z.1 ∧ β = rZeroRadialPosition z.1 := by
  obtain ⟨hTT, hββ⟩ := tower_eq_of_same_towerWord hβ (zero_radial_pos z) hT (zero_height_pos z) hw
  refine ⟨?_, hTT, hββ⟩
  rw [hTT, hββ]
  exact isCarrier_zero z

theorem zeta_eq_zero_of_same_word_as_zero {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (z : TrueZero)
    (hw : towerWord β T = zeroWord z) : riemannZeta (towerPoint β T) = 0 := by
  by_contra h
  exact (not_isCarrier_iff hT).mpr h (tower_is_zero_of_same_word_as_zero hβ hT z hw).1

#print axioms tower_eq_of_same_towerWord
#print axioms isCarrier_iff_of_same_towerWord
#print axioms readsCarriers_totalWordCarrier
#print axioms readsCarriers_unique_on_tower_words
#print axioms readsCarriers_zeroWord
#print axioms readsCarriers_not_finite_window
#print axioms zero_data_eq_of_same_zeroWord
#print axioms tower_is_zero_of_same_word_as_zero
#print axioms zeta_eq_zero_of_same_word_as_zero

end RHV6Fresh
