/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PairArrivalPassage
import RHV6Fresh.Terminal.LowNextZeroSignatures
import RHV6Fresh.Terminal.FixedGapRaccords
import RHV6Fresh.Terminal.FrequencyCascadeStability
import RHV6Fresh.Terminal.OnCrossReadings

/-!
# K5 — La fibre de l'arrivée basse, en fréquence seule (E455, §19.78, 2026-11-08 ; module isolé, NON importé par
`RHV6Fresh.lean` ; aucune hypothèse, aucun axiome, aucun `sorry`, aucune amplitude)

Question de l'auteur : « les fréquences des OFF sont forcément différentes de celles des ON : un OFF ne peut pas prendre la
hauteur du ON occupée, ni atteindre le prochain ON ». Ce module fixe, par l'ordre lexicographique (hauteur, position radiale)
seul, ce que cela veut dire exactement et où s'arrête ce qui est démontré.

* M1 `low_arrival_above_on_history` : sous historique sur la ligne, l'arrivée (basse ou non : l'hypothèse radiale est inutile)
  a une hauteur strictement supérieure à celle du membre qu'elle suit, et aucun membre n'a de hauteur strictement entre les deux.
  C'est la forme compilée de (a) et (b) vers le BAS : l'OFF ne reprend aucune hauteur de son historique, et il prend sa hauteur
  neuve exactement comme un ON l'aurait prise.
* M2 `low_entry_successor_le_half_of_on_fibre` : si un membre sur la ligne a la hauteur d'une entrée basse, le successeur de
  l'entrée est au plus à un demi (l'ordre place ce ON entre l'entrée et son miroir).
* M3 `no_on_in_fibre_of_successor_right` : si le successeur d'une entrée basse est strictement au-dessus d'un demi, aucun membre
  sur la ligne n'a la hauteur de l'entrée.
* M4 `low_entry_successor_trichotomy` : le successeur d'une entrée basse est strictement bas, ou exactement sur la ligne (fibre
  mixte), ou strictement au-dessus d'un demi, borné par le miroir, avec une fibre sans ON. Le côté du successeur décide si l'OFF
  « prend la hauteur d'un ON » ; rien dans l'ordre ne tranche.
* M5 `low_arrival_on_fibre_refutes_noMixedHeight` : une entrée basse et un ON de même hauteur réfutent `NoMixedHeight` (hypothèse
  nommée, impliquée par RH, jamais dérivée) : c'est la frontière exacte de (a) vers le HAUT.
* M6 `on_members_split_by_low_arrival` : tout membre sur la ligne a une hauteur strictement inférieure à celle d'une entrée basse,
  ou une hauteur au moins égale et vient après elle. Forme compilée de (b) : le prochain ON n'est jamais dépassé, il est atteint
  seulement dans la fibre mixte.

Ce qui est compilé ailleurs et sur quoi ce module s'appuie : `frequency_rises_of_history_onLine`,
`consecutive_no_height_between`, `passage_frozen_of_low_entry`, `low_entry_successor_radial_le`. Rappels (non dupliqués) :
`low_arrival_count_jump` (la fibre de l'arrivée basse porte au moins deux unités), `mirror_breaks_frequency_cascade` (un seul
membre hors ligne force deux rangs consécutifs à la même fréquence), `fibre_multiple_iff_off`.

Portée : (c) « la fréquence de l'OFF est affectée » signifie, compilé, « sa fréquence est prise au moins deux fois et la montée
reprend après la fibre », non « sa valeur diffère de celle qu'un ON aurait prise ». Aucune contradiction.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Vers le bas : hauteur neuve, rien entre -/

/-- **M1** Sous historique sur la ligne, l'arrivée a une hauteur strictement supérieure à celle du membre qu'elle suit, et
aucun membre n'a de hauteur strictement entre les deux. Aucune hypothèse radiale sur l'arrivée : un OFF prend sa hauteur neuve
exactement comme un ON. -/
theorem low_arrival_above_on_history (p : TZeroPassage) (l : TrueZero) (hl : l.1 = p.zLaterMember)
    (hE : 0 < rZeroHeight p.zEarlierMember)
    (hHist : ∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) :
    rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
      ∀ w : TNonTrivialZetaZero,
        ¬ (rZeroHeight p.zEarlierMember < rZeroHeight w ∧ rZeroHeight w < rZeroHeight p.zLaterMember) := by
  have hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2 := hHist ⟨p.zEarlierMember, hE⟩ p.precedes
  exact ⟨frequency_rises_of_history_onLine p l hl hOn hHist, fun w => consecutive_no_height_between p w⟩

/-! ## 2. Vers le haut : la fibre mixte, décidée par le côté du successeur -/

/-- **M2** Si un membre sur la ligne a la hauteur d'une entrée basse, le successeur de l'entrée est au plus à un demi. -/
theorem low_entry_successor_le_half_of_on_fibre (p : TZeroPassage) (l : TrueZero) (hl : l.1 = p.zEarlierMember)
    (hlow : rZeroRadialPosition p.zEarlierMember < 1 / 2)
    (w : TrueZero) (hw : rZeroHeight w.1 = rZeroHeight l.1) (hOn : rZeroRadialPosition w.1 = 1 / 2) :
    rZeroRadialPosition p.zLaterMember ≤ 1 / 2 := by
  by_contra hgt
  push Not at hgt
  have hfro := passage_frozen_of_low_entry p hlow
  have h1 : PZeroMemberPrecedes p.zEarlierMember w.1 := by
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]; right
    refine ⟨?_, ?_⟩
    · rw [hw, hl]
    · rw [hOn]; exact hlow
  have h2 : PZeroMemberPrecedes w.1 p.zLaterMember := by
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]; right
    refine ⟨?_, ?_⟩
    · rw [hw, hl]; exact hfro
    · rw [hOn]; exact hgt
  exact p.hConsecutive.2 ⟨_, h1, h2⟩

/-- **M3** Si le successeur d'une entrée basse est strictement au-dessus d'un demi, aucun membre sur la ligne n'a la hauteur
de l'entrée. -/
theorem no_on_in_fibre_of_successor_right (p : TZeroPassage) (l : TrueZero) (hl : l.1 = p.zEarlierMember)
    (hlow : rZeroRadialPosition p.zEarlierMember < 1 / 2)
    (hr : 1 / 2 < rZeroRadialPosition p.zLaterMember) :
    ∀ w : TrueZero, rZeroHeight w.1 = rZeroHeight l.1 → rZeroRadialPosition w.1 ≠ 1 / 2 :=
  fun w hw hOn => absurd (low_entry_successor_le_half_of_on_fibre p l hl hlow w hw hOn) (not_le.mpr hr)

/-- **M4** Trichotomie du successeur d'une entrée basse : strictement bas ; exactement sur la ligne (fibre mixte) ;
strictement au-dessus d'un demi, borné par le miroir, fibre sans ON. -/
theorem low_entry_successor_trichotomy (p : TZeroPassage) (l : TrueZero) (hl : l.1 = p.zEarlierMember)
    (hlow : rZeroRadialPosition p.zEarlierMember < 1 / 2) :
    rZeroRadialPosition p.zLaterMember < 1 / 2 ∨
      rZeroRadialPosition p.zLaterMember = 1 / 2 ∨
      (1 / 2 < rZeroRadialPosition p.zLaterMember ∧
        rZeroRadialPosition p.zLaterMember ≤ 1 - rZeroRadialPosition p.zEarlierMember ∧
        ∀ w : TrueZero, rZeroHeight w.1 = rZeroHeight l.1 → rZeroRadialPosition w.1 ≠ 1 / 2) := by
  rcases lt_trichotomy (rZeroRadialPosition p.zLaterMember) (1 / 2) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h, low_entry_successor_radial_le p l hl hlow,
      no_on_in_fibre_of_successor_right p l hl hlow h⟩)

/-- **M5** Une entrée basse et un membre sur la ligne de même hauteur réfutent `NoMixedHeight` (contraposée ; aucune
hypothèse posée). -/
theorem low_arrival_on_fibre_refutes_noMixedHeight (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2)
    (w : TrueZero) (hw : rZeroHeight w.1 = rZeroHeight l.1) (hOn : rZeroRadialPosition w.1 = 1 / 2) :
    ¬ NoMixedHeight :=
  fun h => absurd (h l w hw.symm hOn) (ne_of_lt hlow)

/-! ## 3. Le prochain ON n'est jamais dépassé -/

/-- **M6** Tout membre sur la ligne a une hauteur strictement inférieure à celle d'une entrée basse, ou une hauteur au moins
égale et vient après elle dans l'ordre. -/
theorem on_members_split_by_low_arrival (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2)
    (w : TrueZero) (hOn : rZeroRadialPosition w.1 = 1 / 2) :
    rZeroHeight w.1 < rZeroHeight l.1 ∨
      (rZeroHeight l.1 ≤ rZeroHeight w.1 ∧ PZeroMemberPrecedes l.1 w.1) := by
  rcases lt_trichotomy (rZeroHeight w.1) (rZeroHeight l.1) with h | h | h
  · exact Or.inl h
  · right
    refine ⟨h.symm.le, ?_⟩
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]; right
    refine ⟨h.symm, ?_⟩; rw [hOn]; exact hlow
  · right
    refine ⟨h.le, ?_⟩
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]; left; exact h

#print axioms low_arrival_above_on_history
#print axioms low_entry_successor_le_half_of_on_fibre
#print axioms no_on_in_fibre_of_successor_right
#print axioms low_entry_successor_trichotomy
#print axioms low_arrival_on_fibre_refutes_noMixedHeight
#print axioms on_members_split_by_low_arrival

end RHV6Fresh
