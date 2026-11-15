/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PairWordInversion

/-!
# RHV6Fresh — Terminal/PairArrivalPassage : la paire lue comme PASSAGE depuis l'arrivée basse (E454, §19.77, K4,
2026-11-08 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse, aucun axiome, aucun `sorry`)

K0–K3 (E450–E453) décrivent la paire par ses deux TERMES. K4 la décrit par la PLACE de ses membres dans l'énumération
canonique et par ce que l'ordre impose au passage qui SORT de l'arrivée (§19.76 : l'arrivée est au plus à un demi).
Tout est composition d'énoncés compilés hors du ban ; deux termes au plus ; aucune somme de Tours.

## L1. `arrival_low_of_off` : une arrivée hors ligne est strictement sous un demi.
## L2. `passage_frozen_of_low_entry` : le passage qui sort d'un membre strictement sous un demi est GELÉ (même hauteur ;
  contraposée de `passage_exit_radial_ge_half`, avec `passage_height_le` d'InterTowerExcess) ; `passage_right_of_low_entry` :
  son membre de sortie est strictement plus à droite.
## L3. `low_arrival_precedes_mirror` : le miroir d'une arrivée basse vient APRÈS elle ; `low_entry_successor_radial_le`,
  `low_entry_successor_band` : le successeur immédiat d'un membre bas ne dépasse pas le miroir, position radiale dans `(β, 1−β]`
  (consécutivité `p.hConsecutive.2`).
## L4. L'arrivée basse est le membre FAIBLE : `low_arrival_contact_ratio_lt` (rapport des valeurs aux contacts plus petit que
  celui du miroir, `mirror_contact_ratio_gt`), `low_arrival_term_ratio_tendsto_zero` (rapport des termes arrivée/miroir → 0,
  `zero_pair_term_ratio`). Dans l'énumération, le faible vient d'abord, le dominant ensuite, sans montée de fréquence.
## L5. `frozen_passage_same_word_slope` : les deux membres d'un passage gelé lisent la même pente de mot.
## L6. `low_entry_not_expected` : un membre d'entrée strictement sous un demi met en échec la prémisse unique
  `ExpectedFrequencyRisesAtMeetings` (compilée ⟺ RH, MeetingPoint) ; `frozen_passage_has_low_member` : tout passage gelé a un
  membre bas à sa hauteur (l'entrée, ou le miroir de la sortie, qui précède l'entrée).
## L7. `arrival_exit_dichotomy` : sous historique sur la ligne, ou bien l'arrivée est sur la ligne, ou bien elle est basse et le
  passage qui en sort est gelé, plus à droite, borné par le miroir. Aucun troisième cas.

Réponse de K4 (consignée d'avance en §19.77.3 et compilée ici) : K4 fixe la FORME du passage OFF ; AUCUNE contradiction ;
la frontière reste la prémisse unique, équivalente à RH, dont K0–K4 ne donnent pas de dérivation.
-/
namespace RHV6Fresh

open Real Filter Topology RHV3Lean

theorem arrival_low_of_off (p : TZeroPassage) (l : TrueZero) (hl : l.1 = p.zLaterMember)
    (hT : rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember)
    (hoff : rZeroRadialPosition l.1 ≠ 1 / 2) : rZeroRadialPosition l.1 < 1 / 2 :=
  lt_of_le_of_ne (arrival_radial_le_half p l hl hT) hoff

theorem passage_frozen_of_low_entry (p : TZeroPassage)
    (hlow : rZeroRadialPosition p.zEarlierMember < 1 / 2) :
    rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember := by
  rcases lt_or_eq_of_le (passage_height_le p) with hlt | heq
  · exact absurd (passage_exit_radial_ge_half p hlt) (not_le.mpr hlow)
  · exact heq

theorem passage_right_of_low_entry (p : TZeroPassage)
    (hlow : rZeroRadialPosition p.zEarlierMember < 1 / 2) :
    rZeroRadialPosition p.zEarlierMember < rZeroRadialPosition p.zLaterMember :=
  shared_frequency_passage_profile p (passage_frozen_of_low_entry p hlow)

theorem low_arrival_precedes_mirror (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2) :
    PZeroMemberPrecedes l.1 (mirrorMember l).1 := by
  rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
  right
  refine ⟨(mirrorMember_ordinate l).symm, ?_⟩
  rw [mirrorMember_radial]
  linarith

theorem low_entry_successor_radial_le (p : TZeroPassage) (l : TrueZero) (hl : l.1 = p.zEarlierMember)
    (hlow : rZeroRadialPosition p.zEarlierMember < 1 / 2) :
    rZeroRadialPosition p.zLaterMember ≤ 1 - rZeroRadialPosition p.zEarlierMember := by
  by_contra hgt
  push Not at hgt
  have hlow' : rZeroRadialPosition l.1 < 1 / 2 := by rw [hl]; exact hlow
  have hm : PZeroMemberPrecedes p.zEarlierMember (mirrorMember l).1 := by
    rw [← hl]; exact low_arrival_precedes_mirror l hlow'
  have hm2 : PZeroMemberPrecedes (mirrorMember l).1 p.zLaterMember := by
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    refine ⟨?_, ?_⟩
    · rw [mirrorMember_ordinate, hl]; exact passage_frozen_of_low_entry p hlow
    · rw [mirrorMember_radial, hl]; exact hgt
  exact p.hConsecutive.2 ⟨_, hm, hm2⟩

theorem low_entry_successor_band (p : TZeroPassage) (l : TrueZero) (hl : l.1 = p.zEarlierMember)
    (hlow : rZeroRadialPosition p.zEarlierMember < 1 / 2) :
    rZeroRadialPosition p.zEarlierMember < rZeroRadialPosition p.zLaterMember ∧
      rZeroRadialPosition p.zLaterMember ≤ 1 - rZeroRadialPosition p.zEarlierMember :=
  ⟨passage_right_of_low_entry p hlow, low_entry_successor_radial_le p l hl hlow⟩

theorem low_arrival_contact_ratio_lt (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2) (k : ℤ) :
    |contactRealValue (rZeroRadialPosition l.1) (rZeroHeight l.1) (k + 1)| /
        |contactRealValue (rZeroRadialPosition l.1) (rZeroHeight l.1) k| <
      |contactRealValue (rZeroRadialPosition (mirrorMember l).1) (rZeroHeight (mirrorMember l).1) (k + 1)| /
        |contactRealValue (rZeroRadialPosition (mirrorMember l).1) (rZeroHeight (mirrorMember l).1) k| := by
  rw [mirrorMember_radial, mirrorMember_ordinate]
  exact mirror_contact_ratio_gt (zero_radial_pos l) hlow (zero_height_pos l) k

theorem low_arrival_term_ratio_tendsto_zero (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2) :
    Tendsto (fun x : ℝ => ‖zeroTerm l x‖ / ‖zeroTerm (mirrorMember l) x‖) atTop (𝓝 0) := by
  have hexp : 0 < 1 - 2 * rZeroRadialPosition l.1 := by linarith
  have h2 : (fun x : ℝ => x ^ (-(1 - 2 * rZeroRadialPosition l.1))) =
      fun x : ℝ => x ^ (2 * rZeroRadialPosition l.1 - 1) := by
    funext x; congr 1; ring
  have ht : Tendsto (fun x : ℝ => x ^ (2 * rZeroRadialPosition l.1 - 1) *
      (‖zeroPoint (mirrorMember l)‖ / ‖zeroPoint l‖)) atTop
      (𝓝 (0 * (‖zeroPoint (mirrorMember l)‖ / ‖zeroPoint l‖))) := by
    have := tendsto_rpow_neg_atTop hexp
    rw [h2] at this
    exact this.mul_const _
  rw [zero_mul] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (zero_pair_term_ratio l hx).symm

theorem frozen_passage_same_word_slope (p : TZeroPassage) (e l : TrueZero)
    (he : e.1 = p.zEarlierMember) (hl : l.1 = p.zLaterMember)
    (hfro : rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember) :
    Tendsto (fun n : ℕ => (lastContactBefore (rZeroRadialPosition e.1) (rZeroHeight e.1)
        (fnPrimeAtRank n : ℝ) : ℝ) / Real.log (fnPrimeAtRank n : ℝ)) atTop (𝓝 (rZeroHeight e.1 / Real.pi)) ∧
      Tendsto (fun n : ℕ => (lastContactBefore (rZeroRadialPosition l.1) (rZeroHeight l.1)
        (fnPrimeAtRank n : ℝ) : ℝ) / Real.log (fnPrimeAtRank n : ℝ)) atTop (𝓝 (rZeroHeight e.1 / Real.pi)) := by
  refine ⟨word_slope_tendsto _ (zero_height_pos e), ?_⟩
  have hh : rZeroHeight l.1 = rZeroHeight e.1 := by rw [he, hl]; exact hfro.symm
  rw [← hh]
  exact word_slope_tendsto _ (zero_height_pos l)

theorem low_entry_not_expected (p : TZeroPassage)
    (hlow : rZeroRadialPosition p.zEarlierMember < 1 / 2) : ¬ ExpectedFrequencyRisesAtMeetings :=
  fun h => absurd (passage_frozen_of_low_entry p hlow) (ne_of_lt (h p))

theorem frozen_passage_has_low_member (p : TZeroPassage) (l : TrueZero) (hl : l.1 = p.zLaterMember)
    (hfro : rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember) :
    rZeroRadialPosition p.zEarlierMember < 1 / 2 ∨
      (rZeroRadialPosition (mirrorMember l).1 < 1 / 2 ∧
        PZeroMemberPrecedes (mirrorMember l).1 p.zEarlierMember) := by
  by_cases hlow : rZeroRadialPosition p.zEarlierMember < 1 / 2
  · exact Or.inl hlow
  · right
    push Not at hlow
    have hr := shared_frequency_passage_profile p hfro
    have hm : rZeroRadialPosition (mirrorMember l).1 < 1 / 2 := by
      rw [mirrorMember_radial, hl]; linarith
    refine ⟨hm, ?_⟩
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    refine ⟨?_, ?_⟩
    · rw [mirrorMember_ordinate, hl]; exact hfro.symm
    · rw [mirrorMember_radial, hl]; linarith

theorem arrival_exit_dichotomy (p q : TZeroPassage) (l : TrueZero) (hl : l.1 = p.zLaterMember)
    (hq : q.zEarlierMember = p.zLaterMember)
    (hHist : ∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ∨
      (rZeroRadialPosition p.zLaterMember < 1 / 2 ∧
        rZeroHeight q.zEarlierMember = rZeroHeight q.zLaterMember ∧
        rZeroRadialPosition q.zEarlierMember < rZeroRadialPosition q.zLaterMember ∧
        rZeroRadialPosition q.zLaterMember ≤ 1 - rZeroRadialPosition q.zEarlierMember) := by
  rcases arrival_onLine_or_low p l hl hHist with h | h
  · exact Or.inl h
  · right
    have hq' : rZeroRadialPosition q.zEarlierMember < 1 / 2 := by rw [hq]; exact h
    exact ⟨h, passage_frozen_of_low_entry q hq', passage_right_of_low_entry q hq',
      low_entry_successor_radial_le q l (hl.trans hq.symm) hq'⟩

#print axioms arrival_low_of_off
#print axioms passage_frozen_of_low_entry
#print axioms passage_right_of_low_entry
#print axioms low_arrival_precedes_mirror
#print axioms low_entry_successor_radial_le
#print axioms low_entry_successor_band
#print axioms low_arrival_contact_ratio_lt
#print axioms low_arrival_term_ratio_tendsto_zero
#print axioms frozen_passage_same_word_slope
#print axioms low_entry_not_expected
#print axioms frozen_passage_has_low_member
#print axioms arrival_exit_dichotomy

end RHV6Fresh
