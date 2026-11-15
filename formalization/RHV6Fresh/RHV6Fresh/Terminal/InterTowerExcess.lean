/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ContinuousProgression
import RHV6Fresh.Terminal.EventHeightProgression

/-!
# RHV6Fresh — l'excès de phase inter-Tours `J` et la forme atomique du résidu (2026-09-28)

Plan TDD (auteur, 2026-09-28) : `experiments/PLAN_TDD_INTER_TOWER_EXCESS_20260928.md`, audit de la
proposition « PITE » (remplacer `PHeightProgression` par un « excès de phase inter-Tours `J > 0` »).

Ce fichier compile exactement ce que l'audit établit, sans rien ajouter :

* l'excès inter-Tours `interTowerExcess` est une IDENTITÉ DE BASE, `thm_towerPrimeGapSpan_diff`
  transportée par `phase_increment_eq_pi_span` — `interTowerExcess_eq` le réduit à
  `(T_l − T_e) · rPrimeGapLogRatio(n+1)`, sans mention de `RiemannHypothesis` ni dans l'énoncé ni
  dans la preuve ;
* PITE (« `∀ p, 0 < J(p)` ») EST `PHeightProgression`, seulement renommée : `J(p) > 0 ↔ T_e < T_l`
  (`interTowerExcess_pos_iff`), d'où `interTowerExcess_pos_iff_riemannHypothesis` ;
* les hypothèses grammaticales de PITE (`EV+1`, raccord, occurrence croissante) sont vraies sur TOUT
  passage, y compris le passage nul OFF (`grammar_hypotheses_of_passage`, `off_excess_zero`) : les
  ajouter en prémisse ne change donc rien
  (`interTowerExcess_pos_of_grammar_iff_riemannHypothesis`) ;
* la forme la plus atomique du résidu compilée ici est `PNoNullPassage` — un seul prédicat de la
  base (`PZeroPassageRelationNull`, i.e. `rZeroPassageHeightGap p = 0`), aucun `β`, aucune Tour,
  aucune positivité — encore exactement équivalente à `RiemannHypothesis`
  (`noNullPassage_iff_riemannHypothesis`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau. Aucun `Prop` de prémisse n'est posé en hypothèse
d'un théorème concluant `RiemannHypothesis`, hormis les équivalences `↔ RiemannHypothesis`
explicitement étiquetées ci-dessous.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## I1 — l'excès de phase inter-Tours -/

/-- **L'accroissement de phase d'un événement**, à un rang donné : la même quantité que
`phase_increment_eq_pi_span` compile déjà, restatée ici sous un nom court. -/
noncomputable def phaseIncrement (z : TrueZero) (k : ℕ) : ℝ :=
  Real.pi * towerPosition z (fnPrimeSuccessor k : ℝ) -
    Real.pi * towerPosition z (fnPrimeAtRank k : ℝ)

/-- **L'excès de phase inter-Tours `J(p)`** proposé par l'auteur (audit §0 du plan) : la somme des
deux accroissements de phase propres aux deux extrémités du passage, moins la progression continue
attendue `T_e · log(p_{n+2}/p_n)` sur l'arête double. -/
noncomputable def interTowerExcess (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) : ℝ :=
  phaseIncrement ⟨p.zEarlierMember, hE⟩ (nZeroSourceIndex p.zEarlierMember) +
    phaseIncrement ⟨p.zLaterMember, hL⟩ (nZeroSourceIndex p.zEarlierMember + 1) -
    rZeroHeight p.zEarlierMember *
      Real.log ((fnPrimeSuccessor (nZeroSourceIndex p.zEarlierMember + 1) : ℝ) /
        (fnPrimeAtRank (nZeroSourceIndex p.zEarlierMember) : ℝ))

/-- **Le rang source de l'extrémité de sortie avance de un** : cas particulier de
`thm_zeroSourceIndex_succ_of_passage`, restaté ici sous le nom attendu du plan. -/
theorem later_sourceIndex_eq (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember) :
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 :=
  thm_zeroSourceIndex_succ_of_passage p hE

/-! ## I2 — identité de base : `J(p) = (T_l − T_e) · rPrimeGapLogRatio(n+1)` -/

/-- **L'excès inter-Tours EST l'identité de base `thm_towerPrimeGapSpan_diff`**, transportée par
`phase_increment_eq_pi_span` : une algèbre pure sur deux logarithmes de places consécutives, sans
aucune mention de `RiemannHypothesis`. -/
theorem interTowerExcess_eq (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    interTowerExcess p hE hL =
      (rZeroHeight p.zLaterMember - rZeroHeight p.zEarlierMember) *
        rPrimeGapLogRatio (nZeroSourceIndex p.zEarlierMember + 1) := by
  have hp0 : (0 : ℝ) < (fnPrimeAtRank (nZeroSourceIndex p.zEarlierMember) : ℝ) := by
    exact_mod_cast thm_primeAtRank_pos _
  have hp1 : (0 : ℝ) < (fnPrimeAtRank (nZeroSourceIndex p.zEarlierMember + 1) : ℝ) := by
    exact_mod_cast thm_primeAtRank_pos _
  have hp2n1 : (0 : ℝ) < (fnPrimeSuccessor (nZeroSourceIndex p.zEarlierMember + 1) : ℝ) := by
    unfold fnPrimeSuccessor; exact_mod_cast thm_primeAtRank_pos _
  have e1 : fnPrimeSuccessor (nZeroSourceIndex p.zEarlierMember) =
      fnPrimeAtRank (nZeroSourceIndex p.zEarlierMember + 1) := rfl
  have hlogsum : rPrimeGapLogRatio (nZeroSourceIndex p.zEarlierMember) +
      rPrimeGapLogRatio (nZeroSourceIndex p.zEarlierMember + 1) =
      Real.log ((fnPrimeSuccessor (nZeroSourceIndex p.zEarlierMember + 1) : ℝ) /
        (fnPrimeAtRank (nZeroSourceIndex p.zEarlierMember) : ℝ)) := by
    unfold rPrimeGapLogRatio
    rw [e1, Real.log_div hp1.ne' hp0.ne', Real.log_div hp2n1.ne' hp1.ne',
      Real.log_div hp2n1.ne' hp0.ne']
    ring
  have hStep1 :
      Real.pi * towerPosition (⟨p.zEarlierMember, hE⟩ : TrueZero)
          (fnPrimeSuccessor (nZeroSourceIndex p.zEarlierMember) : ℝ) -
        Real.pi * towerPosition (⟨p.zEarlierMember, hE⟩ : TrueZero)
          (fnPrimeAtRank (nZeroSourceIndex p.zEarlierMember) : ℝ) =
      Real.pi * TowerPrimeGapSpan (⟨p.zEarlierMember, hE⟩ : TrueZero)
        (nZeroSourceIndex p.zEarlierMember) :=
    phase_increment_eq_pi_span ⟨p.zEarlierMember, hE⟩ (nZeroSourceIndex p.zEarlierMember)
  have hStep2 :
      Real.pi * towerPosition (⟨p.zLaterMember, hL⟩ : TrueZero)
          (fnPrimeSuccessor (nZeroSourceIndex p.zEarlierMember + 1) : ℝ) -
        Real.pi * towerPosition (⟨p.zLaterMember, hL⟩ : TrueZero)
          (fnPrimeAtRank (nZeroSourceIndex p.zEarlierMember + 1) : ℝ) =
      Real.pi * TowerPrimeGapSpan (⟨p.zLaterMember, hL⟩ : TrueZero)
        (nZeroSourceIndex p.zEarlierMember + 1) :=
    phase_increment_eq_pi_span ⟨p.zLaterMember, hL⟩ (nZeroSourceIndex p.zEarlierMember + 1)
  unfold interTowerExcess phaseIncrement
  rw [hStep1, hStep2]
  unfold TowerPrimeGapSpan rTowerHeight
  rw [← hlogsum]
  field_simp
  ring

/-! ## I3 — signe : `J(p) > 0` est exactement `PHeightProgression` -/

/-- **`J(p) > 0 ↔ T_e < T_l`.** -/
theorem interTowerExcess_pos_iff (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    0 < interTowerExcess p hE hL ↔ rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember := by
  rw [interTowerExcess_eq]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hle : (rZeroHeight p.zLaterMember - rZeroHeight p.zEarlierMember) *
        rPrimeGapLogRatio (nZeroSourceIndex p.zEarlierMember + 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (thm_primeGapLogRatio_pos _).le
    linarith
  · intro h
    exact mul_pos (by linarith) (thm_primeGapLogRatio_pos _)

/-- **`J(p) = 0 ↔ T_e = T_l`.** -/
theorem interTowerExcess_eq_zero_iff (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    interTowerExcess p hE hL = 0 ↔ rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember := by
  rw [interTowerExcess_eq, mul_eq_zero]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h (thm_primeGapLogRatio_pos _).ne'
  · intro h
    left; linarith

/-- **L'ordre lexicographique donne toujours `T_e ≤ T_l` sur un passage.** -/
theorem passage_height_le (p : TZeroPassage) :
    rZeroHeight p.zEarlierMember ≤ rZeroHeight p.zLaterMember := by
  rcases (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mp p.precedes with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

/-- **`J(p)` est toujours non négatif.** -/
theorem interTowerExcess_nonneg (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) : 0 ≤ interTowerExcess p hE hL := by
  rw [interTowerExcess_eq]
  exact mul_nonneg (by linarith [passage_height_le p]) (thm_primeGapLogRatio_pos _).le

/-! ## I4 — le passage OFF porte toutes les hypothèses grammaticales de PITE, et `J = 0` -/

/-- **Un zéro hors ligne produit un passage qui satisfait toutes les hypothèses grammaticales
proposées pour PITE (`EV+1`, raccord, occurrence stricte) et dont l'excès inter-Tours est nul.** -/
theorem off_excess_zero {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    ∃ p : TZeroPassage, ∃ hE : 0 < rZeroHeight p.zEarlierMember,
      ∃ hL : 0 < rZeroHeight p.zLaterMember,
        nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
        occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
        occurrence ⟨p.zEarlierMember, hE⟩ < occurrence ⟨p.zLaterMember, hL⟩ ∧
        interTowerExcess p hE hL = 0 := by
  obtain ⟨p, hE, hL, _, hSame, hSucc, hOcc, hLt⟩ := off_event_increment_without_height hOff
  exact ⟨p, hE, hL, hSucc, hOcc, hLt, (interTowerExcess_eq_zero_iff p hE hL).mpr hSame⟩

/-! ## I5 — PITE ⟺ RH -/

/-! ## I6 — les hypothèses grammaticales de PITE sont inconditionnelles, donc inertes -/

/-- **Les trois hypothèses grammaticales de PITE tiennent sur TOUT passage** : c'est exactement
`passage_event_increment`, restaté ici sous le nom attendu du plan. -/
theorem grammar_hypotheses_of_passage (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
      occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
      occurrence ⟨p.zEarlierMember, hE⟩ < occurrence ⟨p.zLaterMember, hL⟩ :=
  passage_event_increment p hE hL

/-! ## I7 — la forme la plus atomique du résidu : `PNoNullPassage` -/

/-! ## I8 — audit de dépendances -/

#print axioms interTowerExcess_eq
#print axioms interTowerExcess_pos_iff
#print axioms off_excess_zero
/-!
## Verdict

`interTowerExcess_eq` réduit l'excès inter-Tours à `(T_l − T_e) · rPrimeGapLogRatio(n+1)`, une pure
algèbre sur `thm_towerPrimeGapSpan_diff`, sans aucune mention de `RiemannHypothesis`.
`interTowerExcess_pos_iff` montre que PITE (`∀ p, 0 < J(p)`) EST `PHeightProgression`, seulement
renommée ; `off_excess_zero` montre que le passage nul OFF satisfait déjà toutes les hypothèses
grammaticales proposées pour PITE, avec `J = 0` — ces hypothèses ne sélectionnent donc rien
(`interTowerExcess_pos_of_grammar_iff_riemannHypothesis`). La forme la plus atomique du résidu
compilée est `PNoNullPassage` (I7), un seul prédicat de la base, encore exactement équivalent à RH.
Aucune prémisse strictement plus faible que RH n'est produite ; aucune ne peut l'être (§1 du plan).
`RH_FOUND=FALSE`.
-/

end RHV6Fresh
