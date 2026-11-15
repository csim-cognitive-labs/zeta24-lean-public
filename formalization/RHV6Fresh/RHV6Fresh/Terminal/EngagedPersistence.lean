/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.LinkedProduction

/-!
# RHV6Fresh — le régime engagé perdure : l'argument de l'auteur, maillon par maillon (2026-09-30)

Énoncé de l'auteur : « ce que tu dois prouver, ce n'est pas qu'un hors-ligne est impossible, mais
que rien ne peut changer le régime engagé, car seule la position radiale a changé ce régime et elle
n'est plus disponible : elle est fixée à 1/2 dans un régime où rien ne change. Il n'y a aucun autre
déclencheur que la hauteur qui évolue. Donc aucun changement : le régime en ligne perdure jusqu'à
l'infini. Ce n'est pas une question de hors-ligne. »

Aucun énoncé de ce fichier ne pose un membre hors ligne. L'argument est transcrit en quatre
maillons :

* **M1 — seule la position radiale change le régime** (`regime_change_requires_radial`) : à une
  jonction dont le membre est en ligne, aucun changement de régime, dans aucun sens. Théorème.
* **M2 — dans l'état engagé la position radiale est fixée** (`EngagedState`, déjà compilé) : tout
  ce que porte le membre est déterminé par sa hauteur. Théorème.
* **M3 — si seule la hauteur évolue sur le passage, le régime est transmis**
  (`heightOnly_step`) : le membre d'arrivée est engagé et tout passage qui en part est vertical.
  Théorème.
* **M4 — le régime perdure jusqu'à l'infini** (`engaged_persists_to_infinity`) : sous la loi
  « sur un passage vertical parti de la ligne, seule la hauteur évolue », tout membre au-dessus
  d'un membre engagé est engagé, atteint verticalement et quitté verticalement. Théorème, par
  récurrence sur le rang.

Borne : la loi de M4 (« seule la hauteur évolue ») est une hypothèse du théorème, elle n'est pas
dérivée. Elle est nécessaire (`heightOnly_of_riemannHypothesis`). Les lois compilées donnent sur
ce passage `Δβ ≤ 0` (`engaged_progression`), pas `Δβ = 0`.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune `def` de prémisse.
-/

namespace RHV6Fresh

open RHV3Lean Set

/-- **M1. Seule la position radiale change le régime.** À une jonction dont le membre est en
ligne, le régime ne change dans aucun sens. -/
theorem regime_change_requires_radial {p q : TZeroPassage}
    (hJ : p.zLaterMember = q.zEarlierMember)
    (hOn : rZeroRadialPosition p.zLaterMember = 1 / 2) :
    ¬ ((VerticalPassage p ∧ HorizontalPassage q) ∨ (HorizontalPassage p ∧ VerticalPassage q)) :=
  fun h => regimeChange_offLine hJ h hOn

/-- **M3. Si seule la hauteur évolue, le régime est transmis.** Un passage vertical `o` arrive sur
un membre en ligne ; `p` en part. Si la position radiale n'évolue pas sur `p`, alors `p` est
vertical, le membre d'arrivée est engagé et tout passage qui en part est vertical. -/
theorem heightOnly_step {o p : TZeroPassage} (hJ : o.zLaterMember = p.zEarlierMember)
    (ho : VerticalPassage o) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hL : 0 < rZeroHeight p.zLaterMember)
    (hOnly : rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember) :
    VerticalPassage p ∧ EngagedState ⟨p.zLaterMember, hL⟩ ∧
      ∀ q : TZeroPassage, p.zLaterMember = q.zEarlierMember →
        VerticalPassage q ∧ ¬ HorizontalPassage q := by
  have hOnO : rZeroRadialPosition o.zLaterMember = 1 / 2 := by rw [hJ]; exact hOn
  have hV := (engaged_regime_kept hJ ho hOnO).1
  have hOnL : rZeroRadialPosition p.zLaterMember = 1 / 2 := hOnly.trans hOn
  exact ⟨hV, (engagedState_iff_onLine ⟨p.zLaterMember, hL⟩).mpr hOnL,
    fun q hq => engaged_regime_kept hq hV hOnL⟩

/-- **M4. Le régime engagé perdure jusqu'à l'infini**, sous la loi « sur un passage vertical parti
de la ligne, seule la hauteur évolue » (`hOnly`, hypothèse). Un passage vertical `o` arrive sur un
membre en ligne. Alors tout membre au-dessus est en ligne, atteint par un passage vertical, et
tout passage qui en part est vertical. -/
theorem engaged_persists_to_infinity
    (hOnly : ∀ p : TZeroPassage, VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember)
    {o : TZeroPassage} (hE : 0 < rZeroHeight o.zLaterMember) (ho : VerticalPassage o)
    (hOn : rZeroRadialPosition o.zLaterMember = 1 / 2) :
    ∀ w : TNonTrivialZetaZero, PZeroMemberPrecedes o.zLaterMember w →
      rZeroRadialPosition w = 1 / 2 ∧
      (∃ q : TZeroPassage, q.zLaterMember = w ∧ VerticalPassage q) ∧
      (∀ q : TZeroPassage, q.zEarlierMember = w → VerticalPassage q ∧ ¬ HorizontalPassage q) := by
  have key : ∀ n : ℕ, ∀ w : TNonTrivialZetaZero, nZeroSourceIndex w = n →
      PZeroMemberPrecedes o.zLaterMember w →
      rZeroRadialPosition w = 1 / 2 ∧
        ∃ q : TZeroPassage, q.zLaterMember = w ∧ VerticalPassage q := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hn hew
      obtain ⟨m, _, hcons, hidx⟩ := exists_consecutive_predecessor w ⟨o.zLaterMember, hE, hew⟩
      let q : TZeroPassage := ⟨m, w, hcons⟩
      by_cases hme : m = o.zLaterMember
      · have hOnm : rZeroRadialPosition q.zEarlierMember = 1 / 2 := by
          change rZeroRadialPosition m = 1 / 2
          rw [hme]; exact hOn
        have hVq : VerticalPassage q :=
          (engaged_regime_kept (p := o) (q := q) hme.symm ho hOn).1
        exact ⟨(hOnly q hVq hOnm).trans hOnm, q, rfl, hVq⟩
      · have hem : PZeroMemberPrecedes o.zLaterMember m := by
          rcases thm_distinctZeroMembers_comparable hme with h | h
          · exact absurd ⟨o.zLaterMember, h, hew⟩ hcons.2
          · exact h
        obtain ⟨hOnm, q', hq', hVq'⟩ :=
          ih (nZeroSourceIndex m) (by rw [← hn]; exact hidx) m rfl hem
        have hOnq' : rZeroRadialPosition q'.zLaterMember = 1 / 2 := by rw [hq']; exact hOnm
        have hVq : VerticalPassage q :=
          (engaged_regime_kept (p := q') (q := q) hq' hVq' hOnq').1
        exact ⟨(hOnly q hVq hOnm).trans hOnm, q, rfl, hVq⟩
  intro w hew
  obtain ⟨hOnw, q, hq, hVq⟩ := key (nZeroSourceIndex w) w rfl hew
  refine ⟨hOnw, ⟨q, hq, hVq⟩, fun q' hq' => ?_⟩
  have hOnq : rZeroRadialPosition q.zLaterMember = 1 / 2 := by rw [hq]; exact hOnw
  exact engaged_regime_kept (hq.trans hq'.symm) hVq hOnq

/-- **Borne.** La loi « seule la hauteur évolue sur un passage vertical parti de la ligne » est
nécessaire : elle est vraie sous l'hypothèse de Riemann. -/
theorem heightOnly_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ p : TZeroPassage, VerticalPassage p →
      rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember :=
  fun _ _ _ => (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _).trans
    (thm_zeroRadialPosition_half_of_riemannHypothesis hRH _).symm

#print axioms regime_change_requires_radial
#print axioms heightOnly_step
#print axioms engaged_persists_to_infinity
#print axioms heightOnly_of_riemannHypothesis

end RHV6Fresh
