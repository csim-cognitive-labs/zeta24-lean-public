/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CanonicalTransition
import RHV6Fresh.Terminal.EngagedPersistence
import RHV6Fresh.Terminal.ZetaParameters
import RHV6Fresh.Terminal.NoRegimeChange

/-!
# RHV6Fresh — verdict compilé sur l'énoncé de clôture de l'auteur (2026-10-01)

Énoncé soumis, en trois phrases :

1. Le régime engagé est celui où le miroir est annulé : entre deux événements successifs, aucun
   mouvement radial n'apparaît et toute la progression restante est portée par la hauteur.
2. Changer de régime exige de créer un mouvement radial entre deux événements successifs ; cette
   création est exactement la signature du passage vers le régime hors ligne.
3. La clôture consiste à établir que la succession canonique conserve la nature du mouvement du
   régime engagé : tant que le miroir reste annulé, la progression reste verticale, le régime ne
   change pas et chaque zéro suivant reste sur la ligne.

Verdict :

* Phrase 1 : VRAIE. Miroir annulé ⟺ en ligne (`mirror_annulled_iff_onLine`) ; un passage entre deux
  membres au miroir annulé n'a aucun mouvement radial et il est vertical (`engaged_passage_height_only`).
* Phrase 2 : VRAIE. Sur tout passage, mouvement radial ⟺ un membre hors ligne
  (`radial_motion_iff_off`) ; tout changement de régime à une jonction crée un mouvement radial sur le
  passage qui arrive, et le membre de jonction est hors ligne (`regime_change_creates_radial_motion`).
* Phrase 3 (portée corrigée, voir la dernière section) : la cible est locale, « depuis l'état engagé le
  régime ne change pas » ; sur un pas vertical elle est exactement « l'arrivée reste en ligne »
  (`vertical_arrival_onLine_iff_no_regime_change`) ; la loi locale n'est pas RH, elle ne la donne qu'avec
  l'amorce (`conservation_leaves_only_base`). Elle n'est pas encore démontrée. RH équivaut à la loi
  de conservation « départ au miroir annulé ⟹ arrivée au miroir annulé », jointe à l'amorce « les
  membres sans prédécesseur sont en ligne » (`riemannHypothesis_iff_conservation_and_base`). La loi
  n'est pas dérivée ; elle n'est pas une conséquence du miroir, de la conjugaison ni de la réalité sur
  la ligne : le monde témoin les vérifie toutes et la viole sur deux membres consécutifs
  (`conservation_not_structural`). Elle doit lire ce que le témoin n'a pas : les premiers et leurs
  poids exacts.

Aucune prémisse n'est posée : la loi de conservation figure seulement comme membre d'une équivalence.
`PNoRegimeChange` n'est pas utilisée. Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## Phrase 1 -/

/-- **Miroir annulé ⟺ en ligne.** -/
theorem mirror_annulled_iff_onLine (z : TrueZero) :
    mirrorMember z = z ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro h
    have hr := mirrorMember_radial z
    rw [h] at hr
    linarith
  · exact mirrorMember_eq_self_of_onLine

/-- **Passage entre deux membres au miroir annulé** : aucun mouvement radial, passage vertical
(toute la progression est portée par la hauteur). -/
theorem engaged_passage_height_only (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (he : mirrorMember ⟨p.zEarlierMember, hE⟩ = ⟨p.zEarlierMember, hE⟩)
    (hl : mirrorMember ⟨p.zLaterMember, hL⟩ = ⟨p.zLaterMember, hL⟩) :
    rZeroRadialPosition p.zLaterMember - rZeroRadialPosition p.zEarlierMember = 0 ∧
      VerticalPassage p := by
  have he' := (mirror_annulled_iff_onLine _).mp he
  have hl' := (mirror_annulled_iff_onLine _).mp hl
  exact ⟨by simp only at he' hl'; rw [he', hl']; ring, onLine_passage_vertical p he' hl'⟩

/-! ## Phrase 2 -/

/-- **Mouvement radial ⟺ un membre hors ligne**, sur tout passage. -/
theorem radial_motion_iff_off (p : TZeroPassage) :
    rZeroRadialPosition p.zEarlierMember ≠ rZeroRadialPosition p.zLaterMember ↔
      (PIsOffCriticalLine p.zEarlierMember ∨ PIsOffCriticalLine p.zLaterMember) := by
  constructor
  · intro h
    by_contra hno
    push Not at hno
    obtain ⟨he, hl⟩ := hno
    exact h ((not_ne_iff.mp he).trans (not_ne_iff.mp hl).symm)
  · intro hOff
    rcases passage_regime_dichotomy p with ⟨hV, _⟩ | ⟨hH, _⟩
    · intro heq
      have h1 := passage_exit_radial_ge_half p hV
      have h2 := passage_entry_radial_le_half p hV
      rcases hOff with h | h
      · exact h (by linarith)
      · exact h (by linarith)
    · exact ne_of_lt (horizontalPassage_radial_lt hH)

/-- **Changer de régime crée un mouvement radial** sur le passage qui arrive à la jonction, et le
membre de jonction est hors ligne. -/
theorem regime_change_creates_radial_motion {p q : TZeroPassage}
    (hJ : p.zLaterMember = q.zEarlierMember)
    (h : (VerticalPassage p ∧ HorizontalPassage q) ∨ (HorizontalPassage p ∧ VerticalPassage q)) :
    rZeroRadialPosition p.zEarlierMember ≠ rZeroRadialPosition p.zLaterMember ∧
      PIsOffCriticalLine p.zLaterMember := by
  have hOff := regimeChange_offLine hJ h
  exact ⟨(radial_motion_iff_off p).mpr (Or.inr hOff), hOff⟩

/-! ## Phrase 3 -/

/-- **La clôture équivaut exactement à la loi de conservation jointe à l'amorce.** Loi : tout passage
parti d'un membre au miroir annulé arrive sur un membre au miroir annulé. Amorce : tout membre sans
prédécesseur est en ligne. Équivalence, aucune des deux n'est dérivée ici. -/
theorem riemannHypothesis_iff_conservation_and_base :
    RiemannHypothesis ↔
      ((∀ p : TZeroPassage, rZeroRadialPosition p.zEarlierMember = 1 / 2 →
          rZeroRadialPosition p.zLaterMember = 1 / 2) ∧
        (∀ z : TrueZero, sUpperZerosBelow z.1 = ∅ → rZeroRadialPosition z.1 = 1 / 2)) := by
  constructor
  · intro hRH
    exact ⟨fun p _ => thm_zeroRadialPosition_half_of_riemannHypothesis hRH _,
      fun z _ => thm_zeroRadialPosition_half_of_riemannHypothesis hRH _⟩
  · rintro ⟨hLaw, hBase⟩
    have key : ∀ n : ℕ, ∀ z : TrueZero, nZeroSourceIndex z.1 = n →
        rZeroRadialPosition z.1 = 1 / 2 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro z hn
        by_cases hemp : sUpperZerosBelow z.1 = ∅
        · exact hBase z hemp
        · obtain ⟨w, hw, hcons, hidx⟩ :=
            exists_consecutive_predecessor z.1 (Set.nonempty_iff_ne_empty.mpr hemp)
          have hwOn : rZeroRadialPosition w = 1 / 2 :=
            ih (nZeroSourceIndex w) (hn ▸ hidx) ⟨w, hw⟩ rfl
          exact hLaw ⟨w, z.1, hcons⟩ hwOn
    exact riemannHypothesis_of_noOff fun z hOff => hOff (key _ z rfl)

/-- **La loi de conservation n'est pas structurelle.** Le témoin a le miroir de zêta, commute à la
conjugaison et est réel sur la ligne ; il a un zéro en ligne seul à la hauteur `1`, aucun zéro entre
les hauteurs `1` et `2`, puis deux jumeaux hors ligne à la hauteur `2` : sur deux membres consécutifs,
le départ a le miroir annulé et l'arrivée ne l'a pas. -/
theorem conservation_not_structural :
    (∀ s : ℂ, regimeWitness (1 - s) = regimeWitness s) ∧
    (∀ s : ℂ, regimeWitness ((starRingEnd ℂ) s) = (starRingEnd ℂ) (regimeWitness s)) ∧
    (∀ t : ℝ, (regimeWitness ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).im = 0) ∧
    regimeWitness (1 / 2 + Complex.I) = 0 ∧
    (∀ s : ℂ, regimeWitness s = 0 → s.im = 1 → s = 1 / 2 + Complex.I) ∧
    (∀ s : ℂ, regimeWitness s = 0 → ¬ (1 < s.im ∧ s.im < 2)) ∧
    regimeWitness (1 / 4 + 2 * Complex.I) = 0 ∧
    (1 / 4 + 2 * Complex.I : ℂ).re ≠ 1 / 2 := by
  obtain ⟨h1, h2, h3, h4, _⟩ := regimeWitness_regime_changes
  refine ⟨regimeWitness_mirror, regimeWitness_conj, regimeWitness_real_onLine, h1, h2, h3, h4, ?_⟩
  norm_num

#print axioms mirror_annulled_iff_onLine
#print axioms engaged_passage_height_only
#print axioms radial_motion_iff_off
#print axioms regime_change_creates_radial_motion
#print axioms riemannHypothesis_iff_conservation_and_base
#print axioms conservation_not_structural

/-! ## Phrase 3, correction de portée (auteur, 2026-10-01) : la loi locale n'est pas RH

La cible de l'auteur est locale : depuis l'état engagé, le régime ne change pas. Sur un pas vertical,
cette cible est exactement « l'arrivée reste en ligne » ; la loi locale qui la porte sur tout passage ne
donne RH qu'avec l'amorce. Seule la forme globale `PNoRegimeChange` (aucun changement de régime à aucune
jonction, y compris celles qui ne partent pas de la ligne) est équivalente à RH
(`noRegimeChange_iff_riemannHypothesis`). -/

/-- **Sur un pas vertical, l'arrivée reste en ligne ⟺ aucun changement de régime à l'arrivée.** -/
theorem vertical_arrival_onLine_iff_no_regime_change (p : TZeroPassage)
    (hL : 0 < rZeroHeight p.zLaterMember) (hV : VerticalPassage p) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ↔
      ∀ q : TZeroPassage, p.zLaterMember = q.zEarlierMember → ¬ HorizontalPassage q := by
  rw [← arrival_radial_le_one_iff_regime_kept p hL hV]
  constructor
  · intro h
    by_contra hr
    have hlt := (radialFactor_gt_one_iff ⟨p.zLaterMember, hL⟩).mp (not_le.mp hr)
    change rZeroRadialPosition p.zLaterMember < 1 / 2 at hlt
    linarith
  · intro hr
    have hle := passage_entry_radial_le_half p hV
    by_contra hne
    have hlt : rZeroRadialPosition (⟨p.zLaterMember, hL⟩ : TrueZero).1 < 1 / 2 :=
      lt_of_le_of_ne hle hne
    exact absurd ((radialFactor_gt_one_iff ⟨p.zLaterMember, hL⟩).mpr hlt) (not_lt.mpr hr)

/-- **La loi locale ne contient pas RH à elle seule** : sous la loi « départ en ligne ⟹ arrivée en
ligne », RH équivaut à la seule amorce (les membres sans prédécesseur sont en ligne). -/
theorem conservation_leaves_only_base
    (hLaw : ∀ p : TZeroPassage, rZeroRadialPosition p.zEarlierMember = 1 / 2 →
      rZeroRadialPosition p.zLaterMember = 1 / 2) :
    RiemannHypothesis ↔
      ∀ z : TrueZero, sUpperZerosBelow z.1 = ∅ → rZeroRadialPosition z.1 = 1 / 2 :=
  ⟨fun h => (riemannHypothesis_iff_conservation_and_base.mp h).2,
    fun hb => riemannHypothesis_iff_conservation_and_base.mpr ⟨hLaw, hb⟩⟩

#print axioms vertical_arrival_onLine_iff_no_regime_change
#print axioms conservation_leaves_only_base

end RHV6Fresh
