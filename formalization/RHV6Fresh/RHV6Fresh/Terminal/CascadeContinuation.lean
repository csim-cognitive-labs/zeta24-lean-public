/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.InterlacingLink
import RHV6Fresh.Terminal.RegimeTrigger
import RHV6Fresh.Voyage.FiberSuccessor

/-!
# Continuation de la cascade : la rupture vue au pas suivant (auteur, 2026-10-19, vingt-troisième message)

Texte collé : une rupture horizontale (zéro précédent sur la ligne, suivant hors ligne) affecterait toute la cascade ; la
contradiction à établir est globale ; identifier une propriété de cohérence déjà prouvée pour l'ensemble authentique que
violerait une première arrivée hors ligne.

Compilé ici, axiomes standard, sur les passages réels (aucun zéro fabriqué, aucune normalisation) :
* lecture de la continuation par l'entrelacement : les décalages `δ_k` du pas suivant `l → s` décroissent strictement ⟺ ce
  pas monte (`cascade_step_rises_iff`) ;
* depuis un membre ON atteint en montant, la cascade continue à tout indice (`engaged_cascade_continues`, par
  `engaged_regime_kept`) : c'est la propriété de cohérence de l'ensemble engagé ;
* une première arrivée sous un demi GÈLE la cascade au pas suivant : tout passage qui la quitte garde la hauteur, ses
  décalages sont constants, la lecture de fréquence donne zéro (`low_arrival_freezes_cascade`), et un tel passage existe
  (`low_arrival_outgoing_exists`, par le successeur de fibre) ; la fréquence NE continue PAS de progresser ;
* fermeture : un pas suivant qui continue la cascade à un indice donne la condition réduite (`cascade_continuation_closes`) ;
  équivalence exacte sous un départ ON (`cascade_continuation_iff`).
Portée : réécriture exacte de la condition dans la langue de la cascade (flèche de référence de l'auteur : le passage qui
quitte le membre atteint doit lui aussi monter) ; ni plus faible ni plus forte que la condition ; quantifiée, force de RH.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **La continuation de la cascade est lue par l'entrelacement** : sur un pas `q`, les décalages décroissent strictement à
un indice ⟺ le pas monte. -/
theorem cascade_step_rises_iff (q : TZeroPassage) (hE : 0 < rZeroHeight q.zEarlierMember)
    (hL : 0 < rZeroHeight q.zLaterMember) (k : ℤ) :
    interlacingOffset ⟨q.zEarlierMember, hE⟩ ⟨q.zLaterMember, hL⟩ (k + 1) <
        interlacingOffset ⟨q.zEarlierMember, hE⟩ ⟨q.zLaterMember, hL⟩ k ↔ VerticalPassage q := by
  have hR := interlacing_frequency_reading ⟨q.zEarlierMember, hE⟩ ⟨q.zLaterMember, hL⟩ k
  simp only at hR
  unfold VerticalPassage
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    have : Real.pi / rZeroHeight q.zEarlierMember ≤ Real.pi / rZeroHeight q.zLaterMember :=
      div_le_div_of_nonneg_left Real.pi_pos.le hL hle
    linarith
  · intro h
    have : Real.pi / rZeroHeight q.zLaterMember < Real.pi / rZeroHeight q.zEarlierMember :=
      div_lt_div_of_pos_left Real.pi_pos hE h
    linarith

/-- **Cohérence de l'ensemble engagé** : depuis un membre ON atteint en montant, le pas suivant continue la cascade à tout
indice. -/
theorem engaged_cascade_continues {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hp : VerticalPassage p) (hOn : rZeroRadialPosition p.zLaterMember = 1 / 2)
    (hE : 0 < rZeroHeight q.zEarlierMember) (hL : 0 < rZeroHeight q.zLaterMember) (k : ℤ) :
    interlacingOffset ⟨q.zEarlierMember, hE⟩ ⟨q.zLaterMember, hL⟩ (k + 1) <
      interlacingOffset ⟨q.zEarlierMember, hE⟩ ⟨q.zLaterMember, hL⟩ k :=
  (cascade_step_rises_iff q hE hL k).mpr (engaged_regime_kept hJ hp hOn).1

/-- **Une première arrivée sous un demi gèle la cascade** : tout pas qui la quitte garde la hauteur ; ses décalages sont
constants (lecture de fréquence nulle). -/
theorem low_arrival_freezes_cascade {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hp : VerticalPassage p) (hβ : rZeroRadialPosition p.zLaterMember < 1 / 2)
    (hE : 0 < rZeroHeight q.zEarlierMember) (hL : 0 < rZeroHeight q.zLaterMember) :
    HorizontalPassage q ∧ ∀ k : ℤ,
      interlacingOffset ⟨q.zEarlierMember, hE⟩ ⟨q.zLaterMember, hL⟩ (k + 1) =
        interlacingOffset ⟨q.zEarlierMember, hE⟩ ⟨q.zLaterMember, hL⟩ k := by
  have hH : HorizontalPassage q := by
    rcases passage_regime_dichotomy q with ⟨hV, _⟩ | ⟨hH, _⟩
    · exact absurd (junction_vertical_vertical hJ hp hV) (ne_of_lt hβ)
    · exact hH
  refine ⟨hH, fun k => ?_⟩
  have hR := interlacing_frequency_reading ⟨q.zEarlierMember, hE⟩ ⟨q.zLaterMember, hL⟩ k
  simp only at hR
  unfold HorizontalPassage at hH
  rw [hH] at hR
  linarith

/-- Le pas qui quitte une arrivée sous un demi existe (successeur de fibre, même hauteur). -/
theorem low_arrival_outgoing_exists (l : TrueZero) (hβ : rZeroRadialPosition l.1 < 1 / 2) :
    ∃ q : TZeroPassage, q.zEarlierMember = l.1 ∧ HorizontalPassage q ∧ 0 < rZeroHeight q.zLaterMember := by
  obtain ⟨s, hT, hC⟩ := exists_fiberSuccessor hβ
  exact ⟨⟨l.1, s.1, hC⟩, rfl, hT.symm, s.2⟩

/-- **Fermeture par la continuation** : si un pas qui quitte l'arrivée continue la cascade à un indice, la condition réduite
est satisfaite. -/
theorem cascade_continuation_closes (p : TZeroPassage) (hV : VerticalPassage p)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (q : TZeroPassage) (hJ : p.zLaterMember = q.zEarlierMember) (hLq : 0 < rZeroHeight q.zLaterMember) (k : ℤ)
    (h : interlacingOffset ⟨q.zEarlierMember, hJ ▸ hL⟩ ⟨q.zLaterMember, hLq⟩ (k + 1) <
      interlacingOffset ⟨q.zEarlierMember, hJ ▸ hL⟩ ⟨q.zLaterMember, hLq⟩ k) :
    ∃ k : ℤ, radialShiftAt ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ k ≤ 0 :=
  (one_sided_iff_onLine p hV hE hL hOn).mpr
    (junction_vertical_vertical hJ hV ((cascade_step_rises_iff q _ hLq k).mp h))

/-- **Équivalence exacte sous un départ ON** : la condition réduite ⟺ tout pas qui quitte l'arrivée continue la cascade à
tout indice. -/
theorem cascade_continuation_iff (p : TZeroPassage) (hV : VerticalPassage p)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    (∃ k : ℤ, radialShiftAt ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ k ≤ 0) ↔
      ∀ q : TZeroPassage, ∀ hJ : p.zLaterMember = q.zEarlierMember, ∀ hLq : 0 < rZeroHeight q.zLaterMember,
        ∀ k : ℤ, interlacingOffset ⟨q.zEarlierMember, hJ ▸ hL⟩ ⟨q.zLaterMember, hLq⟩ (k + 1) <
          interlacingOffset ⟨q.zEarlierMember, hJ ▸ hL⟩ ⟨q.zLaterMember, hLq⟩ k := by
  rw [one_sided_iff_onLine p hV hE hL hOn]
  constructor
  · intro hOnL q hJ hLq k
    exact engaged_cascade_continues hJ hV hOnL _ hLq k
  · intro hAll
    rcases (passage_entry_radial_le_half p hV).lt_or_eq with hlt | heq
    · exfalso
      obtain ⟨q, hq, hH, hLq⟩ := low_arrival_outgoing_exists ⟨p.zLaterMember, hL⟩ hlt
      have hJ : p.zLaterMember = q.zEarlierMember := hq.symm
      have hS := hAll q hJ hLq 0
      have hF := (low_arrival_freezes_cascade hJ hV hlt (hJ ▸ hL) hLq).2 0
      linarith
    · exact heq

end RHV6Fresh

#print axioms RHV6Fresh.cascade_step_rises_iff
#print axioms RHV6Fresh.low_arrival_freezes_cascade
#print axioms RHV6Fresh.cascade_continuation_iff
