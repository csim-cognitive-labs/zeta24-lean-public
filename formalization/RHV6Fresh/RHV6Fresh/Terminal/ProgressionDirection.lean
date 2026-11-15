/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.InterTowerExcess
import RHV6Fresh.Terminal.SuccessionInvariants
import RHV3Lean.Objects.ZetaSmoothedExplicitFormulaP4_6
import RHV3Lean.Objects.ZetaPerronFiniteResidues

/-!
# `Terminal/ProgressionDirection.lean` — sens de progression et somme des Tours (auteur, 2026-09-29)

Demande de l'auteur : « la somme de la formule explicite va vers l'infini : le sens de progression
est acquis, le zéro suivant est supérieur ou égal au précédent et `EV = EV + 1` ; créer le théorème
rigidifiant tout cela ».

* **D1 (rigidification du sens)** : sur tout passage, la place avance d'exactement un, la hauteur ne
  recule jamais, l'occurrence avance strictement, le suivant pointe le minimum attendu du précédent,
  et les minimums attendus avancent strictement. Tout est compilé, sans hypothèse.
* **D2 (ce que porte la somme)** : la somme de la formule explicite est indexée par TOUS les zéros non
  triviaux, fermée par conjugaison (hauteurs `T` et `−T`), et une `tsum` ne dépend d'aucun ordre de
  sommation. Le sens de progression de D1 vient de l'ordre des membres de la base, pas de la somme.
-/

namespace RHV6Fresh
open RHV3Lean
open scoped ComplexConjugate

/-! ## D1 — le sens de progression, rigidifié -/

/-- **Sens de progression rigidifié.** Sur tout passage `e → l` : `n_l = n_e + 1` (EV + 1),
`T_e ≤ T_l` (le suivant n'est jamais plus bas), `Occ(e) < Occ(l)`, `Occ(l) = p_min(e)`,
`p_min(l) = p_{n_e+2}` et `p_min(e) < p_min(l)`. -/
theorem passage_direction_rigid (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
      rZeroHeight p.zEarlierMember ≤ rZeroHeight p.zLaterMember ∧
      occurrence ⟨p.zEarlierMember, hE⟩ < occurrence ⟨p.zLaterMember, hL⟩ ∧
      occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
      expectedMinimumPrime ⟨p.zLaterMember, hL⟩ =
        fnPrimeAtRank (nZeroSourceIndex p.zEarlierMember + 2) ∧
      expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ < expectedMinimumPrime ⟨p.zLaterMember, hL⟩ := by
  obtain ⟨hSucc, hOcc, hLt⟩ := passage_event_increment p hE hL
  obtain ⟨_, _, hPmin⟩ := passage_raccords p hE hL
  exact ⟨hSucc, passage_height_le p, hLt, hOcc, hPmin,
    expectedMinimumPrime_succ_of_passage p hE hL⟩

/-! ## D2 — ce que la somme de la formule explicite porte, et ce qu'elle ne porte pas -/

/-- La conjugaison est une involution de l'ensemble des zéros non triviaux, indice de la somme. -/
noncomputable def nontrivialZeroConj :
    {ρ : ℂ // IsNontrivialZetaZero ρ} ≃ {ρ : ℂ // IsNontrivialZetaZero ρ} where
  toFun ρ := ⟨conj (ρ : ℂ), (isNontrivialZetaZero_conj_iff _).mpr ρ.2⟩
  invFun ρ := ⟨conj (ρ : ℂ), (isNontrivialZetaZero_conj_iff _).mpr ρ.2⟩
  left_inv ρ := Subtype.ext (by simp)
  right_inv ρ := Subtype.ext (by simp)

/-- **D2a.** L'indice de la somme contient, avec chaque zéro de hauteur `T`, le zéro de hauteur
`−T` : la somme parcourt les deux demi-plans. -/
theorem explicitSum_index_has_opposite_height (ρ : {ρ : ℂ // IsNontrivialZetaZero ρ}) :
    ∃ σ : {ρ : ℂ // IsNontrivialZetaZero ρ}, (σ : ℂ).im = -(ρ : ℂ).im ∧ (σ : ℂ).re = (ρ : ℂ).re :=
  ⟨nontrivialZeroConj ρ, by simp [nontrivialZeroConj], by simp [nontrivialZeroConj]⟩

/-- **D2b.** La somme des contributions de la formule explicite est invariante par toute
réindexation des zéros : elle ne porte aucun ordre de sommation, donc aucun sens de progression. -/
theorem explicitSum_reindex_invariant (x : ℝ)
    (e : {ρ : ℂ // IsNontrivialZetaZero ρ} ≃ {ρ : ℂ // IsNontrivialZetaZero ρ}) :
    (∑' ρ, nontrivialZeroResidueTerm x (e ρ)) = ∑' ρ, nontrivialZeroResidueTerm x ρ :=
  e.tsum_eq (nontrivialZeroResidueTerm x)

/-- **D2c.** En particulier, la somme est inchangée si l'on échange chaque zéro avec son conjugué
(hauteur `T` ↔ `−T`). -/
theorem explicitSum_conj_invariant (x : ℝ) :
    (∑' ρ, nontrivialZeroResidueTerm x (nontrivialZeroConj ρ)) =
      ∑' ρ, nontrivialZeroResidueTerm x ρ :=
  explicitSum_reindex_invariant x nontrivialZeroConj

end RHV6Fresh

#print axioms RHV6Fresh.passage_direction_rigid
#print axioms RHV6Fresh.explicitSum_index_has_opposite_height
#print axioms RHV6Fresh.explicitSum_conj_invariant
