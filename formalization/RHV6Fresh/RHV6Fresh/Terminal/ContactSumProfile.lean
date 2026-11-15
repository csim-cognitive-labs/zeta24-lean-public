/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.AmplitudeContact

/-!
# Somme des contacts le long d'un écart : profil, cassure, passage à l'écart suivant (§19.33, E404)

Module ISOLÉ (non ajouté à `RHV6Fresh.lean`). Canal lissé compilé seulement : le canal brut
(fonction de Tchebychev en escalier) n'est pas dans le corpus et reste un jumeau numérique d'E404.

Objet : pour un vrai écart `I = [p_n, p_{n+1}]`, la somme des contacts le long de l'axe réel est,
en chaque abscisse `x`, la somme sur tous les membres du dépôt lissé en `x` moins le dépôt au
début de l'écart.
- Au début de l'écart, le profil vaut zéro (`contactSumProfile_lower`).
- Au point de rencontre, il vaut exactement la demande de l'écart
  (`contactSumProfile_meetingPoint`) : c'est le sommet exact demandé par l'auteur, dans le canal
  lissé.
- Le profil de l'écart suivant repart de zéro à la rencontre (`contactSumProfile_next_at_meeting`)
  et n'est que le profil continué moins la demande déjà réalisée
  (`contactSumProfile_continuation`) : la « redescente » est une remise à zéro de l'origine, pas
  un retour de la somme elle-même.
- Chaque membre y entre avec une amplitude bornée par son poids fois les deux puissances radiales
  (`memberProfile_norm_le`).
Rien ici ne fixe la forme de la montée ni les fréquences qui la portent : E404 les mesure, ce
module ne les compile pas. Aucune conclusion sur la position radiale.
-/

namespace RHV6Fresh

open RHV3Lean

/-- Profil d'un membre le long de l'écart :
dépôt lissé en `x` moins dépôt au début de l'écart. -/
noncomputable def memberProfile (σ : ExplicitIndex) (I : PrimeGapInterval) (x : ℝ) : ℂ :=
  nontrivialZeroResidueTerm x σ - nontrivialZeroResidueTerm I.lower σ

theorem memberProfile_lower (σ : ExplicitIndex) (I : PrimeGapInterval) :
    memberProfile σ I I.lower = 0 := sub_self _

/-- Amplitude d'un membre le long de l'écart :
au plus son poids fois la somme des deux puissances radiales. -/
theorem memberProfile_norm_le (σ : ExplicitIndex) (I : PrimeGapInterval) {x : ℝ} (hx : 0 < x) :
    ‖memberProfile σ I x‖ ≤ indexWeight σ * (x ^ (σ : ℂ).re + I.lower ^ (σ : ℂ).re) := by
  unfold memberProfile
  calc ‖nontrivialZeroResidueTerm x σ - nontrivialZeroResidueTerm I.lower σ‖
      ≤ ‖nontrivialZeroResidueTerm x σ‖ + ‖nontrivialZeroResidueTerm I.lower σ‖ := norm_sub_le _ _
    _ = indexWeight σ * (x ^ (σ : ℂ).re + I.lower ^ (σ : ℂ).re) := by
      rw [norm_residueTerm_eq σ hx, norm_residueTerm_eq σ (zero_lt_one.trans I.one_lt_lower),
        mul_add]

/-- Somme des contacts le long de l'écart : somme sur tous les membres des profils. -/
noncomputable def contactSumProfile (I : PrimeGapInterval) (x : ℝ) : ℂ :=
  ∑' σ : ExplicitIndex, memberProfile σ I x

/-- Au début de l'écart la somme des contacts vaut zéro. -/
theorem contactSumProfile_lower (I : PrimeGapInterval) : contactSumProfile I I.lower = 0 := by
  unfold contactSumProfile
  simp [memberProfile_lower]

/-- Identité réelle : la somme des contacts en `x` est le reste lissé en `x`
moins le reste au début de l'écart. -/
theorem contactSumProfile_eq (I : PrimeGapInterval) {x : ℝ} (hx : 1 < x) :
    contactSumProfile I x = smoothedRemainder x - smoothedRemainder I.lower := by
  unfold contactSumProfile memberProfile
  rw [(nontrivial_zero_residue_series_summable hx).tsum_sub
      (nontrivial_zero_residue_series_summable I.one_lt_lower),
    smoothedRemainder_eq_tsum_residueTerm hx,
    smoothedRemainder_eq_tsum_residueTerm I.one_lt_lower]

/-- Sommet exact : au point de rencontre la somme des contacts est exactement
la demande de l'écart. -/
theorem contactSumProfile_meetingPoint (I : PrimeGapInterval) :
    contactSumProfile I (meetingPoint I) = localArithmeticTarget I := by
  rw [contactSumProfile_eq I (one_lt_meetingPoint I)]
  rfl

/-- L'écart suivant. -/
def PrimeGapInterval.next (I : PrimeGapInterval) : PrimeGapInterval := ⟨I.rank + 1⟩

theorem PrimeGapInterval.next_lower (I : PrimeGapInterval) : I.next.lower = meetingPoint I := rfl

/-- Passage à l'écart suivant : son profil repart de zéro au point de rencontre. -/
theorem contactSumProfile_next_at_meeting (I : PrimeGapInterval) :
    contactSumProfile I.next (meetingPoint I) = 0 :=
  contactSumProfile_lower I.next

/-- Sans remise à zéro : le profil de l'écart suivant est le profil continué de l'écart,
moins la demande déjà réalisée à la rencontre. La redescente est un changement d'origine,
pas un retour de la somme. -/
theorem contactSumProfile_continuation (I : PrimeGapInterval) {x : ℝ} (hx : 1 < x) :
    contactSumProfile I.next x = contactSumProfile I x - localArithmeticTarget I := by
  rw [contactSumProfile_eq I.next hx, contactSumProfile_eq I hx, PrimeGapInterval.next_lower]
  unfold localArithmeticTarget meetingPoint
  ring

/-- Deux écarts consécutifs lus en continu : la somme des deux demandes est le profil continué
au second point de rencontre. -/
theorem contactSumProfile_two_gaps (I : PrimeGapInterval) :
    contactSumProfile I (meetingPoint I.next) =
      localArithmeticTarget I + localArithmeticTarget I.next := by
  have h := contactSumProfile_continuation I (one_lt_meetingPoint I.next)
  rw [contactSumProfile_meetingPoint] at h
  linear_combination -h

end RHV6Fresh
