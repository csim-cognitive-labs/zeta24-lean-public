/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.CleanTerminal

/-!
# RHV6Fresh — expected minimum prime

This is the arithmetic branch of the terminal comparison.  It depends on the
ordered zero history and not on any tower contact or prime readout.
-/

namespace RHV6Fresh

open RHV3Lean

noncomputable def expectedMinimumPrime (z : TrueZero) : ℕ :=
  fnPrimeSuccessor (nZeroSourceIndex z.1)

theorem expectedMinimumPrime_prime (z : TrueZero) :
    Nat.Prime (expectedMinimumPrime z) := by
  unfold expectedMinimumPrime fnPrimeSuccessor
  exact thm_primeAtRank_isPrime _

theorem occurrence_lt_expectedMinimumPrime (z : TrueZero) :
    occurrence z < expectedMinimumPrime z := by
  rw [occurrence_eq_canonicalAnchor]
  unfold nMemberCanonicalAnchor expectedMinimumPrime fnPrimeSuccessor
  exact thm_primeAtRank_lt_successor _

theorem expectedMinimumPrime_eq_laterOccurrence
    (p : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight p.zEarlierMember)
    (hLaterUpper : 0 < rZeroHeight p.zLaterMember) :
    expectedMinimumPrime ⟨p.zEarlierMember, hEarlierUpper⟩ =
      occurrence ⟨p.zLaterMember, hLaterUpper⟩ := by
  unfold expectedMinimumPrime
  exact (occurrence_successor_of_passage p hEarlierUpper hLaterUpper).symm

/-- **Injectivité du pointeur `pmin` (auteur, 2026-09-27).**  `expectedMinimumPrime`
n'est rien d'autre que `fnPrimeAtRank (nZeroSourceIndex z.1 + 1)` : deux zéros
distincts (branche supérieure) pointent donc toujours sur deux premiers distincts.
Aucune nouvelle prémisse : conséquence directe de `thm_zeroSourceIndex_injective`
(l'index zéro-source détermine le membre, `MemberZeroSourceOccurrence.lean`) et de
`thm_primeAtRank_injective` (l'énumération des premiers est injective,
`PrimeGapGrammar.lean`). C'est la forme précise, déjà établie, de « un et un seul
zéro pointe sur un et un seul premier » : un fait sur la fonction `pmin`
elle-même, pas sur le contenu de la cellule géométrique qu'elle désigne (voir
`vonmangoldt_chebyshev_rank_identity_published.py`, E089, pour cette distinction). -/
theorem expectedMinimumPrime_injective {z1 z2 : TrueZero}
    (h : expectedMinimumPrime z1 = expectedMinimumPrime z2) : z1 = z2 := by
  have hIdx : nZeroSourceIndex z1.1 = nZeroSourceIndex z2.1 := by
    have hSucc : nZeroSourceIndex z1.1 + 1 = nZeroSourceIndex z2.1 + 1 :=
      thm_primeAtRank_injective h
    omega
  exact thm_zeroSourceIndex_injective hIdx

/-- **Le sens de la progression, EV = EV+1 (auteur, 2026-09-27).**  Sur TOUT passage de deux zéros
réellement consécutifs (`TZeroPassage`, base zeta23/rhv3_lean), l'index zéro-source du membre plus
tard est exactement celui du membre plus tôt, plus un — jamais une avance de deux crans, jamais une
stagnation. Aucune nouvelle prémisse, aucune restriction sur `β` : `thm_zeroSourceIndex_succ_of_passage`
(déjà compilé, `MemberZeroSourceOccurrence.lean`) l'établit pour tout passage, ON ou OFF. -/
theorem eventIndex_succ_of_passage (p : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight p.zEarlierMember) :
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 :=
  thm_zeroSourceIndex_succ_of_passage p hEarlierUpper

/-- **Les premiers progressent entre deux zéros consécutifs (auteur, 2026-09-27), forme générale et
inconditionnelle.**  Pour TOUT passage de deux zéros consécutifs (`TZeroPassage`), le premier de
référence `pmin` désigné par le membre plus tôt est STRICTEMENT inférieur à celui désigné par le
membre plus tard — pas seulement sur la paire miroir hors ligne (`expectedMinimum_lt_mirror_
expectedMinimum`, qui exige `β < 1/2`), mais pour n'importe quel passage réel, ON comme OFF, sans
aucune hypothèse sur `β`. Preuve directe, aucune nouvelle prémisse : `pmin` du membre plus tôt EST
l'occurrence du membre plus tard (`expectedMinimumPrime_eq_laterOccurrence`, déjà ci-dessus), et
l'occurrence de tout zéro est strictement sous son propre `pmin`
(`occurrence_lt_expectedMinimumPrime`) ; composer les deux donne l'inégalité stricte demandée. C'est
la forme générale, non conditionnée à l'orientation OFF/miroir, du « sens de progression » : chaque
passage avance l'index d'exactement un cran (`eventIndex_succ_of_passage` ci-dessus) ET désigne un
premier de référence strictement plus grand — jamais de régression, jamais de répétition, sur
n'importe quelle paire de zéros consécutifs de la démarche. -/
theorem expectedMinimumPrime_succ_of_passage
    (p : TZeroPassage)
    (hEarlierUpper : 0 < rZeroHeight p.zEarlierMember)
    (hLaterUpper : 0 < rZeroHeight p.zLaterMember) :
    expectedMinimumPrime ⟨p.zEarlierMember, hEarlierUpper⟩ <
      expectedMinimumPrime ⟨p.zLaterMember, hLaterUpper⟩ := by
  rw [expectedMinimumPrime_eq_laterOccurrence p hEarlierUpper hLaterUpper]
  exact occurrence_lt_expectedMinimumPrime ⟨p.zLaterMember, hLaterUpper⟩

end RHV6Fresh
