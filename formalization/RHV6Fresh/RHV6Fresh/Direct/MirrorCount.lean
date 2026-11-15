/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Voyage.TowerReading

/-!
# RHV6Fresh — la seconde Tour (celle du miroir) et le comptage à son dernier rayon

Transcription de la chaîne

    progression déjà prouvée
            ↓
    premier minimum attendu
            │
            │       seconde Tour, même constructeur
            │                    ↓
            │           comptage jusqu'au dernier rayon
            │                    ↓
            │        premier atteint / non atteint
            │                    │
            └──────── vérification ─────────────┘

**Aucune hauteur n'entre dans ce module comme donnée, hypothèse ou
sélecteur.**  La seconde Tour est la Tour du miroir fonctionnel
`(β, T) ↦ (1 − β, T)`, produite par les **mêmes** formules tangentielles, de
la même manière et indépendamment de la première (sixième correction du
2026-09-22, maître Lean §26).  Le fait que le miroir conserve `T` est une
propriété du miroir (fonctionnelle de ζ), jamais une hypothèse.

**Le recul n'est jamais étudié.**  Les théorèmes de recul (`C_k(z*) < C_k(z)`,
« +1 impossible », formes « déficit ») qui occupaient les anciennes sections
§2, §3 (partie miroir) et §5 ont été supprimés le 2026-09-22 (sixième
correction) : le recul est la cause de l'objet d'étude, jamais l'objet ; aucun
traitement ni aucune considération de recul n'entre dans la démonstration ; la
condition « premier non atteint » se vérifie recul ou pas.  Ce module conserve :
la Tour du miroir par les formules tangentielles (§1), `mirror_radial_gt` (le
seul fait sur β utilisé par l'ordre des zéros), la forme indexée du comptage
(§3, contrôle ; L2 sur l'état porté est dans `Direct/StateCount.lean`), le
minimum attendu et `mirror_precedes` (§4), la conversion « non atteint »
(§5), OFF et RH (§6), le canal fixé par réflexion (§9).
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. La seconde Tour : celle du miroir, par les formules tangentielles -/

/-- Le miroir fonctionnel d'un membre supérieur, lui-même vrai zéro
supérieur (`β* = 1 − β`, `T* = T`). -/
noncomputable def mirrorMember (z : TrueZero) : TrueZero := zUpperMirrorZero z

theorem mirrorMember_ordinate (z : TrueZero) :
    rZeroHeight (mirrorMember z).1 = rZeroHeight z.1 :=
  thm_mirror_sameHeight z.1

theorem mirrorMember_radial (z : TrueZero) :
    rZeroRadialPosition (mirrorMember z).1 = 1 - rZeroRadialPosition z.1 :=
  thm_mirror_radialPosition z.1

/-- Sur la droite critique, le membre miroir est le zéro lui-même. -/
theorem mirrorMember_eq_self_of_onLine {z : TrueZero} (hβ : rZeroRadialPosition z.1 = 1 / 2) :
    mirrorMember z = z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Complex.ext
  · have h := mirrorMember_radial z
    unfold rZeroRadialPosition cZeroSupport at h hβ
    rw [h, hβ]
    norm_num
  · have h := mirrorMember_ordinate z
    unfold rZeroHeight cZeroSupport at h
    exact h

/-- Phase tangentielle de la seconde Tour : `φ* = atan(T/(1−β))`. -/
theorem mirrorMember_phase (z : TrueZero) :
    (towerMotionOf (mirrorMember z)).phase =
      Real.arctan (rZeroHeight z.1 / (1 - rZeroRadialPosition z.1)) := by
  rw [towerMotion_phase, mirrorMember_ordinate, mirrorMember_radial]

/-- Contact inférieur de la seconde Tour, formule tangentielle exacte
`C_k(1−β, T) = exp((atan(T/(1−β)) + kπ)/T)`. -/
theorem mirrorMember_contactMinusAt (z : TrueZero) (k : ℤ) :
    contactMinusAt (mirrorMember z) k =
      Real.exp ((Real.arctan (rZeroHeight z.1 / (1 - rZeroRadialPosition z.1)) +
        (k : ℝ) * Real.pi) / rZeroHeight z.1) := by
  unfold contactMinusAt
  rw [towerMotion_incidence, mirrorMember_phase, mirrorMember_ordinate]

/-- Contact supérieur de la seconde Tour : `C_(k+1)(1−β, T)`. -/
theorem mirrorMember_contactPlusAt (z : TrueZero) (k : ℤ) :
    contactPlusAt (mirrorMember z) k =
      Real.exp ((Real.arctan (rZeroHeight z.1 / (1 - rZeroRadialPosition z.1)) +
        ((k + 1 : ℤ) : ℝ) * Real.pi) / rZeroHeight z.1) := by
  unfold contactPlusAt
  rw [towerMotion_incidence, mirrorMember_phase, mirrorMember_ordinate]

/-! ## 2. Côté `β < 1/2` : le miroir est plus à droite (fait d'ordre, aucun recul) -/

theorem mirror_radial_gt {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    rZeroRadialPosition z.1 < rZeroRadialPosition (mirrorMember z).1 := by
  rw [mirrorMember_radial]
  linarith

/-! ## 3. Comptage à la seconde Tour (forme indexée, contrôle) -/

/-- Rang compté (Von Mangoldt/Chebyshev) au contact supérieur de la Tour de
`w` à la coordonnée `k` : `π(C⁺(w,k))`. -/
noncomputable def countedRankAt (w : TrueZero) (k : ℤ) : ℕ :=
  primeCountAtStateUpper (towerStateAt w k)

/-- Premier constaté : `p_(π(C⁺) − 1)`. -/
noncomputable def countedPrimeAt (w : TrueZero) (k : ℤ) : ℕ :=
  producedPrime (towerStateAt w k)

theorem countedPrimeAt_eq_vonMangoldt (w : TrueZero) (k : ℤ) :
    countedPrimeAt w k =
      fnPrimeAtRank (nPrimeCountingFromJ rChebyshevJNat ⌊contactPlusAt w k⌋₊ - 1) :=
  producedPrime_eq_vonMangoldt _

theorem countedPrimeAt_eq_primeAtRank (w : TrueZero) (k : ℤ) :
    countedPrimeAt w k = fnPrimeAtRank (countedRankAt w k - 1) := rfl

/-- Le premier de rang `π(C⁺)` est le premier candidat **au-delà** du contact
(dualité rang/contact). -/
theorem contactPlusAt_lt_primeAtRank_counted (w : TrueZero) (k : ℤ) :
    contactPlusAt w k < (fnPrimeAtRank (countedRankAt w k) : ℝ) :=
  (thm_edgeRank_le_iff_lt_primeAtRank (le_of_lt (contactPlusAt_positive w k))
    (countedRankAt w k)).mp le_rfl

/-! ## 4. Minimum premier attendu, par la progression déjà prouvée

`expectedMinimumPrime a = p_{n(a)+1}` ne dépend que de l'histoire ordonnée des
zéros (module `Voyage/Progression`).  Le miroir d'un membre `β < 1/2` le suit
dans l'ordre des membres ; la progression impose donc que son occurrence
atteigne au moins ce minimum. -/

theorem mirror_precedes {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    PZeroMemberPrecedes z.1 (mirrorMember z).1 := by
  rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
  right
  exact ⟨(mirrorMember_ordinate z).symm, mirror_radial_gt hβ⟩

theorem sourceIndex_lt_mirror {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    nZeroSourceIndex z.1 < nZeroSourceIndex (mirrorMember z).1 :=
  thm_zeroSourceIndex_strictMono z.2 (mirror_precedes hβ)

/-- **Progression → minimum attendu** : l'occurrence du miroir atteint au moins
`p_{n(z)+1}`. -/
theorem expectedMinimum_le_mirror_occurrence {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    expectedMinimumPrime z ≤ occurrence (mirrorMember z) := by
  rw [occurrence_eq_primeAtRank]
  unfold expectedMinimumPrime fnPrimeSuccessor
  exact thm_primeAtRank_strictMono.monotone (sourceIndex_lt_mirror hβ)

/-- Cas consécutif : égalité exacte (progression obligatoire). -/
theorem expectedMinimum_eq_mirror_occurrence_of_consecutive {z : TrueZero}
    (hab : PZeroMembersConsecutive z.1 (mirrorMember z).1) :
    expectedMinimumPrime z = occurrence (mirrorMember z) :=
  (progression_occurrence hab).symm

/-! ## 5. Conversion « non atteint » (aucun recul) -/

/-- Sur un état de la seconde Tour, « premier constaté sous le minimum attendu »
équivaut à « dernier rayon sous le minimum attendu » (compte positif). -/
theorem mirror_counted_lt_expected_iff (a : TrueZero) (k : ℤ)
    (hCount : 0 < countedRankAt (mirrorMember a) k) :
    countedPrimeAt (mirrorMember a) k < expectedMinimumPrime a ↔
      contactPlusAt (mirrorMember a) k < (expectedMinimumPrime a : ℝ) :=
  produced_lt_expectedMinimum_iff a _ hCount

/-- Le premier constaté à toute coordonnée est sous le minimum attendu dès que
le contact supérieur l'est (sans hypothèse de compte positif : le compte nul
lit `2 < 3 ≤ p_min`). -/
theorem countedPrimeAt_lt_expected_of_contact (a w : TrueZero) (k : ℤ)
    (h : contactPlusAt w k < (expectedMinimumPrime a : ℝ)) :
    countedPrimeAt w k < expectedMinimumPrime a := by
  by_cases hCount : 0 < countedRankAt w k
  · exact (produced_lt_expectedMinimum_iff a _ hCount).mpr h
  · have hZero : countedRankAt w k = 0 := by omega
    have h2 : countedPrimeAt w k = 2 := by
      rw [countedPrimeAt_eq_primeAtRank, hZero]
      exact thm_primeAtRank_zero_eq_two
    have := three_le_expectedMinimumPrime a
    omega

/-! ## 6. OFF et RH (aucune hauteur) -/

/-- Un zéro OFF a un côté `β < 1/2` : lui-même ou son miroir. -/
theorem off_lowerSide {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    rZeroRadialPosition z.1 < 1 / 2 ∨
      rZeroRadialPosition (mirrorMember z).1 < 1 / 2 := by
  rcases lt_or_gt_of_ne hOff with h | h
  · exact Or.inl h
  · right
    rw [mirrorMember_radial]
    linarith

theorem mirrorMember_mirrorMember_radial (z : TrueZero) :
    rZeroRadialPosition (mirrorMember (mirrorMember z)).1 = rZeroRadialPosition z.1 := by
  rw [mirrorMember_radial, mirrorMember_radial]
  ring

-- Les théorèmes d'universalisation (`riemannHypothesis_of_noOff`, `riemannHypothesis_of_noLowerSide`)
-- sont dans `Terminal/Universalization.lean` (huitième correction 2026-09-22, maître Lean §36) : aucun
-- module des niveaux GÉOMÉTRIE, LECTURE ARITHMÉTIQUE, CONTRADICTION ne mentionne l'hypothèse de Riemann.

/-! ## 9. Liaison collective de Von Mangoldt : fixe sous réflexion, une seule
lecture sur toute la Tour orientée

Le canal de comptage `nPrimeCountingFromJ rChebyshevJNat` est un objet global
de l'histoire première.  Il ne dépend d'aucun zéro : la Tour et son miroir
lisent **le même** canal (fixe sous réflexion), calculé de la même manière et
indépendamment pour les deux Tours ; la lecture ne dépend que du contact
atteint.  Sur la Tour orientée (coordonnée croissante) cette lecture est une
seule loi monotone. -/

/-- Le canal collectif lu à la seconde Tour est le même que celui de la
première : seul le contact change. -/
theorem vonMangoldt_channel_reflectionFixed (z : TrueZero) (k : ℤ) :
    countedPrimeAt (mirrorMember z) k =
      fnPrimeAtRank (nPrimeCountingFromJ rChebyshevJNat
        ⌊contactPlusAt (mirrorMember z) k⌋₊ - 1) ∧
    countedPrimeAt z k =
      fnPrimeAtRank (nPrimeCountingFromJ rChebyshevJNat ⌊contactPlusAt z k⌋₊ - 1) :=
  ⟨countedPrimeAt_eq_vonMangoldt _ _, countedPrimeAt_eq_vonMangoldt _ _⟩

/-- La lecture ne dépend que du contact : deux membres quelconques dont les
contacts supérieurs coïncident constatent le même premier. -/
theorem countedPrimeAt_of_contactPlus_eq {z w : TrueZero} {k l : ℤ}
    (h : contactPlusAt z k = contactPlusAt w l) :
    countedPrimeAt z k = countedPrimeAt w l := by
  unfold countedPrimeAt producedPrime lastPrimeAtStateUpper primeCountAtStateUpper
  change fnPrimeAtRank (nEdgePrimeRank (contactPlusAt z k) - 1) =
    fnPrimeAtRank (nEdgePrimeRank (contactPlusAt w l) - 1)
  rw [h]

/-- Une seule loi de lecture sur toute la Tour orientée : monotone en la
coordonnée. -/
theorem countedPrimeAt_mono_oriented (z : TrueZero) {k l : ℤ} (hkl : k ≤ l) :
    countedPrimeAt z k ≤ countedPrimeAt z l := by
  rcases lt_or_eq_of_le hkl with hlt | rfl
  · exact producedPrime_mono _ _
      (le_of_lt (towerMotion_incidence_strictOrder z (by omega : k + 1 < l + 1)))
  · exact le_rfl

end RHV6Fresh
