/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PrimalEventRaccord

/-!
# RHV6Fresh — le système rigide global (auteur, 2026-09-30)

Demande de l'auteur : ne pas poser une prémisse `PGlobalRigidity`, mais construire un objet
`GlobalRigidSystem` dont chaque champ est rempli par un théorème déjà acquis, puis regarder ce
qu'un zéro hors ligne force à l'intérieur de ce même objet.

* `GlobalRigidSystem` : treize champs, un par couche (ordre, miroir, rang, membre = terme de la
  formule explicite, raccord grammatical, détecteur dans ses deux régimes, pas énergétique,
  grammaire première, reconstruction complète, formule explicite, fond lisse et reste, incrément
  du reste à chaque événement premier).
* `globalRigidSystem : GlobalRigidSystem` : le système existe, **sans aucune hypothèse**. La
  « rigidité spectrale-arithmétique totale » n'est donc pas une prémisse : c'est un théorème.
* `off_inside_globalRigidSystem` : ce qu'un zéro hors ligne force à l'intérieur du système
  (dérivé des champs du système, pas d'ailleurs).
* `off_conserves_three_equalities` : les trois égalités du diagramme (reste arithmétique = reste
  spectral ; grammaire reconstruite = grammaire première ; géométrie, raccord et énergie du même
  ensemble) sont conservées en présence d'un zéro hors ligne. Le système global, seul, ne produit
  pas de contradiction.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse nouvelle.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **Le système rigide global** : toutes les couches imposées au même ensemble de zéros. Chaque
champ est l'énoncé d'un théorème déjà compilé ; aucun n'est une hypothèse sur la position des
zéros. -/
structure GlobalRigidSystem : Prop where
  /-- Ordre des membres : hauteur d'abord, position radiale ensuite. -/
  order : ∀ z w : TNonTrivialZetaZero, PZeroMemberPrecedes z w ↔
    rZeroHeight z < rZeroHeight w ∨
      (rZeroHeight z = rZeroHeight w ∧ rZeroRadialPosition z < rZeroRadialPosition w)
  /-- Miroir : même hauteur, position radiale réfléchie. -/
  mirror : ∀ z : TNonTrivialZetaZero, rZeroHeight (zMirrorZero z) = rZeroHeight z ∧
    rZeroRadialPosition (zMirrorZero z) = 1 - rZeroRadialPosition z
  /-- Horloge des membres : tout passage avance le rang d'exactement un. -/
  rank : ∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember →
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1
  /-- Horloge des hauteurs : aucun passage ne fait reculer la hauteur. -/
  height : ∀ p : TZeroPassage, rZeroHeight p.zEarlierMember ≤ rZeroHeight p.zLaterMember
  /-- Géométrie de Tour : le terme du membre est réel exactement aux contacts de sa Tour. -/
  contacts : ∀ (z : TrueZero) {x : ℝ}, 0 < x →
    ((zeroTerm z x).im = 0 ↔ ∃ k : ℤ, x = contactMinusAt z k)
  /-- Énergie : le module du terme du membre est `x^β/‖ρ‖`. -/
  energy : ∀ (z : TrueZero) {x : ℝ}, 0 < x →
    ‖zeroTerm z x‖ = x ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖
  /-- Orientation supérieure : le zéro conjugué apporte le terme conjugué, pas un second compteur. -/
  upper : ∀ (z : TrueZero) {x : ℝ}, 0 < x →
    (x : ℂ) ^ (starRingEnd ℂ (zeroPoint z)) / starRingEnd ℂ (zeroPoint z) =
      starRingEnd ℂ (zeroTerm z x)
  /-- Raccord : sur tout passage, le raccord grammatical existe, et il est unique. -/
  raccord : ∀ (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember),
    ∃ G : GrammaticalRaccord ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩,
      (∀ G' : GrammaticalRaccord ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩, G' = G) ∧
      G.event = reconstructedEventAt (nZeroSourceIndex p.zLaterMember) ∧
      primalHistory (nZeroSourceIndex p.zLaterMember) =
        primalHistory (nZeroSourceIndex p.zEarlierMember) ++ [G.event]
  /-- Détecteur, régime vertical ou diagonal : la hauteur avance, le raccord est orienté. -/
  detectorUp : ∀ (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember),
    rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember → 2 ≤ rZeroHeight p.zLaterMember →
      (towerRaccordOf p hE hL).Oriented
  /-- Détecteur, régime horizontal : même hauteur `≥ 2`, le raccord est renversé. -/
  detectorFlat : ∀ (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember),
    rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember → 2 ≤ rZeroHeight p.zEarlierMember →
      ¬ (towerRaccordOf p hE hL).Oriented
  /-- Pas énergétique d'un membre : neutre si et seulement si le membre est en ligne. -/
  step : ∀ z : TrueZero, memberStep z = 1 ↔ rZeroRadialPosition z.1 = 1 / 2
  /-- Grammaire première complète reconstruite par l'ensemble des zéros. -/
  grammar : ∀ n : ℕ, reconstructedHistory n = primalHistory n
  /-- Formule explicite : l'escalier est exactement reconstruit depuis les zéros. -/
  explicit : ∀ x : ℝ, 2 ≤ x → psiRecoveredFromZeros x = (Chebyshev.psi x : ℂ)
  /-- Fond lisse et reste : le canal tronqué est le fond lisse moins la somme des zéros. -/
  background : ∀ x C : ℝ,
    rZeroChannelApprox x C = smoothBackground x - (cSymmetricZeroSum x C).re
  /-- Deux états successifs du reste à un événement premier. -/
  remainder : ∀ n : ℕ,
    arithmeticRemainder (fnPrimeAtRank n) - arithmeticRemainder ((fnPrimeAtRank n : ℝ) - 1) =
      Real.log (fnPrimeAtRank n) -
        (smoothBackground (fnPrimeAtRank n) - smoothBackground ((fnPrimeAtRank n : ℝ) - 1))

/-- **Le système rigide global existe, sans aucune hypothèse.** Chaque champ est rempli par un
théorème déjà compilé. -/
theorem globalRigidSystem : GlobalRigidSystem where
  order := thm_zeroMemberPrecedes_iff_height_radial_lex
  mirror z := ⟨thm_mirror_sameHeight z, thm_mirror_radialPosition z⟩
  rank p hE := thm_zeroSourceIndex_succ_of_passage p hE
  height := passage_height_le
  contacts _ _ hx := zeroTerm_real_iff_ray hx
  energy _ _ hx := zeroTerm_norm hx
  upper _ _ hx := conjugate_term_eq_conj hx
  raccord p hE hL :=
    ⟨grammaticalRaccordOf p hE hL, fun G' => grammaticalRaccord_eq G' _,
      (grammaticalRaccordOf p hE hL).event_reconstructed,
      (grammaticalRaccordOf p hE hL).history_step⟩
  detectorUp := towerRaccord_oriented_of_height_lt
  detectorFlat p hE hL hSame hT2 := by
    have hHMR := nullPassage_horizontal p ((thm_zeroPassage_null_iff_sameHeight p).mpr hSame)
    exact not_le.mpr
      (towerRaccord_reverses_of_sameHeight (towerRaccordOf p hE hL) hSame hT2 hHMR.2.1)
  step := memberStep_eq_one_iff
  grammar := reconstructedHistory_eq_primalHistory
  explicit _ hx := liaison_analytic hx
  background := zeroChannelApprox_eq_background_sub_zeroSum
  remainder := remainder_increment_at_prime

/-- **Ce qu'un zéro hors ligne force à l'intérieur du système**, dérivé des champs du système :
un passage à même hauteur ; le rang avance d'un cran ; le raccord grammatical existe, unique, son
événement est celui que les zéros reconstruisent et l'histoire première gagne exactement cet
événement ; le raccord est renversé ; le pas énergétique du zéro n'est pas neutre ; aucun préfixe
analytique ne sépare les deux membres du passage. -/
theorem off_inside_globalRigidSystem (S : GlobalRigidSystem) {z : TrueZero}
    (hOff : PIsOffCriticalLine z.1) (hT2 : 2 ≤ rZeroHeight z.1) :
    memberStep z ≠ 1 ∧
    ∃ p : TZeroPassage, ∃ hE : 0 < rZeroHeight p.zEarlierMember,
      ∃ hL : 0 < rZeroHeight p.zLaterMember,
        rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember ∧
        nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
        (∃ G : GrammaticalRaccord ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩,
          G.event = reconstructedEventAt (nZeroSourceIndex p.zLaterMember) ∧
          primalHistory (nZeroSourceIndex p.zLaterMember) =
            primalHistory (nZeroSourceIndex p.zEarlierMember) ++ [G.event]) ∧
        ¬ (towerRaccordOf p hE hL).Oriented ∧
        ¬ ∃ C : ℝ, cZeroSupport p.zEarlierMember ∈ finsetSymmetricZeroWindow C ∧
          cZeroSupport p.zLaterMember ∉ finsetSymmetricZeroWindow C := by
  refine ⟨fun h => hOff ((S.step z).mp h), ?_⟩
  obtain ⟨p, hE, hL, hHz, hSame, _, _, _⟩ := off_event_increment_without_height hOff
  obtain ⟨G, _, hRec, hHist⟩ := S.raccord p hE hL
  refine ⟨p, hE, hL, hSame, S.rank p hE, ⟨G, hRec, hHist⟩,
    S.detectorFlat p hE hL hSame (hHz ▸ hT2), ?_⟩
  intro hSep
  exact absurd ((passage_separated_by_window_iff p hE hL).mp hSep) (by rw [hSame]; exact lt_irrefl _)

/-- **Le test de l'auteur : un zéro hors ligne conserve-t-il les trois égalités ?** Oui. Le reste
arithmétique reste égal au reste spectral, la grammaire reconstruite reste la grammaire première,
et la géométrie, le raccord et l'énergie restent ceux du même ensemble : le système entier est un
théorème sans hypothèse, il vaut donc aussi en présence d'un zéro hors ligne. Le système global,
seul, ne contient pas de contradiction avec le hors-ligne. -/
theorem off_conserves_three_equalities {z : TrueZero} (_hOff : PIsOffCriticalLine z.1) :
    (∀ x : ℝ, 2 ≤ x → psiRecoveredFromZeros x = (Chebyshev.psi x : ℂ)) ∧
      (∀ n : ℕ, reconstructedHistory n = primalHistory n) ∧
      GlobalRigidSystem :=
  ⟨globalRigidSystem.explicit, globalRigidSystem.grammar, globalRigidSystem⟩

#print axioms globalRigidSystem
#print axioms off_inside_globalRigidSystem
#print axioms off_conserves_three_equalities

end RHV6Fresh
