/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.EngagedClosureVerdict

/-!
# RHV6Fresh — le verrou unique écrit exactement : la flèche de la position d'entrée (auteur, 2026-10-01)

Demande de l'auteur : « Le verrou mathématique unique est désormais : extraire du produit d'Euler et du
poids exact `Λ` une information locale, événement par événement, qui fixe la position d'entrée du premier
partagé ; tant que cette flèche n'est pas démontrée, aucune clôture n'est acquise. »

Ce fichier écrit cette flèche sans rien lui ajouter et sans rien lui retirer.

* **La flèche** (§1) : sur tout passage de la moitié supérieure parti de la ligne, le premier partagé
  entre dans la Tour d'arrivée à sa position de ligne. Elle équivaut exactement à la loi locale de
  conservation sur la moitié supérieure (`entry_arrow_iff_upper_conservation`).
* **Ce qu'elle donne** (§2) : la flèche jointe à l'amorce (membres sans prédécesseur en ligne) équivaut
  à RH (`riemannHypothesis_iff_entry_arrow_and_base`) ; la flèche seule n'est pas RH.
* **Sa forme événementielle** (§3) : sur la flèche, le terme d'Euler du premier partagé, évalué au membre
  d'arrivée, a pour module `M^{−β_l}` (`local_euler_term_norm`) ; la position d'entrée est la position de
  ligne si et seulement si ce module vaut `M^{−1/2}` (`entry_arrow_iff_local_euler_modulus`). La flèche
  est donc exactement un énoncé sur le terme local d'Euler d'un seul premier, à un seul membre.
* **Ce que le facteur local ne fait pas** (§3) : le facteur d'Euler d'un premier ne s'annule nulle part
  sur le demi-plan `Re s > 0`, en particulier en aucun membre (`local_euler_factor_ne_zero`,
  `local_euler_factor_at_member_ne_zero`) : le facteur de l'événement lit la position d'entrée, il ne
  produit pas le membre ; ce qui fixe la position est la liaison de ce facteur à tous les autres
  (le prolongement), pas le facteur seul.

Statut : la flèche n'est pas démontrée ; elle figure seulement comme membre d'équivalences. Elle est
violée dans le monde témoin (`conservation_not_structural`) et dans le monde de contrôle aux mêmes
premiers (`engagedBreakWorld_change_detected`). Aucune prémisse n'est posée, `PNoRegimeChange` n'est pas
utilisée. Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune `def` de prémisse.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. La flèche, exactement -/

/-- **La flèche ⟺ la loi locale de conservation sur la moitié supérieure.** Membre de gauche : sur tout
passage de la moitié supérieure parti de la ligne, le premier partagé (occurrence de l'arrivée) entre
dans la Tour d'arrivée à sa position de ligne. Membre de droite : l'arrivée reste en ligne. -/
theorem entry_arrow_iff_upper_conservation :
    (∀ (p : TZeroPassage) (_hE : 0 < rZeroHeight p.zEarlierMember)
        (hL : 0 < rZeroHeight p.zLaterMember),
        rZeroRadialPosition p.zEarlierMember = 1 / 2 →
          towerPosition ⟨p.zLaterMember, hL⟩ (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) =
            linePosition (rZeroHeight p.zLaterMember)
              (occurrence ⟨p.zLaterMember, hL⟩ : ℝ)) ↔
      (∀ p : TZeroPassage, 0 < rZeroHeight p.zEarlierMember → 0 < rZeroHeight p.zLaterMember →
        rZeroRadialPosition p.zEarlierMember = 1 / 2 →
          rZeroRadialPosition p.zLaterMember = 1 / 2) := by
  constructor
  · intro hA p hE hL hOn
    exact (transition_conserves_iff_entry_position
      (canonicalTransition_of_passage p hE hL hOn)).mpr (hA p hE hL hOn)
  · intro hC p hE hL hOn
    exact (transition_conserves_iff_entry_position
      (canonicalTransition_of_passage p hE hL hOn)).mp (hC p hE hL hOn)

/-! ## 2. Ce que la flèche donne, et ce qu'elle ne donne pas seule -/

/-- **RH ⟺ la flèche jointe à l'amorce.** La récurrence ne traverse que des passages de la moitié
supérieure : la flèche y suffit. Équivalence ; ni la flèche ni l'amorce ne sont dérivées ici. -/
theorem riemannHypothesis_iff_entry_arrow_and_base :
    RiemannHypothesis ↔
      ((∀ (p : TZeroPassage) (_hE : 0 < rZeroHeight p.zEarlierMember)
          (hL : 0 < rZeroHeight p.zLaterMember),
          rZeroRadialPosition p.zEarlierMember = 1 / 2 →
            towerPosition ⟨p.zLaterMember, hL⟩ (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) =
              linePosition (rZeroHeight p.zLaterMember)
                (occurrence ⟨p.zLaterMember, hL⟩ : ℝ)) ∧
        (∀ z : TrueZero, sUpperZerosBelow z.1 = ∅ → rZeroRadialPosition z.1 = 1 / 2)) := by
  rw [entry_arrow_iff_upper_conservation]
  constructor
  · intro hRH
    exact ⟨fun p _ _ _ => thm_zeroRadialPosition_half_of_riemannHypothesis hRH _,
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
          exact hLaw ⟨w, z.1, hcons⟩ hw z.2 hwOn
    exact riemannHypothesis_of_noOff fun z hOff => hOff (key _ z rfl)

/-! ## 3. Forme événementielle : le terme d'Euler du premier partagé -/

/-- **Module du terme d'Euler d'un entier en un membre** : `‖M^{−ρ}‖ = M^{−β}`. -/
theorem local_euler_term_norm (M : ℕ) (hM : 0 < M) (z : TrueZero) :
    ‖(M : ℂ) ^ (-(zeroPoint z))‖ = (M : ℝ) ^ (-(rZeroRadialPosition z.1)) := by
  rw [Complex.norm_natCast_cpow_of_pos hM, Complex.neg_re, zeroPoint_re]

/-- Pour une base `M > 1`, l'exposant est lu sur la puissance. -/
theorem rpow_exponent_injective {M a b : ℝ} (hM : 1 < M) (h : M ^ a = M ^ b) : a = b := by
  have hpos : (0 : ℝ) < M := by linarith
  have hlog : 0 < Real.log M := Real.log_pos hM
  have := congrArg Real.log h
  rw [Real.log_rpow hpos, Real.log_rpow hpos] at this
  exact mul_right_cancel₀ hlog.ne' this

/-- **La flèche, événement par événement, est un énoncé sur un seul terme d'Euler.** Sur la flèche
partie de l'état engagé, le premier partagé `M` entre dans la Tour d'arrivée à sa position de ligne si
et seulement si son terme d'Euler, évalué au membre d'arrivée, a le module `M^{−1/2}`. -/
theorem entry_arrow_iff_local_euler_modulus {e l : TrueZero} (t : CanonicalTransition e l) :
    towerPosition l (occurrence l : ℝ) = linePosition (rZeroHeight l.1) (occurrence l : ℝ) ↔
      ‖((occurrence l : ℕ) : ℂ) ^ (-(zeroPoint l))‖ = ((occurrence l : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hP : Nat.Prime (occurrence l) := t.shared ▸ expectedMinimumPrime_prime e
  have hM1 : (1 : ℝ) < (occurrence l : ℝ) := by exact_mod_cast hP.one_lt
  rw [← transition_conserves_iff_entry_position t, local_euler_term_norm _ hP.pos]
  constructor
  · intro h
    rw [h]
  · intro h
    have := rpow_exponent_injective hM1 h
    linarith

/-- **Le facteur d'Euler d'un premier ne s'annule nulle part sur `Re s > 0`.** -/
theorem local_euler_factor_ne_zero (M : ℕ) (hM : 1 < M) (s : ℂ) (hs : 0 < s.re) :
    1 - (M : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (M : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hn := Complex.norm_natCast_cpow_of_pos (by omega : 0 < M) (-s)
  rw [h1, norm_one, Complex.neg_re] at hn
  have hM1 : (1 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hlt : (M : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hM1 (by linarith)
  linarith

/-- **Le facteur de l'événement ne produit pas le membre.** En tout membre, le facteur d'Euler de tout
premier est non nul : le facteur local lit la position d'entrée (§3), il ne la fixe pas seul. -/
theorem local_euler_factor_at_member_ne_zero (z : TrueZero) (M : ℕ) (hM : Nat.Prime M) :
    1 - (M : ℂ) ^ (-(zeroPoint z)) ≠ 0 :=
  local_euler_factor_ne_zero M hM.one_lt _ (zeroPoint_re_pos z)

#print axioms entry_arrow_iff_upper_conservation
#print axioms riemannHypothesis_iff_entry_arrow_and_base
#print axioms local_euler_term_norm
#print axioms entry_arrow_iff_local_euler_modulus
#print axioms local_euler_factor_ne_zero
#print axioms local_euler_factor_at_member_ne_zero

end RHV6Fresh
