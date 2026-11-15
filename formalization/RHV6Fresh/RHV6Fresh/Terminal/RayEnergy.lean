/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.VerticalEnergyPush
import RHV6Fresh.Terminal.MirrorDegeneracy

/-!
# RHV6Fresh — l'énergie SUR LES RAYONS de la Tour unique du zéro, et la double contrainte (2026-09-28)

Réponse compilée à trois questions de l'auteur.

**Q1 — l'énergie est-elle reliée à la Tour unique, par sa phase, ses rayons, sa vitesse ?**
Jusqu'ici l'énergie n'était utilisée que par son amplitude `‖zeroTerm‖ = q^β/‖ρ‖`, qui ne voit ni
la phase ni les rayons. Ici : `cos φ = β/‖ρ‖` (R1), `Re(zeroTerm z q) = q^β · cos(π·pos(q)) / ‖ρ‖`
(R2), donc **sur chaque rayon `C_k` de la Tour, l'énergie est RÉELLE et vaut exactement
`(−1)^k · C_k^β/‖ρ‖`** (R3) : signe alterné d'un rayon au suivant (R4), amplitude croissante en
`k` comme `exp(kπβ/T)` (R5, la vitesse de rotation `T` gouverne la croissance de l'énergie le long
des rayons). C'est le point L1 du plan E096–E100, désormais théorème.

**Q2 — les zéros sont-ils enchaînés par `M^Z = M` ?** Oui, par le pointeur de rang : sur tout
passage, `Occ(l) = p_min(e)`. Compilé depuis longtemps (`passage_event_increment`).

**Q3 — la double contrainte (géométrie ET grammaire) exige-t-elle un déplacement d'une certaine
amplitude ?** Vérifié, réponse compilée : NON. (D1) une Tour à N'IMPORTE QUELLE hauteur lit
N'IMPORTE QUEL premier dans une cellule unique (`tower_reads_any_prime`) — la géométrie seule
n'impose aucune hauteur ; (D2) sur tout passage, la double contrainte (grammaire : le LATER lit
`p_min(e)` ; géométrie : chaque Tour tient son premier dans sa cellule ; excès `J ≥ 0`) est
SATISFAITE identiquement, ON ou OFF (`passage_double_constraint`) ; (D3) l'amplitude de
déplacement qu'elle exige est exactement `J = (T_l − T_e)·log(p_{n+2}/p_{n+1}) ≥ 0`, nulle ssi
même hauteur : la double contrainte n'exige un déplacement STRICTEMENT positif que si l'on
suppose déjà `T_e < T_l`, c'est-à-dire RH (`interTowerExcess_pos_iff_riemannHypothesis`, déjà
compilé). Le premier avance toujours ; la coordonnée entière `k` absorbe cette avance à hauteur
fixe. Aucun quantum de phase n'est compilé qui l'interdise.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## R1 — le cosinus de la phase est `β/‖ρ‖` -/

theorem cos_phase_eq (z : TrueZero) :
    Real.cos (towerMotionOf z).phase = rZeroRadialPosition z.1 / ‖zeroPoint z‖ := by
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  rw [towerMotion_phase, Real.cos_arctan]
  have h1 : 1 + (rZeroHeight z.1 / rZeroRadialPosition z.1) ^ 2 =
      (rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2) / rZeroRadialPosition z.1 ^ 2 := by
    field_simp
  rw [h1, Real.sqrt_div (by positivity), Real.sqrt_sq hβ.le, ← zeroPoint_norm_sq,
    Real.sqrt_sq (norm_nonneg _), one_div_div]

/-! ## R2 — la partie réelle du terme est portée par le cosinus de la position de Tour -/

theorem zeroTerm_re {z : TrueZero} {q : ℝ} (hq : 0 < q) :
    (zeroTerm z q).re =
      Real.exp (rZeroRadialPosition z.1 * Real.log q) *
        (rZeroRadialPosition z.1 * Real.cos (rZeroHeight z.1 * Real.log q) +
          rZeroHeight z.1 * Real.sin (rZeroHeight z.1 * Real.log q)) /
        Complex.normSq (zeroPoint z) := by
  unfold zeroTerm
  rw [Complex.div_re, cpow_zeroPoint_re hq, cpow_zeroPoint_im hq, zeroPoint_re, zeroPoint_im]
  ring

/-- L'identité de phase en cosinus : `β cos θ + T sin θ = (β / cos φ) · cos(θ − φ)`. -/
theorem phase_identity_cos (z : TrueZero) (θ : ℝ) :
    rZeroRadialPosition z.1 * Real.cos θ + rZeroHeight z.1 * Real.sin θ =
      rZeroRadialPosition z.1 / Real.cos (towerMotionOf z).phase *
        Real.cos (θ - (towerMotionOf z).phase) := by
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hcos : 0 < Real.cos (towerMotionOf z).phase := by
    rw [towerMotion_phase]; exact Real.cos_arctan_pos _
  have hsin : Real.sin (towerMotionOf z).phase =
      rZeroHeight z.1 / rZeroRadialPosition z.1 * Real.cos (towerMotionOf z).phase := by
    have ht : Real.tan (towerMotionOf z).phase = rZeroHeight z.1 / rZeroRadialPosition z.1 := by
      rw [towerMotion_phase, Real.tan_arctan]
    rw [Real.tan_eq_sin_div_cos] at ht
    field_simp at ht
    rw [div_mul_eq_mul_div, eq_div_iff hβ.ne']
    linear_combination ht
  rw [Real.cos_sub, hsin]
  field_simp

/-- **`Re(zeroTerm z q) = q^β · cos(π · towerPosition z q) / ‖ρ‖`** : la Tour (position, phase)
porte la partie réelle du terme, avec le support `‖ρ‖`. -/
theorem zeroTerm_re_eq_cos_towerPosition {z : TrueZero} {q : ℝ} (hq : 0 < q) :
    (zeroTerm z q).re =
      q ^ rZeroRadialPosition z.1 * Real.cos (Real.pi * towerPosition z q) / ‖zeroPoint z‖ := by
  rw [zeroTerm_re hq, phase_identity_cos z, pi_mul_towerPosition, cos_phase_eq,
    ← Complex.sq_norm, Real.rpow_def_of_pos hq, mul_comm (Real.log q)]
  have hN := zeroPoint_norm_pos z
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  field_simp

/-! ## R3 — sur chaque rayon, l'énergie est réelle et vaut `(−1)^k · C_k^β / ‖ρ‖` -/

/-- **L'énergie sur le rayon `C_k` de la Tour unique du zéro** : réelle, de signe `(−1)^k`,
d'amplitude `C_k^β/‖ρ‖`. -/
theorem ray_energy (z : TrueZero) (k : ℤ) :
    (zeroTerm z (contactMinusAt z k)).re =
      (-1 : ℝ) ^ k * (contactMinusAt z k) ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖ := by
  rw [zeroTerm_re_eq_cos_towerPosition (contactMinusAt_positive z k), pi_mul_towerPosition]
  unfold contactMinusAt
  rw [crossing_side]
  ring

/-- Le terme sur un rayon est exactement son énergie signée (partie imaginaire nulle). -/
theorem ray_zeroTerm_eq (z : TrueZero) (k : ℤ) :
    zeroTerm z (contactMinusAt z k) =
      (((-1 : ℝ) ^ k * (contactMinusAt z k) ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖ : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re, ray_energy]
  · rw [Complex.ofReal_im, ray_zeroTerm_real]

/-! ## R4 — alternance stricte du signe de l'énergie d'un rayon au suivant -/

theorem ray_energy_alternates (z : TrueZero) (k : ℤ) :
    (zeroTerm z (contactMinusAt z (k + 1))).re * (zeroTerm z (contactMinusAt z k)).re < 0 := by
  rw [ray_energy, ray_energy, zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  have hN := zeroPoint_norm_pos z
  have h1 : 0 < (contactMinusAt z k) ^ rZeroRadialPosition z.1 :=
    Real.rpow_pos_of_pos (contactMinusAt_positive z k) _
  have h2 : 0 < (contactMinusAt z (k + 1)) ^ rZeroRadialPosition z.1 :=
    Real.rpow_pos_of_pos (contactMinusAt_positive z (k + 1)) _
  have hsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    exact Even.neg_one_zpow ⟨k, by ring⟩
  have : (-1 : ℝ) ^ k * (-1) * (contactMinusAt z (k + 1)) ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖ *
      ((-1 : ℝ) ^ k * (contactMinusAt z k) ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖) =
      -(((-1 : ℝ) ^ k) ^ 2 * ((contactMinusAt z (k + 1)) ^ rZeroRadialPosition z.1 *
        (contactMinusAt z k) ^ rZeroRadialPosition z.1) / ‖zeroPoint z‖ ^ 2) := by ring
  rw [this, hsq, one_mul, neg_lt_zero]
  positivity

/-! ## R5 — la vitesse de rotation `T` gouverne la croissance de l'énergie le long des rayons -/

/-- **`|E(C_{k+1})| / |E(C_k)| = exp(πβ/T)`** : d'un rayon au suivant, l'amplitude de l'énergie est
multipliée par un facteur fixé par `β` (l'exposant) et `T` (la vitesse de rotation) — jamais par
la phase, jamais par `k`. -/
theorem ray_energy_growth (z : TrueZero) (k : ℤ) :
    ‖zeroTerm z (contactMinusAt z (k + 1))‖ =
      ‖zeroTerm z (contactMinusAt z k)‖ *
        Real.exp (Real.pi * rZeroRadialPosition z.1 / rZeroHeight z.1) := by
  have hk := contactMinusAt_positive z k
  have hk1 := contactMinusAt_positive z (k + 1)
  rw [zeroTerm_norm hk1, zeroTerm_norm hk, div_mul_eq_mul_div]
  congr 1
  rw [Real.rpow_def_of_pos hk1, Real.rpow_def_of_pos hk, ← Real.exp_add]
  congr 1
  have hw := towerMotion_consecutive_width z k
  unfold contactMinusAt
  have hT : rZeroHeight z.1 ≠ 0 := z.2.ne'
  rw [show Real.log ((towerMotionOf z).incidence (k + 1)) =
      Real.log ((towerMotionOf z).incidence k) + Real.pi / rZeroHeight z.1 by linarith]
  field_simp

/-! ## D1 — la géométrie seule n'impose aucune hauteur : toute Tour lit tout premier -/

/-- **Une Tour à n'importe quelle hauteur lit n'importe quel premier** dans une cellule unique. -/
theorem tower_reads_any_prime (z : TrueZero) (n : ℕ) :
    contactMinusAt z (pivotCoordinate z (fnPrimeAtRank n : ℝ)) < (fnPrimeAtRank n : ℝ) ∧
      (fnPrimeAtRank n : ℝ) ≤ contactPlusAt z (pivotCoordinate z (fnPrimeAtRank n : ℝ)) :=
  prime_raccord_has_unique_tower_cell z
    (by exact_mod_cast (thm_primeAtRank_isPrime n).pos)

/-! ## D2 — la double contrainte sur tout passage, satisfaite identiquement -/

/-- **La double contrainte** : grammaire (`Occ(l) = p_min(e)`, `Occ(e) < Occ(l)`), géométrie (le
LATER tient `Occ(l)` dans sa cellule unique, le EARLIER tient `p_min(e)` dans la sienne), excès
`J ≥ 0`. Tout passage la satisfait, ON ou OFF. -/
theorem passage_double_constraint (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
      occurrence ⟨p.zEarlierMember, hE⟩ < occurrence ⟨p.zLaterMember, hL⟩ ∧
      (contactMinusAt ⟨p.zLaterMember, hL⟩
          (pivotCoordinate ⟨p.zLaterMember, hL⟩ (occurrence ⟨p.zLaterMember, hL⟩ : ℝ)) <
          (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) ∧
        (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) ≤ contactPlusAt ⟨p.zLaterMember, hL⟩
          (pivotCoordinate ⟨p.zLaterMember, hL⟩ (occurrence ⟨p.zLaterMember, hL⟩ : ℝ))) ∧
      (contactMinusAt ⟨p.zEarlierMember, hE⟩
          (pivotCoordinate ⟨p.zEarlierMember, hE⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ)) <
          (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) ∧
        (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) ≤ contactPlusAt ⟨p.zEarlierMember, hE⟩
          (pivotCoordinate ⟨p.zEarlierMember, hE⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ))) ∧
      0 ≤ interTowerExcess p hE hL := by
  obtain ⟨_, hOcc, hLt⟩ := passage_event_increment p hE hL
  refine ⟨hOcc, hLt, ?_, ?_, interTowerExcess_nonneg p hE hL⟩
  · exact prime_raccord_has_unique_tower_cell _ (by exact_mod_cast occurrence_pos _)
  · exact prime_raccord_has_unique_tower_cell _ (by exact_mod_cast expectedMinimumPrime_pos _)

/-! ## D3 — l'amplitude de déplacement exigée par la double contrainte -/

/-- **L'amplitude exigée est `J = (T_l − T_e) · log(p_{n+2}/p_{n+1})`, et elle est nulle exactement
sur un passage de même hauteur.** La double contrainte n'exige un déplacement strictement positif
que sous `T_e < T_l`. -/
theorem double_constraint_required_displacement (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    interTowerExcess p hE hL =
        (rZeroHeight p.zLaterMember - rZeroHeight p.zEarlierMember) *
          rPrimeGapLogRatio (nZeroSourceIndex p.zEarlierMember + 1) ∧
      (interTowerExcess p hE hL = 0 ↔
        rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember) :=
  ⟨interTowerExcess_eq p hE hL, interTowerExcess_eq_zero_iff p hE hL⟩

#print axioms cos_phase_eq
#print axioms ray_energy
#print axioms ray_zeroTerm_eq
#print axioms ray_energy_alternates
#print axioms ray_energy_growth
#print axioms tower_reads_any_prime
#print axioms passage_double_constraint
#print axioms double_constraint_required_displacement

end RHV6Fresh
