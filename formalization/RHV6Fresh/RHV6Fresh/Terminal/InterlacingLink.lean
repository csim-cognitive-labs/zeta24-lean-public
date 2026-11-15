/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.WindingReadingChain

/-!
# Entrelacement des contacts : liaison géométrique et lecture récursive des zéros (auteur, 2026-10-19, vingt-deuxième message)

Texte de l'auteur : l'entrelacement des contacts est une liaison géométrique entre le zéro suivant et le précédent, à intégrer à
la lecture de fréquence et au raccord des événements premiers ; le signe de la contribution du suivant dépend de sa fréquence, de
sa phase, de son amplitude et des autres zéros ; l'entrelacement apporte la position des contacts du suivant relativement à ceux
du précédent et relie leurs phases.

Compilé ici, axiomes standard, toute position radiale :
* décalage d'entrelacement `δ_k = log C_{l,k} − log C_{e,k}` (`interlacingOffset`), formule exacte (`interlacingOffset_eq`) ;
* lecture de fréquence par l'entrelacement : `δ_{k+1} − δ_k = π/T_l − π/T_e` (`interlacing_frequency_reading`), décalages
  strictement décroissants sur un passage qui monte (`interlacingOffset_strictAnti`) ;
* signe imposé : en tout point `x`, la contribution du suivant vaut `−(−1)^k a_l(x) cos(T_l(log x − log C_{e,k} − δ_k))`,
  lue sur les contacts du précédent (`next_contribution_via_previous_contacts`) ; au contact `k` du précédent,
  `c_l(C_{e,k}) = −(−1)^k a_l cos(T_l δ_k)` et `c_e·c_l = a_e a_l cos(T_l δ_k)` (`next_sign_at_previous_contact`,
  `contributions_product_at_previous_contact`) ;
* liaison imposée au premier contact : au contact d'indice zéro du suivant, la contribution du précédent est de même signe que
  celle du suivant (`previous_reinforces_at_next_first_contact`, par le demi-pas inter-Tours) ;
* raccord à l'événement premier partagé `M = p_min(e) = Occ(l)` (`next_contribution_at_shared_prime`) ;
* lecture récursive : le zéro suivant est restitué depuis le précédent et deux décalages (`recursive_reading`), et le long de
  toute suite de zéros les contacts sont cumulés par les décalages (`chain_contacts_cumulative`,
  `chain_recursive_reading`).
Portée : identités et identification, vraies pour toute position radiale ; la liaison détermine le signe relatif et restitue le
suivant depuis le précédent, elle ne fixe pas le décalage, donc pas la position radiale.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Décalage d'entrelacement et lecture de fréquence -/

/-- Décalage d'entrelacement à l'indice `k` : position logarithmique du contact du suivant relativement au précédent. -/
noncomputable def interlacingOffset (e l : TrueZero) (k : ℤ) : ℝ :=
  Real.log (contactMinusAt l k) - Real.log (contactMinusAt e k)

theorem interlacingOffset_eq (e l : TrueZero) (k : ℤ) :
    interlacingOffset e l k =
      (memberPhase l + (k : ℝ) * Real.pi) / rZeroHeight l.1 - (memberPhase e + (k : ℝ) * Real.pi) / rZeroHeight e.1 := by
  unfold interlacingOffset memberPhase; rw [log_contactMinusAt, log_contactMinusAt]

/-- **Lecture de fréquence par l'entrelacement** : `δ_{k+1} − δ_k = π/T_l − π/T_e`. -/
theorem interlacing_frequency_reading (e l : TrueZero) (k : ℤ) :
    interlacingOffset e l (k + 1) - interlacingOffset e l k = Real.pi / rZeroHeight l.1 - Real.pi / rZeroHeight e.1 := by
  unfold interlacingOffset
  have h1 := ringJump_logWidth l k (k + 1)
  have h2 := ringJump_logWidth e k (k + 1)
  unfold towerPitch at h1 h2
  push_cast at h1 h2
  linarith

/-- La fréquence du suivant est lue sur le précédent et deux décalages : `T_l = π/(π/T_e + δ_{k+1} − δ_k)`. -/
theorem height_from_interlacing (e l : TrueZero) (k : ℤ) :
    rZeroHeight l.1 =
      Real.pi / (Real.pi / rZeroHeight e.1 + (interlacingOffset e l (k + 1) - interlacingOffset e l k)) := by
  rw [interlacing_frequency_reading]
  have hT : rZeroHeight l.1 ≠ 0 := l.2.ne'
  field_simp
  ring

/-- Sur un passage qui monte, les décalages décroissent strictement : le suivant s'enroule en deçà du précédent. -/
theorem interlacingOffset_strictAnti (e l : TrueZero) (hT : rZeroHeight e.1 < rZeroHeight l.1) (k : ℤ) :
    interlacingOffset e l (k + 1) < interlacingOffset e l k := by
  have := interlacing_frequency_reading e l k
  have := winding_pitch_contracts e l hT
  linarith

/-! ## 2. Signe imposé de la contribution du suivant, lu sur les contacts du précédent -/

/-- **Contribution du suivant lue sur les contacts du précédent** : en tout `x > 0` et à tout indice `k`,
`c_l(x) = −(−1)^k a_l(x) cos(T_l(log x − log C_{e,k} − δ_k))`. -/
theorem next_contribution_via_previous_contacts (e l : TrueZero) {x : ℝ} (hx : 0 < x) (k : ℤ) :
    pairContribution l x =
      -((-1 : ℝ) ^ k * pairEnvelope l x *
        Real.cos (rZeroHeight l.1 * (Real.log x - Real.log (contactMinusAt e k) - interlacingOffset e l k))) := by
  rw [pairContribution_eq_envelope_cos l hx]
  have hl := log_contactMinusAt l k
  have hT : rZeroHeight l.1 ≠ 0 := l.2.ne'
  have harg : rZeroHeight l.1 * Real.log x - memberPhase l =
      rZeroHeight l.1 * (Real.log x - Real.log (contactMinusAt e k) - interlacingOffset e l k) + (k : ℝ) * Real.pi := by
    unfold interlacingOffset memberPhase
    rw [hl]; field_simp; ring
  rw [harg, Real.cos_add_int_mul_pi]
  ring

/-- **Au contact `k` du précédent**, `c_l(C_{e,k}) = −(−1)^k a_l cos(T_l δ_k)`. -/
theorem next_sign_at_previous_contact (e l : TrueZero) (k : ℤ) :
    pairContribution l (contactMinusAt e k) =
      -((-1 : ℝ) ^ k * pairEnvelope l (contactMinusAt e k) * Real.cos (rZeroHeight l.1 * interlacingOffset e l k)) := by
  rw [next_contribution_via_previous_contacts e l (contactMinusAt_positive e k) k, sub_self, zero_sub, mul_neg,
    Real.cos_neg]

/-- **Signe relatif** : au contact `k` du précédent, `c_e · c_l = a_e a_l cos(T_l δ_k)`. -/
theorem contributions_product_at_previous_contact (e l : TrueZero) (k : ℤ) :
    pairContribution e (contactMinusAt e k) * pairContribution l (contactMinusAt e k) =
      pairEnvelope e (contactMinusAt e k) * pairEnvelope l (contactMinusAt e k) *
        Real.cos (rZeroHeight l.1 * interlacingOffset e l k) := by
  have he := next_contribution_via_previous_contacts e e (contactMinusAt_positive e k) k
  have hself : interlacingOffset e e k = 0 := by unfold interlacingOffset; ring
  rw [hself, sub_self, sub_zero, mul_zero, Real.cos_zero, mul_one] at he
  rw [he, next_sign_at_previous_contact]
  have hsq : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
    rw [← mul_zpow]; norm_num
  linear_combination (pairEnvelope e (contactMinusAt e k) * pairEnvelope l (contactMinusAt e k) *
    Real.cos (rZeroHeight l.1 * interlacingOffset e l k)) * hsq

/-- **Liaison imposée au premier contact** : dès que la hauteur ne recule pas, au contact d'indice zéro du suivant la
contribution du précédent a le même signe que celle du suivant (le décalage est sous un demi-pas du précédent). -/
theorem previous_reinforces_at_next_first_contact (e l : TrueZero) (hT : rZeroHeight e.1 ≤ rZeroHeight l.1) :
    0 < pairContribution e (contactMinusAt l 0) * pairContribution l (contactMinusAt l 0) := by
  have hsep := interMemberLogSeparation_lt_half_pitch e l hT
  unfold interMemberLogSeparation towerPitch at hsep
  have hTe : 0 < rZeroHeight e.1 := e.2
  -- contribution du précédent lue sur le contact du suivant
  have hE := next_contribution_via_previous_contacts l e (contactMinusAt_positive l 0) 0
  have hL := next_contribution_via_previous_contacts l l (contactMinusAt_positive l 0) 0
  have hself : interlacingOffset l l 0 = 0 := by unfold interlacingOffset; ring
  rw [hself, sub_self, sub_zero, mul_zero, Real.cos_zero, mul_one] at hL
  rw [hE, hL]
  simp only [zpow_zero, one_mul]
  have hcos : 0 < Real.cos (rZeroHeight e.1 *
      (Real.log (contactMinusAt l 0) - Real.log (contactMinusAt l 0) - interlacingOffset l e 0)) := by
    apply Real.cos_pos_of_mem_Ioo
    have habs : |interlacingOffset l e 0| < Real.pi / rZeroHeight e.1 / 2 := by
      unfold interlacingOffset; rw [abs_sub_comm]; exact hsep
    rw [abs_lt] at habs
    have h2 : Real.pi / rZeroHeight e.1 / 2 * rZeroHeight e.1 = Real.pi / 2 := by field_simp
    constructor <;> nlinarith
  have hpe := pairEnvelope_pos e (contactMinusAt_positive l 0)
  have hpl := pairEnvelope_pos l (contactMinusAt_positive l 0)
  nlinarith [mul_pos (mul_pos hpe hpl) hcos]

/-! ## 3. Raccord à l'événement premier partagé -/

/-- **Raccord** : sur un passage, au premier partagé `M = p_min(e) = Occ(l)`, la contribution du suivant est lue sur les
contacts du précédent et le décalage d'entrelacement. -/
theorem next_contribution_at_shared_prime (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (k : ℤ) :
    occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
    pairContribution ⟨p.zLaterMember, hL⟩ (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) =
      -((-1 : ℝ) ^ k * pairEnvelope ⟨p.zLaterMember, hL⟩ (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) *
        Real.cos (rZeroHeight p.zLaterMember *
          (Real.log (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) - Real.log (contactMinusAt ⟨p.zEarlierMember, hE⟩ k) -
            interlacingOffset ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ k))) := by
  have hshared := (next_zero_reads_previous p hE hL).2.2.1
  refine ⟨hshared, ?_⟩
  have hpos : (0 : ℝ) < (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) := by
    rw [hshared]; exact_mod_cast (expectedMinimumPrime_prime _).pos
  exact next_contribution_via_previous_contacts _ _ hpos k

/-! ## 4. Lecture récursive -/

/-- **Lecture récursive sur un passage** : le zéro suivant est restitué depuis le précédent et deux décalages
d'entrelacement consécutifs : `T_l = π/(π/T_e + δ_{k+1} − δ_k)` et `β_l = T_l / tan(T_l (log C_{e,k} + δ_k))`. -/
theorem recursive_reading (e l : TrueZero) (k : ℤ) :
    rZeroHeight l.1 =
        Real.pi / (Real.pi / rZeroHeight e.1 + (interlacingOffset e l (k + 1) - interlacingOffset e l k)) ∧
      rZeroRadialPosition l.1 =
        rZeroHeight l.1 / Real.tan (rZeroHeight l.1 * (Real.log (contactMinusAt e k) + interlacingOffset e l k)) := by
  refine ⟨height_from_interlacing e l k, ?_⟩
  have h := (inversion_from_consecutive_contacts l k).2
  have hc : Real.log (contactMinusAt e k) + interlacingOffset e l k = Real.log (contactMinusAt l k) := by
    unfold interlacingOffset; ring
  rw [hc]; exact h.symm

/-- **Contacts cumulés le long d'une suite de zéros** : `log C_{z_n,k} = log C_{z_0,k} + Σ_{j<n} δ_k(z_j, z_{j+1})`. -/
theorem chain_contacts_cumulative (z : ℕ → TrueZero) (k : ℤ) (n : ℕ) :
    Real.log (contactMinusAt (z n) k) =
      Real.log (contactMinusAt (z 0) k) + ∑ j ∈ Finset.range n, interlacingOffset (z j) (z (j + 1)) k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    unfold interlacingOffset; ring

/-- **Lecture récursive le long d'une suite** : chaque zéro `z_n` est restitué depuis `z_0` et les décalages cumulés à deux
indices consécutifs. -/
theorem chain_recursive_reading (z : ℕ → TrueZero) (k : ℤ) (n : ℕ) :
    rZeroHeight (z n).1 =
        Real.pi / (Real.log (contactMinusAt (z 0) (k + 1)) - Real.log (contactMinusAt (z 0) k) +
          (∑ j ∈ Finset.range n, interlacingOffset (z j) (z (j + 1)) (k + 1) -
            ∑ j ∈ Finset.range n, interlacingOffset (z j) (z (j + 1)) k)) ∧
      rZeroRadialPosition (z n).1 =
        rZeroHeight (z n).1 / Real.tan (rZeroHeight (z n).1 *
          (Real.log (contactMinusAt (z 0) k) + ∑ j ∈ Finset.range n, interlacingOffset (z j) (z (j + 1)) k)) := by
  have hk := chain_contacts_cumulative z k n
  have hk1 := chain_contacts_cumulative z (k + 1) n
  have hinv := inversion_from_consecutive_contacts (z n) k
  refine ⟨?_, ?_⟩
  · have hw := ringJump_logWidth (z n) k (k + 1)
    unfold towerPitch at hw; push_cast at hw
    have hT : rZeroHeight (z n).1 ≠ 0 := (z n).2.ne'
    have hden : Real.log (contactMinusAt (z 0) (k + 1)) - Real.log (contactMinusAt (z 0) k) +
        (∑ j ∈ Finset.range n, interlacingOffset (z j) (z (j + 1)) (k + 1) -
          ∑ j ∈ Finset.range n, interlacingOffset (z j) (z (j + 1)) k) = Real.pi / rZeroHeight (z n).1 := by
      linarith
    rw [hden]; field_simp
  · rw [← hk]; exact hinv.2.symm

end RHV6Fresh

#print axioms RHV6Fresh.interlacing_frequency_reading
#print axioms RHV6Fresh.next_contribution_via_previous_contacts
#print axioms RHV6Fresh.contributions_product_at_previous_contact
#print axioms RHV6Fresh.previous_reinforces_at_next_first_contact
#print axioms RHV6Fresh.next_contribution_at_shared_prime
#print axioms RHV6Fresh.recursive_reading
#print axioms RHV6Fresh.chain_recursive_reading
