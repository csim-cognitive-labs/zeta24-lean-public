/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.BoundaryContactReading
import RHV6Fresh.Terminal.RawSpectralChannel
import RHV6Fresh.Terminal.OffAmplificationAudit
import RHV6Fresh.Terminal.CompensationRigidity
import RHV6Fresh.Terminal.JointSignatureHorizon

/-!
# Audit de la rigidité du complément au premier partagé (E435, §19.50)

Module isolé (non ajouté à `RHV6Fresh.lean`). Question de l'auteur : la reconstruction arithmétique exacte aux
rencontres impose-t-elle au complément (`packetᶜ` du porteur, cas miroir) une rigidité déjà démontrée qui rende
impossible la dérive de la Tour OFF et de son miroir ? Aucune hypothèse posée, aucun `sorry` ; les sondes `False`
(S4) sont restées ouvertes et ne figurent pas ici (journal `experiments/E435_ComplementRigidityAudit/logs`).

* §S2 Transport vers la série : toute somme de fenêtre du complément est une différence de deux pas locaux
  (`complement_window_eq_boundary`), deux fenêtres consécutives se concatènent (`complement_windows_concat`), une
  suite quelconque de fenêtres ne lit que les bords (`complement_series_of_windows`) ; au niveau des primitives, le
  complément de toute partie est `x·reste lissé − primitive de la partie` (`channelPrimitive_compl_eq`).
* §S1 Bilan exact par contacts : l'effet de bords en un point est la lecture par les contacts des deux membres
  (`contactReading`, `pairPrimitive_re_eq_contactReading`) ; sur une fenêtre, partie réelle du complément = poids de
  von Mangoldt − variation réelle du fond − lecture par contacts aux quatre points de bord
  (`complement_window_re_by_contacts`). Valeur ponctuelle (`complement_value_eq`, `complementPrimitive_eq`).
* §S3 Contraintes retrouvées : cassure portée par le complément de la paire (`complement_break_lower_bound`, instance
  de `break_realized_by_high_frequencies`) ; exposant du reste au moins `1/2 + δ` (`remainderExponent_ge_mirror`) ;
  aucune borne du reste sous `1/2 + δ` (`no_remainder_bound_below_mirror`) ; l'exposant acquis est `1`
  (`acquired_exponent_admits_carrier`) ; une borne du complément seul ne transfère au reste que l'exposant
  `max(θ, 1/2 + δ)` (`norm_pairPrimitive_le`, `complement_bound_transfers`).
* Frontière en forme C : aucun porteur ⟺ `θ* = 1/2` (`no_offCarrier_iff_remainderExponent_half`).
-/
open Real RHV3Lean

namespace RHV6Fresh

/-! ## S2 : transport vers la série des rencontres -/

theorem complement_window_eq_boundary (S : Set ExplicitIndex) (a m : ℕ) :
    ∑ k ∈ Finset.range m, packetIncrement Sᶜ (a + k) = localPacket Sᶜ (a + m) - localPacket Sᶜ a :=
  packetIncrement_series_telescopes Sᶜ a m

theorem complement_windows_concat (S : Set ExplicitIndex) (a m m' : ℕ) :
    (∑ k ∈ Finset.range m, packetIncrement Sᶜ (a + k)) +
        ∑ k ∈ Finset.range m', packetIncrement Sᶜ (a + m + k) =
      ∑ k ∈ Finset.range (m + m'), packetIncrement Sᶜ (a + k) := by
  rw [Finset.sum_range_add]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [add_assoc]

theorem complement_series_of_windows (S : Set ExplicitIndex) (a m : ℕ → ℕ) (J : ℕ) :
    ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range (m j), packetIncrement Sᶜ (a j + k) =
      ∑ j ∈ Finset.range J, (localPacket Sᶜ (a j + m j) - localPacket Sᶜ (a j)) :=
  Finset.sum_congr rfl fun _ _ => packetIncrement_series_telescopes _ _ _

theorem channelPrimitive_compl_eq (S : Set ExplicitIndex) {x : ℝ} (hx : 1 < x) :
    channelPrimitive Sᶜ x = (x : ℂ) * smoothedRemainder x - channelPrimitive S x := by
  unfold channelPrimitive
  rw [smoothedRemainder_eq_tsum_residueTerm hx, channel_eq_packet_add_complement S hx]
  ring

namespace OffCarrier
variable (C : OffCarrier)

/-! ## S1 : bilan exact par contacts -/

noncomputable def contactReading (x : ℝ) : ℝ :=
  -2 * (zetaZeroMultiplicity (zeroPoint C.zero) : ℝ) * x *
    (contactRealValue (1 / 2 - C.radialShift) (rZeroHeight C.zero.1)
          (lastContactBefore (1 / 2 - C.radialShift) (rZeroHeight C.zero.1) x) *
        (x / contactAt (1 / 2 - C.radialShift) (rZeroHeight C.zero.1)
          (lastContactBefore (1 / 2 - C.radialShift) (rZeroHeight C.zero.1) x)) ^ (1 / 2 - C.radialShift) *
        ((1 / 2 - C.radialShift + 1) *
            Real.cos (Real.pi * cellFraction (1 / 2 - C.radialShift) (rZeroHeight C.zero.1) x) +
          rZeroHeight C.zero.1 *
            Real.sin (Real.pi * cellFraction (1 / 2 - C.radialShift) (rZeroHeight C.zero.1) x)) /
        Complex.normSq ((⟨1 / 2 - C.radialShift, rZeroHeight C.zero.1⟩ : ℂ) + 1) +
      contactRealValue (1 / 2 + C.radialShift) (rZeroHeight C.zero.1)
          (lastContactBefore (1 / 2 + C.radialShift) (rZeroHeight C.zero.1) x) *
        (x / contactAt (1 / 2 + C.radialShift) (rZeroHeight C.zero.1)
          (lastContactBefore (1 / 2 + C.radialShift) (rZeroHeight C.zero.1) x)) ^ (1 / 2 + C.radialShift) *
        ((1 / 2 + C.radialShift + 1) *
            Real.cos (Real.pi * cellFraction (1 / 2 + C.radialShift) (rZeroHeight C.zero.1) x) +
          rZeroHeight C.zero.1 *
            Real.sin (Real.pi * cellFraction (1 / 2 + C.radialShift) (rZeroHeight C.zero.1) x)) /
        Complex.normSq ((⟨1 / 2 + C.radialShift, rZeroHeight C.zero.1⟩ : ℂ) + 1))

theorem pairPrimitive_re_eq_contactReading {x : ℝ} (hx : 0 < x) :
    (C.pairPrimitive x).re = C.contactReading x :=
  C.pairPrimitive_re_from_contacts hx

theorem complement_window_re_by_contacts (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) {a : ℕ}
    (ha : 2 ≤ a) (m : ℕ) :
    (∑ k ∈ Finset.range m, packetIncrement C.packetᶜ (a + k)).re =
      (∑ k ∈ Finset.range m, (ArithmeticFunction.vonMangoldt (a + k + 1) : ℝ)) -
        (stepAt backgroundPrimitive (a + m) - stepAt backgroundPrimitive a).re -
        ((C.contactReading (((a + m : ℕ) : ℝ) + 1) - C.contactReading ((a + m : ℕ) : ℝ)) -
          (C.contactReading ((a : ℝ) + 1) - C.contactReading a)) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have ham : (0 : ℝ) < ((a + m : ℕ) : ℝ) := by exact_mod_cast (show 0 < a + m by omega)
  rw [C.pair_window_re_balance h ha m, C.pairPrimitive_re_eq_contactReading (by linarith),
    C.pairPrimitive_re_eq_contactReading ham, C.pairPrimitive_re_eq_contactReading (by linarith),
    C.pairPrimitive_re_eq_contactReading ha0]

/-! ## S2 (suite) : la valeur ponctuelle du complément -/

theorem complement_value_eq (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) {N : ℕ} (hN : 2 ≤ N) :
    localPacket C.packetᶜ N = exactRemainder N - (C.pairPrimitive ((N : ℝ) + 1) - C.pairPrimitive N) := by
  rw [← C.localPacket_pair_eq h hN, exactRemainder_eq_packet_add_complement C.packet hN]
  ring

theorem complementPrimitive_eq (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) {x : ℝ} (hx : 1 < x) :
    channelPrimitive C.packetᶜ x = (x : ℂ) * smoothedRemainder x - C.pairPrimitive x := by
  rw [channelPrimitive_compl_eq _ hx, C.channelPrimitive_packet_eq h hx]

/-! ## S3 : contraintes indépendantes retrouvées -/

open Classical in
theorem complement_break_lower_bound (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) {N : ℕ}
    (hN : 2 ≤ N) :
    (ArithmeticFunction.vonMangoldt (N + 1) : ℝ) - 1 - 4 * trivialTailConstant -
        ∑ ρ ∈ ({memberIndex C.zero, memberIndex (mirrorMember C.zero), conjIndex C.zero,
          conjIndex (mirrorMember C.zero)} : Finset ExplicitIndex), (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤
      ‖packetIncrement C.packetᶜ N‖ := by
  have hb := break_realized_by_high_frequencies ({memberIndex C.zero, memberIndex (mirrorMember C.zero),
    conjIndex C.zero, conjIndex (mirrorMember C.zero)} : Finset ExplicitIndex) hN
  have hs : (↑({memberIndex C.zero, memberIndex (mirrorMember C.zero), conjIndex C.zero,
      conjIndex (mirrorMember C.zero)} : Finset ExplicitIndex) : Set ExplicitIndex) = C.packet := by
    rw [C.packet_eq_four_of_mirror h]
    push_cast
    rfl
  rwa [hs] at hb

theorem remainderExponent_ge_mirror : 1 / 2 + C.radialShift ≤ remainderExponent := by
  have hl := (off_signature_lifts_remainderExponent C.zero C.zero_low).1
  rw [C.zero_radial_eq] at hl
  linarith

theorem no_remainder_bound_below_mirror {θ K : ℝ} (hθ : θ < 1 / 2 + C.radialShift)
    (hK : ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ K * x ^ θ) : False :=
  infinite_complement_closes C.zero ⟨θ, K, by rw [C.zero_radial_eq]; linarith, hK⟩

theorem acquired_exponent_admits_carrier :
    (1 : ℝ) ∈ remainderExponents ∧ ¬ ((1 : ℝ) < 1 / 2 + C.radialShift) := by
  have := acquired_exponent_not_below_mirror C.zero
  rw [C.zero_radial_eq] at this
  refine ⟨one_mem_remainderExponents, ?_⟩
  have := this.2
  intro hc; apply this; linarith

/-- Norme de la primitive de la paire : au plus une constante fois `x^{1+(1/2+δ)}` pour `x ≥ 1`. -/
theorem norm_pairPrimitive_le {x : ℝ} (hx : 1 ≤ x) :
    ‖C.pairPrimitive x‖ ≤
      2 * (zetaZeroMultiplicity (zeroPoint C.zero) : ℝ) *
        (1 / (‖zeroPoint C.zero‖ * ‖zeroPoint C.zero + 1‖) +
          1 / (‖zeroPoint (mirrorMember C.zero)‖ * ‖zeroPoint (mirrorMember C.zero) + 1‖)) *
        x ^ (1 + (1 / 2 + C.radialShift)) := by
  have hx0 : 0 < x := by linarith
  set u := (x : ℂ) * (zeroTerm C.zero x / (zeroPoint C.zero + 1)) with hu
  set v := (x : ℂ) * (zeroTerm (mirrorMember C.zero) x / (zeroPoint (mirrorMember C.zero) + 1)) with hv
  have hrepr : C.pairPrimitive x = -(zetaZeroMultiplicity (zeroPoint C.zero) : ℂ) *
      (u + (starRingEnd ℂ) u + v + (starRingEnd ℂ) v) := by
    unfold pairPrimitive
    rw [hu, hv]
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have hu' := C.norm_zero_primitive_term hx0
  have hv' := C.norm_mirror_primitive_term hx0
  rw [← hu] at hu'
  rw [← hv] at hv'
  have hδ := C.radialShift_pos
  have hzn := zeroPoint_norm_pos C.zero
  have hzn1 : 0 < ‖zeroPoint C.zero + 1‖ := norm_pos_iff.mpr (zeroPoint_add_one_ne_zero C.zero)
  have hmn := zeroPoint_norm_pos (mirrorMember C.zero)
  have hmn1 : 0 < ‖zeroPoint (mirrorMember C.zero) + 1‖ :=
    norm_pos_iff.mpr (zeroPoint_add_one_ne_zero (mirrorMember C.zero))
  have hpow : x ^ (1 + (1 / 2 - C.radialShift)) ≤ x ^ (1 + (1 / 2 + C.radialShift)) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hupow : ‖u‖ ≤ x ^ (1 + (1 / 2 + C.radialShift)) / (‖zeroPoint C.zero‖ * ‖zeroPoint C.zero + 1‖) := by
    rw [hu']
    exact div_le_div_of_nonneg_right hpow (by positivity)
  have hm0 : (0 : ℝ) ≤ zetaZeroMultiplicity (zeroPoint C.zero) := by positivity
  rw [hrepr, norm_mul, norm_neg, Complex.norm_natCast]
  calc (zetaZeroMultiplicity (zeroPoint C.zero) : ℝ) * ‖u + (starRingEnd ℂ) u + v + (starRingEnd ℂ) v‖
      ≤ (zetaZeroMultiplicity (zeroPoint C.zero) : ℝ) * (‖u‖ + ‖u‖ + ‖v‖ + ‖v‖) := by
        gcongr
        calc ‖u + (starRingEnd ℂ) u + v + (starRingEnd ℂ) v‖
            ≤ ‖u + (starRingEnd ℂ) u + v‖ + ‖(starRingEnd ℂ) v‖ := norm_add_le _ _
          _ ≤ (‖u + (starRingEnd ℂ) u‖ + ‖v‖) + ‖(starRingEnd ℂ) v‖ := by gcongr; exact norm_add_le _ _
          _ ≤ ((‖u‖ + ‖(starRingEnd ℂ) u‖) + ‖v‖) + ‖(starRingEnd ℂ) v‖ := by gcongr; exact norm_add_le _ _
          _ = ‖u‖ + ‖u‖ + ‖v‖ + ‖v‖ := by rw [RCLike.norm_conj, RCLike.norm_conj]
    _ ≤ (zetaZeroMultiplicity (zeroPoint C.zero) : ℝ) *
          (2 * (x ^ (1 + (1 / 2 + C.radialShift)) / (‖zeroPoint C.zero‖ * ‖zeroPoint C.zero + 1‖)) +
            2 * (x ^ (1 + (1 / 2 + C.radialShift)) /
              (‖zeroPoint (mirrorMember C.zero)‖ * ‖zeroPoint (mirrorMember C.zero) + 1‖))) :=
        mul_le_mul_of_nonneg_left (by rw [hv']; linarith [hupow]) hm0
    _ = _ := by ring

/-- **Une borne du complément seul ne transfère au reste lissé que l'exposant `max(θ, 1/2+δ)`.** -/
theorem complement_bound_transfers (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) {θ K : ℝ}
    (hK : ∀ x : ℝ, 1 < x → ‖channelPrimitive C.packetᶜ x‖ ≤ K * x ^ (1 + θ)) :
    ∃ K' : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ K' * x ^ (max θ (1 / 2 + C.radialShift)) := by
  set D := 2 * (zetaZeroMultiplicity (zeroPoint C.zero) : ℝ) *
    (1 / (‖zeroPoint C.zero‖ * ‖zeroPoint C.zero + 1‖) +
      1 / (‖zeroPoint (mirrorMember C.zero)‖ * ‖zeroPoint (mirrorMember C.zero) + 1‖)) with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hK0 : 0 ≤ K := by
    have h2 := hK 2 (by norm_num)
    have hp : 0 < (2 : ℝ) ^ (1 + θ) := Real.rpow_pos_of_pos (by norm_num) _
    by_contra hneg
    push Not at hneg
    have : K * (2 : ℝ) ^ (1 + θ) < 0 := mul_neg_of_neg_of_pos hneg hp
    linarith [norm_nonneg (channelPrimitive C.packetᶜ 2)]
  refine ⟨K + D, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hsplit : (x : ℂ) * smoothedRemainder x = channelPrimitive C.packetᶜ x + C.pairPrimitive x := by
    rw [C.complementPrimitive_eq h hx]; ring
  have hnorm : x * ‖smoothedRemainder x‖ = ‖(x : ℂ) * smoothedRemainder x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  have h1 : ‖channelPrimitive C.packetᶜ x‖ ≤ K * x ^ (1 + max θ (1 / 2 + C.radialShift)) :=
    (hK x hx).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith [le_max_left θ (1 / 2 + C.radialShift)])) hK0)
  have h2 : ‖C.pairPrimitive x‖ ≤ D * x ^ (1 + max θ (1 / 2 + C.radialShift)) :=
    (C.norm_pairPrimitive_le hx.le).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith [le_max_right θ (1 / 2 + C.radialShift)])) hD0)
  have htot : x * ‖smoothedRemainder x‖ ≤ (K + D) * x ^ (1 + max θ (1 / 2 + C.radialShift)) := by
    rw [hnorm, hsplit]
    calc ‖channelPrimitive C.packetᶜ x + C.pairPrimitive x‖
        ≤ ‖channelPrimitive C.packetᶜ x‖ + ‖C.pairPrimitive x‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  rw [Real.rpow_add hx0, Real.rpow_one] at htot
  have hxne : x ≠ 0 := hx0.ne'
  calc ‖smoothedRemainder x‖ = (x * ‖smoothedRemainder x‖) / x := by field_simp
    _ ≤ ((K + D) * (x * x ^ (max θ (1 / 2 + C.radialShift)))) / x :=
        div_le_div_of_nonneg_right htot hx0.le
    _ = (K + D) * x ^ (max θ (1 / 2 + C.radialShift)) := by field_simp

end OffCarrier

/-- **Frontière en forme C** : aucun porteur ⟺ `θ* = 1/2`. -/
theorem no_offCarrier_iff_remainderExponent_half : (OffCarrier → False) ↔ remainderExponent = 1 / 2 := by
  rw [← riemannHypothesis_iff_remainderExponent_eq_half]
  constructor
  · intro hno
    by_contra hNot
    obtain ⟨C⟩ := exists_offCarrier_of_not_riemannHypothesis hNot
    exact hno C
  · intro hRH C
    exact no_offCarrier_of_riemannHypothesis hRH C

#print axioms complement_series_of_windows
#print axioms channelPrimitive_compl_eq
#print axioms OffCarrier.complement_window_re_by_contacts
#print axioms OffCarrier.complementPrimitive_eq
#print axioms OffCarrier.complement_break_lower_bound
#print axioms OffCarrier.remainderExponent_ge_mirror
#print axioms OffCarrier.no_remainder_bound_below_mirror
#print axioms OffCarrier.complement_bound_transfers
#print axioms no_offCarrier_iff_remainderExponent_half

end RHV6Fresh
