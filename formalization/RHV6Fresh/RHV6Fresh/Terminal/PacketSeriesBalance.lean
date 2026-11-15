/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PacketChannelBridge

/-!
# Le bilan de la paire sur une série de pas consécutifs (E433, §19.48)

Module isolé (non ajouté à `RHV6Fresh.lean`). Le chaînon laissé par E432 est « le complément ne peut pas absorber,
sur la série des pas, le surplus intégré de la paire ». Ici le bilan exact de ce que le complément doit porter sur une
fenêtre de `m` pas consécutifs à partir de `a ≥ 2` est écrit, pour tout paquet puis pour la paire miroir (cas (a)).

* §1 Effondrement aux bords : la somme des incréments d'un paquet sur la fenêtre se télescope en deux pas locaux, celui
  de la fin moins celui du début (`packetIncrement_series_telescopes`) ; le contenu arithmétique de la fenêtre est la
  somme des poids de von Mangoldt moins la variation du pas du fond (`remainderIncrement_series_arithmetic`) ; bilan
  de série : complément = contenu arithmétique − effet de bords du paquet (`complement_series_balance`).
* §2 Pour la paire : primitive explicite des quatre membres (`pairPrimitive`), le pas local en forme close
  (`localPacket_pair_eq`), bilan de série de la paire (`pair_complement_series_balance`) : la paire n'entre dans la
  série que par sa primitive aux deux bords de la fenêtre (`pair_series_eq_boundary`) ; normes des membres de la
  primitive, `x^{1+(1/2+δ)}` pour le miroir et `x^{1+(1/2−δ)}` pour le zéro.

Aucune hypothèse posée, aucun `sorry`.
-/
open Real RHV3Lean

namespace RHV6Fresh

/-- Télescopage des incréments d'un paquet sur une fenêtre. -/
theorem packetIncrement_series_telescopes (S : Set ExplicitIndex) (a m : ℕ) :
    ∑ k ∈ Finset.range m, packetIncrement S (a + k) = localPacket S (a + m) - localPacket S a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    unfold packetIncrement
    rw [← add_assoc]
    ring

/-- Contenu arithmétique d'une fenêtre : somme des poids de von Mangoldt moins la variation du pas du fond. -/
theorem remainderIncrement_series_arithmetic (a m : ℕ) :
    ∑ k ∈ Finset.range m, remainderIncrement (a + k) =
      (∑ k ∈ Finset.range m, ((ArithmeticFunction.vonMangoldt (a + k + 1) : ℝ) : ℂ)) -
        (stepAt backgroundPrimitive (a + m) - stepAt backgroundPrimitive a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, remainderIncrement_arithmetic]
    rw [← add_assoc]
    ring

/-- Bilan de la série : complément = contenu arithmétique − effet de bords du paquet. -/
theorem complement_series_balance (S : Set ExplicitIndex) {a : ℕ} (ha : 2 ≤ a) (m : ℕ) :
    ∑ k ∈ Finset.range m, packetIncrement Sᶜ (a + k) =
      (∑ k ∈ Finset.range m, remainderIncrement (a + k)) -
        (localPacket S (a + m) - localPacket S a) := by
  rw [← packetIncrement_series_telescopes]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [remainderIncrement_eq_packet_add_complement S (by omega)]
  ring

namespace OffCarrier
variable (C : OffCarrier)

/-- Primitive explicite des quatre membres du paquet (cas (a)). -/
noncomputable def pairPrimitive (x : ℝ) : ℂ :=
  -(zetaZeroMultiplicity (zeroPoint C.zero) : ℂ) * (x : ℂ) *
    (zeroTerm C.zero x / (zeroPoint C.zero + 1) +
      (starRingEnd ℂ) (zeroTerm C.zero x / (zeroPoint C.zero + 1)) +
      zeroTerm (mirrorMember C.zero) x / (zeroPoint (mirrorMember C.zero) + 1) +
      (starRingEnd ℂ) (zeroTerm (mirrorMember C.zero) x / (zeroPoint (mirrorMember C.zero) + 1)))

theorem channelPrimitive_packet_eq (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) {x : ℝ} (hx : 1 < x) :
    channelPrimitive C.packet x = C.pairPrimitive x := by
  have hx0 : 0 < x := by linarith
  unfold channelPrimitive pairPrimitive
  rw [C.packet_channel_four_of_mirror h hx, residueTerm_conjIndex _ hx0, residueTerm_conjIndex _ hx0,
    residueTerm_eq_zeroTerm, residueTerm_eq_zeroTerm, C.mirror_multiplicity_eq]
  simp only [map_mul, map_neg, Complex.conj_natCast]
  ring

theorem localPacket_pair_eq (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) {N : ℕ} (hN : 2 ≤ N) :
    localPacket C.packet N = C.pairPrimitive ((N : ℝ) + 1) - C.pairPrimitive N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold localPacket stepAt
  rw [C.channelPrimitive_packet_eq h (by linarith), C.channelPrimitive_packet_eq h (by linarith)]

/-- Le complément de la paire sur une fenêtre : contenu arithmétique moins la primitive aux quatre points de bord. -/
theorem pair_complement_series_balance (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) {a : ℕ}
    (ha : 2 ≤ a) (m : ℕ) :
    ∑ k ∈ Finset.range m, packetIncrement C.packetᶜ (a + k) =
      (∑ k ∈ Finset.range m, remainderIncrement (a + k)) -
        ((C.pairPrimitive (((a + m : ℕ) : ℝ) + 1) - C.pairPrimitive ((a + m : ℕ) : ℝ)) -
          (C.pairPrimitive ((a : ℝ) + 1) - C.pairPrimitive a)) := by
  rw [complement_series_balance C.packet ha m, C.localPacket_pair_eq h (by omega), C.localPacket_pair_eq h ha]

/-- Norme du membre miroir de la primitive : `x^{2−β} / (‖ρ'‖ ‖ρ'+1‖)`. -/
theorem norm_mirror_primitive_term {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) * (zeroTerm (mirrorMember C.zero) x / (zeroPoint (mirrorMember C.zero) + 1))‖ =
      x ^ (1 + (1 / 2 + C.radialShift)) /
        (‖zeroPoint (mirrorMember C.zero)‖ * ‖zeroPoint (mirrorMember C.zero) + 1‖) := by
  rw [norm_mul, norm_div, norm_zeroTerm_eq _ hx, C.mirror_radial_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hx, Real.rpow_add hx (1 : ℝ), Real.rpow_one]
  field_simp

/-- Norme du membre du zéro : `x^{1+β}`. -/
theorem norm_zero_primitive_term {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) * (zeroTerm C.zero x / (zeroPoint C.zero + 1))‖ =
      x ^ (1 + (1 / 2 - C.radialShift)) / (‖zeroPoint C.zero‖ * ‖zeroPoint C.zero + 1‖) := by
  rw [norm_mul, norm_div, norm_zeroTerm_eq _ hx, C.zero_radial_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hx, Real.rpow_add hx (1 : ℝ), Real.rpow_one]
  field_simp

/-- **Effondrement aux bords pour la paire** : la somme de ses incréments sur une fenêtre ne lit que sa primitive aux
deux bords. -/
theorem pair_series_eq_boundary (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) {a : ℕ}
    (ha : 2 ≤ a) (m : ℕ) :
    ∑ k ∈ Finset.range m, packetIncrement C.packet (a + k) =
      (C.pairPrimitive (((a + m : ℕ) : ℝ) + 1) - C.pairPrimitive ((a + m : ℕ) : ℝ)) -
        (C.pairPrimitive ((a : ℝ) + 1) - C.pairPrimitive a) := by
  rw [packetIncrement_series_telescopes, C.localPacket_pair_eq h (by omega), C.localPacket_pair_eq h ha]

end OffCarrier

#print axioms packetIncrement_series_telescopes
#print axioms remainderIncrement_series_arithmetic
#print axioms complement_series_balance
#print axioms OffCarrier.localPacket_pair_eq
#print axioms OffCarrier.pair_complement_series_balance
#print axioms OffCarrier.pair_series_eq_boundary
#print axioms OffCarrier.norm_mirror_primitive_term

end RHV6Fresh
