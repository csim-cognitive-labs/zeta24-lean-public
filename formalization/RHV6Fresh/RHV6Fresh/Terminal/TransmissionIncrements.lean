/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.WindowComparison

/-!
# Incréments d'une transmission entre mêmes extrémités (auteur, 2026-10-11 ; E198)

E198 (`experiments/e198_transmissions_300.py`, hors Lean) mesure, sur les 299 transmissions et les 831 fenêtres complètes
des trois cents premiers zéros, les incréments du fond, du signal arithmétique et du reste entre les MÊMES extrémités, la
contribution signée consommée par l'historique, le groupe suivant et le complément. Ce module formalise les identités
exactes correspondantes (canal lissé, seule représentation démontrée), sans prémisse :

* `remainder_increment_eq` : `ΔR = ΔS − ΔB` (premiers seuls, aucun zéro) ;
* `remainder_increment_split` : `ΔR = ΔP_H + ΔQ_H` ;
* `removal_increment_eq_tail_increment` : l'incrément du retrait exact `R − P_H` est l'incrément de la queue ;
* `transmission_increment_split` : `ΔR = ΔP_{T_e} + Δfibre]T_e, T_l] + ΔQ_{T_l}` (consommé + groupe suivant + complément) ;
* `history_increment_chain` : l'incrément consommé se télescope le long des transmissions ;
* `removal_increment_le` : `‖Δ(R − P_H)‖ ≤ budget(H)·(a + b)` (exposant `1`, seul acquis).

Portée : identités et une majoration d'exposant `1` ; aucune régularité observée (E198) n'est posée en hypothèse.
-/

namespace RHV6Fresh

open RHV3Lean

/-- `R(b) − R(a) = (S(b) − S(a)) − (B(b) − B(a))` : incrément du reste = incrément du signal arithmétique moins incrément
du fond (premiers seuls). -/
theorem remainder_increment_eq (a b : ℝ) :
    smoothedRemainder b - smoothedRemainder a =
      (smoothedVonMangoldtSum b - smoothedVonMangoldtSum a) - (smoothedZeroBackground b - smoothedZeroBackground a) := by
  unfold smoothedRemainder; ring

/-- `ΔR = ΔP_H + ΔQ_H` entre deux abscisses `> 1`. -/
theorem remainder_increment_split (H : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    smoothedRemainder b - smoothedRemainder a =
      (precedingSum H b - precedingSum H a) + (followingSum H b - followingSum H a) := by
  rw [remainder_eq_preceding_add_following H ha, remainder_eq_preceding_add_following H hb]; ring

/-- L'incrément du retrait exact `R − P_H` entre deux abscisses est l'incrément de la queue `Q_H`. -/
theorem removal_increment_eq_tail_increment (H : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    (smoothedRemainder b - precedingSum H b) - (smoothedRemainder a - precedingSum H a) =
      followingSum H b - followingSum H a := by
  rw [remainder_eq_preceding_add_following H ha, remainder_eq_preceding_add_following H hb]; ring

/-- **Transmission** `T_e → T_l` : `ΔR = ΔP_{T_e} (consommé) + Δfibre]T_e, T_l] (groupe suivant) + ΔQ_{T_l} (complément)`. -/
theorem transmission_increment_split (He Hl : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    smoothedRemainder b - smoothedRemainder a =
      (precedingSum He b - precedingSum He a) + (nextFiberSum He Hl b - nextFiberSum He Hl a) +
        (followingSum Hl b - followingSum Hl a) := by
  rw [remainder_increment_split Hl ha hb]; unfold nextFiberSum; ring

/-- L'incrément consommé se télescope le long d'une suite de transmissions `h 0, …, h K`. -/
theorem history_increment_chain (h : ℕ → ℝ) (K : ℕ) (a b : ℝ) :
    (precedingSum (h K) b - precedingSum (h K) a) - (precedingSum (h 0) b - precedingSum (h 0) a) =
      ∑ i ∈ Finset.range K, (nextFiberSum (h i) (h (i + 1)) b - nextFiberSum (h i) (h (i + 1)) a) := by
  rw [Finset.sum_sub_distrib, ← fiber_chain_telescope, ← fiber_chain_telescope]; ring

/-- Majoration démontrée de l'incrément du retrait : `‖Δ(R − P_H)‖ ≤ budget(H)·(a + b)` (exposant `1`). -/
theorem removal_increment_le (H : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    ‖(smoothedRemainder b - precedingSum H b) - (smoothedRemainder a - precedingSum H a)‖ ≤
      followingBudget H * (a + b) := by
  rw [removal_increment_eq_tail_increment H ha hb]; exact tail_window_increment_bound H ha hb

#print axioms remainder_increment_eq
#print axioms remainder_increment_split
#print axioms removal_increment_eq_tail_increment
#print axioms transmission_increment_split
#print axioms history_increment_chain
#print axioms removal_increment_le

end RHV6Fresh
