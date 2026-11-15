/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RecompositionOnCells
import RHV6Fresh.Terminal.GapSlopeByContacts

/-!
# RHV6Fresh — Terminal/CollectiveSlopeOnPieces : le bilan collectif écrit en pentes de la demande sur les pièces
(E465, plan Φ étape Φ8, §19.95, 2026-11-09 ; module isolé, NON importé par `RHV6Fresh.lean` ;
aucune hypothèse, aucun axiome, aucun `sorry`)

E463 (K7) donnait, sur toute pièce, la somme des parts de tous les membres d'une recomposition arithmétique comme variation du signal
LISSÉ des premiers multiplié par l'abscisse. Ici ce membre arithmétique est écrit avec la demande brute d'E438, pièce par pièce.

* S1 `integratedSignal`, `mul_smoothedVonMangoldtSum_eq_integratedSignal` : l'abscisse fois le signal lissé est la somme, sur les
  entiers franchis depuis l'origine, du poids de chacun fois sa distance à l'abscisse.
* S2 `integratedSignal_variation` : sur une pièce, il varie du niveau de départ fois la longueur, plus chaque poids franchi fois sa
  distance à la fin de la pièce.
* S3 `demandArea`, `integratedSignal_variation_eq_demandArea` : terme principal retiré, c'est l'aire de la demande brute sur la pièce :
  demande au départ fois longueur, moins le demi-carré de la longueur (la descente de pente un d'E438), plus chaque poids franchi fois
  sa distance à la fin.
* S4 `demandArea_pure_descent` ; S5 `demandArea_add` (les aires s'ajoutent de pièce en pièce).
* S6 `demandArea_inner_piece` : à l'intérieur d'un écart, seuls des poids non premiers.
* S7 `demandArea_gap_piece_no_prime_weight` : sur toute pièce d'un écart allant jusqu'à la rencontre, le poids du premier de la
  rencontre entre avec une distance nulle : aucun poids premier dans l'aire d'un écart.
* S8 `demandArea_meeting` : sur une pièce qui franchit un seul entier, premier, son poids entre par sa distance à la fin de la pièce.
* S9 `short_piece_crosses_at_most_one` : une pièce plus courte qu'un pas d'entier franchit au plus un entier (leçon d'E464).
* S10 `residualBackground`, `collective_piece_slope_balance` : la somme des parts de tous les membres sur une pièce égale l'aire de la
  demande sur cette pièce, moins la variation du fond résiduel.
* S11 `contactAt_succ_eq_mul`, `member_contact_cell_eq_towerCellShare`, `collective_contact_cell_balance` : sur une cellule entre deux
  contacts consécutifs d'une Tour, le terme de cette Tour est sa part d'E463 et le total est l'aire de la demande sur la cellule.
* S12 `integratedDemandC`, `integratedDemandC_variation`, `gap_demandArea_eq_pieces`, `initialRemainder_eq_demandArea`,
  `finalRemainder_eq_demandArea`, `collective_gap_balance` : l'aire de la demande sur un écart se découpe par les contacts d'une Tour
  (reste initial, cellules entières, reste final), chaque reste étant une aire.

Portée : identités exactes, valables pour toute recomposition, sur la ligne comme hors ligne. Rien n'exclut un zéro hors ligne.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction Finset

/-! ## S1 : le signal intégré -/

noncomputable def integratedSignal (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (x - n)

theorem mul_smoothedVonMangoldtSum_eq_integratedSignal {x : ℝ} (hx : 0 < x) :
    (x : ℂ) * smoothedVonMangoldtSum x = ((integratedSignal x : ℝ) : ℂ) := by
  have hx0 : x ≠ 0 := hx.ne'
  have h1 : x * ∑ n ∈ Finset.range ⌈x⌉₊, Λ n * (1 - n / x) =
      ∑ n ∈ Finset.range ⌈x⌉₊, Λ n * (x - n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    first
    | (field_simp; done)
    | (field_simp; ring)
  have h2 : ∑ n ∈ Finset.range ⌈x⌉₊, Λ n * (x - n) =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n * (x - n) := by
    refine Finset.sum_subset (Finset.range_mono (Nat.ceil_le_floor_add_one x)) ?_
    intro n hn hn'
    rw [Finset.mem_range] at hn hn'
    have hle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp (by omega)
    have hge : x ≤ (n : ℝ) := Nat.ceil_le.mp (by omega)
    have hz : x - (n : ℝ) = 0 := by linarith
    rw [hz, mul_zero]
  have h3 : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (x - n) =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n * (x - n) := by
    refine Finset.sum_subset ?_ ?_
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_range]
      omega
    · intro n hn hn'
      rw [Finset.mem_range] at hn
      rw [Finset.mem_Ioc] at hn'
      have hn0 : n = 0 := by omega
      rw [hn0]
      simp
  rw [smoothedVonMangoldtSum_real', ← Complex.ofReal_mul]
  unfold integratedSignal
  rw [h1, h2, ← h3]

/-! ## S2 : variation du signal intégré sur une pièce -/

theorem integratedSignal_variation {a b : ℝ} (hab : a ≤ b) :
    integratedSignal b - integratedSignal a =
      Chebyshev.psi a * (b - a) + ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, Λ n * (b - n) := by
  unfold integratedSignal Chebyshev.psi
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊a⌋₊) hfl, Finset.sum_mul]
  have h : ∑ n ∈ Ioc 0 ⌊a⌋₊, Λ n * (b - n) - ∑ n ∈ Ioc 0 ⌊a⌋₊, Λ n * (a - n) =
      ∑ n ∈ Ioc 0 ⌊a⌋₊, Λ n * (b - a) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  linarith

/-! ## S3–S5 : l'aire de la demande brute sur une pièce -/

noncomputable def demandArea (a b : ℝ) : ℝ :=
  rawDemand a * (b - a) - (b - a) ^ 2 / 2 + ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, Λ n * (b - n)

theorem integratedSignal_variation_eq_demandArea {a b : ℝ} (hab : a ≤ b) :
    integratedSignal b - integratedSignal a - (b ^ 2 - a ^ 2) / 2 = demandArea a b := by
  rw [integratedSignal_variation hab]
  unfold demandArea rawDemand
  ring

theorem demandArea_pure_descent {a b : ℝ} (h : ∀ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, Λ n = 0) :
    demandArea a b = rawDemand a * (b - a) - (b - a) ^ 2 / 2 := by
  have hz : ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, Λ n * (b - n) = 0 :=
    Finset.sum_eq_zero fun n hn => by rw [h n hn, zero_mul]
  unfold demandArea
  rw [hz, add_zero]

theorem demandArea_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    demandArea a b + demandArea b c = demandArea a c := by
  rw [← integratedSignal_variation_eq_demandArea hab, ← integratedSignal_variation_eq_demandArea hbc,
    ← integratedSignal_variation_eq_demandArea (hab.trans hbc)]
  ring

/-! ## S6–S8 : les poids dans l'aire d'une pièce d'un écart -/

theorem demandArea_inner_piece (I : PrimeGapInterval) {a b : ℝ} (ha : I.lower ≤ a) (hab : a ≤ b)
    (hb : b < I.upper) :
    demandArea a b = rawDemand a * (b - a) - (b - a) ^ 2 / 2 +
      ∑ n ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun n => ¬ Nat.Prime n), Λ n * (b - n) := by
  unfold demandArea
  rw [Finset.filter_true_of_mem (no_prime_crossed_inside_gap I ha hab hb)]

theorem demandArea_gap_piece_no_prime_weight (I : PrimeGapInterval) {a : ℝ} (ha : I.lower ≤ a) :
    demandArea a I.upper = rawDemand a * (I.upper - a) - (I.upper - a) ^ 2 / 2 +
      ∑ n ∈ (Ioc ⌊a⌋₊ ⌊I.upper⌋₊).filter (fun n => ¬ Nat.Prime n), Λ n * (I.upper - n) := by
  unfold demandArea
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hp : Nat.Prime n
  · rw [if_neg (not_not.mpr hp)]
    rw [Finset.mem_Ioc] at hn
    have hlow : fnPrimeAtRank I.rank ≤ ⌊a⌋₊ := Nat.le_floor ha
    have hfl : ⌊I.upper⌋₊ = fnPrimeAtRank (I.rank + 1) := by
      rw [show I.upper = ((fnPrimeAtRank (I.rank + 1) : ℕ) : ℝ) from rfl]
      exact Nat.floor_natCast _
    have hle : n ≤ fnPrimeAtRank (I.rank + 1) := by omega
    have hnot : ¬ n < fnPrimeAtRank (I.rank + 1) := fun hlt =>
      thm_noPrimeStrictlyBetweenSuccessivePrimes I.rank hp (by omega) hlt
    have hn_eq : n = fnPrimeAtRank (I.rank + 1) := by omega
    have hz : I.upper - (n : ℝ) = 0 := by
      rw [hn_eq]
      exact sub_self _
    rw [hz, mul_zero]
  · rw [if_pos hp]

theorem demandArea_meeting {a b : ℝ} {p : ℕ} (hp : p.Prime) (ha : ⌊a⌋₊ + 1 = p) (hb : ⌊b⌋₊ = p) :
    demandArea a b = rawDemand a * (b - a) - (b - a) ^ 2 / 2 + Real.log p * (b - p) := by
  have h : Ioc ⌊a⌋₊ ⌊b⌋₊ = {p} := by
    ext n
    rw [Finset.mem_Ioc, Finset.mem_singleton]
    omega
  unfold demandArea
  rw [h, Finset.sum_singleton, vonMangoldt_apply_prime hp]

/-! ## S9 : une pièce plus courte qu'un pas d'entier franchit au plus un entier -/

theorem short_piece_crosses_at_most_one {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (h : b - a < 1) :
    ⌊b⌋₊ ≤ ⌊a⌋₊ + 1 := by
  have h1 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (ha.trans hab)
  have h2 : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  have h3 : (⌊b⌋₊ : ℝ) < ((⌊a⌋₊ + 2 : ℕ) : ℝ) := by
    push_cast
    linarith
  have h4 : ⌊b⌋₊ < ⌊a⌋₊ + 2 := by exact_mod_cast h3
  omega

/-! ## S10 : le bilan collectif d'une pièce, écrit avec l'aire de la demande -/

noncomputable def residualBackground (x : ℝ) : ℂ := smoothedZeroBackground x - (x : ℂ) / 2

theorem collective_piece_slope_balance {ι : Type*} (Rec : ArithmeticRecomposition ι) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) :
    ∑' i, Rec.weight i * (integratedKernel b (Rec.point i) - integratedKernel a (Rec.point i)) =
      ((demandArea a b : ℝ) : ℂ) -
        ((b : ℂ) * residualBackground b - (a : ℂ) * residualBackground a) := by
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hIb := mul_smoothedVonMangoldtSum_eq_integratedSignal (show 0 < b by linarith)
  have hIa := mul_smoothedVonMangoldtSum_eq_integratedSignal (show 0 < a by linarith)
  have hA : ((demandArea a b : ℝ) : ℂ) =
      (b : ℂ) * smoothedVonMangoldtSum b - (a : ℂ) * smoothedVonMangoldtSum a -
        ((b : ℂ) ^ 2 - (a : ℂ) ^ 2) / 2 := by
    rw [← integratedSignal_variation_eq_demandArea hab, hIb, hIa]
    first
    | (push_cast; ring)
    | push_cast
  rw [recomposition_piece_balance Rec ha hb, hA]
  unfold residualBackground
  ring

/-! ## S11 : sur une cellule entre deux contacts consécutifs d'une Tour -/

theorem contactAt_succ_eq_mul {β T : ℝ} (hT : T ≠ 0) (k : ℤ) :
    contactAt β T (k + 1) = contactAt β T k * Real.exp (π / T) := by
  have hk : contactAt β T k ≠ 0 := (contactAt_pos β T k).ne'
  rw [← contactAt_ratio (β := β) hT k]
  field_simp

theorem member_contact_cell_eq_towerCellShare {β T : ℝ} (hT : T ≠ 0) (w : ℂ) (k : ℤ) :
    w * (integratedKernel (contactAt β T (k + 1)) (towerPoint β T) -
        integratedKernel (contactAt β T k) (towerPoint β T)) =
      towerCellShare w β T (contactAt β T k) := by
  unfold towerCellShare
  rw [contactAt_succ_eq_mul hT k]

theorem collective_contact_cell_balance {ι : Type*} (Rec : ArithmeticRecomposition ι) {β T : ℝ}
    (hT : 0 < T) (k : ℤ) (h1 : 1 < contactAt β T k) :
    ∑' i, Rec.weight i * (integratedKernel (contactAt β T (k + 1)) (Rec.point i) -
        integratedKernel (contactAt β T k) (Rec.point i)) =
      ((demandArea (contactAt β T k) (contactAt β T (k + 1)) : ℝ) : ℂ) -
        ((contactAt β T (k + 1) : ℂ) * residualBackground (contactAt β T (k + 1)) -
          (contactAt β T k : ℂ) * residualBackground (contactAt β T k)) :=
  collective_piece_slope_balance Rec h1 (contactAt_mono hT (by omega))

/-! ## S12 : l'aire de la demande sur un écart, découpée par les contacts d'une Tour -/

noncomputable def integratedDemandC (x : ℝ) : ℂ := ((integratedSignal x - x ^ 2 / 2 : ℝ) : ℂ)

theorem integratedDemandC_variation {a b : ℝ} (hab : a ≤ b) :
    integratedDemandC b - integratedDemandC a = ((demandArea a b : ℝ) : ℂ) := by
  unfold integratedDemandC
  rw [← integratedSignal_variation_eq_demandArea hab, ← Complex.ofReal_sub]
  congr 1
  ring

theorem gap_demandArea_eq_pieces {β T : ℝ} {I : PrimeGapInterval} (h : GapHasContact β T I) :
    ((demandArea I.lower I.upper : ℝ) : ℂ) =
      initialEdgeRemainder integratedDemandC β T I + wholeCellSum integratedDemandC β T I +
        finalEdgeRemainder integratedDemandC β T I := by
  rw [← integratedDemandC_variation I.lower_lt_upper.le]
  exact gap_variation_eq_remainders integratedDemandC h

theorem initialRemainder_eq_demandArea {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) :
    initialEdgeRemainder integratedDemandC β T I =
      ((demandArea I.lower (contactAt β T (firstContactAfterLower β T I)) : ℝ) : ℂ) := by
  unfold initialEdgeRemainder
  exact integratedDemandC_variation (firstContact_gt_lower hT I).le

theorem finalRemainder_eq_demandArea {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) :
    finalEdgeRemainder integratedDemandC β T I =
      ((demandArea (contactAt β T (lastContactBefore β T I.upper)) I.upper : ℝ) : ℂ) := by
  unfold finalEdgeRemainder
  exact integratedDemandC_variation (lastContact_le_upper hT I)

theorem collective_gap_balance {ι : Type*} (Rec : ArithmeticRecomposition ι) (I : PrimeGapInterval) :
    ∑' i, Rec.weight i * (integratedKernel I.upper (Rec.point i) - integratedKernel I.lower (Rec.point i)) =
      ((demandArea I.lower I.upper : ℝ) : ℂ) -
        ((I.upper : ℂ) * residualBackground I.upper - (I.lower : ℂ) * residualBackground I.lower) :=
  collective_piece_slope_balance Rec I.one_lt_lower I.lower_lt_upper.le

#print axioms mul_smoothedVonMangoldtSum_eq_integratedSignal
#print axioms integratedSignal_variation_eq_demandArea
#print axioms demandArea_add
#print axioms demandArea_inner_piece
#print axioms demandArea_gap_piece_no_prime_weight
#print axioms demandArea_meeting
#print axioms short_piece_crosses_at_most_one
#print axioms collective_piece_slope_balance
#print axioms member_contact_cell_eq_towerCellShare
#print axioms collective_contact_cell_balance
#print axioms gap_demandArea_eq_pieces
#print axioms initialRemainder_eq_demandArea
#print axioms finalRemainder_eq_demandArea
#print axioms collective_gap_balance

end RHV6Fresh
