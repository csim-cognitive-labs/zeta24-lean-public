/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CollectiveGapRecomposition

/-!
# RHV6Fresh — Terminal/GapSlopeByContacts : la pente de l'écart reconstituée par les contacts, les
intervalles et leurs signes
(E438, §19.55–19.56, 2026-11-07 ; module isolé, NON importé par `RHV6Fresh.lean` ; aucune hypothèse,
aucun axiome, aucun `sorry`, aucune position radiale, aucune famille de Tours, aucune somme de
contributions, aucune théorie spectrale)

Ordre de l'auteur (§19.55) : expliquer UNIQUEMENT avec les contacts, les intervalles et leurs signes la
reconstitution des écarts. Objets : UNE Tour, SES contacts (`contactAt`, signe `(−1)^k` porté par
`contactRealValue`), les pièces qu'ils découpent dans un écart (reste initial, cellules entières, reste
final : `GapPartialRemainders`), la demande brute `rawDemand x = ψ(x) − x` lue comme PENTE.

## R1–R2. La pente sur toute pièce
* `rawDemand_variation` : sur toute pièce `[a, b]`, la demande varie de (poids des entiers franchis) −
  (longueur) : descente d'une unité par unité de longueur, plus le poids de chaque entier franchi ;
* `rawDemand_pure_descent` : sans poids franchi, la pièce est une descente pure.

## R3. Longueur et demande de l'écart découpées par les mêmes contacts
* `gap_length_eq_pieces` : la longueur de l'écart est reste initial + cellules entières + reste final ;
* `gap_demand_eq_pieces` : la demande de l'écart se découpe par les mêmes contacts.

## R4. Aucune pièce intérieure ne franchit un premier ; le poids de la rencontre est dans le reste final
* `no_prime_crossed_inside_gap`, `inner_piece_variation` : une pièce strictement intérieure à l'écart ne
  franchit aucun premier : descente de sa longueur, poids non premiers seulement ;
* `finalRemainder_carries_meeting` : dès que le dernier contact est strictement avant la rencontre, le
  reste final vaut `log p_{n+1}` + (poids non premiers) − (sa longueur) : **la rencontre est dans le
  reste final, jamais dans une cellule entière ni dans le reste initial.**

## R5. Les signes des contacts qui bordent l'écart
* `contactRealValue_add_nat` : le `m`-ième contact après `k` porte le signe `(−1)^m` fois celui de `k` ;
* `gap_edge_contacts_sign` : le dernier contact de l'écart a le signe du premier contact de l'écart fois
  la parité du nombre de cellules entières.

## R6. Longueur linéaire d'une cellule ; les restes partiels sont plus courts que leur cellule
* `cell_linear_length` : une cellule mesure `C_k (e^{π/T} − 1)` ;
* `finalRemainder_shorter_than_cell`, `initialRemainder_shorter_than_cell`.

## R7. Le nombre de cellules entières est lu par la fréquence et le rapport des bords
* `wholeCellCount_bounds` : `|cellules + 1 − T·log(p_{n+1}/p_n)/π| < 1`.

## R8. Somme signée des longueurs de cellules
* `alternating_sum_bounds`, `signed_cells_bounded_by_last` : la somme signée (signes alternés) des
  longueurs de cellules consécutives a le signe de la dernière et ne dépasse pas la dernière cellule.

Rien ici ne parle de la position radiale ni d'aucune somme de Tours.
-/

namespace RHV6Fresh

open Real RHV3Lean ArithmeticFunction Finset

/-! ## R1–R2. La pente de la demande brute sur une pièce quelconque -/

theorem rawDemand_variation {a b : ℝ} (hab : a ≤ b) :
    rawDemand b - rawDemand a = ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, Λ n - (b - a) := by
  unfold rawDemand Chebyshev.psi
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊a⌋₊) hfl]
  ring

theorem rawDemand_pure_descent {a b : ℝ} (hab : a ≤ b)
    (h : ∀ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, Λ n = 0) :
    rawDemand b - rawDemand a = -(b - a) := by
  rw [rawDemand_variation hab, Finset.sum_eq_zero h]
  ring

/-! ## R3. Longueur et demande de l'écart découpées par les mêmes contacts -/

noncomputable def lengthC : ℝ → ℂ := fun x => (x : ℂ)

noncomputable def rawDemandC : ℝ → ℂ := fun x => ((rawDemand x : ℝ) : ℂ)

theorem gap_length_eq_pieces {β T : ℝ} {I : PrimeGapInterval} (h : GapHasContact β T I) :
    ((I.upper - I.lower : ℝ) : ℂ) =
      initialEdgeRemainder lengthC β T I + wholeCellSum lengthC β T I + finalEdgeRemainder lengthC β T I := by
  push_cast
  exact gap_variation_eq_remainders lengthC h

theorem gap_demand_eq_pieces {β T : ℝ} {I : PrimeGapInterval} (h : GapHasContact β T I) :
    ((rawDemand I.upper - rawDemand I.lower : ℝ) : ℂ) =
      initialEdgeRemainder rawDemandC β T I + wholeCellSum rawDemandC β T I +
        finalEdgeRemainder rawDemandC β T I := by
  push_cast
  exact gap_variation_eq_remainders rawDemandC h

/-! ## R4. Aucune pièce intérieure ne franchit un premier ; le poids de la rencontre est dans le reste final -/

theorem no_prime_crossed_inside_gap (I : PrimeGapInterval) {a b : ℝ} (ha : I.lower ≤ a) (hab : a ≤ b)
    (hb : b < I.upper) : ∀ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, ¬ Nat.Prime n := by
  intro n hn hp
  rw [Finset.mem_Ioc] at hn
  have h0 : (0 : ℝ) ≤ a := by linarith [I.one_lt_lower]
  have hlow : fnPrimeAtRank I.rank ≤ ⌊a⌋₊ := Nat.le_floor ha
  have hup : (n : ℝ) < fnPrimeAtRank (I.rank + 1) := by
    have h1 : (n : ℝ) ≤ (⌊b⌋₊ : ℝ) := by exact_mod_cast hn.2
    have h2 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (h0.trans hab)
    unfold PrimeGapInterval.upper at hb
    linarith
  have hup' : n < fnPrimeAtRank (I.rank + 1) := by exact_mod_cast hup
  exact thm_noPrimeStrictlyBetweenSuccessivePrimes I.rank hp (by omega) hup'

/-- Sur toute pièce intérieure à l'écart, la demande descend de la longueur et ne reçoit que des poids
d'entiers non premiers. -/
theorem inner_piece_variation (I : PrimeGapInterval) {a b : ℝ} (ha : I.lower ≤ a) (hab : a ≤ b)
    (hb : b < I.upper) :
    rawDemand b - rawDemand a =
      ∑ n ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun n => ¬ Nat.Prime n), Λ n - (b - a) := by
  rw [rawDemand_variation hab,
    Finset.filter_true_of_mem (no_prime_crossed_inside_gap I ha hab hb)]

theorem contactAt_mono {β T : ℝ} (hT : 0 < T) {k l : ℤ} (hkl : k ≤ l) :
    contactAt β T k ≤ contactAt β T l := by
  rw [contactAt_eq, contactAt_eq]
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ hT.le
  have : (k : ℝ) ≤ l := by exact_mod_cast hkl
  nlinarith [Real.pi_pos]

/-- Le poids de la rencontre `log p_{n+1}` tombe dans le reste final, avec les poids non premiers du reste
final et la descente de sa longueur. -/
theorem finalRemainder_carries_meeting {β T : ℝ} (hT : 0 < T) {I : PrimeGapInterval}
    (h : GapHasContact β T I)
    (hlt : contactAt β T (lastContactBefore β T I.upper) < I.upper) :
    finalEdgeRemainder rawDemandC β T I =
      ((Real.log (fnPrimeAtRank (I.rank + 1)) +
        ∑ n ∈ (Ioc ⌊contactAt β T (lastContactBefore β T I.upper)⌋₊
            (fnPrimeAtRank (I.rank + 1) - 1)).filter (fun n => ¬ Nat.Prime n), Λ n -
        (I.upper - contactAt β T (lastContactBefore β T I.upper)) : ℝ) : ℂ) := by
  set C := contactAt β T (lastContactBefore β T I.upper) with hC
  have hC0 : 0 ≤ C := (contactAt_pos β T _).le
  have hp2 := thm_primeAtRank_ge_two (I.rank + 1)
  set p := fnPrimeAtRank (I.rank + 1) with hp
  have hupper : I.upper = (p : ℝ) := rfl
  have hfl : ⌊C⌋₊ < p := (Nat.floor_lt hC0).mpr (by rw [← hupper]; exact hlt)
  have hfl' : ⌊C⌋₊ ≤ p - 1 := by omega
  unfold finalEdgeRemainder rawDemandC
  rw [← Complex.ofReal_sub, rawDemand_variation hlt.le]
  congr 1
  rw [hupper, Nat.floor_natCast]
  have hsplit : p = (p - 1) + 1 := by omega
  have hsum : ∑ n ∈ Ioc ⌊C⌋₊ p, Λ n = ∑ n ∈ Ioc ⌊C⌋₊ (p - 1), Λ n + Λ p := by
    conv_lhs => rw [hsplit]
    rw [Finset.sum_Ioc_succ_top hfl']
    rw [← hsplit]
  rw [hsum, vonMangoldt_apply_prime (thm_primeAtRank_isPrime _)]
  have hinner : ∑ n ∈ Ioc ⌊C⌋₊ (p - 1), Λ n =
      ∑ n ∈ (Ioc ⌊C⌋₊ (p - 1)).filter (fun n => ¬ Nat.Prime n), Λ n := by
    rw [Finset.filter_true_of_mem]
    intro n hn hprime
    rw [Finset.mem_Ioc] at hn
    have hlow : fnPrimeAtRank I.rank ≤ ⌊C⌋₊ := by
      apply Nat.le_floor
      have h1 : I.lower ≤ C := by
        rw [hC]
        have hl := lt_contact_succ (β := β) hT (by linarith [I.one_lt_lower] : 0 < I.lower)
        unfold GapHasContact at h
        exact hl.le.trans (contactAt_mono hT (by omega))
      exact h1
    have hsucc : fnPrimeSuccessor I.rank = p := rfl
    exact thm_noPrimeStrictlyBetweenSuccessivePrimes I.rank hprime (by omega) (by omega)
  rw [hinner]
  ring


/-! ## R5. Les signes des contacts qui bordent l'écart -/

theorem contactRealValue_add_nat {β T : ℝ} (hT : T ≠ 0) (k : ℤ) (m : ℕ) :
    contactRealValue β T (k + m) = (-Real.exp (β * Real.pi / T)) ^ m * contactRealValue β T k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (k + ((m + 1 : ℕ) : ℤ)) = (k + m) + 1 := by push_cast; ring
    rw [e, contactRealValue_succ hT, ih, pow_succ]
    ring

theorem gap_edge_contacts_sign {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) {I : PrimeGapInterval}
    (h : GapHasContact β T I) :
    0 < (-1 : ℝ) ^ (wholeCellCount β T I) *
      contactRealValue β T (lastContactBefore β T I.upper) *
        contactRealValue β T (firstContactAfterLower β T I) := by
  rw [← firstContact_add_count h, contactRealValue_add_nat hT.ne']
  set m := wholeCellCount β T I
  set v := contactRealValue β T (firstContactAfterLower β T I)
  set E := Real.exp (β * Real.pi / T)
  rw [neg_pow E m]
  have sq : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by rw [← mul_pow]; norm_num
  have hv : 0 < v * v := mul_self_pos.mpr (contactRealValue_ne_zero hβ _)
  have hE : 0 < E ^ m := pow_pos (Real.exp_pos _) m
  calc (0:ℝ) < ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) * (E ^ m * (v * v)) := by rw [sq, one_mul]; positivity
    _ = (-1 : ℝ) ^ m * ((-1 : ℝ) ^ m * E ^ m * v) * v := by ring

/-! ## R6. Longueur linéaire d'une cellule ; les restes partiels sont plus courts que leur cellule -/

theorem cell_linear_length {β T : ℝ} (hT : T ≠ 0) (k : ℤ) :
    contactAt β T (k + 1) - contactAt β T k = contactAt β T k * (Real.exp (Real.pi / T) - 1) := by
  have h := contactAt_ratio (β := β) hT k
  have hk : contactAt β T k ≠ 0 := (contactAt_pos β T k).ne'
  rw [div_eq_iff hk] at h
  rw [h]; ring

theorem finalRemainder_shorter_than_cell {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) :
    I.upper - contactAt β T (lastContactBefore β T I.upper) <
      contactAt β T (lastContactBefore β T I.upper) * (Real.exp (Real.pi / T) - 1) := by
  rw [← cell_linear_length hT.ne']
  have := lt_contact_succ (β := β) hT (by linarith [I.one_lt_upper] : 0 < I.upper)
  linarith

theorem initialRemainder_shorter_than_cell {β T : ℝ} (hT : 0 < T) (I : PrimeGapInterval) :
    contactAt β T (firstContactAfterLower β T I) - I.lower ≤
      contactAt β T (lastContactBefore β T I.lower) * (Real.exp (Real.pi / T) - 1) := by
  rw [← cell_linear_length hT.ne']
  unfold firstContactAfterLower
  have := lastContact_le (β := β) hT (by linarith [I.one_lt_lower] : 0 < I.lower)
  linarith

/-! ## R7. Le nombre de cellules entières est lu par la fréquence et le rapport des bords -/

theorem wholeCellCount_bounds {β T : ℝ} {I : PrimeGapInterval} (h : GapHasContact β T I) :
    |((wholeCellCount β T I : ℕ) : ℝ) + 1 - T * Real.log (I.upper / I.lower) / Real.pi| < 1 := by
  have hb := lastContact_difference_bounds β T (p := I.lower) (q := I.upper)
    (by linarith [I.one_lt_lower]) (by linarith [I.one_lt_upper])
  have hk := firstContact_add_count h
  unfold firstContactAfterLower at hk
  have hz : ((lastContactBefore β T I.upper - lastContactBefore β T I.lower : ℤ) : ℝ) =
      (wholeCellCount β T I : ℝ) + 1 := by
    have : lastContactBefore β T I.upper - lastContactBefore β T I.lower =
        (wholeCellCount β T I : ℤ) + 1 := by omega
    rw [this]; push_cast; ring
  rw [hz] at hb
  exact hb

/-! ## R8. Somme signée des longueurs de cellules : bornée par la dernière cellule -/

theorem alternating_sum_bounds (f : ℕ → ℝ) (hf : Monotone f) (h0 : 0 ≤ f 0) (m : ℕ) :
    0 ≤ (-1 : ℝ) ^ m * ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * f i ∧
      (-1 : ℝ) ^ m * ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * f i ≤ f m := by
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.sum_range_succ]
    have sq : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by rw [← mul_pow]; norm_num
    have e : (-1 : ℝ) ^ (m + 1) = -(-1 : ℝ) ^ m := by rw [pow_succ]; ring
    have key : (-1 : ℝ) ^ (m + 1) *
        (∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * f i + (-1 : ℝ) ^ (m + 1) * f (m + 1)) =
        -((-1 : ℝ) ^ m * ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * f i) + f (m + 1) := by
      rw [e]; linear_combination (f (m + 1)) * sq
    rw [key]
    have hmono := hf (Nat.le_succ m)
    constructor <;> linarith

theorem signed_cells_bounded_by_last {β T : ℝ} (hT : 0 < T) (k₀ : ℤ) (m : ℕ) :
    |∑ j ∈ range (m + 1), (-1 : ℝ) ^ j * (contactAt β T (k₀ + j + 1) - contactAt β T (k₀ + j))| ≤
      contactAt β T (k₀ + m + 1) - contactAt β T (k₀ + m) := by
  have hexp : 1 ≤ Real.exp (Real.pi / T) := Real.one_le_exp (by positivity)
  have hmono : Monotone (fun j : ℕ => contactAt β T (k₀ + j + 1) - contactAt β T (k₀ + j)) := by
    intro i j hij
    simp only
    rw [cell_linear_length hT.ne', cell_linear_length hT.ne']
    exact mul_le_mul_of_nonneg_right (contactAt_mono hT (by omega)) (by linarith)
  have h0 : 0 ≤ contactAt β T (k₀ + ((0:ℕ):ℤ) + 1) - contactAt β T (k₀ + ((0:ℕ):ℤ)) := by
    rw [cell_linear_length hT.ne']
    have := contactAt_pos β T (k₀ + ((0:ℕ):ℤ))
    exact mul_nonneg this.le (by linarith)
  obtain ⟨h1, h2⟩ := alternating_sum_bounds _ hmono h0 m
  rw [abs_le]
  rcases neg_one_pow_eq_or ℝ m with hu | hu
  · rw [hu, one_mul] at h1 h2; constructor <;> linarith
  · rw [hu, neg_one_mul] at h1 h2; constructor <;> linarith


#print axioms rawDemand_variation
#print axioms rawDemand_pure_descent
#print axioms gap_length_eq_pieces
#print axioms gap_demand_eq_pieces
#print axioms no_prime_crossed_inside_gap
#print axioms inner_piece_variation
#print axioms finalRemainder_carries_meeting
#print axioms contactRealValue_add_nat
#print axioms gap_edge_contacts_sign
#print axioms cell_linear_length
#print axioms finalRemainder_shorter_than_cell
#print axioms initialRemainder_shorter_than_cell
#print axioms wholeCellCount_bounds
#print axioms alternating_sum_bounds
#print axioms signed_cells_bounded_by_last

end RHV6Fresh
