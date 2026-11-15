/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FrequencyCap
import RHV6Fresh.Terminal.OffCarrier

/-!
# RHV6Fresh — Terminal/ThreeZeroWindow : l'écart encadré par le zéro précédent et le zéro suivant
(§19.16, 2026-10-30)

Module isolé (non ajouté à `RHV6Fresh.lean`). Il prolonge `FrequencyCap` : la liaison démontrée
rang → comptage analytique → fréquence → espacement des contacts est appliquée à la fenêtre de trois
zéros consécutifs, dans toutes les situations : membre quelconque, et paire OFF/miroir du porteur.

Tout est **inconditionnel** (RvM et comptage local du port `Zeta23`, aucune hypothèse RH).

## 1. Fenêtre générique de trois membres consécutifs (rangs `k+1`, `k+2`, `k+3`)
* `middle_bracketed` : le membre du milieu est entre le précédent et le suivant (ordre canonique).
* `three_window_bracketed` : les trois membres sont dans `[n, 2T]` sous les deux caps de `FrequencyCap`.
* `zerosIn_between_consecutive_empty`, `Ncount_between_consecutive_zero` : aucun zéro entre deux
  membres consécutifs ; le comptage de la bande ouverte est nul.
* `rvm_main_dominates` : le terme principal de Riemann–von Mangoldt dépasse l'erreur dès une hauteur
  explicite.
* `next_le_double` : **le zéro suivant est au plus au double du précédent** (dès une hauteur `T₁`) —
  l'écart `h(k+1) − h(k)` est borné par le zéro précédent (`gap_le_previous`), et la fenêtre de trois
  tient sous `4·h(k)` (`three_window_le_four`).
* `far_member_above_unit` : **le `m`-ième suivant est à plus d'une unité** dès que `m + 1` dépasse
  deux fois le comptage local — borne inférieure sur l'écart cumulé, par le comptage par fenêtre unité.
  (La borne inférieure sur l'écart *d'un seul pas* est strictement positive si et seulement si RH :
  `strict_frequency_cascade_iff_riemannHypothesis` ; elle n'est pas posée ici.)

## 2. La paire OFF/miroir du porteur, cas (a) : les trois événements `p_n, p_{n+1}, p_{n+2}`
* `mirror_height`, `nextMember_eq` : identités de rang.
* `three_events_bracketed` : **la fréquence du membre porté par `p_{n+2}` est strictement supérieure
  à celle de la paire et au plus son double** (dès `T₁`).
* `pair_two_places`, `pair_local_room` : la paire occupe deux places du comptage dans la fenêtre unité
  sous sa hauteur ; le comptage local doit donc y laisser deux places (condition de place, pas une
  contradiction : `caps_count_off_pairs_twice`).
* `pair_contacts_equal`, `next_contacts_bracketed` : les contacts de la paire sont au même pas ; les
  contacts du membre suivant sont entre `π/(2T)` et `π/T`.

Ce que ce module ne fait pas : il ne distingue pas ON de OFF (les caps sont aveugles à la position
radiale) ; il ne borne pas l'écart d'un seul pas par le bas ; il ne prouve pas `ContinuationForced`.
Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean Finset

/-! ## 1. Fenêtre générique de trois membres consécutifs -/

/-- Le membre du milieu est pris entre le précédent et le suivant. -/
theorem middle_bracketed (k : ℕ) :
    rZeroHeight (canonicalMember k).1 ≤ rZeroHeight (canonicalMember (k + 1)).1 ∧
    rZeroHeight (canonicalMember (k + 1)).1 ≤ rZeroHeight (canonicalMember (k + 1 + 1)).1 :=
  ⟨canonicalMember_height_mono (Nat.le_succ k), canonicalMember_height_mono (Nat.le_succ (k + 1))⟩

/-- **Les trois membres consécutifs de rangs `k+1`, `k+2`, `k+3` sont dans `[n, 2T]`** sous le plancher
(`lower_cap`, rang `k+1`) et le plafond (`upper_cap`, rang `k+3`). -/
theorem three_window_bracketed : ∃ A₀ C T₀ A₁ : ℝ, 1 ≤ A₀ ∧ 0 ≤ A₁ ∧ ∀ (k n : ℕ) (T : ℝ),
    (n : ℝ) * (A₀ * Real.log (n + 3)) < k + 1 → T₀ ≤ T → 1 ≤ T →
    ((k : ℝ) + 3) * (A₁ * Real.log (2 * T + 3)) < T / (2 * Real.pi) * Zeta23.ell1 T - C * Real.log T →
    (n : ℝ) < rZeroHeight (canonicalMember k).1 ∧
    rZeroHeight (canonicalMember k).1 ≤ rZeroHeight (canonicalMember (k + 1)).1 ∧
    rZeroHeight (canonicalMember (k + 1)).1 ≤ rZeroHeight (canonicalMember (k + 1 + 1)).1 ∧
    rZeroHeight (canonicalMember (k + 1 + 1)).1 ≤ 2 * T := by
  obtain ⟨A₀, hA1, hlow⟩ := lower_cap
  obtain ⟨C, T₀, A₁, hA1', hup⟩ := upper_cap
  refine ⟨A₀, C, T₀, A₁, hA1, hA1', fun k n T hn hT0 hT1 hT => ?_⟩
  refine ⟨hlow k n hn, (middle_bracketed k).1, (middle_bracketed k).2, ?_⟩
  have h3 : (((k + 1 + 1 : ℕ) : ℝ) + 1) = (k : ℝ) + 3 := by push_cast; ring
  have hT' : (((k + 1 + 1 : ℕ) : ℝ) + 1) * (A₁ * Real.log (2 * T + 3)) <
      T / (2 * Real.pi) * Zeta23.ell1 T - C * Real.log T := by
    rw [h3]; exact hT
  exact hup (k + 1 + 1) T hT0 hT1 hT'

/-- **Aucun zéro entre deux membres consécutifs** : la bande `]a, b]` avec `h(k) ≤ a` et `b < h(k+1)`
ne contient aucun zéro non trivial. -/
theorem zerosIn_between_consecutive_empty (k : ℕ) {a b : ℝ}
    (ha : rZeroHeight (canonicalMember k).1 ≤ a) (hb : b < rZeroHeight (canonicalMember (k + 1)).1) :
    Zeta23.zerosIn a b = ∅ := by
  ext ρ
  simp only [Zeta23.zerosIn, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hρ, hρa, hρb⟩
  have hk0 : 0 < rZeroHeight (canonicalMember k).1 := (canonicalMember k).2
  have hmem : ρ ∈ upperWindow b := by
    rw [mem_upperWindow_iff_zerosIn]
    exact ⟨hρ, by linarith, hρb⟩
  obtain ⟨w, rfl, _⟩ := mem_upperWindow_iff.mp hmem
  obtain ⟨m, rfl⟩ := canonicalMember_surjective w
  rw [zeroPoint_im] at hρa hρb
  rcases le_or_lt m k with hmk | hkm
  · have := canonicalMember_height_mono hmk; linarith
  · have := canonicalMember_height_mono (Nat.succ_le_of_lt hkm); linarith

/-- Le comptage de la bande ouverte entre deux membres consécutifs est nul. -/
theorem Ncount_between_consecutive_zero (k : ℕ) {a b : ℝ}
    (ha : rZeroHeight (canonicalMember k).1 ≤ a) (hb : b < rZeroHeight (canonicalMember (k + 1)).1) :
    Zeta23.Ncount a b = 0 := by
  unfold Zeta23.Ncount
  rw [zerosIn_between_consecutive_empty k ha hb, finsum_mem_empty]

/-- **Le terme principal de Riemann–von Mangoldt domine l'erreur** dès une hauteur explicite
`T₁ = max (T₀, 2π·e², (4π·max(C,0) + 1)²)`. -/
theorem rvm_main_dominates (C T₀ : ℝ) : ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T →
    T₀ ≤ T ∧ C * Real.log T < T / (2 * Real.pi) * Zeta23.ell1 T := by
  set K : ℝ := max C 0 with hK
  refine ⟨max (max T₀ (2 * Real.pi * Real.exp 2)) ((4 * Real.pi * K + 1) ^ 2), fun T hT => ?_⟩
  have hT0 : T₀ ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hT)
  have hTe : 2 * Real.pi * Real.exp 2 ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hT)
  have hTs : (4 * Real.pi * K + 1) ^ 2 ≤ T := le_trans (le_max_right _ _) hT
  have hpi := Real.pi_pos
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hK0 : 0 ≤ K := le_max_right _ _
  have hCK : C ≤ K := le_max_left _ _
  have hexp : 0 < Real.exp 2 := Real.exp_pos 2
  have he3 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
  have h18 : (18 : ℝ) ≤ 2 * Real.pi * Real.exp 2 := by
    have h1 : (2 : ℝ) * 3 * 3 ≤ 2 * Real.pi * 3 := by nlinarith
    have h2 : (2 : ℝ) * Real.pi * 3 ≤ 2 * Real.pi * Real.exp 2 :=
      mul_le_mul_of_nonneg_left he3 (by positivity)
    linarith
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  -- ℓ₁(T) ≥ 1
  have hl : 2 ≤ Zeta23.l T := by
    unfold Zeta23.l
    have : Real.exp 2 ≤ T / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log (T / (2 * Real.pi)) := Real.log_le_log hexp this
  have hell : 1 ≤ Zeta23.ell1 T := by
    unfold Zeta23.ell1
    have := Real.log_nonneg (one_le_two : (1 : ℝ) ≤ 2)
    linarith
  have hT2pi : 0 < T / (2 * Real.pi) := by positivity
  have h1 : T / (2 * Real.pi) ≤ T / (2 * Real.pi) * Zeta23.ell1 T := by
    calc T / (2 * Real.pi) = T / (2 * Real.pi) * 1 := (mul_one _).symm
      _ ≤ T / (2 * Real.pi) * Zeta23.ell1 T := mul_le_mul_of_nonneg_left hell hT2pi.le
  -- log T ≤ 2 √T
  have hsq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hlogT : Real.log T ≤ 2 * Real.sqrt T := by
    have h := Real.log_le_sub_one_of_pos hsq
    rw [Real.log_sqrt hTpos.le] at h
    linarith
  -- √T ≥ 4πK + 1
  have hsqrt : 4 * Real.pi * K + 1 ≤ Real.sqrt T := by
    have := Real.sqrt_le_sqrt hTs
    rwa [Real.sqrt_sq (by positivity)] at this
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hCl : C * Real.log T ≤ K * Real.log T := mul_le_mul_of_nonneg_right hCK hlog0
  have hKl : K * Real.log T ≤ K * (2 * Real.sqrt T) := mul_le_mul_of_nonneg_left hlogT hK0
  have hmain : 2 * K * Real.sqrt T < T / (2 * Real.pi) := by
    rw [lt_div_iff₀ (by positivity)]
    have hlt : 4 * Real.pi * K < Real.sqrt T := by linarith
    have hprod := mul_pos hsq (sub_pos.mpr hlt)
    have hs := Real.mul_self_sqrt hTpos.le
    nlinarith
  exact ⟨hT0, by linarith⟩

/-- **Le zéro suivant est au plus au double du précédent**, dès une hauteur `T₁` : sinon la bande
`]h(k), 2h(k)]` serait vide, contre le terme principal de Riemann–von Mangoldt. Inconditionnel. -/
theorem next_le_double : ∃ T₁ : ℝ, ∀ k : ℕ, T₁ ≤ rZeroHeight (canonicalMember k).1 →
    rZeroHeight (canonicalMember (k + 1)).1 ≤ 2 * rZeroHeight (canonicalMember k).1 := by
  obtain ⟨C, T₀, hmain⟩ := (Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts).main
  obtain ⟨T₁, hT₁⟩ := rvm_main_dominates C T₀
  refine ⟨T₁, fun k hk => ?_⟩
  by_contra hgt
  have hgt' : 2 * rZeroHeight (canonicalMember k).1 < rZeroHeight (canonicalMember (k + 1)).1 :=
    not_le.mp hgt
  obtain ⟨hT0, hdom⟩ := hT₁ _ hk
  have hN := hmain _ hT0
  rw [Zeta23.zetaZeroConfig_N, Ncount_between_consecutive_zero k le_rfl hgt'] at hN
  simp only [Nat.cast_zero, zero_sub, abs_neg] at hN
  have := le_abs_self (rZeroHeight (canonicalMember k).1 / (2 * Real.pi) *
    Zeta23.ell1 (rZeroHeight (canonicalMember k).1))
  linarith

/-- **L'écart d'un pas est borné par le zéro précédent** : `h(k+1) − h(k) ≤ h(k)` dès `T₁`. -/
theorem gap_le_previous : ∃ T₁ : ℝ, ∀ k : ℕ, T₁ ≤ rZeroHeight (canonicalMember k).1 →
    rZeroHeight (canonicalMember (k + 1)).1 - rZeroHeight (canonicalMember k).1 ≤
      rZeroHeight (canonicalMember k).1 := by
  obtain ⟨T₁, h⟩ := next_le_double
  exact ⟨T₁, fun k hk => by have := h k hk; linarith⟩

/-- **La fenêtre de trois tient sous quatre fois le premier** : `h(k+2) ≤ 4·h(k)` dès `T₁`. -/
theorem three_window_le_four : ∃ T₁ : ℝ, ∀ k : ℕ, T₁ ≤ rZeroHeight (canonicalMember k).1 →
    rZeroHeight (canonicalMember (k + 1 + 1)).1 ≤ 4 * rZeroHeight (canonicalMember k).1 := by
  obtain ⟨T₁, h⟩ := next_le_double
  refine ⟨T₁, fun k hk => ?_⟩
  have h1 := h k hk
  have h2 := h (k + 1) (hk.trans (canonicalMember_height_mono (Nat.le_succ k)))
  linarith

/-- **Le `m`-ième suivant est à plus d'une unité** dès que `m + 1 > 2·A₀·log(h(k) + 4)` : les `m + 1`
membres `k, …, k+m` ne tiennent pas dans les deux fenêtres unité `]h−1, h]`, `]h, h+1]`. Borne
inférieure inconditionnelle sur l'écart cumulé, par le comptage local du port. -/
theorem far_member_above_unit : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (k m : ℕ),
    2 * (A₀ * Real.log (rZeroHeight (canonicalMember k).1 + 4)) < m + 1 →
    rZeroHeight (canonicalMember k).1 + 1 < rZeroHeight (canonicalMember (k + m)).1 := by
  obtain ⟨A₀, hA1, hA⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨A₀, hA1, fun k m hlt => ?_⟩
  by_contra hle
  have hle' : rZeroHeight (canonicalMember (k + m)).1 ≤ rZeroHeight (canonicalMember k).1 + 1 :=
    not_lt.mp hle
  set h := rZeroHeight (canonicalMember k).1 with hh
  have hpos : 0 < h := (canonicalMember k).2
  let S : Finset ℂ := (Finset.range (m + 1)).image (fun j => zeroPoint (canonicalMember (k + j)))
  have hmemW : ∀ j, j ≤ m → zeroPoint (canonicalMember (k + j)) ∈ upperWindow (h + 1) := by
    intro j hj
    have hhi : rZeroHeight (canonicalMember (k + j)).1 ≤ h + 1 :=
      (canonicalMember_height_mono (Nat.add_le_add_left hj k)).trans hle'
    exact mem_upperWindow_iff.mpr ⟨_, rfl, hhi⟩
  have hS : S ⊆ (Zeta23.zerosIn_finite (h - 1) (h + 1)).toFinset := by
    intro ρ hρ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hρ
    have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hmem := hmemW j hj'
    rw [mem_upperWindow_iff_zerosIn] at hmem
    rw [Set.Finite.mem_toFinset]
    simp only [Zeta23.zerosIn, Set.mem_setOf_eq] at hmem ⊢
    obtain ⟨hnt, _, hhi⟩ := hmem
    have hlo : h ≤ rZeroHeight (canonicalMember (k + j)).1 :=
      canonicalMember_height_mono (Nat.le_add_right k j)
    refine ⟨hnt, ?_, hhi⟩
    rw [zeroPoint_im]; linarith
  have hcard : S.card = m + 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i _ j _ hij
    have h' : canonicalMember (k + i) = canonicalMember (k + j) := by
      apply Subtype.ext; apply Subtype.ext; exact hij
    have := canonicalMember_injective h'
    omega
  have hN : m + 1 ≤ Zeta23.Ncount (h - 1) (h + 1) := by
    unfold Zeta23.Ncount
    rw [finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite (h - 1) (h + 1))]
    calc m + 1 = S.card := hcard.symm
      _ = ∑ _ρ ∈ S, 1 := Finset.card_eq_sum_ones S
      _ ≤ ∑ ρ ∈ S, Zeta23.zeroMult ρ := Finset.sum_le_sum (fun ρ hρ => by
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hρ
          rw [← zetaZeroMultiplicity_eq_zeroMult]
          exact one_le_multiplicity_of_mem_upperWindow
            (hmemW j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))))
      _ ≤ ∑ ρ ∈ (Zeta23.zerosIn_finite (h - 1) (h + 1)).toFinset, Zeta23.zeroMult ρ :=
          Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)
  have hsplit : Zeta23.Ncount (h - 1) (h + 1) = Zeta23.Ncount (h - 1) h + Zeta23.Ncount h (h + 1) :=
    Zeta23.Ncount_add (by linarith) (by linarith)
  have h1 := hA (h - 1)
  rw [show h - 1 + 1 = h by ring] at h1
  have h2 := hA h
  have hl1 : Real.log (|h - 1| + 3) ≤ Real.log (h + 4) := by
    apply Real.log_le_log (by positivity)
    have := abs_sub h 1
    rw [abs_of_pos hpos, abs_one] at this
    linarith
  have hl2 : Real.log (|h| + 3) ≤ Real.log (h + 4) := by
    rw [abs_of_pos hpos]; exact Real.log_le_log (by positivity) (by linarith)
  have hA0 : 0 ≤ A₀ := by linarith
  have hN' : ((m + 1 : ℕ) : ℝ) ≤ (Zeta23.Ncount (h - 1) (h + 1) : ℝ) := by exact_mod_cast hN
  rw [hsplit] at hN'
  push_cast at hN'
  have hm1 := mul_le_mul_of_nonneg_left hl1 hA0
  have hm2 := mul_le_mul_of_nonneg_left hl2 hA0
  linarith

/-! ## 2. La paire OFF/miroir du porteur : les trois événements `p_n`, `p_{n+1}`, `p_{n+2}` -/

namespace OffCarrier

variable (C : OffCarrier)

/-- Le membre de rang `n+2` (le sortant, miroir dans le cas (a)) a la hauteur du zéro OFF. -/
theorem mirror_height : rZeroHeight (canonicalMember (C.n + 1)).1 = rZeroHeight C.zero.1 :=
  C.outgoing_same_height

/-- Le membre porté par `p_{n+2}` est le membre canonique de rang `n+3`. -/
theorem nextMember_eq : C.nextMember.1 = (canonicalMember (C.n + 1 + 1)).1 := rfl

/-- **Les trois événements sont encadrés en fréquence** (cas (a), hauteur `≥ T₁`) : le membre porté
par `p_{n+2}` est strictement au-dessus de la paire et au plus à son double. Inconditionnel. -/
theorem three_events_bracketed : ∃ T₁ : ℝ, ∀ C : OffCarrier,
    C.outgoing.zLaterMember = (mirrorMember C.zero).1 → T₁ ≤ rZeroHeight C.zero.1 →
    rZeroHeight C.zero.1 < rZeroHeight C.nextMember.1 ∧
    rZeroHeight C.nextMember.1 ≤ 2 * rZeroHeight C.zero.1 := by
  obtain ⟨T₁, hT⟩ := next_le_double
  refine ⟨T₁, fun C h hC => ⟨?_, ?_⟩⟩
  · have hv : rZeroHeight C.postPassage.zEarlierMember < rZeroHeight C.postPassage.zLaterMember :=
      C.post_mirror_vertical h
    rw [C.postPassage_earlier_height] at hv
    exact hv
  · have := hT (C.n + 1) (by rw [C.mirror_height]; exact hC)
    rw [C.mirror_height] at this
    exact this

/-- **La paire occupe deux places du comptage** dans la fenêtre unité `]T−1, T]` sous sa hauteur `T`. -/
theorem pair_two_places : 2 ≤ Zeta23.Ncount (rZeroHeight C.zero.1 - 1) (rZeroHeight C.zero.1) := by
  set h := rZeroHeight C.zero.1 with hh
  have hpos : 0 < h := C.zero.2
  have hmh : rZeroHeight (mirrorMember C.zero).1 = h := mirrorMember_ordinate C.zero
  have hne : zeroPoint C.zero ≠ zeroPoint (mirrorMember C.zero) := by
    intro heq
    have := congrArg Complex.re heq
    rw [zeroPoint_re, zeroPoint_re, mirrorMember_radial] at this
    have hlow := C.low
    linarith
  let S : Finset ℂ := {zeroPoint C.zero, zeroPoint (mirrorMember C.zero)}
  have hcard : S.card = 2 := Finset.card_pair hne
  have hmemS : ∀ ρ ∈ S, ρ ∈ upperWindow h := by
    intro ρ hρ
    rcases Finset.mem_insert.mp hρ with rfl | hρ
    · exact mem_upperWindow_iff.mpr ⟨_, rfl, le_rfl⟩
    · rw [Finset.mem_singleton] at hρ; subst hρ
      exact mem_upperWindow_iff.mpr ⟨_, rfl, hmh.le⟩
  have hS : S ⊆ (Zeta23.zerosIn_finite (h - 1) h).toFinset := by
    intro ρ hρ
    have hw := hmemS ρ hρ
    rw [mem_upperWindow_iff_zerosIn] at hw
    rw [Set.Finite.mem_toFinset]
    simp only [Zeta23.zerosIn, Set.mem_setOf_eq] at hw ⊢
    obtain ⟨hnt, _, hle⟩ := hw
    refine ⟨hnt, ?_, hle⟩
    rcases Finset.mem_insert.mp hρ with rfl | hρ'
    · rw [zeroPoint_im]; linarith
    · rw [Finset.mem_singleton] at hρ'; subst hρ'
      rw [zeroPoint_im, hmh]; linarith
  unfold Zeta23.Ncount
  rw [finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite (h - 1) h)]
  calc 2 = S.card := hcard.symm
    _ = ∑ _ρ ∈ S, 1 := Finset.card_eq_sum_ones S
    _ ≤ ∑ ρ ∈ S, Zeta23.zeroMult ρ := Finset.sum_le_sum (fun ρ hρ => by
          rw [← zetaZeroMultiplicity_eq_zeroMult]
          exact one_le_multiplicity_of_mem_upperWindow (hmemS ρ hρ))
    _ ≤ ∑ ρ ∈ (Zeta23.zerosIn_finite (h - 1) h).toFinset, Zeta23.zeroMult ρ :=
          Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)

/-- **Condition de place** : le comptage local doit laisser deux places à la paire dans sa fenêtre
unité. C'est une condition, pas une contradiction (le comptage est aveugle à la position radiale). -/
theorem pair_local_room : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ C : OffCarrier,
    2 ≤ A₀ * Real.log (|rZeroHeight C.zero.1 - 1| + 3) := by
  obtain ⟨A₀, hA1, hA⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨A₀, hA1, fun C => ?_⟩
  have h1 := hA (rZeroHeight C.zero.1 - 1)
  rw [show rZeroHeight C.zero.1 - 1 + 1 = rZeroHeight C.zero.1 by ring] at h1
  have h2 : (2 : ℝ) ≤ Zeta23.Ncount (rZeroHeight C.zero.1 - 1) (rZeroHeight C.zero.1) := by
    exact_mod_cast C.pair_two_places
  linarith

/-- Les contacts du zéro OFF et de son miroir ont le même pas logarithmique `π/T`. -/
theorem pair_contacts_equal (k : ℤ) :
    Real.log (contactMinusAt (mirrorMember C.zero) (k + 1) / contactMinusAt (mirrorMember C.zero) k) =
    Real.log (contactMinusAt C.zero (k + 1) / contactMinusAt C.zero k) := by
  rw [contact_interval_eq, contact_interval_eq, mirrorMember_ordinate]

/-- **Les contacts du membre porté par `p_{n+2}` sont entre `π/(2T)` et `π/T`** (cas (a), hauteur
`≥ T₁`) : plus serrés que ceux de la paire, au plus deux fois plus serrés. -/
theorem next_contacts_bracketed : ∃ T₁ : ℝ, ∀ C : OffCarrier,
    C.outgoing.zLaterMember = (mirrorMember C.zero).1 → T₁ ≤ rZeroHeight C.zero.1 → ∀ k : ℤ,
    Real.pi / (2 * rZeroHeight C.zero.1) ≤
      Real.log (contactMinusAt C.nextMember (k + 1) / contactMinusAt C.nextMember k) ∧
    Real.log (contactMinusAt C.nextMember (k + 1) / contactMinusAt C.nextMember k) <
      Real.pi / rZeroHeight C.zero.1 := by
  obtain ⟨T₁, hT⟩ := three_events_bracketed
  refine ⟨T₁, fun C h hC k => ?_⟩
  obtain ⟨hlt, hle⟩ := hT C h hC
  exact ⟨contact_interval_ge_of_height_le hle k, contact_interval_lt_of_lt_height C.zero.2 hlt k⟩

end OffCarrier

end RHV6Fresh

#print axioms RHV6Fresh.three_window_bracketed
#print axioms RHV6Fresh.next_le_double
#print axioms RHV6Fresh.gap_le_previous
#print axioms RHV6Fresh.three_window_le_four
#print axioms RHV6Fresh.far_member_above_unit
#print axioms RHV6Fresh.OffCarrier.three_events_bracketed
#print axioms RHV6Fresh.OffCarrier.pair_local_room
#print axioms RHV6Fresh.OffCarrier.next_contacts_bracketed
