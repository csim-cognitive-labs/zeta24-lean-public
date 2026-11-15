/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ContactValueGeometry

/-!
# RHV6Fresh — valeurs réelles aux contacts : identités exactes, inversion tangentielle,
entrelacement
(objectif de l'auteur, 2026-11-03 ; module isolé, NON importé par `RHV6Fresh.lean`)

Objets : la valeur réelle d'une Tour `x^ρ/ρ` (`ρ = β + iT`, `β > 0`, `T > 0`) à son contact `C_k`
(`contactAt β T k = exp((arctan(T/β) + kπ)/T)`, passage sur l'axe réel : `contact_is_axis_passage`).

Résultats (tous inconditionnels, aucune prémisse, aucun `sorry`) :

* `towerValue_at_contact` : **la valeur au contact** est réelle et vaut
  `v_k = (−1)^k · C_k^β / ‖ρ‖` (signe `(−1)^k`, amplitude `C_k^β/‖ρ‖`).
* `contactRealValue_succ`, `contactRealValue_alternates` : **alternance** `v_{k+1} = −e^{βπ/T} v_k`,
  deux contacts consécutifs ont des valeurs de signes opposés ; `contactRealValue_mul_pos` : à même
  indice `k`, deux Tours quelconques ont le même signe.
* **Inversion tangentielle** : `height_of_contact_log_step` (`T = π/(log C_{k+1} − log C_k)`),
  `radial_of_contact_tangent` (`β = T / tan(T·log C_k − kπ)`),
  `radial_of_contact_value_ratio` (`β = T·log(|v_{k+1}|/|v_k|)/π`).
* **Enroulement** : `log_abs_contactRealValue` : `log|v_k|` est affine en `k`, pente `βπ/T`.
* **Entrelacement** : `interleaving_offset` (décalage exact entre contacts de deux Tours) ;
  `interleavingCount_bounds` : entre deux contacts consécutifs de `(β₁,T₁)` il y a `⌊T₂/T₁⌋` ou
  `⌈T₂/T₁⌉` contacts de `(β₂,T₂)`, quelles que soient `β₁, β₂` (le comptage est aveugle au radial) ;
  `contact_displacement_lt_half_step` : le déplacement d'un contact de `β` à `½` est inférieur à un
  demi-pas de la Tour déplacée (mais peut dépasser plusieurs pas d'une Tour plus haute : rien ici
  ne borne le rang dans la fusion) ; `mirror_contacts_coincide_iff` : les contacts d'une paire
  miroir `(β, 1−β)` à même hauteur coïncident si et seulement si `β = ½`.
* **Somme collective** : `collectiveAxisSum_at_contact` : au contact d'un membre, la somme de la
  famille se décompose en valeur propre réelle plus les autres Tours évaluées à la même position.

Portée : géométrie exacte des contacts sur l'axe réel. Aucune de ces identités n'exclut un zéro
OFF : elles décrivent où et avec quelle valeur chaque Tour passe sur l'axe, et comment ces passages
s'entrelacent ; la position radiale y entre par la phase `arctan(T/β)` et par l'amplitude `C_k^β`.
-/

namespace RHV6Fresh

open Real Complex

/-! ## 1. La valeur réelle au contact -/

/-- **Valeur réelle de la Tour `(β, T)` à son contact `k`** : `(−1)^k · C_k^β / ‖β + iT‖`. -/
noncomputable def contactRealValue (β T : ℝ) (k : ℤ) : ℝ :=
  (-1 : ℝ) ^ k * contactAt β T k ^ β / ‖(⟨β, T⟩ : ℂ)‖

theorem mk_ne_zero_of_re_pos {β T : ℝ} (hβ : 0 < β) : (⟨β, T⟩ : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem norm_mk_pos {β T : ℝ} (hβ : 0 < β) : 0 < ‖(⟨β, T⟩ : ℂ)‖ :=
  norm_pos_iff.mpr (mk_ne_zero_of_re_pos hβ)

/-- L'argument de `β + iT` (`β > 0`) est la phase `arctan(T/β)`. -/
theorem arg_mk_eq_towerPhase {β T : ℝ} (hβ : 0 < β) :
    Complex.arg (⟨β, T⟩ : ℂ) = towerPhase β T := by
  have h := Complex.tan_arg (⟨β, T⟩ : ℂ)
  have hlt : |Complex.arg (⟨β, T⟩ : ℂ)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hβ)
  rw [abs_lt] at hlt
  unfold towerPhase
  rw [← Real.arctan_tan hlt.1 hlt.2, h]

/-- La phase au contact : `T · log C_k = arctan(T/β) + kπ`. -/
theorem height_mul_log_contactAt {β T : ℝ} (hT : T ≠ 0) (k : ℤ) :
    T * Real.log (contactAt β T k) = towerPhase β T + k * Real.pi := by
  unfold contactAt windingContact towerPhase
  rw [Real.log_exp]
  field_simp

/-- `exp(i(arctan(T/β) + kπ)) = (−1)^k · ρ/‖ρ‖`. -/
theorem exp_I_phase_contact {β T : ℝ} (hβ : 0 < β) (k : ℤ) :
    Complex.exp (Complex.I * ((towerPhase β T + k * Real.pi : ℝ) : ℂ)) =
      (((-1 : ℝ) ^ k : ℝ) : ℂ) * ((⟨β, T⟩ : ℂ) / ‖(⟨β, T⟩ : ℂ)‖) := by
  have hn : (‖(⟨β, T⟩ : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_mk_pos (T := T) hβ).ne'
  have hpolar := Complex.norm_mul_exp_arg_mul_I (⟨β, T⟩ : ℂ)
  rw [arg_mk_eq_towerPhase hβ] at hpolar
  have hsplit : Complex.I * ((towerPhase β T + k * Real.pi : ℝ) : ℂ) =
      (towerPhase β T : ℂ) * Complex.I + (k : ℂ) * (Real.pi * Complex.I) := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hexp : Complex.exp ((towerPhase β T : ℂ) * Complex.I) = (⟨β, T⟩ : ℂ) / ‖(⟨β, T⟩ : ℂ)‖ := by
    rw [eq_div_iff hn, mul_comm]
    exact hpolar
  rw [hexp]
  push_cast
  ring

/-- **La valeur de la Tour à son contact est réelle** :
`x^ρ/ρ = (−1)^k · C_k^β/‖ρ‖` en `x = C_k`. -/
theorem towerValue_at_contact {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (k : ℤ) :
    towerValue (⟨β, T⟩ : ℂ) (contactAt β T k) = ((contactRealValue β T k : ℝ) : ℂ) := by
  have hx : 0 < contactAt β T k := contactAt_pos β T k
  have hρ : (⟨β, T⟩ : ℂ) ≠ 0 := mk_ne_zero_of_re_pos hβ
  have hn : (‖(⟨β, T⟩ : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_mk_pos (T := T) hβ).ne'
  unfold towerValue contactRealValue
  rw [ofReal_cpow_eq_rpow_mul_exp hx]
  have him : ((⟨β, T⟩ : ℂ).im : ℂ) * (Real.log (contactAt β T k) : ℂ) =
      ((towerPhase β T + k * Real.pi : ℝ) : ℂ) := by
    rw [← height_mul_log_contactAt hT.ne' k]; push_cast; rfl
  rw [him, exp_I_phase_contact hβ k]
  have hre : (⟨β, T⟩ : ℂ).re = β := rfl
  rw [hre]
  push_cast
  field_simp

/-- Module de la valeur au contact : `C_k^β/‖ρ‖`. -/
theorem abs_contactRealValue {β T : ℝ} (hβ : 0 < β) (k : ℤ) :
    |contactRealValue β T k| = contactAt β T k ^ β / ‖(⟨β, T⟩ : ℂ)‖ := by
  unfold contactRealValue
  rw [abs_div, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul,
    abs_of_pos (Real.rpow_pos_of_pos (contactAt_pos β T k) β), abs_of_pos (norm_mk_pos hβ)]

theorem contactRealValue_ne_zero {β T : ℝ} (hβ : 0 < β) (k : ℤ) : contactRealValue β T k ≠ 0 := by
  intro h
  have := abs_contactRealValue (T := T) hβ k
  rw [h, abs_zero] at this
  have : 0 < contactAt β T k ^ β / ‖(⟨β, T⟩ : ℂ)‖ :=
    div_pos (Real.rpow_pos_of_pos (contactAt_pos β T k) β) (norm_mk_pos hβ)
  linarith

/-! ## 2. Alternance et signes -/

/-- **Alternance** : `v_{k+1} = −e^{βπ/T} · v_k`. -/
theorem contactRealValue_succ {β T : ℝ} (hT : T ≠ 0) (k : ℤ) :
    contactRealValue β T (k + 1) = -Real.exp (β * Real.pi / T) * contactRealValue β T k := by
  unfold contactRealValue
  have hC : contactAt β T (k + 1) = contactAt β T k * Real.exp (Real.pi / T) := by
    have hk : contactAt β T k ≠ 0 := (contactAt_pos β T k).ne'
    rw [← contactAt_ratio (β := β) hT k]
    field_simp
  rw [hC, Real.mul_rpow (contactAt_pos β T k).le (Real.exp_pos _).le, ← Real.exp_mul,
    zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  have : Real.pi / T * β = β * Real.pi / T := by ring
  rw [this]
  ring

/-- Deux contacts consécutifs portent des valeurs de signes opposés. -/
theorem contactRealValue_alternates {β T : ℝ} (hβ : 0 < β) (hT : T ≠ 0) (k : ℤ) :
    contactRealValue β T (k + 1) * contactRealValue β T k < 0 := by
  rw [contactRealValue_succ hT k]
  have h1 : 0 < Real.exp (β * Real.pi / T) := Real.exp_pos _
  have h2 : 0 < contactRealValue β T k * contactRealValue β T k :=
    mul_self_pos.mpr (contactRealValue_ne_zero hβ k)
  nlinarith

/-- **Même signe à même indice** : deux Tours quelconques `(β, T)`, `(β', T')` (`β, β' > 0`) ont,
à leur `k`-ième contact, des valeurs de même signe `(−1)^k`. -/
theorem contactRealValue_mul_pos {β T β' T' : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (k : ℤ) :
    0 < contactRealValue β T k * contactRealValue β' T' k := by
  unfold contactRealValue
  have h1 : 0 < contactAt β T k ^ β / ‖(⟨β, T⟩ : ℂ)‖ :=
    div_pos (Real.rpow_pos_of_pos (contactAt_pos β T k) β) (norm_mk_pos hβ)
  have h2 : 0 < contactAt β' T' k ^ β' / ‖(⟨β', T'⟩ : ℂ)‖ :=
    div_pos (Real.rpow_pos_of_pos (contactAt_pos β' T' k) β') (norm_mk_pos hβ')
  have h3 : 0 < ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) := mul_self_pos.mpr (zpow_ne_zero k (by norm_num))
  calc 0 < (((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k)) *
        ((contactAt β T k ^ β / ‖(⟨β, T⟩ : ℂ)‖) * (contactAt β' T' k ^ β' / ‖(⟨β', T'⟩ : ℂ)‖)) :=
          mul_pos h3 (mul_pos h1 h2)
    _ = _ := by ring

/-! ## 3. Inversion tangentielle -/

/-- **Hauteur depuis deux contacts consécutifs** : `T = π/(log C_{k+1} − log C_k)`. -/
theorem height_of_contact_log_step {β T : ℝ} (hT : T ≠ 0) (k : ℤ) :
    T = Real.pi / (Real.log (contactAt β T (k + 1)) - Real.log (contactAt β T k)) := by
  rw [contactAt_log_step hT k]
  field_simp

/-- **Position radiale par la tangente** : `tan(T·log C_k − kπ) = T/β`, donc `β = T/tan(…)`. -/
theorem tan_contact_phase {β T : ℝ} (hT : T ≠ 0) (k : ℤ) :
    Real.tan (T * Real.log (contactAt β T k) - k * Real.pi) = T / β := by
  rw [height_mul_log_contactAt hT k]
  unfold towerPhase
  rw [add_sub_cancel_right, Real.tan_arctan]

theorem radial_of_contact_tangent {β T : ℝ} (hβ : 0 < β) (hT : T ≠ 0) (k : ℤ) :
    β = T / Real.tan (T * Real.log (contactAt β T k) - k * Real.pi) := by
  rw [tan_contact_phase hT k]
  field_simp

/-- **Position radiale par le rapport des amplitudes** : `|v_{k+1}|/|v_k| = e^{βπ/T}`. -/
theorem abs_contactRealValue_ratio {β T : ℝ} (hβ : 0 < β) (hT : T ≠ 0) (k : ℤ) :
    |contactRealValue β T (k + 1)| / |contactRealValue β T k| = Real.exp (β * Real.pi / T) := by
  rw [contactRealValue_succ hT k, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _),
    mul_div_assoc, div_self (abs_ne_zero.mpr (contactRealValue_ne_zero hβ k)), mul_one]

theorem radial_of_contact_value_ratio {β T : ℝ} (hβ : 0 < β) (hT : T ≠ 0) (k : ℤ) :
    β = T * Real.log (|contactRealValue β T (k + 1)| / |contactRealValue β T k|) / Real.pi := by
  rw [abs_contactRealValue_ratio hβ hT k, Real.log_exp]
  field_simp

/-! ## 4. Enroulement : l'amplitude est géométrique en `k` -/

/-- `log|v_k| = β(φ + kπ)/T − log‖ρ‖` : affine en `k`, pente `βπ/T`. -/
theorem log_abs_contactRealValue {β T : ℝ} (hβ : 0 < β) (k : ℤ) :
    Real.log |contactRealValue β T k| =
      β * ((towerPhase β T + k * Real.pi) / T) - Real.log ‖(⟨β, T⟩ : ℂ)‖ := by
  rw [abs_contactRealValue hβ k,
    Real.log_div (Real.rpow_pos_of_pos (contactAt_pos β T k) β).ne' (norm_mk_pos hβ).ne',
    Real.log_rpow (contactAt_pos β T k)]
  unfold contactAt windingContact towerPhase
  rw [Real.log_exp]

/-! ## 5. Entrelacement des contacts de deux Tours sur le même axe -/

/-- **Décalage exact** entre un contact de `(β₂,T₂)` et un contact de `(β₁,T₁)`. -/
theorem interleaving_offset (β₁ T₁ β₂ T₂ : ℝ) (k j : ℤ) :
    Real.log (contactAt β₂ T₂ j) - Real.log (contactAt β₁ T₁ k) =
      (towerPhase β₂ T₂ + j * Real.pi) / T₂ - (towerPhase β₁ T₁ + k * Real.pi) / T₁ := by
  unfold contactAt windingContact towerPhase
  rw [Real.log_exp, Real.log_exp]

/-- Indice réel du cycle de la Tour `(β, T)` à la position `u = log x` : `(T·u − φ)/π`
(il vaut `j` exactement aux contacts). -/
noncomputable def cycleIndex (β T u : ℝ) : ℝ := (T * u - towerPhase β T) / Real.pi

theorem cycleIndex_contactAt {β T : ℝ} (hT : T ≠ 0) (j : ℤ) :
    cycleIndex β T (Real.log (contactAt β T j)) = j := by
  unfold cycleIndex
  rw [height_mul_log_contactAt hT j]
  field_simp
  ring

theorem cycleIndex_strictMono {β T : ℝ} (hT : 0 < T) : StrictMono (cycleIndex β T) := by
  intro a b hab
  unfold cycleIndex
  apply div_lt_div_of_pos_right _ Real.pi_pos
  linarith [mul_lt_mul_of_pos_left hab hT]

/-- Un contact `j` de `(β₂,T₂)` est dans `[log a, log b)` ssi
`⌈cycleIndex a⌉ ≤ j < ⌈cycleIndex b⌉`. -/
theorem contact_mem_iff_cycleIndex {β₂ T₂ : ℝ} (hT₂ : 0 < T₂) (a b : ℝ) (j : ℤ) :
    (a ≤ Real.log (contactAt β₂ T₂ j) ∧ Real.log (contactAt β₂ T₂ j) < b) ↔
      (⌈cycleIndex β₂ T₂ a⌉ ≤ j ∧ j < ⌈cycleIndex β₂ T₂ b⌉) := by
  have hmono := cycleIndex_strictMono (β := β₂) hT₂
  rw [Int.ceil_le, Int.lt_ceil, ← cycleIndex_contactAt (β := β₂) hT₂.ne' j]
  exact and_congr hmono.le_iff_le.symm hmono.lt_iff_lt.symm

/-- **Nombre de contacts de `(β₂,T₂)` entre les contacts `k` et `k+1` de `(β₁,T₁)`** (entier). -/
noncomputable def interleavingCount (β₁ T₁ β₂ T₂ : ℝ) (k : ℤ) : ℤ :=
  ⌈cycleIndex β₂ T₂ (Real.log (contactAt β₁ T₁ (k + 1)))⌉ -
    ⌈cycleIndex β₂ T₂ (Real.log (contactAt β₁ T₁ k))⌉

/-- Le compte est le cardinal de l'ensemble des indices `j` dont le contact est dans
l'intervalle. -/
theorem interleavingCount_eq_card (β₁ T₁ β₂ T₂ : ℝ) (k : ℤ) :
    ((Finset.Ico ⌈cycleIndex β₂ T₂ (Real.log (contactAt β₁ T₁ k))⌉
        ⌈cycleIndex β₂ T₂ (Real.log (contactAt β₁ T₁ (k + 1)))⌉).card : ℤ) =
      interleavingCount β₁ T₁ β₂ T₂ k ∨ interleavingCount β₁ T₁ β₂ T₂ k ≤ 0 := by
  unfold interleavingCount
  rw [Int.card_Ico]
  by_cases h : ⌈cycleIndex β₂ T₂ (Real.log (contactAt β₁ T₁ (k + 1)))⌉ -
      ⌈cycleIndex β₂ T₂ (Real.log (contactAt β₁ T₁ k))⌉ ≤ 0
  · exact Or.inr h
  · left; exact Int.toNat_of_nonneg (le_of_lt (not_le.mp h))

theorem mem_Ico_iff_contact_between {β₁ T₁ β₂ T₂ : ℝ} (hT₂ : 0 < T₂) (k j : ℤ) :
    j ∈ Finset.Ico ⌈cycleIndex β₂ T₂ (Real.log (contactAt β₁ T₁ k))⌉
        ⌈cycleIndex β₂ T₂ (Real.log (contactAt β₁ T₁ (k + 1)))⌉ ↔
      (Real.log (contactAt β₁ T₁ k) ≤ Real.log (contactAt β₂ T₂ j) ∧
        Real.log (contactAt β₂ T₂ j) < Real.log (contactAt β₁ T₁ (k + 1))) := by
  rw [Finset.mem_Ico, contact_mem_iff_cycleIndex hT₂]

/-- D'un contact au suivant de `(β₁,T₁)`, l'indice de cycle de `(β₂,T₂)` avance de `T₂/T₁`. -/
theorem cycleIndex_step {β₁ T₁ β₂ T₂ : ℝ} (hT₁ : T₁ ≠ 0) (k : ℤ) :
    cycleIndex β₂ T₂ (Real.log (contactAt β₁ T₁ (k + 1))) =
      cycleIndex β₂ T₂ (Real.log (contactAt β₁ T₁ k)) + T₂ / T₁ := by
  unfold cycleIndex
  have h := contactAt_log_step (β := β₁) hT₁ k
  have : Real.log (contactAt β₁ T₁ (k + 1)) = Real.log (contactAt β₁ T₁ k) + Real.pi / T₁ := by
    linarith
  rw [this]
  field_simp
  ring

/-- **Bornes de l'entrelacement** : `⌊T₂/T₁⌋ ≤ compte ≤ ⌈T₂/T₁⌉`, pour toutes positions radiales
`β₁, β₂` : le comptage entre deux contacts consécutifs est aveugle au radial. -/
theorem interleavingCount_bounds {β₁ T₁ β₂ T₂ : ℝ} (hT₁ : T₁ ≠ 0) (k : ℤ) :
    ⌊T₂ / T₁⌋ ≤ interleavingCount β₁ T₁ β₂ T₂ k ∧
      interleavingCount β₁ T₁ β₂ T₂ k ≤ ⌈T₂ / T₁⌉ := by
  unfold interleavingCount
  rw [cycleIndex_step hT₁ k]
  set u := cycleIndex β₂ T₂ (Real.log (contactAt β₁ T₁ k))
  set L := T₂ / T₁
  constructor
  · have h1 := Int.le_ceil (u + L)
    have h2 := Int.ceil_lt_add_one u
    have h3 := Int.floor_le L
    have h4 : ((⌊L⌋ : ℤ) : ℝ) - 1 < ((⌈u + L⌉ - ⌈u⌉ : ℤ) : ℝ) := by
      push_cast; linarith
    have h5 : ⌊L⌋ - 1 < ⌈u + L⌉ - ⌈u⌉ := by exact_mod_cast h4
    omega
  · have := Int.ceil_add_le u L
    omega

/-- **Le déplacement radial d'un contact est inférieur à un demi-pas de la Tour déplacée** :
`|log C_k(β,T) − log C_k(½,T)| < π/(2T)`. (Il peut dépasser plusieurs pas `π/T'` d'une Tour
plus haute `T' > 2T` : ce module ne borne pas le rang dans la fusion.) -/
theorem contact_displacement_lt_half_step {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) (k : ℤ) :
    |Real.log (contactAt β T k) - Real.log (contactAt (1 / 2) T k)| < Real.pi / (2 * T) := by
  rw [interleaving_offset]
  have h : (towerPhase β T + k * Real.pi) / T - (towerPhase (1 / 2) T + k * Real.pi) / T =
      (towerPhase β T - towerPhase (1 / 2) T) / T := by
    rw [div_sub_div_same]
    congr 1
    ring
  rw [h, abs_div, abs_of_pos hT, ← div_div, div_lt_div_iff_of_pos_right hT]
  unfold towerPhase
  have a1 : 0 < Real.arctan (T / β) := Real.arctan_pos.mpr (div_pos hT hβ)
  have a2 : Real.arctan (T / β) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have b1 : 0 < Real.arctan (T / (1 / 2)) := Real.arctan_pos.mpr (div_pos hT (by norm_num))
  have b2 : Real.arctan (T / (1 / 2)) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  rw [abs_lt]
  constructor <;> linarith

/-- **Paire miroir** : les contacts de `(β, T)` et `(1−β, T)` coïncident si et seulement si
`β = ½` (et même indice). Ce n'est pas une exclusion des zéros OFF : hors ligne, les deux membres
d'une paire passent sur l'axe en des positions distinctes. -/
theorem mirror_contacts_coincide_iff {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hT : 0 < T) (k j : ℤ) :
    contactAt β T k = contactAt (1 - β) T j ↔ β = 1 / 2 ∧ k = j := by
  constructor
  · intro h
    unfold contactAt windingContact at h
    rw [Real.exp_eq_exp] at h
    have h' : Real.arctan (T / β) - Real.arctan (T / (1 - β)) = (j - k : ℤ) * Real.pi := by
      have := h
      field_simp at this
      push_cast
      linarith
    have a1 : 0 < Real.arctan (T / β) := Real.arctan_pos.mpr (div_pos hT hβ)
    have a2 : Real.arctan (T / β) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have b1 : 0 < Real.arctan (T / (1 - β)) := Real.arctan_pos.mpr (div_pos hT (by linarith))
    have b2 : Real.arctan (T / (1 - β)) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have hjk : j - k = 0 := by
      have hlt : |((j - k : ℤ) : ℝ)| < 1 := by
        rw [abs_lt]
        constructor
        · by_contra hc
          have hc' : ((j - k : ℤ) : ℝ) ≤ -1 := not_lt.mp hc
          have : ((j - k : ℤ) : ℝ) * Real.pi ≤ -1 * Real.pi :=
            mul_le_mul_of_nonneg_right hc' Real.pi_pos.le
          linarith
        · by_contra hc
          have hc' : 1 ≤ ((j - k : ℤ) : ℝ) := not_lt.mp hc
          have : 1 * Real.pi ≤ ((j - k : ℤ) : ℝ) * Real.pi :=
            mul_le_mul_of_nonneg_right hc' Real.pi_pos.le
          linarith
      have : |j - k| < 1 := by exact_mod_cast hlt
      exact Int.abs_lt_one_iff.mp this
    have hkj : k = j := by omega
    refine ⟨?_, hkj⟩
    have h'' : Real.arctan (T / β) = Real.arctan (T / (1 - β)) := by
      rw [hjk] at h'
      push_cast at h'
      linarith
    have := Real.arctan_injective h''
    have h1β : 1 - β ≠ 0 := by linarith
    field_simp at this
    linarith
  · rintro ⟨hb, hk⟩
    subst hk
    rw [hb]
    norm_num

/-! ## 6. La somme collective aux positions des contacts -/

/-- Somme collective d'une famille finie de Tours à la position `x`. -/
noncomputable def collectiveAxisSum (s : Finset ℂ) (x : ℝ) : ℂ := ∑ ρ ∈ s, towerValue ρ x

/-- **Décomposition au contact d'un membre** : valeur propre réelle plus les autres Tours
évaluées à la même position (en général hors de leurs propres contacts). -/
theorem collectiveAxisSum_at_contact {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) {s : Finset ℂ}
    (hs : (⟨β, T⟩ : ℂ) ∈ s) (k : ℤ) :
    collectiveAxisSum s (contactAt β T k) =
      ((contactRealValue β T k : ℝ) : ℂ) +
        ∑ ρ ∈ s.erase (⟨β, T⟩ : ℂ), towerValue ρ (contactAt β T k) := by
  unfold collectiveAxisSum
  rw [← Finset.add_sum_erase s _ hs, towerValue_at_contact hβ hT]

end RHV6Fresh

#print axioms RHV6Fresh.towerValue_at_contact
#print axioms RHV6Fresh.contactRealValue_alternates
#print axioms RHV6Fresh.radial_of_contact_tangent
#print axioms RHV6Fresh.radial_of_contact_value_ratio
#print axioms RHV6Fresh.interleavingCount_bounds
#print axioms RHV6Fresh.mirror_contacts_coincide_iff
#print axioms RHV6Fresh.collectiveAxisSum_at_contact
