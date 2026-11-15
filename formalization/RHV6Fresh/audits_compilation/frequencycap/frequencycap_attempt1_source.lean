/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CountingDeficit
import RHV6Fresh.Zeta23Port.RvM.Statement
import RHV6Fresh.Zeta23Port.RvM.NcountWindow
import RHV6Fresh.Zeta23Port.GammaFacts.Complete

/-!
# Plafond et plancher de la fréquence d'un membre canonique (§19.15, 2026-10-30)

Module isolé (non ajouté à `RHV6Fresh.lean`). Demande de l'auteur : la fréquence d'un zéro est capée par le haut et
par le bas ; un zéro ne peut pas occuper une fréquence qui empêcherait tous les autres d'occuper les leurs jusqu'à
l'infini. Audit du corpus (Lean et maîtres) : l'obligation « tous les zéros occupent leurs fréquences jusqu'à l'infini »
est compilée, du côté des zéros, par le comptage de Riemann–von Mangoldt déjà porté (`Zeta23Port/RvM`, inconditionnel
depuis les faits Γ démontrés), et par le comptage local `N(t, t+1] ≤ A₀ log(|t|+3)` (inconditionnel). Le rang d'un
membre canonique est lié au comptage par `upperCount_ge_of_canonical_le` (déjà compilé). Ce module assemble les trois.

Compilé ici :
* `height_le_iff_card` : **rang et comptage distinct sont équivalents** : le membre de rang `k+1` est de hauteur
  au plus `a` si et seulement si la fenêtre fermée de hauteur `a` contient au moins `k+1` points-zéros.
* `upperCount_eq_Ncount` : le comptage avec multiplicité du corpus terminal **est** le comptage `N(0, a]` du port
  zeta23 (même ensemble, même multiplicité analytique).
* `lower_cap` : **plancher** : il existe `A₀ ≥ 1` tel que, pour tout rang `k` et tout entier `n`, si
  `n · A₀ · log(n+3) < k+1`, alors la hauteur du membre de rang `k+1` dépasse `n`. Inconditionnel.
* `upper_cap` : **plafond** : il existe `C`, `T₀`, `A₀` tels que, pour tout rang `k` et tout `T ≥ max(T₀, 1)`, si
  `(k+1) · A₀ · log(2T+3) < T/(2π) · ℓ₁(T) − C · log T`, alors la hauteur du membre de rang `k+1` est au plus `2T`.
  Inconditionnel (Riemann–von Mangoldt pour ζ de Mathlib, `riemannVonMangoldt gammaFacts`, plus la borne de
  multiplicité tirée du comptage local).

Portée exacte, consignée : les deux caps portent sur le **comptage total avec multiplicité**, ON et OFF confondus
(`upperCount_eq_on_add_two_low`, CountingDeficit) : une paire OFF/miroir entre deux fois, à une seule fréquence, et
satisfait les deux caps comme deux zéros ON de fréquences distinctes. Les caps bornent la fréquence du membre de rang
`k+1` par des fonctions de `k` seul ; ils ne bornent pas la fréquence du membre suivant par celle du membre courant,
et ne distinguent pas une paire OFF d'un zéro ON. Aucune hypothèse ajoutée ; axiomes standard attendus.
-/

namespace RHV6Fresh

open RHV3Lean Finset

/-! ## 1. Rang et comptage distinct : équivalence exacte -/

/-- Si la fenêtre fermée de hauteur `a` contient au moins `k+1` points, le membre de rang `k+1` est sous `a`
(sinon tous les membres de rang `≥ k+1` sont au-dessus de `a`, et la fenêtre a au plus `k` points). -/
theorem height_le_of_card (k : ℕ) {a : ℝ} (h : k + 1 ≤ (upperWindow a).card) :
    rZeroHeight (canonicalMember k).1 ≤ a := by
  by_contra hgt
  have hgt' : a < rZeroHeight (canonicalMember k).1 := lt_of_not_ge hgt
  have hsub : upperWindow a ⊆ (Finset.range k).image (fun j => zeroPoint (canonicalMember j)) := by
    intro ρ hρ
    obtain ⟨w, rfl, hw⟩ := mem_upperWindow_iff.mp hρ
    obtain ⟨j, rfl⟩ := canonicalMember_surjective w
    refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr ?_, rfl⟩
    by_contra hjk
    have hkj : k ≤ j := not_lt.mp hjk
    have := canonicalMember_height_mono hkj
    linarith
  have hcard := Finset.card_le_card hsub
  have hle : ((Finset.range k).image (fun j => zeroPoint (canonicalMember j))).card ≤ k :=
    Finset.card_image_le.trans (Finset.card_range k).le
  omega

/-- Réciproque : le membre de rang `k+1` sous `a` force au moins `k+1` points dans la fenêtre. -/
theorem card_ge_of_height_le {a : ℝ} {k : ℕ} (h : rZeroHeight (canonicalMember k).1 ≤ a) :
    k + 1 ≤ (upperWindow a).card := by
  have hsub : (Finset.range (k + 1)).image (fun j => zeroPoint (canonicalMember j)) ⊆ upperWindow a := by
    intro ρ hρ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hρ
    exact mem_upperWindow_iff.mpr ⟨canonicalMember j, rfl,
      (canonicalMember_height_mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).trans h⟩
  have hinj : Set.InjOn (fun j => zeroPoint (canonicalMember j))
      ((Finset.range (k + 1) : Finset ℕ) : Set ℕ) := by
    intro i _ j _ hij
    apply canonicalMember_injective
    apply Subtype.ext; apply Subtype.ext; exact hij
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard

/-- **Rang ⟺ comptage distinct.** -/
theorem height_le_iff_card (k : ℕ) (a : ℝ) :
    rZeroHeight (canonicalMember k).1 ≤ a ↔ k + 1 ≤ (upperWindow a).card :=
  ⟨card_ge_of_height_le, height_le_of_card k⟩

/-! ## 2. Pont exact avec le comptage du port zeta23 -/

theorem mem_upperWindow_iff_zerosIn {a : ℝ} {ρ : ℂ} : ρ ∈ upperWindow a ↔ ρ ∈ Zeta23.zerosIn 0 a := by
  rw [mem_upperWindow]
  exact Iff.rfl

theorem upperWindow_coe_eq (a : ℝ) : ((upperWindow a : Finset ℂ) : Set ℂ) = Zeta23.zerosIn 0 a := by
  ext ρ
  rw [Finset.mem_coe]
  exact mem_upperWindow_iff_zerosIn

theorem zetaZeroMultiplicity_eq_zeroMult (ρ : ℂ) : zetaZeroMultiplicity ρ = Zeta23.zeroMult ρ := rfl

/-- **Le comptage du corpus terminal est le comptage `N(0, a]` du port zeta23.** -/
theorem upperCount_eq_Ncount (a : ℝ) : upperCountWithMultiplicity a = Zeta23.Ncount 0 a := by
  unfold upperCountWithMultiplicity Zeta23.Ncount
  rw [← upperWindow_coe_eq a]
  exact (finsum_mem_coe_finset (s := upperWindow a) (f := Zeta23.zeroMult)).symm

/-! ## 3. Plancher : le comptage local inconditionnel -/

theorem Ncount_zero_zero : Zeta23.Ncount 0 0 = 0 := by
  unfold Zeta23.Ncount
  have h : Zeta23.zerosIn 0 0 = ∅ := by
    ext ρ
    simp only [Zeta23.zerosIn, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_, h1, h2⟩
    linarith
  rw [h, finsum_mem_empty]

/-- `N(0, n] ≤ n · A₀ · log(n+3)` par additivité des fenêtres unité. -/
theorem Ncount_nat_le (A₀ : ℝ) (hA0 : 0 ≤ A₀)
    (hA : ∀ t : ℝ, (Zeta23.Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    ∀ n : ℕ, (Zeta23.Ncount 0 n : ℝ) ≤ n * (A₀ * Real.log (n + 3)) := by
  intro n
  induction n with
  | zero => simp [Ncount_zero_zero]
  | succ n ih =>
    have hadd : Zeta23.Ncount 0 ((n + 1 : ℕ) : ℝ) = Zeta23.Ncount 0 n + Zeta23.Ncount n (n + 1) := by
      push_cast
      exact Zeta23.Ncount_add (by positivity) (by linarith)
    have hn := hA n
    rw [abs_of_nonneg (Nat.cast_nonneg n)] at hn
    have hlog : Real.log ((n : ℝ) + 3) ≤ Real.log ((n : ℝ) + 1 + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog0 : 0 ≤ Real.log ((n : ℝ) + 3) := Real.log_nonneg (by linarith)
    have hM : A₀ * Real.log ((n : ℝ) + 3) ≤ A₀ * Real.log ((n : ℝ) + 1 + 3) :=
      mul_le_mul_of_nonneg_left hlog hA0
    have h1 : (n : ℝ) * (A₀ * Real.log ((n : ℝ) + 3)) ≤ n * (A₀ * Real.log ((n : ℝ) + 1 + 3)) :=
      mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg n)
    rw [hadd]
    push_cast
    linarith

/-- **Plancher inconditionnel** : si `n · A₀ · log(n+3) < k+1`, le membre de rang `k+1` est au-dessus de `n`. -/
theorem lower_cap : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (k n : ℕ),
    (n : ℝ) * (A₀ * Real.log (n + 3)) < k + 1 → (n : ℝ) < rZeroHeight (canonicalMember k).1 := by
  obtain ⟨A₀, hA1, hA⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨A₀, hA1, fun k n hlt => ?_⟩
  by_contra hle
  have hle' : rZeroHeight (canonicalMember k).1 ≤ n := not_lt.mp hle
  have h1 := upperCount_ge_of_canonical_le hle'
  rw [upperCount_eq_Ncount] at h1
  have h2 := Ncount_nat_le A₀ (by linarith) hA n
  have h1' : ((k : ℝ) + 1) ≤ (Zeta23.Ncount 0 n : ℝ) := by exact_mod_cast h1
  linarith

/-! ## 4. Plafond : Riemann–von Mangoldt inconditionnel et multiplicité bornée -/

/-- Une multiplicité est au plus le comptage de sa fenêtre unité. -/
theorem zeroMult_le_Ncount {t : ℝ} {ρ : ℂ} (h : ρ ∈ Zeta23.zerosIn t (t + 1)) :
    Zeta23.zeroMult ρ ≤ Zeta23.Ncount t (t + 1) := by
  unfold Zeta23.Ncount
  rw [finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite t (t + 1))]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    ((Zeta23.zerosIn_finite t (t + 1)).mem_toFinset.mpr h)

/-- Comptage avec multiplicité ≤ nombre de points × borne de multiplicité (fenêtre de hauteur `a ≥ 1`). -/
theorem upperCount_le_card_mul (A₀ : ℝ) (hA0 : 0 ≤ A₀)
    (hA : ∀ t : ℝ, (Zeta23.Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {a : ℝ} (ha : 1 ≤ a) :
    (upperCountWithMultiplicity a : ℝ) ≤ (upperWindow a).card * (A₀ * Real.log (a + 3)) := by
  unfold upperCountWithMultiplicity
  push_cast
  have hM : ∀ ρ ∈ upperWindow a, (zetaZeroMultiplicity ρ : ℝ) ≤ A₀ * Real.log (a + 3) := by
    intro ρ hρ
    obtain ⟨hz, h0, hle⟩ := mem_upperWindow.mp hρ
    have hmem : ρ ∈ Zeta23.zerosIn (ρ.im - 1) (ρ.im - 1 + 1) := by
      simp only [Zeta23.zerosIn, Set.mem_setOf_eq]
      exact ⟨hz, by linarith, by linarith⟩
    have h1 : (zetaZeroMultiplicity ρ : ℝ) ≤ Zeta23.Ncount (ρ.im - 1) (ρ.im - 1 + 1) := by
      exact_mod_cast zeroMult_le_Ncount hmem
    have h2 := hA (ρ.im - 1)
    have h3 : |ρ.im - 1| ≤ a := abs_le.mpr ⟨by linarith, by linarith⟩
    have h4 : Real.log (|ρ.im - 1| + 3) ≤ Real.log (a + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    calc (zetaZeroMultiplicity ρ : ℝ) ≤ Zeta23.Ncount (ρ.im - 1) (ρ.im - 1 + 1) := h1
      _ ≤ A₀ * Real.log (|ρ.im - 1| + 3) := h2
      _ ≤ A₀ * Real.log (a + 3) := mul_le_mul_of_nonneg_left h4 hA0
  have := Finset.sum_le_card_nsmul (upperWindow a) (fun ρ => (zetaZeroMultiplicity ρ : ℝ)) _ hM
  simpa [nsmul_eq_mul] using this

/-- **Plafond inconditionnel** (Riemann–von Mangoldt pour ζ, faits Γ démontrés) : si
`(k+1) · A₀ · log(2T+3) < T/(2π) · ℓ₁(T) − C · log T` avec `T ≥ max(T₀, 1)`, le membre de rang `k+1` est de hauteur
au plus `2T`. -/
theorem upper_cap : ∃ C T₀ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ (k : ℕ) (T : ℝ), T₀ ≤ T → 1 ≤ T →
    ((k : ℝ) + 1) * (A₀ * Real.log (2 * T + 3)) < T / (2 * Real.pi) * Zeta23.ell1 T - C * Real.log T →
    rZeroHeight (canonicalMember k).1 ≤ 2 * T := by
  obtain ⟨C, T₀, hmain⟩ := (Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts).main
  obtain ⟨A₀, hA1, hA⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨C, T₀, A₀, by linarith, fun k T hT0 hT1 hlt => ?_⟩
  have hN := hmain T hT0
  rw [Zeta23.zetaZeroConfig_N] at hN
  have hlow : T / (2 * Real.pi) * Zeta23.ell1 T - C * Real.log T ≤ (Zeta23.Ncount T (2 * T) : ℝ) := by
    have := (abs_le.mp hN).1
    linarith
  have hmono : Zeta23.Ncount T (2 * T) ≤ Zeta23.Ncount 0 (2 * T) :=
    Zeta23.Ncount_mono (by linarith) le_rfl
  have hmono' : (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.Ncount 0 (2 * T) := by exact_mod_cast hmono
  have hcnt : (upperCountWithMultiplicity (2 * T) : ℝ) = Zeta23.Ncount 0 (2 * T) := by
    rw [upperCount_eq_Ncount]
  have hcard := upperCount_le_card_mul A₀ (by linarith) hA (a := 2 * T) (by linarith)
  have hMpos : 0 < A₀ * Real.log (2 * T + 3) :=
    mul_pos (by linarith) (Real.log_pos (by linarith))
  have hk : ((k : ℝ) + 1) < (upperWindow (2 * T)).card := by
    by_contra hge
    have hge' : ((upperWindow (2 * T)).card : ℝ) ≤ k + 1 := not_lt.mp hge
    have := mul_le_mul_of_nonneg_right hge' hMpos.le
    linarith
  have hk' : k + 1 ≤ (upperWindow (2 * T)).card := by
    have h : ((k + 1 : ℕ) : ℝ) < (upperWindow (2 * T)).card := by push_cast; exact hk
    exact_mod_cast h.le
  exact height_le_of_card k hk'

/-! ## 5. Les deux caps ne distinguent pas ON de OFF -/

/-- Le comptage plafonné et planché est `N₀ + 2·W` : une paire OFF/miroir y entre deux fois à une seule fréquence
(`upperCount_eq_on_add_two_low`, déjà compilé) ; les caps ne portent aucune information radiale. -/
theorem caps_count_off_pairs_twice (a : ℝ) :
    Zeta23.Ncount 0 a = onCount a + 2 * lowCount a := by
  rw [← upperCount_eq_Ncount]
  exact upperCount_eq_on_add_two_low a

end RHV6Fresh

#print axioms RHV6Fresh.height_le_iff_card
#print axioms RHV6Fresh.upperCount_eq_Ncount
#print axioms RHV6Fresh.lower_cap
#print axioms RHV6Fresh.upper_cap
#print axioms RHV6Fresh.caps_count_off_pairs_twice
