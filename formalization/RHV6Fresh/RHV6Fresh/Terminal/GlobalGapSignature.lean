/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RegimeTransportAudit
import RHV6Fresh.Terminal.FirstTowerHorizon
import RHV6Fresh.Terminal.JointParameterReading
import RHV6Fresh.Terminal.TowerHierarchy
import RHV6Fresh.Terminal.LocalRaccordCaptivity

/-!
# RHV6Fresh — signature d'un zéro sur tous les écarts de premiers (mission E218–E223, 2026-10-13)

Objet central de la mission : la variation de la Tour d'un zéro sur un écart `[a, b]` (un écart de premiers quand
`a = p_n`, `b = p_{n+1}`), `Δ_{ρ}(a, b) = u_ρ(b) − u_ρ(a) = (b^ρ − a^ρ)/ρ`. Résultats (axiomes standard, aucune hypothèse de
ligne) :

1. **Représentation intégrale exacte** `Δ_ρ(a, b) = ∫_a^b t^{ρ−1} dt` (`gapVariation_eq_integral`), pour toute signature
   `s` de partie réelle `> 0` (`signatureGap_eq_integral`) : profils hypothétiques compris, explicitement distingués des zéros.
2. **Aucun écart ne rejette aucune signature** : `Δ_ρ(a, b) ≠ 0` pour `0 < a < b` et toute partie réelle `> 0`
   (`signatureGap_ne_zero`, `gapVariation_ne_zero`) ; enveloppe exacte `‖Δ_ρ(a, b)‖ ≤ (b^β − a^β)/β` (`gapVariation_norm_le`).
3. **La lecture sur TOUS les écarts télescope** : la somme des variations le long de toute suite d'abscisses vaut la différence
   des extrémités (`gapVariation_telescope`). La compatibilité d'une signature avec toute la suite des écarts est donc une
   identité vraie pour tout `(β, T)` (`gap_signature_constraint_vacuous`) : elle ne contraint pas `β`.
4. **Décalage radial à hauteur fixée** : l'intégrande est repondéré par le facteur réel `t^d` (`radial_shift_integrand`) ;
   enveloppe `≤ b^d` fois celle de la ligne (`signatureGap_shift_norm_le`).
5. **Hiérarchie et croisement** : deux Tours ON ordonnées en hauteur sont strictement ordonnées en amplitude en tout `x > 0`
   (rappel `onLine_tower_hierarchy`) ; un membre haut `β = 1/2 + δ` dépasse TOUTE Tour ON au-delà de `(‖ρ_w‖/‖ρ_z‖)^{1/δ}`, et
   seulement là (`upper_member_exact_horizon`) ; son miroir bas `β = 1/2 − δ` reste sous elle exactement pour
   `x ≥ (‖ρ_z‖/‖ρ_w‖)^{1/δ}` (`lower_member_below_iff`) : la paire croise des deux côtés de `x = 1`
   (`mirror_pair_crossing_profile`).
6. **Rigidité amplitude–fréquence** : la relation `A = x^{β−1/2}·ℓ/√(π² + β²ℓ²)`, `ℓ = π/T`, vaut pour toute partie réelle
   (`amplitude_frequency_relation_all_beta`) ; elle ne force pas `β = 1/2`.

Aucune de ces identités ne contraint `β` : elles sont vraies pour tout profil. Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Variation d'une signature sur un écart -/

/-- Variation de la signature `s` (exposant complexe quelconque, pas forcément un zéro) sur `[a, b]` : `(b^s − a^s)/s`. -/
noncomputable def signatureGap (s : ℂ) (a b : ℝ) : ℂ := ((b : ℂ) ^ s - (a : ℂ) ^ s) / s

/-- Variation de la Tour d'un vrai zéro sur `[a, b]`. -/
noncomputable def gapVariation (z : TrueZero) (a b : ℝ) : ℂ := zeroTerm z b - zeroTerm z a

theorem gapVariation_eq_signatureGap (z : TrueZero) (a b : ℝ) :
    gapVariation z a b = signatureGap (zeroPoint z) a b := by
  unfold gapVariation signatureGap zeroTerm
  rw [sub_div]

/-- **Représentation intégrale** : `(b^s − a^s)/s = ∫_a^b t^{s−1} dt` dès que `Re s > 0`. -/
theorem signatureGap_eq_integral {s : ℂ} (hs : 0 < s.re) (a b : ℝ) :
    signatureGap s a b = ∫ t in a..b, (t : ℂ) ^ (s - 1) := by
  have h : -1 < (s - 1).re := by simp; linarith
  rw [integral_cpow (Or.inl h), sub_add_cancel]
  rfl

theorem gapVariation_eq_integral (z : TrueZero) (a b : ℝ) :
    gapVariation z a b = ∫ t in a..b, (t : ℂ) ^ (zeroPoint z - 1) := by
  rw [gapVariation_eq_signatureGap, signatureGap_eq_integral (zeroPoint_re_pos z)]

/-- **Aucun écart ne rejette aucune signature** : pour `0 < a < b` et `Re s > 0`, la variation n'est jamais nulle. -/
theorem signatureGap_ne_zero {s : ℂ} (hs : 0 < s.re) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    signatureGap s a b ≠ 0 := by
  have hb : 0 < b := lt_trans ha hab
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  unfold signatureGap
  intro h
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · have heq : (b : ℂ) ^ s = (a : ℂ) ^ s := sub_eq_zero.mp h
    have hn := congrArg norm heq
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb, Complex.norm_cpow_eq_rpow_re_of_pos ha] at hn
    exact absurd hn (ne_of_gt (Real.rpow_lt_rpow ha.le hab hs))
  · exact hs0 h

theorem gapVariation_ne_zero (z : TrueZero) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    gapVariation z a b ≠ 0 := by
  rw [gapVariation_eq_signatureGap]
  exact signatureGap_ne_zero (zeroPoint_re_pos z) ha hab

/-- **Enveloppe exacte d'une variation** : `‖(b^s − a^s)/s‖ ≤ (b^σ − a^σ)/σ`, `σ = Re s > 0`, `0 < a ≤ b`. -/
theorem signatureGap_norm_le {s : ℂ} (hs : 0 < s.re) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖signatureGap s a b‖ ≤ (b ^ s.re - a ^ s.re) / s.re := by
  rw [signatureGap_eq_integral hs]
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans (le_of_eq ?_)
  have hcongr : Set.EqOn (fun t : ℝ => ‖(t : ℂ) ^ (s - 1)‖) (fun t : ℝ => t ^ (s.re - 1)) (Set.uIcc a b) := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    simp only
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp
  rw [intervalIntegral.integral_congr hcongr, integral_rpow (Or.inl (by linarith)), sub_add_cancel]

theorem gapVariation_norm_le (z : TrueZero) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖gapVariation z a b‖ ≤
      (b ^ rZeroRadialPosition z.1 - a ^ rZeroRadialPosition z.1) / rZeroRadialPosition z.1 := by
  rw [gapVariation_eq_signatureGap]
  exact signatureGap_norm_le (zeroPoint_re_pos z) ha hab

/-! ## 2. La lecture sur tous les écarts télescope -/

/-- **Télescopage** : le long de toute suite d'abscisses, la somme des variations ne lit que les extrémités. -/
theorem gapVariation_telescope (z : TrueZero) (q : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, gapVariation z (q n) (q (n + 1)) = zeroTerm z (q N) - zeroTerm z (q 0) := by
  unfold gapVariation
  exact Finset.sum_range_sub (fun n => zeroTerm z (q n)) N

theorem signatureGap_telescope (s : ℂ) (q : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, signatureGap s (q n) (q (n + 1)) = signatureGap s (q 0) (q N) := by
  unfold signatureGap
  rw [← Finset.sum_div, Finset.sum_range_sub (fun n => ((q n : ℝ) : ℂ) ^ s) N]

/-- **La compatibilité d'une signature avec tous les écarts ne contraint pas la partie réelle.** Pour TOUT exposant de partie
réelle `> 0` (vrai zéro ou profil hypothétique) et toute suite strictement croissante d'abscisses positives (les premiers en
particulier) : chaque variation est non nulle, bornée par son enveloppe, et la somme télescope. -/
theorem gap_signature_constraint_vacuous {s : ℂ} (hs : 0 < s.re) (q : ℕ → ℝ) (hq0 : 0 < q 0)
    (hq : StrictMono q) :
    (∀ n, signatureGap s (q n) (q (n + 1)) ≠ 0) ∧
      (∀ n, ‖signatureGap s (q n) (q (n + 1))‖ ≤ (q (n + 1) ^ s.re - q n ^ s.re) / s.re) ∧
      (∀ N, ∑ n ∈ Finset.range N, signatureGap s (q n) (q (n + 1)) = signatureGap s (q 0) (q N)) := by
  have hpos : ∀ n, 0 < q n := fun n => lt_of_lt_of_le hq0 (hq.monotone (Nat.zero_le n))
  exact ⟨fun n => signatureGap_ne_zero hs (hpos n) (hq (Nat.lt_succ_self n)),
    fun n => signatureGap_norm_le hs (hpos n) (hq (Nat.lt_succ_self n)).le,
    fun N => signatureGap_telescope s q N⟩

/-! ## 3. Décalage radial à hauteur fixée -/

/-- **Repondération par `t^d`** : décaler la partie réelle de `d` multiplie l'intégrande par le facteur réel `t^d`. -/
theorem radial_shift_integrand {t : ℝ} (ht : 0 < t) (s : ℂ) (d : ℝ) :
    (t : ℂ) ^ (s + d - 1) = ((t ^ d : ℝ) : ℂ) * (t : ℂ) ^ (s - 1) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [show s + (d : ℂ) - 1 = (d : ℂ) + (s - 1) by ring, Complex.cpow_add _ _ ht0,
    Complex.ofReal_cpow ht.le]

/-- **Enveloppe du profil décalé** : `‖Δ_{s+d}(a, b)‖ ≤ b^d·(b^σ − a^σ)/σ` pour `d ≥ 0`. Le décalage radial multiplie
l'enveloppe d'au plus `b^d` sur l'écart ; il ne crée aucune incompatibilité avec l'écart. -/
theorem signatureGap_shift_norm_le {s : ℂ} (hs : 0 < s.re) {d : ℝ} (hd : 0 ≤ d) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    ‖signatureGap (s + d) a b‖ ≤ b ^ d * ((b ^ s.re - a ^ s.re) / s.re) := by
  have hs' : 0 < (s + d).re := by simp; linarith
  rw [signatureGap_eq_integral hs']
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
  have hcongr : Set.EqOn (fun t : ℝ => ‖(t : ℂ) ^ (s + d - 1)‖)
      (fun t : ℝ => t ^ d * t ^ (s.re - 1)) (Set.uIcc a b) := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    simp only
    rw [radial_shift_integrand ht0, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
      Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
    simp
  rw [intervalIntegral.integral_congr hcongr]
  have hle : ∫ t in a..b, t ^ d * t ^ (s.re - 1) ≤ ∫ t in a..b, b ^ d * t ^ (s.re - 1) := by
    apply intervalIntegral.integral_mono_on hab
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul
      · exact fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl (by
          rw [Set.uIcc_of_le hab] at ht; linarith [ht.1]))).continuousWithinAt
      · exact fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl (by
          rw [Set.uIcc_of_le hab] at ht; linarith [ht.1]))).continuousWithinAt
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      exact fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl (by
          rw [Set.uIcc_of_le hab] at ht; linarith [ht.1]))).continuousWithinAt
    · intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht0.le ht.2 hd) (Real.rpow_nonneg ht0.le _)
  refine hle.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), sub_add_cancel]

/-! ## 4. Hiérarchie ON et croisement d'une paire miroir -/

/-- **Le membre bas d'une paire reste sous une Tour ON exactement au-delà d'un seuil `< 1` côté petites abscisses** :
pour `β_w = 1/2 − δ`, `‖u_w(x)‖ ≤ ‖u_z(x)‖ ⟺ ‖ρ_z‖/‖ρ_w‖ ≤ x^δ`. -/
theorem lower_member_below_iff {z w : TrueZero} (hz : rZeroRadialPosition z.1 = 1 / 2) {δ : ℝ}
    (hw : rZeroRadialPosition w.1 = 1 / 2 - δ) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm w x‖ ≤ ‖zeroTerm z x‖ ↔ ‖zeroPoint z‖ / ‖zeroPoint w‖ ≤ x ^ δ := by
  have hA := norm_zeroPoint_pos w
  have hB := norm_zeroPoint_pos z
  rw [norm_zeroTerm_eq w hx, norm_zeroTerm_eq z hx, hw, hz, div_le_div_iff₀ hA hB,
    div_le_iff₀ hA]
  have hsplit : x ^ (1 / 2 : ℝ) = x ^ (1 / 2 - δ) * x ^ δ := by
    rw [← Real.rpow_add hx]; ring_nf
  rw [hsplit]
  have hpos : 0 < x ^ (1 / 2 - δ) := Real.rpow_pos_of_pos hx _
  constructor
  · intro h
    have h' : x ^ (1 / 2 - δ) * ‖zeroPoint z‖ ≤ x ^ (1 / 2 - δ) * (x ^ δ * ‖zeroPoint w‖) := by
      nlinarith
    exact le_of_mul_le_mul_left h' hpos
  · intro h
    nlinarith [mul_le_mul_of_nonneg_left h hpos.le]

/-- **Profil de croisement d'une paire miroir face à une Tour ON** (`z` ON, membres `1/2 ± δ`, `δ > 0`) : le membre haut
reste sous la Tour ON exactement jusqu'à `(‖ρ_w‖/‖ρ_z‖)^{1/δ}` ; le membre bas y reste exactement à partir du seuil où
`x^δ ≥ ‖ρ_z‖/‖ρ_{w'}‖`. Les deux membres croisent : l'un vers l'infini, l'autre vers zéro. -/
theorem mirror_pair_crossing_profile {z w w' : TrueZero} (hz : rZeroRadialPosition z.1 = 1 / 2) {δ : ℝ}
    (hδ : 0 < δ) (hw : rZeroRadialPosition w.1 = 1 / 2 + δ) (hw' : rZeroRadialPosition w'.1 = 1 / 2 - δ)
    {x : ℝ} (hx : 0 < x) :
    (‖zeroTerm w x‖ ≤ firstField z x ↔ x ≤ (‖zeroPoint w‖ / ‖zeroPoint z‖) ^ (1 / δ)) ∧
      (‖zeroTerm w' x‖ ≤ ‖zeroTerm z x‖ ↔ ‖zeroPoint z‖ / ‖zeroPoint w'‖ ≤ x ^ δ) :=
  ⟨upper_member_exact_horizon hz hδ hw hx, lower_member_below_iff hz hw' hx⟩

/-- **Hiérarchie des Tours ON** (rappel composé) : rapport constant en `x`, `< 1`, amplitude strictement plus faible partout. -/
theorem onLine_amplitude_hierarchy {z w : TrueZero} (hz : rZeroRadialPosition z.1 = 1 / 2)
    (hw : rZeroRadialPosition w.1 = 1 / 2) (hT : rZeroHeight z.1 < rZeroHeight w.1) :
    (∀ x : ℝ, 0 < x → ‖zeroTerm w x‖ < ‖zeroTerm z x‖) ∧
      (∀ x : ℝ, 0 < x → ‖zeroTerm w x‖ / ‖zeroTerm z x‖ = ‖zeroPoint z‖ / ‖zeroPoint w‖) ∧
      ‖zeroPoint z‖ / ‖zeroPoint w‖ < 1 := by
  obtain ⟨h1, -, h3, -⟩ := onLine_tower_hierarchy hz hw hT
  refine ⟨h1, fun x hx => ?_, h3⟩
  rw [successive_tower_ratio z w hx, hw, hz, sub_self, Real.rpow_zero, one_mul]

/-! ## 5. Rigidité amplitude–fréquence : vraie pour toute partie réelle -/

/-- **Relation amplitude–fréquence** : `A(x) = x^{β−1/2}·ℓ/√(π² + β²ℓ²)`, `ℓ = π/T`, pour toute partie réelle `β`. Elle lie la
fréquence et l'amplitude sans fixer `β` : à `β = 1/2` elle devient la relation ON, ailleurs elle porte le facteur `x^{β−1/2}`. -/
theorem amplitude_frequency_relation_all_beta (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    normalizedRadius z x =
      x ^ (rZeroRadialPosition z.1 - 1 / 2) * towerPitch z /
        Real.sqrt (Real.pi ^ 2 + rZeroRadialPosition z.1 ^ 2 * towerPitch z ^ 2) :=
  normalizedRadius_eq_pitch z hx

end RHV6Fresh
