/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.AnchorStructure
import RHV6Fresh.Terminal.FirstGainPremise
import RHV6Fresh.Terminal.RayCapture
import RHV3Lean.Objects.ZetaReflectionMultiplicity
import RHV3Lean.Objects.ZetaConjugationOrbit

/-!
# Déficit de comptage et saturation ON (auteur, 2026-10-09)

Comptage avec multiplicité dans la moitié supérieure, sur la même fenêtre fermée que `upperCountWithMultiplicity` :
`N(T) = Σ_{0 < Im ρ ≤ T} m_ρ`, `N₀(T)` (membres ON, `Re ρ = 1/2`), `W(T)` (membres BAS, `Re ρ < 1/2`), `W⁺(T)` (membres
HAUTS, `Re ρ > 1/2`). Démontré, axiomes standard :
* partition `N = N₀ + W + W⁺` (`upperCount_eq_on_add_low_add_high`) ;
* réflexion `ρ ↦ 1 − ρ̄` : bijection des bas sur les hauts, même hauteur, même multiplicité (`lowCount_eq_highCount`) ;
* `N = N₀ + 2W` (`upperCount_eq_on_add_two_low`), `N₀ ≤ N`, déficit ENTIER `(N : ℤ) − N₀ = 2W` (`zeroCountDeficit_eq`) ;
* `W` croissant en la hauteur (`lowCount_mono`), `W(T) = 0 ⟺` aucun membre bas de hauteur `≤ T` (`lowCount_eq_zero_iff`) ;
* saturation : `N(T) = 1 ⟹ N(T) = N₀(T)` (`saturation_of_count_one`) ;
* fermeture CONDITIONNELLE : saturation à `H` et inégalité de prolongement `∀ U > H, N₀(U) − N₀(H) ≥ N(U) − N(H)` (différences
  entières) ⟹ aucun membre bas, aucun membre hors ligne, RH (`noLowerSide_of_counting`, `riemannHypothesis_of_counting`) ;
  elle vérifie que l'obligation choisie SUFFIT, elle ne la démontre pas ;
* lecture géométrique : l'inégalité de prolongement est violée exactement par un membre bas de hauteur dans `]H, U]`
  (`extension_violated_iff`), dont le miroir est un membre HAUT, de même hauteur, qui DÉPASSE le champ du premier sur
  l'un de ses contacts authentiques (`upper_member_exceeds_at_contact`) ; sous l'ancre, l'inégalité découle de l'absence de
  membre haut (`extension_of_no_upper`).

Portée : `N₀` compte des zéros ON avec multiplicité analytique ; ce n'est PAS le nombre de changements de signe d'une
fonction réelle (détecteur par existence, `onLine_member_of_sign_change`). RH ⟹ inégalité de prolongement
(`extension_of_riemannHypothesis`) : l'obligation est au plus aussi forte que RH ; elle n'est démontrée nulle part.
Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean Finset
open scoped ComplexConjugate

/-! ## 1. Comptages ON, bas, hauts sur la fenêtre supérieure fermée -/

/-- Comptage ON avec multiplicité : `N₀(T) = Σ_{ρ ∈ fenêtre, Re ρ = 1/2} m_ρ`. -/
noncomputable def onCount (T : ℝ) : ℕ :=
  ∑ ρ ∈ (upperWindow T).filter (fun ρ => ρ.re = 1 / 2), zetaZeroMultiplicity ρ

/-- Comptage des membres BAS avec multiplicité : `W(T) = Σ_{ρ ∈ fenêtre, Re ρ < 1/2} m_ρ`. -/
noncomputable def lowCount (T : ℝ) : ℕ :=
  ∑ ρ ∈ (upperWindow T).filter (fun ρ => ρ.re < 1 / 2), zetaZeroMultiplicity ρ

/-- Comptage des membres HAUTS avec multiplicité : `W⁺(T) = Σ_{ρ ∈ fenêtre, 1/2 < Re ρ} m_ρ`. -/
noncomputable def highCount (T : ℝ) : ℕ :=
  ∑ ρ ∈ (upperWindow T).filter (fun ρ => 1 / 2 < ρ.re), zetaZeroMultiplicity ρ

/-- **Partition** : `N = N₀ + W + W⁺`. -/
theorem upperCount_eq_on_add_low_add_high (T : ℝ) :
    upperCountWithMultiplicity T = onCount T + lowCount T + highCount T := by
  unfold upperCountWithMultiplicity onCount lowCount highCount
  rw [← Finset.sum_filter_add_sum_filter_not (upperWindow T) (fun ρ => ρ.re < 1 / 2)]
  rw [← Finset.sum_filter_add_sum_filter_not ((upperWindow T).filter fun ρ => ¬ ρ.re < 1 / 2)
    (fun ρ => ρ.re = 1 / 2), Finset.filter_filter, Finset.filter_filter]
  have h1 : ((upperWindow T).filter fun ρ => ¬ ρ.re < 1 / 2 ∧ ρ.re = 1 / 2) =
      (upperWindow T).filter fun ρ => ρ.re = 1 / 2 := by
    ext ρ; simp only [Finset.mem_filter]; constructor
    · rintro ⟨h, -, h2⟩; exact ⟨h, h2⟩
    · rintro ⟨h, h2⟩; exact ⟨h, by rw [h2]; exact lt_irrefl _, h2⟩
  have h2 : ((upperWindow T).filter fun ρ => ¬ ρ.re < 1 / 2 ∧ ¬ ρ.re = 1 / 2) =
      (upperWindow T).filter fun ρ => 1 / 2 < ρ.re := by
    ext ρ; simp only [Finset.mem_filter]; constructor
    · rintro ⟨h, h1, h2⟩; exact ⟨h, lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)⟩
    · rintro ⟨h, h1⟩; exact ⟨h, not_lt.mpr h1.le, h1.ne'⟩
  rw [h1, h2]; ring

/-! ## 2. Réflexion : les comptes bas et hauts sont égaux -/

/-- Le point miroir `1 − ρ̄` d'un zéro non trivial est un zéro non trivial de même hauteur, de position radiale `1 − Re ρ`. -/
theorem mirrorPoint_nontrivial {ρ : ℂ} (h : PIsNonTrivialZetaZero ρ) :
    PIsNonTrivialZetaZero (1 - conj ρ) := by
  obtain ⟨hz, h0, h1⟩ := h
  have hc : riemannZeta (conj ρ) = 0 := riemannZeta_conj_eq_zero_of_zero hz
  refine ⟨?_, ?_, ?_⟩
  · exact riemannZeta_zetaReflect_eq_zero hc (by simpa using h0)
  · simp; linarith
  · simp; linarith

/-- La multiplicité analytique est conservée par le miroir `ρ ↦ 1 − ρ̄` (conjugaison puis réflexion fonctionnelle). -/
theorem zetaZeroMultiplicity_mirrorPoint {ρ : ℂ} (h : PIsNonTrivialZetaZero ρ) :
    zetaZeroMultiplicity (1 - conj ρ) = zetaZeroMultiplicity ρ := by
  obtain ⟨hz, h0, h1⟩ := h
  have hc : riemannZeta (conj ρ) = 0 := riemannZeta_conj_eq_zero_of_zero hz
  have h₁ : zetaZeroMultiplicity (RHV3Lean.zetaReflect (conj ρ)) = zetaZeroMultiplicity (conj ρ) :=
    zetaZeroMultiplicity_zetaReflect hc (by simpa using h0) (by simpa using h1)
  have h₂ : zetaZeroMultiplicity (conj ρ) = zetaZeroMultiplicity ρ := zetaZeroMultiplicity_conj hz
  exact h₁.trans h₂

theorem mirrorPoint_mem_upperWindow {T : ℝ} {ρ : ℂ} (h : ρ ∈ upperWindow T) :
    1 - conj ρ ∈ upperWindow T := by
  rw [mem_upperWindow] at h ⊢
  refine ⟨mirrorPoint_nontrivial h.1, ?_, ?_⟩ <;> simp [h.2.1, h.2.2]

theorem mirrorPoint_mirrorPoint (ρ : ℂ) : 1 - conj (1 - conj ρ) = ρ := by
  simp

/-- **La réflexion échange les comptes bas et hauts** : `W(T) = W⁺(T)`, par la bijection `ρ ↦ 1 − ρ̄` entre les membres bas
et les membres hauts de la fenêtre, conservant la hauteur et la multiplicité. -/
theorem lowCount_eq_highCount (T : ℝ) : lowCount T = highCount T := by
  unfold lowCount highCount
  refine Finset.sum_nbij' (fun ρ => 1 - conj ρ) (fun ρ => 1 - conj ρ) ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ ⊢
    refine ⟨mirrorPoint_mem_upperWindow hρ.1, ?_⟩
    have := hρ.2; simp; linarith
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ ⊢
    refine ⟨mirrorPoint_mem_upperWindow hρ.1, ?_⟩
    have := hρ.2; simp; linarith
  · intro ρ _; exact mirrorPoint_mirrorPoint ρ
  · intro ρ _; exact mirrorPoint_mirrorPoint ρ
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ
    exact (zetaZeroMultiplicity_mirrorPoint (mem_upperWindow.mp hρ.1).1).symm

/-- **`N = N₀ + 2W`**. -/
theorem upperCount_eq_on_add_two_low (T : ℝ) :
    upperCountWithMultiplicity T = onCount T + 2 * lowCount T := by
  rw [upperCount_eq_on_add_low_add_high, ← lowCount_eq_highCount]; ring

/-- `N₀ ≤ N`. -/
theorem onCount_le_upperCount (T : ℝ) : onCount T ≤ upperCountWithMultiplicity T := by
  rw [upperCount_eq_on_add_two_low]; omega

/-- **Déficit de comptage**, en entiers relatifs : `(N : ℤ) − N₀`. -/
noncomputable def zeroCountDeficit (T : ℝ) : ℤ :=
  (upperCountWithMultiplicity T : ℤ) - (onCount T : ℤ)

theorem zeroCountDeficit_eq (T : ℝ) : zeroCountDeficit T = 2 * (lowCount T : ℤ) := by
  unfold zeroCountDeficit
  rw [upperCount_eq_on_add_two_low]; push_cast; ring

theorem zeroCountDeficit_nonneg (T : ℝ) : 0 ≤ zeroCountDeficit T := by
  rw [zeroCountDeficit_eq]; positivity

/-! ## 3. Monotonie et annulation du déficit -/

/-- **`W` est croissant** en la hauteur de coupure. -/
theorem lowCount_mono {T U : ℝ} (h : T ≤ U) : lowCount T ≤ lowCount U := by
  unfold lowCount
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
  intro ρ hρ
  rw [Finset.mem_filter, mem_upperWindow] at hρ ⊢
  exact ⟨⟨hρ.1.1, hρ.1.2.1, hρ.1.2.2.trans h⟩, hρ.2⟩

theorem zeroCountDeficit_mono {T U : ℝ} (h : T ≤ U) : zeroCountDeficit T ≤ zeroCountDeficit U := by
  rw [zeroCountDeficit_eq, zeroCountDeficit_eq]
  exact_mod_cast Nat.mul_le_mul_left 2 (lowCount_mono h)

/-- Un membre bas de hauteur `≤ T` est compté dans `W(T)` avec sa multiplicité `≥ 1`. -/
theorem one_le_lowCount_of_low {T : ℝ} (z : TrueZero) (hT : rZeroHeight z.1 ≤ T)
    (hβ : rZeroRadialPosition z.1 < 1 / 2) : 1 ≤ lowCount T := by
  unfold lowCount
  have hmem : zeroPoint z ∈ (upperWindow T).filter (fun ρ => ρ.re < 1 / 2) := by
    rw [Finset.mem_filter]
    exact ⟨mem_upperWindow_iff.mpr ⟨z, rfl, hT⟩, hβ⟩
  calc 1 ≤ zetaZeroMultiplicity (zeroPoint z) :=
        one_le_multiplicity_of_mem_upperWindow (Finset.mem_filter.mp hmem).1
    _ ≤ _ := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem

/-- **`W(T) = 0 ⟺` aucun membre bas de hauteur au plus `T`.** -/
theorem lowCount_eq_zero_iff (T : ℝ) :
    lowCount T = 0 ↔ ∀ z : TrueZero, rZeroHeight z.1 ≤ T → ¬ rZeroRadialPosition z.1 < 1 / 2 := by
  constructor
  · intro h z hT hβ
    have := one_le_lowCount_of_low z hT hβ; omega
  · intro h
    unfold lowCount
    apply Finset.sum_eq_zero
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨w, rfl, hw⟩ := mem_upperWindow_iff.mp hρ.1
    exact absurd hρ.2 (h w hw)

/-- **Saturation** : `N(T) = N₀(T) ⟺ W(T) = 0`. -/
theorem saturation_iff_lowCount_zero (T : ℝ) :
    upperCountWithMultiplicity T = onCount T ↔ lowCount T = 0 := by
  rw [upperCount_eq_on_add_two_low]; omega

/-- **Saturation depuis le comptage égal à un** : `N(T) = 1 ⟹ N(T) = N₀(T)`. L'unique membre de la bande coïncide avec
son miroir (`unique_band_of_count_one`, `onLine_of_unique_band`) ; aucun membre bas n'y est compté. -/
theorem saturation_of_count_one {T : ℝ} (h : upperCountWithMultiplicity T = 1) :
    upperCountWithMultiplicity T = onCount T := by
  rw [saturation_iff_lowCount_zero, lowCount_eq_zero_iff]
  intro z hT hβ
  have hU := unique_band_of_count_one h
  have hOn := onLine_of_unique_band hU hT
  linarith

/-! ## 4. Fermeture conditionnelle : saturation + inégalité de prolongement ⟹ RH -/

/-- **Inégalité de prolongement** à partir de la hauteur `H` : `∀ U > H, N₀(U) − N₀(H) ≥ N(U) − N(H)` en différences
entières. C'est l'obligation ; elle n'est démontrée nulle part dans ce module. -/
def CountingExtension (H : ℝ) : Prop :=
  ∀ U : ℝ, H < U →
    (upperCountWithMultiplicity U : ℤ) - upperCountWithMultiplicity H ≤ (onCount U : ℤ) - onCount H

/-- Sous l'inégalité de prolongement, le déficit n'augmente jamais au-delà de `H`. -/
theorem zeroCountDeficit_le_of_extension {H : ℝ} (hExt : CountingExtension H) {U : ℝ} (hU : H < U) :
    zeroCountDeficit U ≤ zeroCountDeficit H := by
  unfold zeroCountDeficit
  have := hExt U hU; linarith

/-- Saturation à `H` et prolongement ⟹ `W(U) = 0` pour tout `U`. -/
theorem lowCount_eq_zero_of_saturation_extension {H : ℝ}
    (hSat : upperCountWithMultiplicity H = onCount H) (hExt : CountingExtension H) (U : ℝ) :
    lowCount U = 0 := by
  have hH : lowCount H = 0 := (saturation_iff_lowCount_zero H).mp hSat
  rcases le_or_gt U H with hUH | hHU
  · have := lowCount_mono hUH; omega
  · have h1 := zeroCountDeficit_le_of_extension hExt hHU
    rw [zeroCountDeficit_eq, zeroCountDeficit_eq, hH] at h1
    have : (lowCount U : ℤ) ≤ 0 := by push_cast at h1; linarith
    omega

/-- **Aucun membre bas** sous saturation et prolongement. -/
theorem noLowerSide_of_counting {H : ℝ}
    (hSat : upperCountWithMultiplicity H = onCount H) (hExt : CountingExtension H) :
    ∀ z : TrueZero, ¬ rZeroRadialPosition z.1 < 1 / 2 := fun z =>
  (lowCount_eq_zero_iff _).mp (lowCount_eq_zero_of_saturation_extension hSat hExt (rZeroHeight z.1)) z le_rfl

/-- **Aucun membre hors ligne** : un membre haut aurait un miroir bas. -/
theorem noOff_of_counting {H : ℝ}
    (hSat : upperCountWithMultiplicity H = onCount H) (hExt : CountingExtension H) :
    ∀ z : TrueZero, rZeroRadialPosition z.1 = 1 / 2 := by
  intro z
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact noLowerSide_of_counting hSat hExt z h
  · apply noLowerSide_of_counting hSat hExt (mirrorMember z)
    rw [mirrorMember_radial]; linarith

/-- **Fermeture conditionnelle** : saturation certifiée à `H` et inégalité de prolongement ⟹ RH. Cette composition vérifie
que l'obligation SUFFIT ; elle ne la démontre pas. -/
theorem riemannHypothesis_of_counting {H : ℝ}
    (hSat : upperCountWithMultiplicity H = onCount H) (hExt : CountingExtension H) :
    RiemannHypothesis :=
  riemannHypothesis_of_noLowerSide (noLowerSide_of_counting hSat hExt)

/-- RH ⟹ inégalité de prolongement à toute hauteur (le déficit est identiquement nul) : l'obligation est au plus aussi forte
que RH. -/
theorem extension_of_riemannHypothesis (hRH : RiemannHypothesis) (H : ℝ) : CountingExtension H := by
  intro U _
  have hz : ∀ T, lowCount T = 0 := fun T => (lowCount_eq_zero_iff T).mpr fun z _ hβ =>
    absurd (thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1) (ne_of_lt hβ)
  have h1 := upperCount_eq_on_add_two_low U
  have h2 := upperCount_eq_on_add_two_low H
  rw [hz] at h1 h2
  omega

/-! ## 5. Lecture géométrique de la violation : un membre bas, son miroir haut, et le dépassement sur un contact -/

/-- **La violation du prolongement est un membre bas apparu dans `]H, U]`** (sous `W(H) = 0`). -/
theorem extension_violated_iff {H : ℝ} (hSat : upperCountWithMultiplicity H = onCount H) :
    (¬ CountingExtension H) ↔
      ∃ z : TrueZero, H < rZeroHeight z.1 ∧ rZeroRadialPosition z.1 < 1 / 2 := by
  have hH : lowCount H = 0 := (saturation_iff_lowCount_zero H).mp hSat
  constructor
  · intro hNot
    unfold CountingExtension at hNot
    push_neg at hNot
    obtain ⟨U, hU, hlt⟩ := hNot
    have h1 := upperCount_eq_on_add_two_low U
    have h2 := upperCount_eq_on_add_two_low H
    have hpos : 0 < lowCount U := by
      by_contra h0
      push_neg at h0
      have : lowCount U = 0 := by omega
      rw [this] at h1; rw [hH] at h2
      omega
    unfold lowCount at hpos
    obtain ⟨ρ, hρ, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
    rw [Finset.mem_filter] at hρ
    obtain ⟨z, rfl, hz⟩ := mem_upperWindow_iff.mp hρ.1
    refine ⟨z, ?_, hρ.2⟩
    by_contra hle
    push_neg at hle
    exact absurd hρ.2 ((lowCount_eq_zero_iff H).mp hH z hle)
  · rintro ⟨z, hz, hβ⟩ hExt
    exact noLowerSide_of_counting hSat hExt z hβ

/-- Les contacts authentiques d'un membre dépassent toute abscisse : il existe un indice `k ≥ 0` avec `x₀ ≤ C_k`. -/
theorem exists_contact_ge (w : TrueZero) (x₀ : ℝ) : ∃ k : ℤ, 0 ≤ k ∧ x₀ ≤ contactMinusAt w k := by
  have hT : 0 < rZeroHeight w.1 := w.2
  have hφ : 0 ≤ Real.arctan (rZeroHeight w.1 / rZeroRadialPosition w.1) :=
    (Real.arctan_pos.mpr (div_pos hT (thm_zeroRadialPosition_positive w.1))).le
  obtain ⟨k, hk⟩ := exists_nat_ge (rZeroHeight w.1 * Real.log x₀ / Real.pi)
  refine ⟨k, by positivity, ?_⟩
  rw [contactMinusAt_eq_exp]
  rcases le_or_gt x₀ 0 with hx | hx
  · exact hx.trans (Real.exp_pos _).le
  · rw [← Real.log_le_iff_le_exp hx, le_div_iff₀ hT]
    have := (div_le_iff₀ Real.pi_pos).mp hk
    push_cast
    nlinarith [Real.pi_pos]

/-- **Un membre haut dépasse le champ du premier sur l'un de ses contacts authentiques** (sous l'ancre ON) : il existe
`k ≥ 0` avec `A_1 < A_w(C_k)`, et le dépassement persiste sur tous les contacts suivants. -/
theorem upper_member_exceeds_at_contact {z₁ w : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hUp : 1 / 2 < rZeroRadialPosition w.1) :
    ∃ k : ℤ, 0 ≤ k ∧ pairAmplitude z₁ (contactMinusAt w k) < pairAmplitude w (contactMinusAt w k) := by
  obtain ⟨x₀, hx₀, hEx⟩ := (not_insideField_iff_exists_exceedance _ _).mp (upper_not_insideField h₁ hUp)
  obtain ⟨k, hk, hC⟩ := exists_contact_ge w x₀
  exact ⟨k, hk, exceedance_persists h₁ hUp.le (by linarith) hC hEx⟩

/-- **Sous l'ancre, l'absence de membre haut donne l'inégalité de prolongement** : un membre bas apparu après `H` aurait un
miroir haut. Forme exacte de la liaison entre les deux obligations (déficit de comptage, dépassement du champ). -/
theorem extension_of_no_upper {H : ℝ} (hSat : upperCountWithMultiplicity H = onCount H)
    (hNoUp : ∀ w : TrueZero, ¬ 1 / 2 < rZeroRadialPosition w.1) : CountingExtension H := by
  by_contra hNot
  obtain ⟨z, -, hβ⟩ := (extension_violated_iff hSat).mp hNot
  apply hNoUp (mirrorMember z)
  rw [mirrorMember_radial]; linarith

/-- Réciproquement, sous saturation et prolongement il n'y a aucun membre haut. -/
theorem no_upper_of_extension {H : ℝ} (hSat : upperCountWithMultiplicity H = onCount H)
    (hExt : CountingExtension H) : ∀ w : TrueZero, ¬ 1 / 2 < rZeroRadialPosition w.1 := fun w h =>
  absurd (noOff_of_counting hSat hExt w) h.ne'

/-! ## 6. Pas de comptage : la saturation se transmet tant que le comptage avance de moins de deux

Une rupture du régime ON ajoute DEUX unités au comptage (le membre bas et son miroir haut, même hauteur, même
multiplicité) sans en ajouter aucune à `N₀`. Entre deux hauteurs de coupure, si le comptage total avance de moins de deux
et que la bande inférieure est saturée, la bande supérieure l'est aussi : tous ses membres sont ON et coïncident avec leur
miroir. Appliqué aux deux premières bandes (`N(15) = 1`, `N(22) = 2`, valeurs NUMÉRIQUES en hypothèse explicite, jamais
admises) : les deux premiers membres canoniques sont ON, annulent le miroir, et le second est le seul membre de `]15, 22]`.
Les valeurs des comptages restent l'obligation (a)/(b) de la chaîne ; aucune d'elles n'est démontrée ici. -/

/-- `N₀` est croissant en la hauteur de coupure. -/
theorem onCount_mono {T U : ℝ} (h : T ≤ U) : onCount T ≤ onCount U := by
  unfold onCount
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
  intro ρ hρ
  rw [Finset.mem_filter, mem_upperWindow] at hρ ⊢
  exact ⟨⟨hρ.1.1, hρ.1.2.1, hρ.1.2.2.trans h⟩, hρ.2⟩

/-- **Parité** : `N ≡ N₀ (mod 2)` ; un comptage impair contient au moins un membre ON. -/
theorem upperCount_mod_two (T : ℝ) : upperCountWithMultiplicity T % 2 = onCount T % 2 := by
  rw [upperCount_eq_on_add_two_low]; omega

theorem one_le_onCount_of_odd {T : ℝ} (h : upperCountWithMultiplicity T % 2 = 1) : 1 ≤ onCount T := by
  have := upperCount_mod_two T; omega

/-- **`W(T) = 0 ⟹ tout membre de hauteur `≤ T` est ON** : le côté bas est exclu directement, le côté haut par
son miroir, bas et de même hauteur. -/
theorem all_onLine_of_lowCount_zero {T : ℝ} (h : lowCount T = 0) :
    ∀ w : TrueZero, rZeroHeight w.1 ≤ T → rZeroRadialPosition w.1 = 1 / 2 := by
  intro w hw
  have hNoLow := (lowCount_eq_zero_iff T).mp h
  rcases lt_trichotomy (rZeroRadialPosition w.1) (1 / 2) with hlt | heq | hgt
  · exact absurd hlt (hNoLow w hw)
  · exact heq
  · exfalso
    apply hNoLow (mirrorMember w) (mirror_mem_band hw)
    rw [mirrorMember_radial]; linarith

/-- Sous `W(T) = 0`, tout membre de hauteur `≤ T` coïncide avec son miroir (miroir annulé). -/
theorem mirror_annulled_of_lowCount_zero {T : ℝ} (h : lowCount T = 0) {w : TrueZero}
    (hw : rZeroHeight w.1 ≤ T) : mirrorMember w = w :=
  mirrorMember_eq_self_of_onLine (all_onLine_of_lowCount_zero h w hw)

/-- **Pas de comptage** : `T ≤ U`, `W(T) = 0` et `N(U) < N(T) + 2` ⟹ `W(U) = 0`. Une rupture coûterait deux unités. -/
theorem lowCount_eq_zero_of_count_step {T U : ℝ} (hTU : T ≤ U) (hT : lowCount T = 0)
    (hStep : upperCountWithMultiplicity U < upperCountWithMultiplicity T + 2) : lowCount U = 0 := by
  have h1 := upperCount_eq_on_add_two_low T
  have h2 := upperCount_eq_on_add_two_low U
  have h3 := onCount_mono hTU
  omega

/-- Forme en pas de l'inégalité de prolongement : si `W(U) = 0` pour tout `U > H`, le prolongement tient à
partir de `H`. -/
theorem extension_of_lowCount_zero {H : ℝ} (h : ∀ U : ℝ, H < U → lowCount U = 0) : CountingExtension H := by
  intro U hU
  have hWU := h U hU
  have hWH : lowCount H = 0 := Nat.eq_zero_of_le_zero (hWU ▸ lowCount_mono hU.le)
  have h1 := upperCount_eq_on_add_two_low H
  have h2 := upperCount_eq_on_add_two_low U
  omega

/-! ### Les deux premières bandes -/

/-- `N(15) = 1 ∧ N(22) = 2 ⟹ W(22) = 0` : la seconde bande n'ajoute qu'une unité, aucune rupture n'y tient. -/
theorem lowCount_twentytwo_eq_zero (h15 : upperCountWithMultiplicity 15 = 1)
    (h22 : upperCountWithMultiplicity 22 = 2) : lowCount 22 = 0 :=
  lowCount_eq_zero_of_count_step (by norm_num)
    ((saturation_iff_lowCount_zero 15).mp (saturation_of_count_one h15)) (by omega)

/-- **Tout membre de hauteur `≤ 22` est ON et annule son miroir** (sous les deux comptages). -/
theorem all_onLine_le_twentytwo (h15 : upperCountWithMultiplicity 15 = 1)
    (h22 : upperCountWithMultiplicity 22 = 2) :
    ∀ w : TrueZero, rZeroHeight w.1 ≤ 22 →
      rZeroRadialPosition w.1 = 1 / 2 ∧ mirrorMember w = w := fun w hw =>
  ⟨all_onLine_of_lowCount_zero (lowCount_twentytwo_eq_zero h15 h22) w hw,
   mirror_annulled_of_lowCount_zero (lowCount_twentytwo_eq_zero h15 h22) hw⟩

/-- Sous `N(15) = 1 ∧ N(22) = 2`, la fenêtre `22` contient un point distinct du premier zéro (le premier est simple). -/
theorem exists_second_point (h15 : upperCountWithMultiplicity 15 = 1)
    (h22 : upperCountWithMultiplicity 22 = 2) :
    ∃ w : TrueZero, w ≠ canonicalZero 1 ∧ rZeroHeight w.1 ≤ 22 := by
  by_contra hNot
  push_neg at hNot
  have hT₁ : rZeroHeight (canonicalZero 1).1 ≤ 15 := by
    obtain ⟨u, hu, -⟩ := unique_band_of_count_one h15
    rw [unique_band_eq_canonical_one (unique_band_of_count_one h15) hu]; exact hu
  have hsub : upperWindow 22 ⊆ {zeroPoint (canonicalZero 1)} := by
    intro ρ hρ
    obtain ⟨w, rfl, hw⟩ := mem_upperWindow_iff.mp hρ
    rw [Finset.mem_singleton]
    by_cases hw1 : w = canonicalZero 1
    · rw [hw1]
    · exact absurd hw (not_le.mpr (hNot w hw1))
  have hle : upperCountWithMultiplicity 22 ≤ zetaZeroMultiplicity (zeroPoint (canonicalZero 1)) := by
    unfold upperCountWithMultiplicity
    calc ∑ ρ ∈ upperWindow 22, zetaZeroMultiplicity ρ
        ≤ ∑ ρ ∈ ({zeroPoint (canonicalZero 1)} : Finset ℂ), zetaZeroMultiplicity ρ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
      _ = _ := Finset.sum_singleton _ _
  rw [simple_of_count_one h15 hT₁] at hle
  omega

/-- **Le second membre canonique a une hauteur au plus `22`** (sous les deux comptages). -/
theorem canonicalZero_two_height_le (h15 : upperCountWithMultiplicity 15 = 1)
    (h22 : upperCountWithMultiplicity 22 = 2) : rZeroHeight (canonicalZero 2).1 ≤ 22 := by
  obtain ⟨w, hne, hw⟩ := exists_second_point h15 h22
  obtain ⟨n, rfl⟩ := canonicalMember_surjective w
  have hn : 1 ≤ n := Nat.pos_of_ne_zero fun h => hne (by rw [h]; rfl)
  exact (canonicalMember_height_mono hn).trans hw

/-- **Les deux premiers membres canoniques sont ON et annulent leur miroir** (sous `N(15) = 1 ∧ N(22) = 2`). -/
theorem first_two_canonical_onLine (h15 : upperCountWithMultiplicity 15 = 1)
    (h22 : upperCountWithMultiplicity 22 = 2) :
    (rZeroRadialPosition (canonicalZero 1).1 = 1 / 2 ∧
      mirrorMember (canonicalZero 1) = canonicalZero 1) ∧
    (rZeroRadialPosition (canonicalZero 2).1 = 1 / 2 ∧
      mirrorMember (canonicalZero 2) = canonicalZero 2) := by
  have hT₁ : rZeroHeight (canonicalZero 1).1 ≤ 22 :=
    (canonicalMember_height_mono (Nat.zero_le 1)).trans (canonicalZero_two_height_le h15 h22)
  exact ⟨all_onLine_le_twentytwo h15 h22 _ hT₁,
    all_onLine_le_twentytwo h15 h22 _ (canonicalZero_two_height_le h15 h22)⟩

/-- Le second membre canonique est strictement au-dessus de quinze : la première bande ne contient que le
premier. -/
theorem canonicalZero_two_height_gt (h15 : upperCountWithMultiplicity 15 = 1) :
    15 < rZeroHeight (canonicalZero 2).1 := by
  by_contra h
  have hU := unique_band_of_count_one h15
  have := unique_band_eq_canonical_one hU (not_lt.mp h)
  have hinj := canonicalMember_injective (show canonicalMember 0 = canonicalMember 1 from this)
  omega


/-! ## 7. Bandes certifiées à des coupures quelconques (coupures d'E176 : 14, 17, 23, 28)

Généralisation des lemmes de §6 à toute suite de coupures, sans rien réécrire de §6 : un pas de comptage `N(a) < N(b)`
place le membre canonique de rang suivant dans `]a, b]`, et le pas « +1 » propage `W = 0` (`lowCount_eq_zero_of_count_step`). -/

/-- La fenêtre fermée croît avec la coupure. -/
theorem upperWindow_mono {a b : ℝ} (h : a ≤ b) : upperWindow a ⊆ upperWindow b := by
  intro ρ hρ
  obtain ⟨w, rfl, hw⟩ := mem_upperWindow_iff.mp hρ
  exact mem_upperWindow_iff.mpr ⟨w, rfl, hw.trans h⟩

/-- Si les `k + 1` premiers membres canoniques sont sous `a`, le comptage en `a` vaut au moins `k + 1`. -/
theorem upperCount_ge_of_canonical_le {a : ℝ} {k : ℕ} (h : rZeroHeight (canonicalMember k).1 ≤ a) :
    k + 1 ≤ upperCountWithMultiplicity a := by
  have hsub : (Finset.range (k + 1)).image (fun j => zeroPoint (canonicalMember j)) ⊆ upperWindow a := by
    intro ρ hρ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hρ
    exact mem_upperWindow_iff.mpr ⟨canonicalMember j, rfl,
      (canonicalMember_height_mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).trans h⟩
  have hinj : Set.InjOn (fun j => zeroPoint (canonicalMember j)) ((Finset.range (k + 1) : Finset ℕ) : Set ℕ) := by
    intro i _ j _ hij
    apply canonicalMember_injective
    apply Subtype.ext; apply Subtype.ext; exact hij
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
  exact hcard.trans (upperWindow_card_le_count a)

/-- **Pas de comptage localisant** : si les `k` premiers membres canoniques sont sous `a`, `N(a) ≤ k` et
`N(a) < N(b)` (`a ≤ b`), le membre canonique d'index `k` (rang `k + 1`) est dans `]a, b]`. -/
theorem canonical_in_band_of_count_step {a b : ℝ} {k : ℕ} (hab : a ≤ b)
    (hk : ∀ j < k, rZeroHeight (canonicalMember j).1 ≤ a) (ha : upperCountWithMultiplicity a ≤ k)
    (hstep : upperCountWithMultiplicity a < upperCountWithMultiplicity b) :
    a < rZeroHeight (canonicalMember k).1 ∧ rZeroHeight (canonicalMember k).1 ≤ b := by
  refine ⟨lt_of_not_ge fun h => ?_, ?_⟩
  · have := upperCount_ge_of_canonical_le h; omega
  · have hne : ¬ upperWindow b ⊆ upperWindow a := by
      intro hsub
      have : upperCountWithMultiplicity b ≤ upperCountWithMultiplicity a := by
        unfold upperCountWithMultiplicity
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
      omega
    obtain ⟨ρ, hρb, hρa⟩ := Finset.not_subset.mp hne
    obtain ⟨w, rfl, hwb⟩ := mem_upperWindow_iff.mp hρb
    have hwa : a < rZeroHeight w.1 := lt_of_not_ge fun h => hρa (mem_upperWindow_iff.mpr ⟨w, rfl, h⟩)
    obtain ⟨m, rfl⟩ := canonicalMember_surjective w
    have hkm : k ≤ m := by
      by_contra hlt
      exact absurd (hk m (not_le.mp hlt)) (not_le.mpr hwa)
    exact (canonicalMember_height_mono hkm).trans hwb

/-- **Les trois premiers membres canoniques, aux coupures certifiées** `c₀ ≤ c₁ ≤ c₂ ≤ c₃` avec comptages
`0, 1, 2, 3` (E176 : `14, 17, 23, 28`) : chacun dans sa tranche `]c_{i−1}, c_i]`, ON, miroir annulé ; tout membre de
hauteur `≤ c₃` est ON. -/
theorem first_three_canonical_onLine {c₀ c₁ c₂ c₃ : ℝ} (h01 : c₀ ≤ c₁) (h12 : c₁ ≤ c₂) (h23 : c₂ ≤ c₃)
    (hN₀ : upperCountWithMultiplicity c₀ = 0) (hN₁ : upperCountWithMultiplicity c₁ = 1)
    (hN₂ : upperCountWithMultiplicity c₂ = 2) (hN₃ : upperCountWithMultiplicity c₃ = 3) :
    (c₀ < rZeroHeight (canonicalMember 0).1 ∧ rZeroHeight (canonicalMember 0).1 ≤ c₁) ∧
    (c₁ < rZeroHeight (canonicalMember 1).1 ∧ rZeroHeight (canonicalMember 1).1 ≤ c₂) ∧
    (c₂ < rZeroHeight (canonicalMember 2).1 ∧ rZeroHeight (canonicalMember 2).1 ≤ c₃) ∧
    (∀ j < 3, rZeroRadialPosition (canonicalMember j).1 = 1 / 2 ∧
      mirrorMember (canonicalMember j) = canonicalMember j) ∧
    (∀ w : TrueZero, rZeroHeight w.1 ≤ c₃ → rZeroRadialPosition w.1 = 1 / 2) := by
  have b0 := canonical_in_band_of_count_step (k := 0) h01 (fun j hj => absurd hj (Nat.not_lt_zero j))
    (by omega) (by omega)
  have b1 := canonical_in_band_of_count_step (k := 1) h12
    (fun j hj => by obtain rfl : j = 0 := by omega
                    exact b0.2) (by omega) (by omega)
  have b2 := canonical_in_band_of_count_step (k := 2) h23
    (fun j hj => by
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact b0.2.trans h12
      · exact b1.2) (by omega) (by omega)
  have hW₀ : lowCount c₀ = 0 := by
    have := upperCount_eq_on_add_two_low c₀; omega
  have hW₃ : lowCount c₃ = 0 :=
    lowCount_eq_zero_of_count_step h23
      (lowCount_eq_zero_of_count_step h12
        (lowCount_eq_zero_of_count_step h01 hW₀ (by omega)) (by omega)) (by omega)
  have hle : ∀ j < 3, rZeroHeight (canonicalMember j).1 ≤ c₃ := fun j hj => by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · exact b0.2.trans (h12.trans h23)
    · exact b1.2.trans h23
    · exact b2.2
  exact ⟨b0, b1, b2, fun j hj => ⟨all_onLine_of_lowCount_zero hW₃ _ (hle j hj),
    mirror_annulled_of_lowCount_zero hW₃ (hle j hj)⟩, all_onLine_of_lowCount_zero hW₃⟩

/-- Transport de coupure : `N(15) = 1` et `N(17) = 1` désignent la même bande (aucun membre dans `]15, 17]`). -/
theorem upperCount_band_eq {a b : ℝ} (hab : a ≤ b) (h : upperCountWithMultiplicity a = upperCountWithMultiplicity b) :
    ∀ w : TrueZero, rZeroHeight w.1 ≤ b → rZeroHeight w.1 ≤ a := by
  intro w hw
  by_contra hlt
  have hsub : upperWindow a ⊆ upperWindow b := upperWindow_mono hab
  have hmem : zeroPoint w ∈ upperWindow b \ upperWindow a := Finset.mem_sdiff.mpr
    ⟨mem_upperWindow_iff.mpr ⟨w, rfl, hw⟩, fun hm => by
      obtain ⟨v, hv, hva⟩ := mem_upperWindow_iff.mp hm
      have : v = w := by apply Subtype.ext; apply Subtype.ext; exact hv
      exact hlt (this ▸ hva)⟩
  have hlt' : upperCountWithMultiplicity a < upperCountWithMultiplicity b := by
    unfold upperCountWithMultiplicity
    rw [← Finset.sum_sdiff hsub]
    have : 0 < ∑ ρ ∈ upperWindow b \ upperWindow a, zetaZeroMultiplicity ρ :=
      Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨_, hmem,
        one_le_multiplicity_of_mem_upperWindow (Finset.mem_sdiff.mp hmem).1⟩
    omega
  omega


end RHV6Fresh

#print axioms RHV6Fresh.lowCount_eq_highCount
#print axioms RHV6Fresh.upperCount_eq_on_add_two_low
#print axioms RHV6Fresh.zeroCountDeficit_eq
#print axioms RHV6Fresh.lowCount_mono
#print axioms RHV6Fresh.saturation_of_count_one
#print axioms RHV6Fresh.riemannHypothesis_of_counting
#print axioms RHV6Fresh.extension_of_riemannHypothesis
#print axioms RHV6Fresh.extension_violated_iff
#print axioms RHV6Fresh.upper_member_exceeds_at_contact
#print axioms RHV6Fresh.extension_of_no_upper
#print axioms RHV6Fresh.upperCount_eq_on_add_low_add_high
#print axioms RHV6Fresh.onCount_le_upperCount
#print axioms RHV6Fresh.zeroCountDeficit_mono
#print axioms RHV6Fresh.lowCount_eq_zero_iff
#print axioms RHV6Fresh.saturation_iff_lowCount_zero
#print axioms RHV6Fresh.noLowerSide_of_counting
#print axioms RHV6Fresh.noOff_of_counting
#print axioms RHV6Fresh.exists_contact_ge
#print axioms RHV6Fresh.no_upper_of_extension
#print axioms RHV6Fresh.mirrorPoint_nontrivial
#print axioms RHV6Fresh.zetaZeroMultiplicity_mirrorPoint
#print axioms RHV6Fresh.onCount_mono
#print axioms RHV6Fresh.all_onLine_of_lowCount_zero
#print axioms RHV6Fresh.lowCount_eq_zero_of_count_step
#print axioms RHV6Fresh.extension_of_lowCount_zero
#print axioms RHV6Fresh.first_two_canonical_onLine
#print axioms RHV6Fresh.canonicalZero_two_height_le
#print axioms RHV6Fresh.canonicalZero_two_height_gt
#print axioms RHV6Fresh.canonical_in_band_of_count_step
#print axioms RHV6Fresh.first_three_canonical_onLine
#print axioms RHV6Fresh.upperCount_band_eq
