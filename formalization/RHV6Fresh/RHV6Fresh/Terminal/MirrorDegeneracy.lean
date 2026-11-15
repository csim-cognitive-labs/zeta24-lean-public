/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TranslationVsProgression
import RHV6Fresh.Terminal.HorizontalExclusion
import RHV6Fresh.Terminal.VerticalEnergyPush

/-!
# RHV6Fresh — dégénérescence du mécanisme miroir sur la ligne critique (2026-09-28)

Chaîne demandée par l'auteur, rendue exacte :

```
Δβ := β* − β = 1 − 2β                                   (D1, tout zéro)
β = 1/2 ⟹ Δβ = 0 ⟹ Δφ = 0 ⟹ ΔC_k = 0 ∀k ⟹ ΔE(q) = 0 ∀q   (D3, sur la ligne)
```

et ses réciproques (D4) : UN seul `ΔC_k = 0`, ou `Δφ = 0`, ou `Δβ = 0`, force déjà `β = 1/2`.

Fait structurel supplémentaire (D2, tout zéro) : la translation miroir des rayons est UNIFORME —
`C_k(z*) / C_k(z) = exp((φ* − φ)/T)` pour tout `k`, indépendant de `k`. Sur la ligne ce rapport
vaut `1` ; hors ligne il est `≠ 1` pour TOUS les `k` à la fois : le mécanisme horizontal est soit
totalement dégénéré (ligne), soit totalement actif (hors ligne), jamais partiel.

Verdict honnête : tout ceci est de la géométrie de la Tour, vraie pour tout zéro ; la
dégénérescence sur la ligne est un théorème, l'ACTIVITÉ hors ligne aussi. Aucune contradiction :
le passage horizontal reste exactement `HorizontalMirrorRealization`, exclu ssi RH.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## D1 — le déplacement horizontal zéro → miroir -/

/-- **`Δβ = β* − β = 1 − 2β`**, pour tout zéro. -/
theorem mirror_radial_shift (z : TrueZero) :
    rZeroRadialPosition (mirrorMember z).1 - rZeroRadialPosition z.1 =
      1 - 2 * rZeroRadialPosition z.1 := by
  rw [mirrorMember_radial]; ring

/-- **`Δβ = 0 ⟺ β = 1/2`**. -/
theorem mirror_radial_shift_eq_zero_iff (z : TrueZero) :
    rZeroRadialPosition (mirrorMember z).1 - rZeroRadialPosition z.1 = 0 ↔
      rZeroRadialPosition z.1 = 1 / 2 := by
  rw [mirror_radial_shift]
  constructor <;> intro h <;> linarith

/-! ## D2 — la translation miroir des rayons est uniforme en `k` -/

/-- **`C_k(z*) = C_k(z) · exp((φ* − φ)/T)` pour tout `k`** : la translation horizontale des rayons
est un facteur multiplicatif UNIQUE, indépendant du rayon. -/
theorem mirror_contact_ratio_const (z : TrueZero) (k : ℤ) :
    contactMinusAt (mirrorMember z) k =
      contactMinusAt z k *
        Real.exp (((towerMotionOf (mirrorMember z)).phase - (towerMotionOf z).phase) /
          rZeroHeight z.1) := by
  unfold contactMinusAt
  rw [towerMotion_incidence, towerMotion_incidence, mirrorMember_ordinate, ← Real.exp_add]
  congr 1
  have hT : rZeroHeight z.1 ≠ 0 := z.2.ne'
  field_simp
  ring

/-- Le facteur de translation vaut `1` ssi `Δφ = 0`. -/
theorem mirror_translation_factor_eq_one_iff (z : TrueZero) :
    Real.exp (((towerMotionOf (mirrorMember z)).phase - (towerMotionOf z).phase) /
        rZeroHeight z.1) = 1 ↔
      (towerMotionOf (mirrorMember z)).phase - (towerMotionOf z).phase = 0 := by
  rw [Real.exp_eq_one_iff, div_eq_zero_iff]
  have hT : rZeroHeight z.1 ≠ 0 := z.2.ne'
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hT
  · intro h; exact Or.inl h

/-! ## D3 — sur la ligne, la chaîne complète de dégénérescence -/

/-- **`Δφ = 0` sur la ligne.** -/
theorem mirror_phase_shift_eq_zero_of_onLine {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 = 1 / 2) :
    (towerMotionOf (mirrorMember z)).phase - (towerMotionOf z).phase = 0 := by
  rw [mirrorMember_eq_self_of_onLine hβ, sub_self]

/-- **`ΔC_k = 0` pour tout `k`, sur la ligne** (les deux contacts de chaque cellule). -/
theorem mirror_contacts_eq_of_onLine {z : TrueZero} (hβ : rZeroRadialPosition z.1 = 1 / 2)
    (k : ℤ) :
    contactMinusAt (mirrorMember z) k = contactMinusAt z k ∧
      contactPlusAt (mirrorMember z) k = contactPlusAt z k := by
  rw [mirrorMember_eq_self_of_onLine hβ]; exact ⟨rfl, rfl⟩

/-- **`ΔE(q) = 0` pour tout `q`, sur la ligne** : le terme explicite lui-même coïncide, pas
seulement son amplitude. -/
theorem mirror_zeroTerm_eq_of_onLine {z : TrueZero} (hβ : rZeroRadialPosition z.1 = 1 / 2)
    (q : ℝ) : zeroTerm (mirrorMember z) q = zeroTerm z q := by
  rw [mirrorMember_eq_self_of_onLine hβ]

/-- **La chaîne de l'auteur, compilée** :
`β = 1/2 ⟹ Δβ = 0 ∧ Δφ = 0 ∧ (∀ k, ΔC⁻_k = 0 ∧ ΔC⁺_k = 0) ∧ (∀ q, ΔE(q) = 0)`.
Le mécanisme miroir horizontal est totalement dégénéré sur la ligne. -/
theorem mirror_degeneracy_of_onLine {z : TrueZero} (hβ : rZeroRadialPosition z.1 = 1 / 2) :
    rZeroRadialPosition (mirrorMember z).1 - rZeroRadialPosition z.1 = 0 ∧
      (towerMotionOf (mirrorMember z)).phase - (towerMotionOf z).phase = 0 ∧
      (∀ k : ℤ, contactMinusAt (mirrorMember z) k = contactMinusAt z k ∧
        contactPlusAt (mirrorMember z) k = contactPlusAt z k) ∧
      (∀ q : ℝ, zeroTerm (mirrorMember z) q = zeroTerm z q) :=
  ⟨(mirror_radial_shift_eq_zero_iff z).mpr hβ, mirror_phase_shift_eq_zero_of_onLine hβ,
    mirror_contacts_eq_of_onLine hβ, mirror_zeroTerm_eq_of_onLine hβ⟩

/-! ## D4 — réciproques : la moindre coïncidence force la ligne -/

/-- **`Δφ = 0 ⟹ β = 1/2`** (injectivité de `arctan`, puis de `T/β`). -/
theorem onLine_of_mirror_phase_shift_eq_zero {z : TrueZero}
    (h : (towerMotionOf (mirrorMember z)).phase - (towerMotionOf z).phase = 0) :
    rZeroRadialPosition z.1 = 1 / 2 := by
  have hk := (contactMinus_eq_iff_radial_eq (mirrorMember z) z (mirrorMember_ordinate z) 0).mp
    (by rw [mirror_contact_ratio_const, (mirror_translation_factor_eq_one_iff z).mpr h, mul_one])
  rw [mirrorMember_radial] at hk
  linarith

/-- **UN seul `ΔC_k = 0` ⟹ β = 1/2** (déjà `mirror_contact_eq_iff_onLine`, rappelé ici comme
réciproque de D3). -/
theorem onLine_of_mirror_contact_eq {z : TrueZero} {k : ℤ}
    (h : contactMinusAt (mirrorMember z) k = contactMinusAt z k) :
    rZeroRadialPosition z.1 = 1 / 2 :=
  (mirror_contact_eq_iff_onLine z k).mp h

/-- **L'équivalence complète** : `β = 1/2 ⟺ Δβ = 0 ⟺ Δφ = 0 ⟺ (∃ k, ΔC_k = 0) ⟺ (∀ k, ΔC_k = 0)`. -/
theorem mirror_degeneracy_tfae (z : TrueZero) :
    [rZeroRadialPosition z.1 = 1 / 2,
      rZeroRadialPosition (mirrorMember z).1 - rZeroRadialPosition z.1 = 0,
      (towerMotionOf (mirrorMember z)).phase - (towerMotionOf z).phase = 0,
      ∃ k : ℤ, contactMinusAt (mirrorMember z) k = contactMinusAt z k,
      ∀ k : ℤ, contactMinusAt (mirrorMember z) k = contactMinusAt z k].TFAE := by
  tfae_have 1 → 2 := fun h => (mirror_radial_shift_eq_zero_iff z).mpr h
  tfae_have 2 → 1 := fun h => (mirror_radial_shift_eq_zero_iff z).mp h
  tfae_have 1 → 3 := fun h => mirror_phase_shift_eq_zero_of_onLine h
  tfae_have 3 → 1 := fun h => onLine_of_mirror_phase_shift_eq_zero h
  tfae_have 1 → 5 := fun h k => (mirror_contacts_eq_of_onLine h k).1
  tfae_have 5 → 4 := fun h => ⟨0, h 0⟩
  tfae_have 4 → 1 := fun ⟨_, hk⟩ => onLine_of_mirror_contact_eq hk
  tfae_finish

/-! ## D5 — hors ligne : le mécanisme est TOTALEMENT actif, jamais partiel -/

/-- **Hors ligne, TOUS les rayons sont translatés à la fois**, par le même facteur `≠ 1`. -/
theorem mirror_all_contacts_shift_of_offLine {z : TrueZero}
    (hOff : PIsOffCriticalLine z.1) :
    Real.exp (((towerMotionOf (mirrorMember z)).phase - (towerMotionOf z).phase) /
        rZeroHeight z.1) ≠ 1 ∧
      ∀ k : ℤ, contactMinusAt (mirrorMember z) k ≠ contactMinusAt z k := by
  refine ⟨fun h => hOff (onLine_of_mirror_phase_shift_eq_zero
    ((mirror_translation_factor_eq_one_iff z).mp h)), fun k h => hOff (onLine_of_mirror_contact_eq h)⟩

/-! ## D6 — les deux modes : horizontal (translation rigide, pas inchangé) et vertical (pas changé)

Précision de l'auteur : `Δβ ≠ 0, ΔT = 0` est un DÉPLACEMENT dans l'espace des zéros ; son effet
géométrique est une translation de phase, transmise rigidement à tous les rayons, sans changer le
pas `π/T`. `Δβ = 0, ΔT ≠ 0` change le pas. Ce sont des translations, pas des forces ; une « force »
exige une énergie dont la translation est l'action — cette énergie EST compilée
(`‖zeroTerm z q‖ = q^β/‖ρ‖`), et son action le long du déplacement horizontal est D6.4. -/

/-- **Mode horizontal, D6.1** : à même hauteur, quelle que soit la paire `(z, w)`, la grille de `w`
est la grille de `z` translatée par le facteur UNIQUE `exp((φ_w − φ_z)/T)`, pour tout `k`. -/
theorem sameHeight_grid_rigid_translation (z w : TrueZero)
    (hT : rZeroHeight z.1 = rZeroHeight w.1) (k : ℤ) :
    contactMinusAt w k =
      contactMinusAt z k *
        Real.exp (((towerMotionOf w).phase - (towerMotionOf z).phase) / rZeroHeight z.1) := by
  unfold contactMinusAt
  rw [towerMotion_incidence, towerMotion_incidence, ← hT, ← Real.exp_add]
  congr 1
  have hTne : rZeroHeight z.1 ≠ 0 := z.2.ne'
  field_simp
  ring

/-- **Mode horizontal, D6.2** : le pas logarithmique de la Tour est INVARIANT sous tout déplacement
horizontal — `log C_{k+1} − log C_k = π/T` ne voit pas `β`. -/
theorem sameHeight_pitch_invariant (z w : TrueZero)
    (hT : rZeroHeight z.1 = rZeroHeight w.1) (k : ℤ) :
    Real.log (contactPlusAt w k) - Real.log (contactMinusAt w k) =
      Real.log (contactPlusAt z k) - Real.log (contactMinusAt z k) := by
  rw [contactAt_consecutive_logWidth, contactAt_consecutive_logWidth, hT]

/-- **Mode vertical, D6.3** : à même position radiale, un changement de hauteur change le pas ; la
grille n'est PAS translatée rigidement (le rapport `C_k(w)/C_k(z)` dépend de `k`). -/
theorem sameRadial_height_changes_pitch (z w : TrueZero)
    (hT : rZeroHeight z.1 ≠ rZeroHeight w.1) (k : ℤ) :
    Real.log (contactPlusAt w k) - Real.log (contactMinusAt w k) ≠
      Real.log (contactPlusAt z k) - Real.log (contactMinusAt z k) := by
  rw [contactAt_consecutive_logWidth, contactAt_consecutive_logWidth]
  intro h
  have hz : (0 : ℝ) < rZeroHeight z.1 := z.2
  have hw : (0 : ℝ) < rZeroHeight w.1 := w.2
  rw [div_eq_div_iff hw.ne' hz.ne'] at h
  exact hT (mul_left_cancel₀ Real.pi_pos.ne' h)

/-- **L'action énergétique du déplacement horizontal, D6.4** : pour deux zéros de même hauteur,
`log E_w(q) − log E_z(q) = Δβ · log q − log(‖ρ_w‖/‖ρ_z‖)`. C'est la quantité dont V2/V3
(`VerticalEnergyPush.lean`) établissent le signe : positive dès `q ≥ 2`, `T ≥ 2`, `Δβ > 0`. -/
theorem horizontal_energy_action (z w : TrueZero) {q : ℝ} (hq : 0 < q) :
    Real.log ‖zeroTerm w q‖ - Real.log ‖zeroTerm z q‖ =
      (rZeroRadialPosition w.1 - rZeroRadialPosition z.1) * Real.log q -
        (Real.log ‖zeroPoint w‖ - Real.log ‖zeroPoint z‖) := by
  rw [zeroTerm_norm hq, zeroTerm_norm hq,
    Real.log_div (Real.rpow_pos_of_pos hq _).ne' (zeroPoint_norm_pos w).ne',
    Real.log_div (Real.rpow_pos_of_pos hq _).ne' (zeroPoint_norm_pos z).ne',
    Real.log_rpow hq, Real.log_rpow hq]
  ring

/-- **Sur la ligne, l'action horizontale est nulle** : `Δβ = 0` et `‖ρ*‖ = ‖ρ‖`, donc
`log E_{z*}(q) − log E_z(q) = 0` pour tout `q > 0`. -/
theorem horizontal_energy_action_zero_of_onLine {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 = 1 / 2) (q : ℝ) :
    Real.log ‖zeroTerm (mirrorMember z) q‖ - Real.log ‖zeroTerm z q‖ = 0 := by
  rw [mirror_zeroTerm_eq_of_onLine hβ, sub_self]

#print axioms sameHeight_grid_rigid_translation
#print axioms sameHeight_pitch_invariant
#print axioms sameRadial_height_changes_pitch
#print axioms horizontal_energy_action
#print axioms mirror_radial_shift
#print axioms mirror_contact_ratio_const
#print axioms mirror_degeneracy_of_onLine
#print axioms mirror_degeneracy_tfae
#print axioms mirror_all_contacts_shift_of_offLine

end RHV6Fresh
