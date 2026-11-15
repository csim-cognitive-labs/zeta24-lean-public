/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.PerronPort.ZetaBounds
import RHV6Fresh.Direct.MirrorCount

/-!
# Région sans zéro inconditionnelle appliquée aux vrais zéros

Classement : théorème indépendant, inconditionnel, démontré depuis les bornes de ζ
(port PNT+ de rhv3_lean, `ZetaZeroFree`) ; il rétrécit la bande admissible d'une première
rupture de régime (membre bas et son miroir) sans fixer `β = 1/2` ; il est aussi vrai dans le
monde témoin `ζ(s−δ)ζ(s+δ)` (région sans zéro translatée), donc il ne sépare pas et ne ferme
pas le but `:854`.

Le théorème `low_member_band_of_height` prend `3 < T` en hypothèse explicite :
`DemonstrationChain` n'est pas importé (module non compilé tant que ses buts sont ouverts).
-/

namespace RHV6Fresh

open RHV3Lean Complex

/-- Borne supérieure : tout vrai zéro de hauteur `> 3` est strictement sous `1 − A/(log T)^9`. -/
theorem zeroFree_radial_upper :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1 / 2 ∧ ∀ w : TrueZero, 3 < rZeroHeight w.1 →
      rZeroRadialPosition w.1 < 1 - A / (Real.log (rZeroHeight w.1)) ^ 9 := by
  obtain ⟨A, hA, hfree⟩ := ZetaZeroFree
  refine ⟨A, hA.1, hA.2, fun w hT => ?_⟩
  by_contra hge
  push_neg at hge
  have hlt : rZeroRadialPosition w.1 < 1 := thm_zeroRadialPosition_lt_one w.1
  have hpos : 0 < rZeroHeight w.1 := lt_trans (by norm_num) hT
  have hz := hfree (rZeroRadialPosition w.1) (rZeroHeight w.1)
    (by rw [abs_of_pos hpos]; exact hT)
    (by rw [abs_of_pos hpos]; exact ⟨hge, hlt⟩)
  apply hz
  have : ((rZeroRadialPosition w.1 : ℝ) : ℂ) + (rZeroHeight w.1 : ℝ) * I = cZeroSupport w.1 := by
    apply Complex.ext <;> simp [rZeroRadialPosition, rZeroHeight]
  rw [this]
  exact thm_zeroProvenance_zeta w.1

/-- Borne inférieure, par application de la borne supérieure au miroir. -/
theorem zeroFree_radial_lower :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1 / 2 ∧ ∀ w : TrueZero, 3 < rZeroHeight w.1 →
      A / (Real.log (rZeroHeight w.1)) ^ 9 < rZeroRadialPosition w.1 := by
  obtain ⟨A, hA, hA2, h⟩ := zeroFree_radial_upper
  refine ⟨A, hA, hA2, fun w hT => ?_⟩
  have := h (mirrorMember w) (by rw [mirrorMember_ordinate]; exact hT)
  rw [mirrorMember_radial, mirrorMember_ordinate] at this
  linarith

/-- Bande commune, un seul `A`. -/
theorem zeroFree_band :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1 / 2 ∧ ∀ w : TrueZero, 3 < rZeroHeight w.1 →
      A / (Real.log (rZeroHeight w.1)) ^ 9 < rZeroRadialPosition w.1 ∧
      rZeroRadialPosition w.1 < 1 - A / (Real.log (rZeroHeight w.1)) ^ 9 := by
  obtain ⟨A, hA, hA2, h⟩ := zeroFree_radial_upper
  refine ⟨A, hA, hA2, fun w hT => ⟨?_, h w hT⟩⟩
  have := h (mirrorMember w) (by rw [mirrorMember_ordinate]; exact hT)
  rw [mirrorMember_radial, mirrorMember_ordinate] at this
  linarith

/-- Membre bas (hauteur `> 3` en hypothèse) : bande du membre et de son miroir. -/
theorem low_member_band_of_height (w : TrueZero) (hT : 3 < rZeroHeight w.1)
    (hβ : rZeroRadialPosition w.1 < 1 / 2) :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1 / 2 ∧
      A / (Real.log (rZeroHeight w.1)) ^ 9 < rZeroRadialPosition w.1 ∧
      rZeroRadialPosition w.1 < 1 / 2 ∧ 1 / 2 < rZeroRadialPosition (mirrorMember w).1 ∧
      rZeroRadialPosition (mirrorMember w).1 < 1 - A / (Real.log (rZeroHeight w.1)) ^ 9 := by
  obtain ⟨A, hA, hA2, h⟩ := zeroFree_band
  obtain ⟨h1, _⟩ := h w hT
  refine ⟨A, hA, hA2, h1, hβ, ?_, ?_⟩
  · rw [mirrorMember_radial]; linarith
  · rw [mirrorMember_radial]; linarith

/-- L'épaisseur admissible `1/2 − A/(log T)^9` est strictement positive dès que
`A/(log T)^9 < β < 1/2`, et elle tend vers `1/2` (cf. `tendsto_zeroFree_margin`). -/
theorem low_member_margin_pos (w : TrueZero) (hT : 3 < rZeroHeight w.1)
    (hβ : rZeroRadialPosition w.1 < 1 / 2) :
    ∃ A : ℝ, 0 < A ∧ 0 < 1 / 2 - A / (Real.log (rZeroHeight w.1)) ^ 9 := by
  obtain ⟨A, hA, _, h1, h2, _⟩ := low_member_band_of_height w hT hβ
  exact ⟨A, hA, by linarith⟩

/-- La marge `A/(log T)^9` tend vers `0` quand `T → ∞` : la bande admissible s'élargit
vers `]0, 1/2[`. -/
theorem tendsto_zeroFree_margin (A : ℝ) :
    Filter.Tendsto (fun T : ℝ => A / (Real.log T) ^ 9) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun T : ℝ => (Real.log T) ^ 9) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  exact h1.const_div_atTop A

#print axioms zeroFree_radial_upper
#print axioms zeroFree_radial_lower
#print axioms zeroFree_band
#print axioms low_member_band_of_height
#print axioms low_member_margin_pos
#print axioms tendsto_zeroFree_margin

end RHV6Fresh
