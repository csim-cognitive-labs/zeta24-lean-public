/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.ZetaSmoothedUnsmoothingP5
import RHV3Lean.Objects.ExplicitFormulaArithmeticBridge

/-!
# RHV3Lean — raccord entre la reconstruction zéro-source et `rPiMangoldt`/`rPiWeighted`

Ce fichier existe séparément de `ZetaSmoothedUnsmoothingP5.lean` pour éviter un
cycle d'imports : `ZeroSourceExplicitFormulaChannel` (qui définit
`rPsiZeroChannel` via `psiRecoveredFromZeros`) importe
`ZetaSmoothedUnsmoothingP5`, tandis que `ExplicitFormulaArithmeticBridge`
(qui définit `rPiMangoldt`/`rPiWeighted`) est lui-même importé par
`ZeroSourceExplicitFormulaChannel`. Les deux théorèmes ci-dessous, qui relient
`PiMangoldtFromZeros` (côté zéro) à `rPiMangoldt`/`rPiWeighted` (côté
arithmétique), ne sont consommés par aucun des deux et vivent donc au-dessus
des deux dans l'ordre d'import, sans casser rien.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV3Lean

theorem PiMangoldtFromZeros_eq_PiMangoldt
    {x : ℝ}
    (hx : 2 ≤ x) :
    PiMangoldtFromZeros x = rPiMangoldt x := by
  unfold PiMangoldtFromZeros
  rw [thm_piMangoldt_eq_psi_abel_raw hx]
  rw [psiRecoveredFromZeros_eq_psi hx]
  simp only [Complex.ofReal_re]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc 2 x := by
    simpa [Set.uIcc_of_le hx] using ht
  have ht2 : 2 ≤ t := ht'.1
  have hpsi : (psiRecoveredFromZeros t).re = Chebyshev.psi t := by
    rw [psiRecoveredFromZeros_eq_psi ht2]
    simp
  simp [hpsi]

theorem smoothed_formula_recovers_weighted_prime_count
    {x : ℝ}
    (hx : 2 ≤ x) :
    PiMangoldtFromZeros x =
      rPiWeighted x ⌊Real.log x / Real.log 2⌋₊ := by
  rw [PiMangoldtFromZeros_eq_PiMangoldt hx]
  exact thm_piMangoldt_eq_piWeighted hx

#check PiMangoldtFromZeros_eq_PiMangoldt
#check smoothed_formula_recovers_weighted_prime_count

end RHV3Lean
