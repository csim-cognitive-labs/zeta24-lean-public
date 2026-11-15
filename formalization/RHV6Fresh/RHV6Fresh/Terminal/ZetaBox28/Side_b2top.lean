/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaBoxNumeric
import RHV6Fresh.Terminal.ZetaBox28.Side_b2top_c0
/-!
# Certificat (V2), côté b2top (b2)

Fichier GENERE par `experiments/e192_zeta_box_certificate_generator.py` : constantes rationnelles calculees en
arithmetique exacte puis verifiees par Lean (`norm_num`, `linarith`, `decide`). Aucune preuve admise, aucun axiome ajoute.
-/

set_option maxHeartbeats 4000000
set_option linter.style.longLine false

namespace RHV6Fresh
namespace ZB
namespace Cert
namespace H28

open Complex Set

def xL_b2top : List ℤ := [24, 34, 46, 64]
def zL_b2top : List ℤ := [0, 0, 0]
noncomputable def xF_b2top (k : ℕ) : ℝ := ((xL_b2top.getD k 0 : ℤ) : ℝ) / 32
def zF_b2top (k : ℕ) : ℤ := zL_b2top.getD k 0

set_option maxRecDepth 100000 in
theorem side_b2top : ∫ t in (1 - 1/4:ℝ)..(2:ℝ), logDeriv zetaFactor ((t:ℂ) + ((28:ℝ):ℂ) * I) =
    log (I ^ ((-3):ℤ) * I ^ ((0):ℤ) * zetaFactor ((((2:ℝ)):ℂ) + ((28:ℝ):ℂ) * I)) -
      log (I ^ ((-3):ℤ) * I ^ ((0):ℤ) * zetaFactor ((((1 - 1/4:ℝ)):ℂ) + ((28:ℝ):ℂ) * I)) -
      ((((0) - (0) : ℤ)) : ℂ) * ((Real.pi / 2 : ℝ) * I) := by
  have h := horizontal_side (28:ℝ) (by norm_num) xF_b2top zF_b2top (-3) 2 (list_mono xL_b2top 32 (by norm_num) 3 (by decide)) (by decide) (fun t _ => u1_top t)
    (fun k hk => by interval_cases k; exacts [pc_b2top_0, pc_b2top_1, pc_b2top_2])
  have e0 : xF_b2top 0 = 1 - 1/4 := by norm_num [xF_b2top, xL_b2top]
  have e1 : xF_b2top (2 + 1) = 2 := by norm_num [xF_b2top, xL_b2top]
  have f0 : zF_b2top 0 = 0 := rfl
  have f1 : zF_b2top 2 = 0 := rfl
  rw [e0, e1, f0, f1] at h
  exact h

set_option maxRecDepth 100000 in
theorem nz_b2top : ∀ t ∈ Set.Icc (1 - 1/4:ℝ) (2:ℝ), riemannZeta ((t:ℂ) + ((28:ℝ):ℂ) * I) ≠ 0 := by
  have h := cover xF_b2top (fun t => riemannZeta ((t:ℂ) + ((28:ℝ):ℂ) * I) ≠ 0) 2 (list_mono xL_b2top 32 (by norm_num) 3 (by decide))
    (fun k hk t ht => by interval_cases k; exacts [zeta_ne_of_re_pos (pc_b2top_0 t ht), zeta_ne_of_re_pos (pc_b2top_1 t ht), zeta_ne_of_re_pos (pc_b2top_2 t ht)])
  have e0 : xF_b2top 0 = 1 - 1/4 := by norm_num [xF_b2top, xL_b2top]
  have e1 : xF_b2top (2 + 1) = 2 := by norm_num [xF_b2top, xL_b2top]
  rw [e0, e1] at h
  exact h

end H28
end Cert
end ZB
end RHV6Fresh
