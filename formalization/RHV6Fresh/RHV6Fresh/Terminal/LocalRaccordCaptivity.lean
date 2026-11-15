/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.DoubleRigidity
import RHV6Fresh.Terminal.PrimalEventRaccord
import RHV6Fresh.Terminal.InverseReading
import RHV6Fresh.Terminal.RegimeCell

/-!
# RHV6Fresh — captivité locale au raccord exact, renouvelée de raccord en raccord (auteur, 2026-10-04)

Revue de l'auteur : l'objet n'est pas la comparaison de chaque Tour à la première jusqu'à l'infini, ni une
borne globale du reste. Pour deux Tours successives,

    ‖Z_l(x)‖ / ‖Z_e(x)‖ = x^{β_l − β_e} · ‖ρ_e‖ / ‖ρ_l‖,

et la captivité recherchée est l'inégalité `≤ 1` au seul premier du raccord, répétée à chaque événement.

Seconde revue de l'auteur (2026-10-04) : la captivité locale est définie par l'inégalité d'énergie elle-même,
sans passer par l'orientation du raccord ; ses deux directions sont démontrées par le budget, sans importer
le théorème d'orientation ; l'identification avec l'orientation du raccord est un théorème séparé.

* **§1 Le budget local** : coût de sortie `(β_l − β_e)·log x`, disponible `log ‖ρ_l‖ − log ‖ρ_e‖` ; la Tour
  d'arrivée est sous la Tour de départ en `x` ⟺ coût ≤ disponible (`successive_tower_ratio`,
  `tower_le_iff_local_budget`, `localCaptivity_iff_budget`). Ni phase, ni reste : deux modules et un premier.
* **§2 Le budget calculé au raccord exact** : dès que la position radiale ne monte pas et que la hauteur ne
  recule pas, le disponible peut être négatif mais vaut au moins `−(β_e − β_l)/4`, le coût au plus
  `−(β_e − β_l)·log 2` : excédent `(β_e − β_l)(log 2 − 1/4)` (`radial_descent_budget_surplus`,
  `height_advance_local_budget`) ; à même hauteur, le coût dépasse le disponible d'au moins
  `(β_l − β_e)·(log 2 − 1/4)` (`sameHeight_budget_deficit`, `sameHeight_local_budget_refuted`) ; dès la
  hauteur 2, captivité locale ⟺ budget ⟺ la hauteur avance, par le budget seul (`local_captivity_computed`) ;
  la captivité d'énergie et l'orientation du raccord sont la même propriété (`localCaptivity_iff_oriented`).
* **§3 La même loi répétée** : une Tour lue en deux points (`zeroTerm_norm_transport`) ; captivité à chaque
  raccord d'une chaîne ⟹ borne par l'énergie de la première Tour multipliée par les pas intérieurs
  (`captivity_renewed_along_chain`) ; ce produit vaut au moins `1` (`chain_interior_steps_ge_one`) : la loi
  répétée n'est PAS une décroissance cumulée de l'énergie, ni une prison globale.
* **§4 La transition première exacte** : l'objet `ExactPrimeTransition` réunit ce qui est démontré de
  l'événement premier du raccord (événement complet, prédécesseur, successeur, écarts, poids exact, histoire,
  incrément exact du reste, position de phase, registre, rapport d'énergie) ; il existe sur tout passage
  (`exactPrimeTransitionOf`), passage de même hauteur compris, où l'énergie est renversée
  (`sameHeight_exactPrimeTransition_reversed`) ; le lemme cible « même hauteur + transition exacte ⟹
  captivité » équivaut donc à « aucun passage de même hauteur » (`sameHeight_capture_target_iff`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse `def P… : Prop`.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Le budget local -/

/-- **Captivité locale d'un passage**, définie par l'énergie seule : au premier de l'événement qui raccorde
les deux Tours, la Tour d'arrivée ne lit pas plus d'énergie que la Tour de départ. Aucune référence à
l'orientation du raccord. -/
def LocalCaptivity (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) : Prop :=
  ‖zeroTerm ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ)‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ)‖

/-- **Coût de sortie** de la Tour `l` hors de la Tour `e` au point `q` : `(β_l − β_e)·log q`. -/
noncomputable def exitCost (e l : TrueZero) (q : ℝ) : ℝ :=
  (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * Real.log q

/-- **Disponible au raccord** : `log ‖ρ_l‖ − log ‖ρ_e‖`, lu sur les deux supports seuls. -/
noncomputable def raccordAvailable (e l : TrueZero) : ℝ :=
  Real.log ‖zeroPoint l‖ - Real.log ‖zeroPoint e‖

/-- **Rapport de deux Tours successives** en tout point : `x^{β_l − β_e}·‖ρ_e‖/‖ρ_l‖`. -/
theorem successive_tower_ratio (e l : TrueZero) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm l x‖ / ‖zeroTerm e x‖ =
      x ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * (‖zeroPoint e‖ / ‖zeroPoint l‖) :=
  energyRatio_eq e l hx

/-- **Le budget local** : la Tour `l` est sous la Tour `e` en `q` ⟺ coût de sortie ≤ disponible. -/
theorem tower_le_iff_local_budget (e l : TrueZero) {q : ℝ} (hq : 0 < q) :
    ‖zeroTerm l q‖ ≤ ‖zeroTerm e q‖ ↔ exitCost e l q ≤ raccordAvailable e l := by
  have hNe := zeroPoint_norm_pos e
  have hNl := zeroPoint_norm_pos l
  have hpe : 0 < q ^ rZeroRadialPosition e.1 := Real.rpow_pos_of_pos hq _
  have hpl : 0 < q ^ rZeroRadialPosition l.1 := Real.rpow_pos_of_pos hq _
  rw [zeroTerm_norm hq, zeroTerm_norm hq, div_le_div_iff₀ hNl hNe,
    ← Real.log_le_log_iff (mul_pos hpl hNe) (mul_pos hpe hNl), Real.log_mul hpl.ne' hNe.ne',
    Real.log_mul hpe.ne' hNl.ne', Real.log_rpow hq, Real.log_rpow hq]
  unfold exitCost raccordAvailable
  constructor <;> intro h <;> linarith

/-- Le premier du raccord est au moins `2`. -/
theorem raccordPrime_two_le (e : TrueZero) : (2 : ℝ) ≤ (expectedMinimumPrime e : ℝ) := by
  exact_mod_cast (expectedMinimumPrime_prime e).two_le

/-- **Captivité locale ⟺ budget au premier du raccord.** -/
theorem localCaptivity_iff_budget (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    LocalCaptivity p hE hL ↔
      exitCost ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) ≤
        raccordAvailable ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ :=
  tower_le_iff_local_budget _ _ (by linarith [raccordPrime_two_le ⟨p.zEarlierMember, hE⟩])

/-! ## 2. Le budget calculé au raccord exact -/

/-- **Excédent du budget quand la position radiale ne monte pas** : pour `T_e ≤ T_l`, `T_l ≥ 2`,
`β_l ≤ β_e`, en tout point `q ≥ 2`. Le disponible n'est pas nécessairement positif (`‖ρ_l‖ < ‖ρ_e‖` est
possible quand les hauteurs sont proches) ; il vaut au moins `−(β_e − β_l)/4`, et le coût au plus
`−(β_e − β_l)·log 2`. Preuve par les deux supports seuls. -/
theorem radial_descent_budget_surplus (e l : TrueZero) (hT : rZeroHeight e.1 ≤ rZeroHeight l.1)
    (hT2 : 2 ≤ rZeroHeight l.1) (hβ : rZeroRadialPosition l.1 ≤ rZeroRadialPosition e.1)
    {q : ℝ} (hq : 2 ≤ q) :
    exitCost e l q +
        (rZeroRadialPosition e.1 - rZeroRadialPosition l.1) * (Real.log 2 - 1 / 4) ≤
      raccordAvailable e l := by
  have hNe := zeroPoint_norm_pos e
  have hNl := zeroPoint_norm_pos l
  have hse := zeroPoint_norm_sq e
  have hsl := zeroPoint_norm_sq l
  have ha0 : 0 ≤ rZeroRadialPosition e.1 - rZeroRadialPosition l.1 := by linarith
  have hb1 : rZeroRadialPosition e.1 < 1 := thm_zeroRadialPosition_lt_one e.1
  have hb0 : 0 < rZeroRadialPosition l.1 := thm_zeroRadialPosition_positive l.1
  have hTe : 0 < rZeroHeight e.1 := e.2
  have hTsq : rZeroHeight e.1 ^ 2 ≤ rZeroHeight l.1 ^ 2 := by nlinarith
  have hs4 : 4 ≤ ‖zeroPoint l‖ ^ 2 := by rw [hsl]; nlinarith
  have hratio : ‖zeroPoint e‖ ^ 2 / ‖zeroPoint l‖ ^ 2 - 1 ≤
      (rZeroRadialPosition e.1 - rZeroRadialPosition l.1) / 2 := by
    rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    have h2 : (rZeroRadialPosition e.1 - rZeroRadialPosition l.1) *
        (rZeroRadialPosition e.1 + rZeroRadialPosition l.1) ≤
        (rZeroRadialPosition e.1 - rZeroRadialPosition l.1) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) ha0
    have h3 : (rZeroRadialPosition e.1 - rZeroRadialPosition l.1) * 4 ≤
        (rZeroRadialPosition e.1 - rZeroRadialPosition l.1) * ‖zeroPoint l‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hs4 ha0
    have h4 : ‖zeroPoint e‖ ^ 2 - ‖zeroPoint l‖ ^ 2 ≤
        (rZeroRadialPosition e.1 - rZeroRadialPosition l.1) *
          (rZeroRadialPosition e.1 + rZeroRadialPosition l.1) := by
      rw [hsl, hse]; nlinarith
    nlinarith
  have hlog : raccordAvailable e l =
      -(1 / 2 * Real.log (‖zeroPoint e‖ ^ 2 / ‖zeroPoint l‖ ^ 2)) := by
    unfold raccordAvailable
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hle := Real.log_le_sub_one_of_pos
    (show 0 < ‖zeroPoint e‖ ^ 2 / ‖zeroPoint l‖ ^ 2 by positivity)
  have hq2 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq
  have hcost := mul_le_mul_of_nonneg_left hq2 ha0
  unfold exitCost
  rw [hlog]
  nlinarith

/-- **La hauteur avance** : le coût de sortie est négatif ou nul (`β_l ≤ 1/2 ≤ β_e`) ; dès la hauteur 2 le
budget est tenu avec l'excédent `(β_e − β_l)(log 2 − 1/4)` et la captivité locale suit, par le budget seul
(le théorème d'orientation du raccord n'est pas utilisé). -/
theorem height_advance_local_budget (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hV : VerticalPassage p) :
    exitCost ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) ≤ 0 ∧
      (2 ≤ rZeroHeight p.zLaterMember →
        exitCost ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) +
            (rZeroRadialPosition p.zEarlierMember - rZeroRadialPosition p.zLaterMember) *
              (Real.log 2 - 1 / 4) ≤ raccordAvailable ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ ∧
          LocalCaptivity p hE hL) := by
  have hM := raccordPrime_two_le ⟨p.zEarlierMember, hE⟩
  have hHi := passage_exit_radial_ge_half p hV
  have hLo := passage_entry_radial_le_half p hV
  have hβ : rZeroRadialPosition p.zLaterMember ≤ rZeroRadialPosition p.zEarlierMember := by linarith
  refine ⟨mul_nonpos_of_nonpos_of_nonneg
    (by show rZeroRadialPosition p.zLaterMember - rZeroRadialPosition p.zEarlierMember ≤ 0; linarith)
    (Real.log_nonneg (by linarith)), fun hT2 => ?_⟩
  have hS := radial_descent_budget_surplus ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ (le_of_lt hV) hT2 hβ hM
  have hlog2 := Real.log_two_gt_d9
  have hnn : 0 ≤ (rZeroRadialPosition p.zEarlierMember - rZeroRadialPosition p.zLaterMember) *
      (Real.log 2 - 1 / 4) := mul_nonneg (by linarith) (by linarith)
  have hS' : exitCost ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) +
      (rZeroRadialPosition p.zEarlierMember - rZeroRadialPosition p.zLaterMember) *
        (Real.log 2 - 1 / 4) ≤ raccordAvailable ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ := hS
  exact ⟨hS', (localCaptivity_iff_budget p hE hL).mpr (by linarith)⟩

/-- **Déficit du budget à même hauteur** : pour deux Tours de même hauteur `T ≥ 2`, `β_e < β_l`, en tout
point `q ≥ 2`, le coût de sortie dépasse le disponible d'au moins `(β_l − β_e)·(log 2 − 1/4)`. -/
theorem sameHeight_budget_deficit (e l : TrueZero) (hT : rZeroHeight e.1 = rZeroHeight l.1)
    (hT2 : 2 ≤ rZeroHeight e.1) (hβ : rZeroRadialPosition e.1 < rZeroRadialPosition l.1)
    {q : ℝ} (hq : 2 ≤ q) :
    raccordAvailable e l +
        (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * (Real.log 2 - 1 / 4) ≤
      exitCost e l q := by
  have hNe := zeroPoint_norm_pos e
  have hNl := zeroPoint_norm_pos l
  have hse := zeroPoint_norm_sq e
  have hsl := zeroPoint_norm_sq l
  have ha0 : 0 < rZeroRadialPosition l.1 - rZeroRadialPosition e.1 := by linarith
  have hb1 : rZeroRadialPosition l.1 < 1 := thm_zeroRadialPosition_lt_one l.1
  have hb0 : 0 < rZeroRadialPosition e.1 := thm_zeroRadialPosition_positive e.1
  have hs4 : 4 ≤ ‖zeroPoint e‖ ^ 2 := by rw [hse]; nlinarith
  have hratio : ‖zeroPoint l‖ ^ 2 / ‖zeroPoint e‖ ^ 2 - 1 ≤
      (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) / 2 := by
    rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    have h2 : (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) *
        (rZeroRadialPosition l.1 + rZeroRadialPosition e.1) ≤
        (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) ha0.le
    have h3 : (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * 4 ≤
        (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) * ‖zeroPoint e‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hs4 ha0.le
    have h4 : ‖zeroPoint l‖ ^ 2 - ‖zeroPoint e‖ ^ 2 =
        (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) *
          (rZeroRadialPosition l.1 + rZeroRadialPosition e.1) := by
      rw [hsl, hse, hT]; ring
    nlinarith
  have hlog : raccordAvailable e l =
      1 / 2 * Real.log (‖zeroPoint l‖ ^ 2 / ‖zeroPoint e‖ ^ 2) := by
    unfold raccordAvailable
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hle := Real.log_le_sub_one_of_pos
    (show 0 < ‖zeroPoint l‖ ^ 2 / ‖zeroPoint e‖ ^ 2 by positivity)
  have hq2 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq
  have hcost := mul_le_mul_of_nonneg_left hq2 ha0.le
  unfold exitCost
  rw [hlog]
  nlinarith

/-- **Au raccord d'un passage de même hauteur**, dès la hauteur 2 : le disponible est strictement sous le
coût de sortie, et la captivité locale est fausse. L'inégalité locale y est calculée, elle est renversée. -/
theorem sameHeight_local_budget_refuted (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hH : HorizontalPassage p)
    (hT2 : 2 ≤ rZeroHeight p.zEarlierMember) :
    raccordAvailable ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ <
        exitCost ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) ∧
      ¬ LocalCaptivity p hE hL := by
  have hM := raccordPrime_two_le ⟨p.zEarlierMember, hE⟩
  have hRad := horizontalPassage_radial_lt hH
  have hD := sameHeight_budget_deficit ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hH hT2 hRad hM
  have hlog2 := Real.log_two_gt_d9
  have hpos : 0 < (rZeroRadialPosition p.zLaterMember - rZeroRadialPosition p.zEarlierMember) *
      (Real.log 2 - 1 / 4) := mul_pos (by linarith) (by linarith)
  have hlt : raccordAvailable ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ <
      exitCost ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) := by
    have hD' : raccordAvailable ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ +
        (rZeroRadialPosition p.zLaterMember - rZeroRadialPosition p.zEarlierMember) *
          (Real.log 2 - 1 / 4) ≤
        exitCost ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) := hD
    linarith
  exact ⟨hlt, fun hC => absurd ((localCaptivity_iff_budget p hE hL).mp hC) (not_le.mpr hlt)⟩

/-- **L'inégalité locale, calculée par le budget seul** : dès la hauteur 2, captivité locale au raccord ⟺
budget tenu ⟺ la hauteur avance. Les deux sens de la seconde équivalence viennent du budget (déficit à même
hauteur, excédent quand la hauteur avance), pas du théorème d'orientation. -/
theorem local_captivity_computed (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) (hT2 : 2 ≤ rZeroHeight p.zEarlierMember) :
    (LocalCaptivity p hE hL ↔
        exitCost ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) ≤
          raccordAvailable ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩) ∧
      (LocalCaptivity p hE hL ↔ rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember) := by
  refine ⟨localCaptivity_iff_budget p hE hL, fun hC => ?_, fun hV => ?_⟩
  · by_contra hn
    have hH : HorizontalPassage p := le_antisymm (passage_height_le p) (not_lt.mp hn)
    exact (sameHeight_local_budget_refuted p hE hL hH hT2).2 hC
  · exact ((height_advance_local_budget p hE hL hV).2 (hT2.trans (le_of_lt hV))).2

/-- **Deux structures indépendantes identifiées** : la captivité d'énergie (définie sans le raccord) est
l'orientation du raccord de Tours (définie sur le premier partagé du raccord). -/
theorem localCaptivity_iff_oriented (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    LocalCaptivity p hE hL ↔ (towerRaccordOf p hE hL).Oriented := by
  unfold LocalCaptivity TowerRaccord.Oriented
  rw [(towerRaccordOf p hE hL).exit_eq]

/-! ## 3. La même loi répétée de raccord en raccord -/

/-- **Une Tour lue en deux points** : `‖Z(y)‖ = ‖Z(x)‖·(y/x)^β`. -/
theorem zeroTerm_norm_transport (z : TrueZero) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ‖zeroTerm z y‖ = ‖zeroTerm z x‖ * (y / x) ^ rZeroRadialPosition z.1 := by
  have hN := zeroPoint_norm_pos z
  have hpx : 0 < x ^ rZeroRadialPosition z.1 := Real.rpow_pos_of_pos hx _
  rw [zeroTerm_norm hy, zeroTerm_norm hx, Real.div_rpow hy.le hx.le]
  field_simp

/-- **Captivité renouvelée le long d'une chaîne** : si à chaque raccord `M k` la Tour `k+1` est sous la Tour
`k`, alors l'énergie de la Tour `n+1` à son raccord est bornée par celle de la Tour `0` au sien, multipliée
par les pas intérieurs `(M_{k+1}/M_k)^{β_{k+1}}`. Ce produit vaut au moins `1` (`chain_interior_steps_ge_one`) :
l'énoncé ne donne PAS `‖Z_{n+1}(M_n)‖ ≤ ‖Z_0(M_0)‖`, ce n'est ni une décroissance cumulée ni une prison
globale. -/
theorem captivity_renewed_along_chain (z : ℕ → TrueZero) (M : ℕ → ℝ) (hM : ∀ k, 0 < M k)
    (h : ∀ k, ‖zeroTerm (z (k + 1)) (M k)‖ ≤ ‖zeroTerm (z k) (M k)‖) (n : ℕ) :
    ‖zeroTerm (z (n + 1)) (M n)‖ ≤ ‖zeroTerm (z 0) (M 0)‖ *
      ∏ k ∈ Finset.range n, (M (k + 1) / M k) ^ rZeroRadialPosition (z (k + 1)).1 := by
  induction n with
  | zero => simpa using h 0
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc]
    calc ‖zeroTerm (z (n + 1 + 1)) (M (n + 1))‖
        ≤ ‖zeroTerm (z (n + 1)) (M (n + 1))‖ := h (n + 1)
      _ = ‖zeroTerm (z (n + 1)) (M n)‖ * (M (n + 1) / M n) ^ rZeroRadialPosition (z (n + 1)).1 :=
          zeroTerm_norm_transport _ (hM n) (hM (n + 1))
      _ ≤ _ := mul_le_mul_of_nonneg_right ih
          (Real.rpow_nonneg (div_pos (hM (n + 1)) (hM n)).le _)

/-- **Les pas intérieurs valent au moins `1`** quand les premiers des raccords croissent : la loi répétée
laisse croître la borne. -/
theorem chain_interior_steps_ge_one (z : ℕ → TrueZero) (M : ℕ → ℝ) (hM : ∀ k, 0 < M k)
    (hmono : ∀ k, M k ≤ M (k + 1)) (n : ℕ) :
    1 ≤ ∏ k ∈ Finset.range n, (M (k + 1) / M k) ^ rZeroRadialPosition (z (k + 1)).1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    exact one_le_mul_of_one_le_of_one_le ih
      (Real.one_le_rpow ((one_le_div (hM n)).mpr (hmono n))
        (thm_zeroRadialPosition_positive _).le)

/-! ## 4. La transition première exacte -/

/-- **Transition première exacte d'un passage** : tout ce qui est démontré de l'événement premier qui
raccorde les deux Tours, réuni sur le même objet. Événement complet (rang, premier, prédécesseur,
successeur, écarts entrant et sortant, état et classes, poids), premier partagé, poids exact de von
Mangoldt, reconstruction depuis les zéros, pas de l'histoire, incrément exact du reste à cet événement,
position de phase du premier dans la Tour d'arrivée, registre du passage, rapport d'énergie. -/
structure ExactPrimeTransition (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) where
  /-- L'événement premier complet du raccord. -/
  raccord : GrammaticalRaccord ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
  shared : occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩
  prime : Nat.Prime (occurrence ⟨p.zLaterMember, hL⟩)
  order : occurrence ⟨p.zEarlierMember, hE⟩ < occurrence ⟨p.zLaterMember, hL⟩
  weight : ArithmeticFunction.vonMangoldt (occurrence ⟨p.zLaterMember, hL⟩) = Real.log (occurrence ⟨p.zLaterMember, hL⟩ : ℝ)
  reconstructed : raccord.event = reconstructedEventAt (nZeroSourceIndex p.zLaterMember)
  history : primalHistory (nZeroSourceIndex p.zLaterMember) =
    primalHistory (nZeroSourceIndex p.zEarlierMember) ++ [raccord.event]
  /-- Incrément exact du reste à l'événement : le poids du premier moins l'avance du fond. -/
  increment : remainderBetween (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ - 1) (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩) =
    ((Real.log (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) : ℝ) : ℂ) -
      (stepAt backgroundPrimitive (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩) -
        stepAt backgroundPrimitive (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ - 1))
  position : Real.pi * towerPosition ⟨p.zLaterMember, hL⟩ (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) =
    rZeroHeight p.zLaterMember * Real.log (occurrence ⟨p.zLaterMember, hL⟩ : ℝ) -
      Real.arctan (rZeroHeight p.zLaterMember / rZeroRadialPosition p.zLaterMember)
  ledger : occurrencePosition ⟨p.zLaterMember, hL⟩ - occurrencePosition ⟨p.zEarlierMember, hE⟩ =
    raccordShift ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ +
      rZeroHeight p.zEarlierMember * rPrimeGapLogRatio (nZeroSourceIndex p.zEarlierMember)
  ratio : ‖zeroTerm ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ)‖ / ‖zeroTerm ⟨p.zEarlierMember, hE⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ)‖ =
    (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) ^ (rZeroRadialPosition p.zLaterMember - rZeroRadialPosition p.zEarlierMember) *
      (‖zeroPoint ⟨p.zEarlierMember, hE⟩‖ / ‖zeroPoint ⟨p.zLaterMember, hL⟩‖)

/-- **La transition première exacte existe sur tout passage**, sans hypothèse : chaque champ est un
théorème. -/
noncomputable def exactPrimeTransitionOf (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) : ExactPrimeTransition p hE hL where
  raccord := grammaticalRaccordOf p hE hL
  shared := (passage_prime_tower_bond p hE hL).1
  prime := (passage_prime_tower_bond p hE hL).2.1
  order := (passage_prime_tower_bond p hE hL).2.2.1
  weight := (passage_prime_tower_bond p hE hL).2.2.2.1
  reconstructed := (reconstructedEvent_eq_primalEvent _).symm
  history := (passage_history_step p hE hL).2.2.1
  increment := by
    have hp := expectedMinimumPrime_prime ⟨p.zEarlierMember, hE⟩
    have hIoc : Finset.Ioc (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ - 1) (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩) =
        {expectedMinimumPrime ⟨p.zEarlierMember, hE⟩} := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_singleton]
      have := hp.two_le
      omega
    rw [remainderBetween_arithmetic (Nat.sub_le _ _), hIoc, Finset.sum_singleton,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  position := (passage_prime_tower_bond p hE hL).2.2.2.2.1
  ledger := (passage_prime_tower_bond p hE hL).2.2.2.2.2
  ratio := successive_tower_ratio _ _ (by linarith [raccordPrime_two_le ⟨p.zEarlierMember, hE⟩])

/-- **Sur un passage de même hauteur**, dès la hauteur 2 : la transition première exacte existe avec tous
ses champs, les deux termes au premier partagé sont liés par une rotation de phase constante et le rapport
d'énergie, et l'énergie est strictement renversée. Rien de ce que contient la transition n'interdit ce
passage. -/
theorem sameHeight_exactPrimeTransition_reversed (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hH : HorizontalPassage p) (hT2 : 2 ≤ rZeroHeight p.zEarlierMember) :
    Nonempty (ExactPrimeTransition p hE hL) ∧
      zeroTerm ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) =
        zeroTerm ⟨p.zEarlierMember, hE⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) *
          ((energyRatio ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ) : ℝ) : ℂ) *
          Complex.exp ((((towerMotionOf ⟨p.zEarlierMember, hE⟩).phase - (towerMotionOf ⟨p.zLaterMember, hL⟩).phase : ℝ) : ℂ) *
            Complex.I) ∧
      ‖zeroTerm ⟨p.zEarlierMember, hE⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ)‖ < ‖zeroTerm ⟨p.zLaterMember, hL⟩ (expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ : ℝ)‖ :=
  ⟨⟨exactPrimeTransitionOf p hE hL⟩,
    horizontal_term_phase_lock ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hH (by linarith [raccordPrime_two_le ⟨p.zEarlierMember, hE⟩]),
    lt_of_not_ge (sameHeight_local_budget_refuted p hE hL hH hT2).2⟩

/-- **Le lemme cible, mesuré** : « même hauteur + transition première exacte ⟹ captivité locale » équivaut
à « aucun passage de même hauteur » (dès la hauteur 2). La transition, faite de faits démontrés, existe sur
tout passage : comme hypothèse elle n'apporte rien ; l'information qui porterait le lemme n'est dans aucun
de ses champs. -/
theorem sameHeight_capture_target_iff :
    (∀ (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
        (hL : 0 < rZeroHeight p.zLaterMember), HorizontalPassage p →
        2 ≤ rZeroHeight p.zEarlierMember → ExactPrimeTransition p hE hL → LocalCaptivity p hE hL) ↔
      ∀ p : TZeroPassage, 2 ≤ rZeroHeight p.zEarlierMember → ¬ HorizontalPassage p := by
  constructor
  · intro h p hT2 hH
    have hE : 0 < rZeroHeight p.zEarlierMember := by linarith
    have hL : 0 < rZeroHeight p.zLaterMember := hE.trans_le (passage_height_le p)
    exact (sameHeight_local_budget_refuted p hE hL hH hT2).2
      (h p hE hL hH hT2 (exactPrimeTransitionOf p hE hL))
  · intro h p _ _ hH hT2 _
    exact absurd hH (h p hT2)

#print axioms successive_tower_ratio
#print axioms tower_le_iff_local_budget
#print axioms localCaptivity_iff_budget
#print axioms radial_descent_budget_surplus
#print axioms height_advance_local_budget
#print axioms sameHeight_budget_deficit
#print axioms sameHeight_local_budget_refuted
#print axioms local_captivity_computed
#print axioms localCaptivity_iff_oriented
#print axioms zeroTerm_norm_transport
#print axioms captivity_renewed_along_chain
#print axioms chain_interior_steps_ge_one
#print axioms exactPrimeTransitionOf
#print axioms sameHeight_exactPrimeTransition_reversed
#print axioms sameHeight_capture_target_iff

end RHV6Fresh
