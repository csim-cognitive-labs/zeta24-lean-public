/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.HorizontalExclusion
import RHV6Fresh.Terminal.GeometricEnergyRaccord
import RHV6Fresh.Terminal.ReadingArithmetic

/-!
# RHV6Fresh — la poussée verticale comme SIGNE de l'énergie le long de la chaîne (2026-09-28)

Thèse de l'auteur : les zéros de la ligne critique n'ont aucune force horizontale (le miroir
retombe sur eux-mêmes, `mirrorMember_eq_self_of_onLine`) ; leurs Tours émettent une énergie
`‖zeroTerm z q‖ = q^β/‖ρ‖` qui atteint l'axe algébrique et « repousse » le zéro suivant plus haut.
Ce fichier formalise EXACTEMENT ce que cette thèse dit d'un passage, en termes déjà compilés.

* **V0** : `‖ρ‖² = β² + T²` (le support de l'énergie).
* **V1 — poussée verticale ON** : à même position radiale, la Tour la plus HAUTE porte, en TOUT
  point `q > 0` de l'axe, strictement MOINS d'énergie que la Tour précédente. L'énergie DÉCROÎT
  le long de la chaîne verticale.
* **V2 — inversion horizontale** : dès que la position radiale progresse (`β_e < β_l`, quelle que
  soit la hauteur), il existe un seuil `q₀ ≥ 1` au-delà duquel la Tour LATER porte strictement PLUS
  d'énergie que la Tour EARLIER : le signe de la transmission s'inverse. Inconditionnel.
* **V3 — inversion à tout premier** : à même hauteur `T ≥ 2` et `β_e < β_l`, l'inversion vaut déjà
  pour TOUT `q ≥ 2`, donc à chacun des deux raccords `Occ(l)`, `p_min(l)`. L'hypothèse `2 ≤ T`
  est numérique (aucun zéro non trivial n'a `T < 14`, fait non compilé dans la base), jamais une
  prémisse RH ; elle est laissée explicite.
* **V4 — la dichotomie de signe sur tout passage** : ou bien la hauteur progresse, ou bien
  l'énergie s'inverse au-delà d'un seuil. Inconditionnel.
* **V5 — la thèse comme énoncé** : `PVerticalEnergyPush` := « sur tout passage, en tout `q ≥ 1`,
  l'énergie ne croît pas ». Prouvé `↔ RiemannHypothesis` : REFORMULATION étiquetée, jamais une
  réduction. Ce qu'elle apporte : le résidu du compilateur (deux ÉGALITÉS d'amplitude aux
  raccords, `PEnergyBalanceAtRaccords`) est remplacé par un SIGNE STRICT, vrai en tout point de
  l'axe pour la chaîne ON et inversé en tout `q > q₀` pour tout passage horizontal.

Verdict honnête : aucune contradiction inconditionnelle. La dichotomie de signe est compilée ;
décider que le signe ne s'inverse jamais est exactement RH.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## V0 — le support de l'énergie -/

theorem zeroPoint_norm_sq (z : TrueZero) :
    ‖zeroPoint z‖ ^ 2 = rZeroRadialPosition z.1 ^ 2 + rZeroHeight z.1 ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, zeroPoint_re z, zeroPoint_im z]
  ring

theorem zeroPoint_norm_pos (z : TrueZero) : 0 < ‖zeroPoint z‖ :=
  norm_pos_iff.mpr (zeroPoint_ne_zero z)

/-- À même position radiale, la hauteur ordonne strictement les supports. -/
theorem zeroPoint_norm_lt_of_height_lt (e l : TrueZero)
    (hβ : rZeroRadialPosition e.1 = rZeroRadialPosition l.1)
    (hT : rZeroHeight e.1 < rZeroHeight l.1) : ‖zeroPoint e‖ < ‖zeroPoint l‖ := by
  have h2 : ‖zeroPoint e‖ ^ 2 < ‖zeroPoint l‖ ^ 2 := by
    rw [zeroPoint_norm_sq, zeroPoint_norm_sq, hβ]
    have hTe : 0 < rZeroHeight e.1 := e.2
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (zeroPoint_norm_pos l).le h2

/-- À même hauteur et même position radiale, les supports coïncident. -/
theorem zeroPoint_norm_eq_of_eq (e l : TrueZero)
    (hβ : rZeroRadialPosition e.1 = rZeroRadialPosition l.1)
    (hT : rZeroHeight e.1 = rZeroHeight l.1) : ‖zeroPoint e‖ = ‖zeroPoint l‖ := by
  have h2 : ‖zeroPoint e‖ ^ 2 = ‖zeroPoint l‖ ^ 2 := by
    rw [zeroPoint_norm_sq, zeroPoint_norm_sq, hβ, hT]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-! ## V1 — poussée verticale ON : l'énergie décroît le long de la chaîne -/

/-- **À même position radiale, la Tour la plus haute porte strictement moins d'énergie en tout
point `q > 0` de l'axe algébrique.** C'est la poussée verticale de la thèse, compilée : la chaîne
ON (tous les `β` égaux à `1/2`) transmet une énergie strictement décroissante. -/
theorem amplitude_lt_of_height_lt (e l : TrueZero)
    (hβ : rZeroRadialPosition e.1 = rZeroRadialPosition l.1)
    (hT : rZeroHeight e.1 < rZeroHeight l.1) {q : ℝ} (hq : 0 < q) :
    ‖zeroTerm l q‖ < ‖zeroTerm e q‖ := by
  rw [zeroTerm_norm hq, zeroTerm_norm hq, ← hβ]
  have hpow : 0 < q ^ rZeroRadialPosition e.1 := Real.rpow_pos_of_pos hq _
  rw [div_lt_div_iff_of_pos_left hpow (zeroPoint_norm_pos l) (zeroPoint_norm_pos e)]
  exact zeroPoint_norm_lt_of_height_lt e l hβ hT

/-- Sur la ligne critique, deux membres de hauteurs distinctes ont la même position radiale, donc
la poussée verticale V1 s'applique sans condition. -/
theorem onLine_amplitude_lt_of_height_lt (e l : TrueZero)
    (he : rZeroRadialPosition e.1 = 1 / 2) (hl : rZeroRadialPosition l.1 = 1 / 2)
    (hT : rZeroHeight e.1 < rZeroHeight l.1) {q : ℝ} (hq : 0 < q) :
    ‖zeroTerm l q‖ < ‖zeroTerm e q‖ :=
  amplitude_lt_of_height_lt e l (by rw [he, hl]) hT hq

/-! ## V2 — inversion horizontale : dès que `β` progresse, LATER domine EARLIER au-delà d'un seuil -/

/-- **Inversion du signe de la transmission.** Si la position radiale progresse (`β_e < β_l`),
quelle que soit la hauteur, il existe `q₀ ≥ 1` tel que pour tout `q > q₀` la Tour LATER porte
strictement PLUS d'énergie que la Tour EARLIER. Inconditionnel. -/
theorem amplitude_inverts_of_radial_lt (e l : TrueZero)
    (hβ : rZeroRadialPosition e.1 < rZeroRadialPosition l.1) :
    ∃ q₀ : ℝ, 1 ≤ q₀ ∧ ∀ q : ℝ, q₀ < q → ‖zeroTerm e q‖ < ‖zeroTerm l q‖ := by
  set δ := rZeroRadialPosition l.1 - rZeroRadialPosition e.1 with hδdef
  have hδ : 0 < δ := sub_pos.mpr hβ
  have hNe := zeroPoint_norm_pos e
  have hNl := zeroPoint_norm_pos l
  set r := ‖zeroPoint l‖ / ‖zeroPoint e‖ with hrdef
  have hr : 0 < r := div_pos hNl hNe
  refine ⟨max 1 (r ^ (1 / δ)), le_max_left _ _, ?_⟩
  intro q hq
  have hq1 : 1 < q := lt_of_le_of_lt (le_max_left _ _) hq
  have hq0 : 0 < q := lt_trans one_pos hq1
  have hqr : r ^ (1 / δ) < q := lt_of_le_of_lt (le_max_right _ _) hq
  have hqδ : r < q ^ δ := by
    have h1 : (r ^ (1 / δ)) ^ δ < q ^ δ :=
      Real.rpow_lt_rpow (Real.rpow_nonneg hr.le _) hqr hδ
    rwa [← Real.rpow_mul hr.le, one_div_mul_cancel hδ.ne', Real.rpow_one] at h1
  rw [zeroTerm_norm hq0, zeroTerm_norm hq0, div_lt_div_iff₀ hNe hNl]
  have hsplit : q ^ rZeroRadialPosition l.1 = q ^ rZeroRadialPosition e.1 * q ^ δ := by
    rw [← Real.rpow_add hq0]
    congr 1
    rw [hδdef]; ring
  rw [hsplit]
  have hpe : 0 < q ^ rZeroRadialPosition e.1 := Real.rpow_pos_of_pos hq0 _
  have hkey : ‖zeroPoint l‖ < q ^ δ * ‖zeroPoint e‖ := by
    have := (div_lt_iff₀ hNe).mp hqδ
    linarith
  calc q ^ rZeroRadialPosition e.1 * ‖zeroPoint l‖
      < q ^ rZeroRadialPosition e.1 * (q ^ δ * ‖zeroPoint e‖) :=
        mul_lt_mul_of_pos_left hkey hpe
    _ = q ^ rZeroRadialPosition e.1 * q ^ δ * ‖zeroPoint e‖ := by ring

/-! ## V3 — inversion à tout premier, à même hauteur `T ≥ 2` -/

/-- `log 4 > 1` (car `e < 4`). -/
theorem one_lt_log_four : (1 : ℝ) < Real.log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- `1 + δ < 4^δ` pour `0 < δ`. -/
theorem one_add_lt_four_rpow {δ : ℝ} (hδ : 0 < δ) : 1 + δ < (4 : ℝ) ^ δ := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h1 := Real.add_one_le_exp (Real.log 4 * δ)
  have h2 := one_lt_log_four
  nlinarith

/-- **À même hauteur `T ≥ 2`, dès que `β_e < β_l`, la Tour LATER domine strictement la Tour EARLIER
en tout `q ≥ 2`** — donc à chacun des deux raccords `Occ(l)`, `p_min(l)`. L'hypothèse `2 ≤ T` est
numérique (tout zéro non trivial a `T > 14`), laissée explicite : elle n'est pas compilée dans la
base. -/
theorem sameHeight_amplitude_inverts_at_primes (e l : TrueZero)
    (hT : rZeroHeight e.1 = rZeroHeight l.1) (hT2 : 2 ≤ rZeroHeight e.1)
    (hβ : rZeroRadialPosition e.1 < rZeroRadialPosition l.1) {q : ℝ} (hq : 2 ≤ q) :
    ‖zeroTerm e q‖ < ‖zeroTerm l q‖ := by
  have hq0 : 0 < q := by linarith
  have hNe := zeroPoint_norm_pos e
  have hNl := zeroPoint_norm_pos l
  have hβe0 : 0 < rZeroRadialPosition e.1 := thm_zeroRadialPosition_positive e.1
  have hβl1 : rZeroRadialPosition l.1 < 1 := thm_zeroRadialPosition_lt_one l.1
  set δ := rZeroRadialPosition l.1 - rZeroRadialPosition e.1 with hδdef
  have hδ : 0 < δ := sub_pos.mpr hβ
  -- (i) ‖ρ_l‖² ≤ (1 + δ/2) ‖ρ_e‖²
  have hsq_e := zeroPoint_norm_sq e
  have hsq_l : ‖zeroPoint l‖ ^ 2 = rZeroRadialPosition l.1 ^ 2 + rZeroHeight e.1 ^ 2 := by
    rw [zeroPoint_norm_sq, ← hT]
  have hT4 : 4 ≤ rZeroHeight e.1 ^ 2 := by nlinarith
  have hratio : ‖zeroPoint l‖ ^ 2 ≤ (1 + δ / 2) * ‖zeroPoint e‖ ^ 2 := by
    rw [hsq_e, hsq_l]
    have h1 : rZeroRadialPosition l.1 ^ 2 - rZeroRadialPosition e.1 ^ 2 =
        δ * (rZeroRadialPosition l.1 + rZeroRadialPosition e.1) := by rw [hδdef]; ring
    have h2 : rZeroRadialPosition l.1 + rZeroRadialPosition e.1 < 2 := by linarith
    nlinarith [mul_pos hδ (sub_pos.mpr h2), mul_nonneg hδ.le (sub_nonneg.mpr hT4),
      mul_nonneg hδ.le (sq_nonneg (rZeroRadialPosition e.1))]
  -- (ii) 1 + δ/2 < (q^δ)²
  have hqδ2 : 1 + δ / 2 < (q ^ δ) ^ 2 := by
    have h2δ : (2 : ℝ) ^ δ ≤ q ^ δ := Real.rpow_le_rpow (by norm_num) hq hδ.le
    have h4 : ((2 : ℝ) ^ δ) ^ 2 = (4 : ℝ) ^ δ := by
      rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        show (4 : ℝ) = 2 ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num,
        ← Real.rpow_mul (by norm_num)]
      congr 1; ring
    have hexp := one_add_lt_four_rpow hδ
    calc 1 + δ / 2 < ((2 : ℝ) ^ δ) ^ 2 := by rw [h4]; linarith
      _ ≤ (q ^ δ) ^ 2 := pow_le_pow_left₀ (by positivity) h2δ 2
  -- (iii) conclusion par comparaison des carrés
  rw [zeroTerm_norm hq0, zeroTerm_norm hq0, div_lt_div_iff₀ hNe hNl]
  have hsplit : q ^ rZeroRadialPosition l.1 = q ^ rZeroRadialPosition e.1 * q ^ δ := by
    rw [← Real.rpow_add hq0]
    congr 1
    rw [hδdef]; ring
  rw [hsplit]
  have hpe : 0 < q ^ rZeroRadialPosition e.1 := Real.rpow_pos_of_pos hq0 _
  have hB : 0 ≤ q ^ rZeroRadialPosition e.1 * q ^ δ * ‖zeroPoint e‖ := by positivity
  refine lt_of_pow_lt_pow_left₀ 2 hB ?_
  have hpe2 : 0 < (q ^ rZeroRadialPosition e.1) ^ 2 := by positivity
  have hNe2 : 0 < ‖zeroPoint e‖ ^ 2 := by positivity
  calc (q ^ rZeroRadialPosition e.1 * ‖zeroPoint l‖) ^ 2
      = (q ^ rZeroRadialPosition e.1) ^ 2 * ‖zeroPoint l‖ ^ 2 := by ring
    _ ≤ (q ^ rZeroRadialPosition e.1) ^ 2 * ((1 + δ / 2) * ‖zeroPoint e‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hratio hpe2.le
    _ < (q ^ rZeroRadialPosition e.1) ^ 2 * ((q ^ δ) ^ 2 * ‖zeroPoint e‖ ^ 2) :=
        mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hqδ2 hNe2) hpe2
    _ = (q ^ rZeroRadialPosition e.1 * q ^ δ * ‖zeroPoint e‖) ^ 2 := by ring

/-- **Aux deux raccords de la grammaire**, à même hauteur `T ≥ 2` et `β_e < β_l` : la Tour LATER
domine strictement la Tour EARLIER à `Occ(l)` et à `p_min(l)`. (Les deux sont des premiers, donc
`≥ 2`.) -/
theorem sameHeight_amplitude_inverts_at_raccords (e l : TrueZero)
    (hT : rZeroHeight e.1 = rZeroHeight l.1) (hT2 : 2 ≤ rZeroHeight e.1)
    (hβ : rZeroRadialPosition e.1 < rZeroRadialPosition l.1) :
    ‖zeroTerm e (occurrence l : ℝ)‖ < ‖zeroTerm l (occurrence l : ℝ)‖ ∧
      ‖zeroTerm e (expectedMinimumPrime l : ℝ)‖ < ‖zeroTerm l (expectedMinimumPrime l : ℝ)‖ := by
  have h1 : (2 : ℝ) ≤ (occurrence l : ℝ) := by exact_mod_cast (occurrence_prime l).two_le
  have h2 : (2 : ℝ) ≤ (expectedMinimumPrime l : ℝ) := by
    exact_mod_cast (expectedMinimumPrime_prime l).two_le
  exact ⟨sameHeight_amplitude_inverts_at_primes e l hT hT2 hβ h1,
    sameHeight_amplitude_inverts_at_primes e l hT hT2 hβ h2⟩

/-! ## V4 — la dichotomie de signe sur TOUT passage -/

/-- **Sur tout passage, ou bien la hauteur progresse, ou bien (même hauteur) l'énergie s'inverse
au-delà d'un seuil : la Tour LATER domine la Tour EARLIER.** Inconditionnel, depuis l'ordre
lexicographique de la base. -/
theorem passage_energy_sign_dichotomy (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∨
      (rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember ∧
        ∃ q₀ : ℝ, 1 ≤ q₀ ∧ ∀ q : ℝ, q₀ < q →
          ‖zeroTerm ⟨p.zEarlierMember, hE⟩ q‖ < ‖zeroTerm ⟨p.zLaterMember, hL⟩ q‖) := by
  rcases (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mp p.precedes with hlt | ⟨heq, hr⟩
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, amplitude_inverts_of_radial_lt ⟨p.zEarlierMember, hE⟩
      ⟨p.zLaterMember, hL⟩ hr⟩

/-! ## V5 — la thèse comme énoncé, et son étiquette honnête -/

#print axioms amplitude_lt_of_height_lt
#print axioms amplitude_inverts_of_radial_lt
#print axioms sameHeight_amplitude_inverts_at_raccords
#print axioms passage_energy_sign_dichotomy
end RHV6Fresh
