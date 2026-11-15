/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TowerRaccord

/-!
# RHV6Fresh — le détecteur du raccord est complet (auteur, 2026-09-30)

Le cas laissé ouvert dans `Terminal/TowerRaccord.lean` est le passage « diagonal » : hauteur
strictement croissante ET positions radiales différentes. Il est fermé ici, sans prémisse.

* **Sortie et entrée de fibre** (`passage_exit_radial_ge_half`, `passage_entry_radial_le_half`) :
  sur un passage à hauteur strictement croissante, le membre de sortie est le DERNIER de sa fibre et
  le membre d'entrée le PREMIER de la sienne ; le miroir fonctionnel (même hauteur, `β ↦ 1 − β`)
  impose donc `β_l ≤ 1/2 ≤ β_e`.
* **Orientation** (`towerRaccord_oriented_of_height_lt`) : tout passage à hauteur strictement
  croissante (hauteur d'arrivée `≥ 2`) a un raccord orienté, quelle que soit la position radiale.
* **Détecteur complet** (`towerRaccord_oriented_iff_height_lt`) : sur un passage dont le membre de
  sortie est à hauteur `≥ 2`, le raccord est orienté si et seulement si la hauteur avance
  strictement. Le raccord est renversé exactement aux passages horizontaux.

* **Charge radiale d'une fibre** (`fibre_transport_product_off`, `fibre_charge_eq_one_iff`,
  `fibre_charge_gt_one_iff`) : sur la traversée `a → e → l → b` d'une paire `1/2 ∓ d`, le produit des
  trois transports est le produit en ligne multiplié par `(M₂²/(M₁·M₃))^d` ; ce facteur vaut `1` si
  et seulement si `d = 0` (trois premiers distincts ne sont jamais en progression géométrique), et
  son signe est décidé par la succession des deux écarts de premiers.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse nouvelle.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **Sortie de fibre** : si la hauteur avance strictement, le membre de sortie vérifie `1/2 ≤ β_e`
(sinon son miroir, à la même hauteur et plus à droite, s'intercalerait dans le passage). -/
theorem passage_exit_radial_ge_half (p : TZeroPassage)
    (hT : rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember) :
    1 / 2 ≤ rZeroRadialPosition p.zEarlierMember := by
  by_contra hlt
  push Not at hlt
  apply p.hConsecutive.2
  refine ⟨zMirrorZero p.zEarlierMember, ?_, ?_⟩
  · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    refine ⟨(thm_mirror_sameHeight _).symm, ?_⟩
    rw [thm_mirror_radialPosition]
    linarith
  · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    left
    rw [thm_mirror_sameHeight]
    exact hT

/-- **Entrée de fibre** : si la hauteur avance strictement, le membre d'entrée vérifie `β_l ≤ 1/2`
(sinon son miroir, à la même hauteur et plus à gauche, s'intercalerait dans le passage). -/
theorem passage_entry_radial_le_half (p : TZeroPassage)
    (hT : rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember) :
    rZeroRadialPosition p.zLaterMember ≤ 1 / 2 := by
  by_contra hlt
  push Not at hlt
  apply p.hConsecutive.2
  refine ⟨zMirrorZero p.zLaterMember, ?_, ?_⟩
  · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    left
    rw [thm_mirror_sameHeight]
    exact hT
  · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    refine ⟨thm_mirror_sameHeight _, ?_⟩
    rw [thm_mirror_radialPosition]
    linarith

/-- **Amplitude entre une sortie et une entrée de fibre** : si `β_l ≤ β_e`, `T_e ≤ T_l`, `2 ≤ T_l`
et `2 ≤ q`, alors la Tour `l` ne lit pas plus d'énergie en `q` que la Tour `e`. -/
theorem amplitude_le_of_radial_ge (e l : TrueZero)
    (hβ : rZeroRadialPosition l.1 ≤ rZeroRadialPosition e.1)
    (hT : rZeroHeight e.1 ≤ rZeroHeight l.1) (hT2 : 2 ≤ rZeroHeight l.1)
    {q : ℝ} (hq : 2 ≤ q) : ‖zeroTerm l q‖ ≤ ‖zeroTerm e q‖ := by
  have hq0 : 0 < q := by linarith
  have hNe := zeroPoint_norm_pos e
  have hNl := zeroPoint_norm_pos l
  have hβe1 : rZeroRadialPosition e.1 < 1 := thm_zeroRadialPosition_lt_one e.1
  have hβl0 : 0 < rZeroRadialPosition l.1 := thm_zeroRadialPosition_positive l.1
  have hTe : 0 < rZeroHeight e.1 := e.2
  rw [zeroTerm_norm hq0, zeroTerm_norm hq0, div_le_div_iff₀ hNl hNe]
  have hpow : q ^ rZeroRadialPosition e.1 =
      q ^ rZeroRadialPosition l.1 * q ^ (rZeroRadialPosition e.1 - rZeroRadialPosition l.1) := by
    rw [← Real.rpow_add hq0]
    congr 1
    ring
  rw [hpow, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hq0.le _)
  -- reste : ‖ρ_e‖ ≤ q^{β_e − β_l} · ‖ρ_l‖
  set a := rZeroRadialPosition e.1 - rZeroRadialPosition l.1 with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hlog : 1 / 2 ≤ Real.log q := by
    have h2 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq
    have := Real.log_two_gt_d9
    linarith
  have hc : 1 + a / 2 ≤ q ^ a := by
    rw [Real.rpow_def_of_pos hq0]
    have h1 : Real.log q * a + 1 ≤ Real.exp (Real.log q * a) := Real.add_one_le_exp _
    nlinarith
  have hcpos : 0 < q ^ a := Real.rpow_pos_of_pos hq0 _
  refine le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hcpos.le hNl.le) ?_
  rw [mul_pow, zeroPoint_norm_sq, zeroPoint_norm_sq]
  have hc2 : 1 + a ≤ (q ^ a) ^ 2 := by nlinarith
  have hsum : 0 < rZeroRadialPosition l.1 ^ 2 + rZeroHeight l.1 ^ 2 := by positivity
  have hTl2 : 4 ≤ rZeroHeight l.1 ^ 2 := by nlinarith
  have hTT : rZeroHeight e.1 ^ 2 ≤ rZeroHeight l.1 ^ 2 := by nlinarith
  have hβsq : rZeroRadialPosition e.1 ^ 2 - rZeroRadialPosition l.1 ^ 2 ≤ 2 * a := by
    have : rZeroRadialPosition e.1 ^ 2 - rZeroRadialPosition l.1 ^ 2 =
        a * (rZeroRadialPosition e.1 + rZeroRadialPosition l.1) := by rw [ha]; ring
    rw [this]
    have hs : rZeroRadialPosition e.1 + rZeroRadialPosition l.1 ≤ 2 := by linarith
    nlinarith
  calc rZeroRadialPosition e.1 ^ 2 + rZeroHeight e.1 ^ 2
      ≤ (1 + a) * (rZeroRadialPosition l.1 ^ 2 + rZeroHeight l.1 ^ 2) := by nlinarith
    _ ≤ (q ^ a) ^ 2 * (rZeroRadialPosition l.1 ^ 2 + rZeroHeight l.1 ^ 2) :=
        mul_le_mul_of_nonneg_right hc2 hsum.le

/-- **Le cas diagonal est fermé** : tout passage à hauteur strictement croissante, de hauteur
d'arrivée `≥ 2`, a un raccord orienté — quelles que soient les positions radiales. -/
theorem towerRaccord_oriented_of_height_lt (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hT : rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember)
    (hT2 : 2 ≤ rZeroHeight p.zLaterMember) : (towerRaccordOf p hE hL).Oriented := by
  have hM : (2 : ℝ) ≤ ((towerRaccordOf p hE hL).M : ℝ) := by
    rw [(towerRaccordOf p hE hL).exit_eq]
    exact_mod_cast (expectedMinimumPrime_prime _).two_le
  exact amplitude_le_of_radial_ge ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩
    ((passage_entry_radial_le_half p hT).trans (passage_exit_radial_ge_half p hT)) hT.le hT2 hM

/-- **Le détecteur est complet** : sur un passage dont le membre de sortie est à hauteur `≥ 2`, le
raccord est orienté si et seulement si la hauteur avance strictement. Il est renversé exactement
aux passages horizontaux. -/
theorem towerRaccord_oriented_iff_height_lt (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hT2 : 2 ≤ rZeroHeight p.zEarlierMember) :
    (towerRaccordOf p hE hL).Oriented ↔
      rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember := by
  constructor
  · intro hO
    by_contra hnlt
    have hSame : rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember :=
      le_antisymm (passage_height_le p) (not_lt.mp hnlt)
    have hHMR := nullPassage_horizontal p ((thm_zeroPassage_null_iff_sameHeight p).mpr hSame)
    exact absurd hO (not_le.mpr
      (towerRaccord_reverses_of_sameHeight (towerRaccordOf p hE hL) hSame hT2 hHMR.2.1))
  · intro hT
    exact towerRaccord_oriented_of_height_lt p hE hL hT (hT2.trans hT.le)

/-! ## La charge radiale d'une fibre hors ligne : où la grammaire des écarts rencontre `δ`

Traversée d'une fibre : `a → e → l → b`, avec `e`, `l` la paire à même hauteur (`β_e = 1/2 − d`,
`β_l = 1/2 + d`). Les trois raccords se font en trois premiers `M₁ < M₂ < M₃`. Le produit des trois
transports vaut le produit « en ligne » multiplié par `(M₂² / (M₁·M₃))^d`. Ce facteur est la seule
trace de `d` ; son signe est décidé par la succession des deux écarts `M₂ − M₁`, `M₃ − M₂`. -/

/-- **Produit des transports sur trois raccords successifs** `a → e → l → b` : les normes
télescopent, il reste les trois puissances des premiers partagés. -/
theorem fibre_transport_product (a e l b : TrueZero) {M₁ M₂ M₃ : ℝ}
    (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃) :
    energyRatio a e M₁ * energyRatio e l M₂ * energyRatio l b M₃ =
      M₁ ^ (rZeroRadialPosition e.1 - rZeroRadialPosition a.1) *
        M₂ ^ (rZeroRadialPosition l.1 - rZeroRadialPosition e.1) *
        M₃ ^ (rZeroRadialPosition b.1 - rZeroRadialPosition l.1) *
        (‖zeroPoint a‖ / ‖zeroPoint b‖) := by
  rw [energyRatio_eq a e h₁, energyRatio_eq e l h₂, energyRatio_eq l b h₃]
  have ha := (zeroPoint_norm_pos a).ne'
  have he := (zeroPoint_norm_pos e).ne'
  have hl := (zeroPoint_norm_pos l).ne'
  have hb := (zeroPoint_norm_pos b).ne'
  field_simp

/-- **La charge radiale de la fibre** : si `β_e = 1/2 − d` et `β_l = 1/2 + d`, le produit des trois
transports est le produit en ligne (`d = 0`) multiplié par `(M₂² / (M₁·M₃))^d`. -/
theorem fibre_transport_product_off (a e l b : TrueZero) {M₁ M₂ M₃ d : ℝ}
    (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃)
    (he : rZeroRadialPosition e.1 = 1 / 2 - d) (hl : rZeroRadialPosition l.1 = 1 / 2 + d) :
    energyRatio a e M₁ * energyRatio e l M₂ * energyRatio l b M₃ =
      M₁ ^ (1 / 2 - rZeroRadialPosition a.1) * M₃ ^ (rZeroRadialPosition b.1 - 1 / 2) *
        (‖zeroPoint a‖ / ‖zeroPoint b‖) * (M₂ ^ 2 / (M₁ * M₃)) ^ d := by
  rw [fibre_transport_product a e l b h₁ h₂ h₃, he, hl]
  have e1 : M₁ ^ (1 / 2 - d - rZeroRadialPosition a.1) =
      M₁ ^ (1 / 2 - rZeroRadialPosition a.1) / M₁ ^ d := by
    rw [← Real.rpow_sub h₁]; congr 1; ring
  have e3 : M₃ ^ (rZeroRadialPosition b.1 - (1 / 2 + d)) =
      M₃ ^ (rZeroRadialPosition b.1 - 1 / 2) / M₃ ^ d := by
    rw [← Real.rpow_sub h₃]; congr 1; ring
  have e2 : M₂ ^ (1 / 2 + d - (1 / 2 - d)) = (M₂ ^ 2) ^ d := by
    rw [← Real.rpow_natCast M₂ 2, ← Real.rpow_mul h₂.le]
    congr 1
    push_cast
    ring
  have e4 : (M₂ ^ 2 / (M₁ * M₃)) ^ d = (M₂ ^ 2) ^ d / (M₁ ^ d * M₃ ^ d) := by
    rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow h₁.le h₃.le]
  have hd1 : M₁ ^ d ≠ 0 := (Real.rpow_pos_of_pos h₁ d).ne'
  have hd3 : M₃ ^ d ≠ 0 := (Real.rpow_pos_of_pos h₃ d).ne'
  rw [e1, e2, e3, e4]
  field_simp

/-- **Arithmétique** : trois premiers distincts ne sont jamais en progression géométrique. -/
theorem prime_sq_ne_mul {M₁ M₂ M₃ : ℕ} (hp₁ : M₁.Prime) (hp₂ : M₂.Prime) (hp₃ : M₃.Prime)
    (h₁₂ : M₁ ≠ M₂) (h₂₃ : M₂ ≠ M₃) : M₂ ^ 2 ≠ M₁ * M₃ := by
  intro h
  have hdvd : M₂ ∣ M₁ * M₃ := ⟨M₂, by rw [← h]; ring⟩
  rcases (Nat.Prime.dvd_mul hp₂).mp hdvd with h' | h'
  · exact h₁₂ ((Nat.prime_dvd_prime_iff_eq hp₂ hp₁).mp h').symm
  · exact h₂₃ ((Nat.prime_dvd_prime_iff_eq hp₂ hp₃).mp h')

/-- **Neutralité de la charge ⟺ en ligne** : pour trois premiers distincts, le facteur
`(M₂² / (M₁·M₃))^d` vaut `1` si et seulement si `d = 0`. -/
theorem fibre_charge_eq_one_iff {M₁ M₂ M₃ : ℕ} (hp₁ : M₁.Prime) (hp₂ : M₂.Prime) (hp₃ : M₃.Prime)
    (h₁₂ : M₁ ≠ M₂) (h₂₃ : M₂ ≠ M₃) (d : ℝ) :
    (((M₂ : ℝ) ^ 2) / ((M₁ : ℝ) * (M₃ : ℝ))) ^ d = 1 ↔ d = 0 := by
  have h1 : (0 : ℝ) < M₁ := by exact_mod_cast hp₁.pos
  have h2 : (0 : ℝ) < M₂ := by exact_mod_cast hp₂.pos
  have h3 : (0 : ℝ) < M₃ := by exact_mod_cast hp₃.pos
  have hx : (0 : ℝ) < (M₂ : ℝ) ^ 2 / ((M₁ : ℝ) * (M₃ : ℝ)) := by positivity
  have hne : (M₂ : ℝ) ^ 2 / ((M₁ : ℝ) * (M₃ : ℝ)) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq (by positivity)]
    exact_mod_cast prime_sq_ne_mul hp₁ hp₂ hp₃ h₁₂ h₂₃
  have hlog : Real.log ((M₂ : ℝ) ^ 2 / ((M₁ : ℝ) * (M₃ : ℝ))) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hx hne
  rw [Real.rpow_def_of_pos hx, Real.exp_eq_one_iff, mul_eq_zero]
  exact ⟨fun h => h.resolve_left hlog, Or.inr⟩

/-- **Signe de la charge** (`d > 0`) : amplification nette si et seulement si `M₁·M₃ < M₂²`. -/
theorem fibre_charge_gt_one_iff {M₁ M₂ M₃ d : ℝ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃)
    (hd : 0 < d) : 1 < (M₂ ^ 2 / (M₁ * M₃)) ^ d ↔ M₁ * M₃ < M₂ ^ 2 := by
  have hx : 0 < M₂ ^ 2 / (M₁ * M₃) := by positivity
  rw [Real.one_lt_rpow_iff_of_pos hx, one_lt_div (by positivity)]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact h
    · linarith
  · exact fun h => Or.inl ⟨h, hd⟩

/-- **La grammaire des écarts décide le signe** : `M₂² − M₁·M₃` en fonction des deux écarts
`g = M₂ − M₁` (avant) et `g' = M₃ − M₂` (après). -/
theorem sq_sub_mul_eq_gaps (M₁ M₂ M₃ : ℝ) :
    M₂ ^ 2 - M₁ * M₃ = M₂ * ((M₂ - M₁) - (M₃ - M₂)) + (M₂ - M₁) * (M₃ - M₂) := by
  ring

/-- Écart avant `≥` écart après (par exemple `4` puis `2`, ou deux écarts égaux) : amplification. -/
theorem fibre_amplifies_of_gap_ge {M₁ M₂ M₃ : ℝ} (h₂ : 0 < M₂) (h₁₂ : M₁ < M₂) (h₂₃ : M₂ < M₃)
    (hg : M₃ - M₂ ≤ M₂ - M₁) : M₁ * M₃ < M₂ ^ 2 := by
  nlinarith [mul_pos (sub_pos.mpr h₁₂) (sub_pos.mpr h₂₃),
    mul_nonneg h₂.le (sub_nonneg.mpr hg)]

/-- Écart avant `2`, écart après `4`, premier central `> 4` : atténuation. -/
theorem fibre_attenuates_of_gap_two_four {M₂ : ℝ} (h : 4 < M₂) :
    M₂ ^ 2 < (M₂ - 2) * (M₂ + 4) := by
  nlinarith

#print axioms passage_exit_radial_ge_half
#print axioms passage_entry_radial_le_half
#print axioms amplitude_le_of_radial_ge
#print axioms towerRaccord_oriented_of_height_lt
#print axioms towerRaccord_oriented_iff_height_lt
#print axioms fibre_transport_product_off
#print axioms fibre_charge_eq_one_iff
#print axioms fibre_charge_gt_one_iff

end RHV6Fresh
