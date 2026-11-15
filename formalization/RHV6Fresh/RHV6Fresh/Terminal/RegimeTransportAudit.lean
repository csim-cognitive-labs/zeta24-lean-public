/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.OnRegimeInduction
import RHV6Fresh.Terminal.SymmetricWinding

/-!
# RHV6Fresh — audit du transport du régime ON (mission E212–E217, 2026-10-13)

Trois questions de la mission, tranchées par des théorèmes (axiomes standard, aucune hypothèse de ligne sur l'arrivée) :

1. **Fibre mixte** (§1). La configuration « un membre ON et une paire miroir hors ligne à la même hauteur » n'est exclue par
   AUCUNE définition : l'ordre des membres est lexicographique (hauteur, puis partie réelle), clé injective. Sur un passage
   consécutif qui monte, l'arrivée est le membre de partie réelle MINIMALE de sa fibre (`arrival_radial_le_fiber`) ; dans une
   fibre mixte l'arrivée est donc le membre BAS, jamais le membre ON. D'où, SANS historique ON : arrivée ON ⟺ fibre entière ON
   ⟺ aucun hors ligne dans `]T_e, T_l]` ⟺ `ΔD = 0` (`arrival_onLine_iff_fiber_onLine`, `arrival_onLine_iff_lineDefect_zero`).
   L'hypothèse cachée est le CLASSEMENT (consécutivité dans l'ordre lexicographique) ; c'est une convention d'énumération des
   vrais zéros, sans contenu analytique : elle ne décrit aucune dynamique.
2. **Domaines de l'inclusion des Tours** (§2). Depuis une Tour ON : inclusion sur `x ≥ 1` ⟺ `β_l ≤ 1/2` ∧ supports ordonnés ;
   inclusion sur `0 < x ≤ 1` ⟺ `1/2 ≤ β_l` ∧ supports ordonnés ; sur tout `x > 0` ⟺ `β_l = 1/2` ∧ supports ordonnés. Sur un
   passage qui monte, la moitié `x ≥ 1` est la seule condition de support (lue par la hauteur) ; TOUTE la conservation radiale
   est dans la zone `0 < x < 1`, qui ne contient aucun premier ni aucun entier `≥ 2`. Sur les premiers, l'inclusion se réduit à
   la seule abscisse `2` dès que `β_l ≤ β_e` (`inside_primes_iff_at_two`).
3. **Raccords d'énergie** (§3). Égalité des rapports de normes `‖u_l‖/‖u_e‖` en deux abscisses distinctes ⟺ `β_l = β_e`
   (`transport_ratio_eq_at_two_points_iff`) : les deux égalités de normes « manquantes » aux raccords et l'inclusion sur tout
   `x > 0` exigent la MÊME conservation radiale. Les deux égalités d'E116 elles-mêmes (`‖u_e(q)‖ = ‖u_l(q)‖` en deux premiers)
   ⟺ même partie réelle ET même module (`raccord_norm_equalities_iff`) : elles sont FAUSSES sur tout passage qui monte, arrivée
   ON comprise (`raccord_norm_equalities_false_of_vertical`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Fibre mixte : l'arrivée d'un passage qui monte est le membre minimal de sa fibre -/

/-- **L'arrivée est le membre de partie réelle minimale de sa fibre.** Sur un passage consécutif qui monte, tout vrai zéro de
même hauteur que l'arrivée a une partie réelle au moins égale. Seule la consécutivité lexicographique sert. -/
theorem arrival_radial_le_fiber (p : TZeroPassage) (hV : VerticalPassage p) (z : TNonTrivialZetaZero)
    (hz : rZeroHeight z = rZeroHeight p.zLaterMember) :
    rZeroRadialPosition p.zLaterMember ≤ rZeroRadialPosition z := by
  by_contra hlt
  push Not at hlt
  refine p.hConsecutive.2 ⟨z, ?_, ?_⟩
  · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]; left; rw [hz]; exact hV
  · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]; right; exact ⟨hz, hlt⟩

/-- **Fibre mixte : l'arrivée est basse.** Si la fibre d'arrivée contient un membre bas (`β < 1/2`), l'arrivée d'un passage qui
monte est basse : le membre ON d'une fibre mixte n'est jamais l'arrivée. -/
theorem mixed_fiber_arrival_low (p : TZeroPassage) (hV : VerticalPassage p) (z : TNonTrivialZetaZero)
    (hz : rZeroHeight z = rZeroHeight p.zLaterMember) (hlow : rZeroRadialPosition z < 1 / 2) :
    rZeroRadialPosition p.zLaterMember < 1 / 2 :=
  lt_of_le_of_lt (arrival_radial_le_fiber p hV z hz) hlow

/-- **Arrivée ON ⟺ fibre entière ON**, sur un passage qui monte, SANS historique ON. Sens direct : un membre bas de la fibre
serait avant l'arrivée (`arrival_radial_le_fiber`), un membre haut a son miroir bas dans la même fibre. -/
theorem arrival_onLine_iff_fiber_onLine (p : TZeroPassage) (hV : VerticalPassage p)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ↔
      ∀ z : TrueZero, rZeroHeight z.1 = rZeroHeight p.zLaterMember → rZeroRadialPosition z.1 = 1 / 2 := by
  constructor
  · intro hOnL z hz
    have hge := arrival_radial_le_fiber p hV z.1 hz
    have hgeM := arrival_radial_le_fiber p hV (mirrorMember z).1 (by rw [mirrorMember_ordinate]; exact hz)
    rw [mirrorMember_radial, hOnL] at hgeM
    rw [hOnL] at hge
    linarith
  · intro h
    exact h ⟨p.zLaterMember, hL⟩ rfl

/-- **Arrivée ON ⟺ `ΔD(T_e, T_l) = 0`**, sur un passage qui monte, SANS historique ON (l'historique de
`regime_probes_equivalent` n'est pas nécessaire : la consécutivité suffit). -/
theorem arrival_onLine_iff_lineDefect_zero (p : TZeroPassage) (hV : VerticalPassage p)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ↔
      lineDefect (rZeroHeight p.zEarlierMember) (rZeroHeight p.zLaterMember) = 0 := by
  rw [counting_increment_eq_iff_noOffInInterval hV.le, arrival_onLine_iff_fiber_onLine p hV hL]
  constructor
  · intro h z hTz hzU
    by_contra hne
    have hzT : rZeroHeight z.1 = rZeroHeight p.zLaterMember := by
      by_contra hneT
      exact consecutive_no_height_between p z.1 ⟨hTz, lt_of_le_of_ne hzU hneT⟩
    exact hne (h z hzT)
  · intro h z hz
    exact h z (by rw [hz]; exact hV) hz.le

/-- **Les trois propositions A, B, C coïncident sur un passage qui monte** : A (arrivée ON), B (fibre d'arrivée entière ON),
C (aucun hors ligne dans `]T_e, T_l]`), et `fibre_BASSE(T_l) = 0`. Aucune hypothèse d'historique. -/
theorem arrival_fiber_interval_equivalent (p : TZeroPassage) (hV : VerticalPassage p)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    (rZeroRadialPosition p.zLaterMember = 1 / 2 ↔
        ∀ z : TrueZero, rZeroHeight z.1 = rZeroHeight p.zLaterMember → rZeroRadialPosition z.1 = 1 / 2) ∧
      (rZeroRadialPosition p.zLaterMember = 1 / 2 ↔
        ∀ z : TrueZero, rZeroHeight p.zEarlierMember < rZeroHeight z.1 →
          rZeroHeight z.1 ≤ rZeroHeight p.zLaterMember → rZeroRadialPosition z.1 = 1 / 2) ∧
      (rZeroRadialPosition p.zLaterMember = 1 / 2 ↔ lowFiberCount (rZeroHeight p.zLaterMember) = 0) := by
  refine ⟨arrival_onLine_iff_fiber_onLine p hV hL, ?_, ?_⟩
  · rw [arrival_onLine_iff_lineDefect_zero p hV hL, counting_increment_eq_iff_noOffInInterval hV.le]
  · rw [arrival_onLine_iff_lineDefect_zero p hV hL, passage_lineDefect_eq_fiber p hV,
      offLine_fiber_contribution_even]
    omega

/-! ## 2. Domaines de l'inclusion d'une Tour dans une Tour ON -/

/-- Lemme : `x ^ β / A ≤ x ^ γ / B` pour tout `x ≥ 1` force `β ≤ γ` ; lu en `1/y`, pour tout `0 < x ≤ 1` il force `γ ≤ β`. -/
theorem exponent_ge_of_inside_small {β γ A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : ∀ x : ℝ, 0 < x → x ≤ 1 → x ^ β / A ≤ x ^ γ / B) : γ ≤ β := by
  have := exponent_le_of_inside (β := -β) (γ := -γ) hA hB (fun y hy => by
    have hy0 : 0 < y := by linarith
    have hx := h y⁻¹ (inv_pos.mpr hy0) (inv_le_one_of_one_le₀ hy)
    rwa [Real.inv_rpow hy0.le, Real.inv_rpow hy0.le, ← Real.rpow_neg hy0.le,
      ← Real.rpow_neg hy0.le] at hx)
  linarith

/-- **Inclusion sur `x ≥ 1` dans une Tour ON** ⟺ `β_w ≤ 1/2` ∧ supports ordonnés. -/
theorem inside_large_iff {z w : TrueZero} (hz : rZeroRadialPosition z.1 = 1 / 2) :
    (∀ x : ℝ, 1 ≤ x → ‖zeroTerm w x‖ ≤ ‖zeroTerm z x‖) ↔
      rZeroRadialPosition w.1 ≤ 1 / 2 ∧ ‖zeroPoint z‖ ≤ ‖zeroPoint w‖ := by
  constructor
  · intro h
    have hβ : rZeroRadialPosition w.1 ≤ rZeroRadialPosition z.1 :=
      exponent_le_of_inside (norm_zeroPoint_pos w) (norm_zeroPoint_pos z) (fun x hx => by
        have := h x hx
        rwa [norm_zeroTerm_eq w (by linarith), norm_zeroTerm_eq z (by linarith)] at this)
    have h1 := h 1 le_rfl
    rw [norm_zeroTerm_eq w one_pos, norm_zeroTerm_eq z one_pos, Real.one_rpow, Real.one_rpow] at h1
    exact ⟨hz ▸ hβ, (one_div_le_one_div (norm_zeroPoint_pos w) (norm_zeroPoint_pos z)).mp h1⟩
  · rintro ⟨hβ, hρ⟩ x hx
    have hx0 : 0 < x := by linarith
    rw [norm_zeroTerm_eq w hx0, norm_zeroTerm_eq z hx0]
    calc x ^ rZeroRadialPosition w.1 / ‖zeroPoint w‖
        ≤ x ^ rZeroRadialPosition z.1 / ‖zeroPoint w‖ := by
          exact div_le_div_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hx (by rw [hz]; exact hβ)) (norm_zeroPoint_pos w).le
      _ ≤ x ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖ :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) (norm_zeroPoint_pos z) hρ

/-- **Inclusion sur `0 < x ≤ 1` dans une Tour ON** ⟺ `1/2 ≤ β_w` ∧ supports ordonnés. Cette zone ne contient aucun premier. -/
theorem inside_small_iff {z w : TrueZero} (hz : rZeroRadialPosition z.1 = 1 / 2) :
    (∀ x : ℝ, 0 < x → x ≤ 1 → ‖zeroTerm w x‖ ≤ ‖zeroTerm z x‖) ↔
      1 / 2 ≤ rZeroRadialPosition w.1 ∧ ‖zeroPoint z‖ ≤ ‖zeroPoint w‖ := by
  constructor
  · intro h
    have hβ : rZeroRadialPosition z.1 ≤ rZeroRadialPosition w.1 :=
      exponent_ge_of_inside_small (norm_zeroPoint_pos w) (norm_zeroPoint_pos z) (fun x hx hx1 => by
        have := h x hx hx1
        rwa [norm_zeroTerm_eq w hx, norm_zeroTerm_eq z hx] at this)
    have h1 := h 1 one_pos le_rfl
    rw [norm_zeroTerm_eq w one_pos, norm_zeroTerm_eq z one_pos, Real.one_rpow, Real.one_rpow] at h1
    exact ⟨hz ▸ hβ, (one_div_le_one_div (norm_zeroPoint_pos w) (norm_zeroPoint_pos z)).mp h1⟩
  · rintro ⟨hβ, hρ⟩ x hx hx1
    rw [norm_zeroTerm_eq w hx, norm_zeroTerm_eq z hx]
    calc x ^ rZeroRadialPosition w.1 / ‖zeroPoint w‖
        ≤ x ^ rZeroRadialPosition z.1 / ‖zeroPoint w‖ := by
          exact div_le_div_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by rw [hz]; exact hβ)) (norm_zeroPoint_pos w).le
      _ ≤ x ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖ :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (norm_zeroPoint_pos z) hρ

/-- **Sur un passage qui monte depuis un membre ON, la moitié `x ≥ 1` de l'inclusion est la seule condition de support**
(`β_l ≤ 1/2` est acquis), et la moitié `0 < x ≤ 1` porte exactement l'arrivée ON (avec le support). -/
theorem passage_inclusion_split (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hV : VerticalPassage p) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2) :
    let hL : 0 < rZeroHeight p.zLaterMember := lt_trans hE hV
    ((∀ x : ℝ, 1 ≤ x → ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖) ↔
        ‖zeroPoint ⟨p.zEarlierMember, hE⟩‖ ≤ ‖zeroPoint ⟨p.zLaterMember, hL⟩‖) ∧
      ((∀ x : ℝ, 0 < x → x ≤ 1 → ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ ‖zeroTerm ⟨p.zEarlierMember, hE⟩ x‖) ↔
        rZeroRadialPosition p.zLaterMember = 1 / 2 ∧
          ‖zeroPoint ⟨p.zEarlierMember, hE⟩‖ ≤ ‖zeroPoint ⟨p.zLaterMember, hL⟩‖) := by
  intro hL
  have hle : rZeroRadialPosition p.zLaterMember ≤ 1 / 2 := passage_entry_radial_le_half p hV
  refine ⟨?_, ?_⟩
  · rw [inside_large_iff (z := ⟨p.zEarlierMember, hE⟩) (w := ⟨p.zLaterMember, hL⟩) hOn]
    exact ⟨fun h => h.2, fun h => ⟨hle, h⟩⟩
  · rw [inside_small_iff (z := ⟨p.zEarlierMember, hE⟩) (w := ⟨p.zLaterMember, hL⟩) hOn]
    exact ⟨fun h => ⟨le_antisymm hle h.1, h.2⟩, fun h => ⟨h.1.ge, h.2⟩⟩

/-- **Sur les premiers, l'inclusion se lit en la seule abscisse 2** dès que `β_w ≤ β_z` : le rapport
`x^{β_w − β_z}‖ρ_z‖/‖ρ_w‖` décroît. Les nombres premiers ne voient de l'inclusion qu'une condition de support à `x = 2`. -/
theorem inside_primes_iff_at_two {z w : TrueZero}
    (hβ : rZeroRadialPosition w.1 ≤ rZeroRadialPosition z.1) :
    (∀ q : ℕ, q.Prime → ‖zeroTerm w q‖ ≤ ‖zeroTerm z q‖) ↔ ‖zeroTerm w 2‖ ≤ ‖zeroTerm z 2‖ := by
  constructor
  · intro h; exact_mod_cast h 2 Nat.prime_two
  · intro h2 q hq
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
    have hq0 : (0 : ℝ) < q := by linarith
    rw [norm_zeroTerm_eq w (by norm_num), norm_zeroTerm_eq z (by norm_num)] at h2
    rw [norm_zeroTerm_eq w hq0, norm_zeroTerm_eq z hq0]
    set a := rZeroRadialPosition w.1
    set b := rZeroRadialPosition z.1
    have hA := norm_zeroPoint_pos w
    have hB := norm_zeroPoint_pos z
    rw [div_le_div_iff₀ hA hB] at h2 ⊢
    -- `q^a = q^b · (q/2)^{a−b} · 2^{a−b}` et `(q/2)^{a−b} ≤ 1`
    have hsplit : (q : ℝ) ^ a = (q : ℝ) ^ b * (q : ℝ) ^ (a - b) := by
      rw [← Real.rpow_add hq0]; ring_nf
    have hsplit2 : (2 : ℝ) ^ a = (2 : ℝ) ^ b * (2 : ℝ) ^ (a - b) := by
      rw [← Real.rpow_add (by norm_num)]; ring_nf
    have hmono : (q : ℝ) ^ (a - b) ≤ (2 : ℝ) ^ (a - b) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hq2 (by linarith)
    have h2b : 0 < (2 : ℝ) ^ b := Real.rpow_pos_of_pos (by norm_num) _
    have hqb : 0 < (q : ℝ) ^ b := Real.rpow_pos_of_pos hq0 _
    rw [hsplit2] at h2
    -- `2^{a−b}·‖ρ_z‖ ≤ ‖ρ_w‖`
    have hkey : (2 : ℝ) ^ (a - b) * ‖zeroPoint z‖ ≤ ‖zeroPoint w‖ := by
      have : (2 : ℝ) ^ b * ((2 : ℝ) ^ (a - b) * ‖zeroPoint z‖) ≤ (2 : ℝ) ^ b * ‖zeroPoint w‖ := by
        nlinarith
      exact le_of_mul_le_mul_left this h2b
    rw [hsplit]
    have hqab : 0 ≤ (q : ℝ) ^ (a - b) := Real.rpow_nonneg hq0.le _
    nlinarith [mul_le_mul_of_nonneg_right hmono hB.le]

/-! ## 3. Raccords d'énergie : deux égalités de rapports de normes ⟺ même partie réelle -/

/-- **Rapport transporté en deux abscisses.** Pour `0 < M₁ < M₂`, le rapport des normes `‖u_w‖/‖u_z‖` prend la même valeur en
`M₁` et en `M₂` si et seulement si `β_w = β_z`. Les « deux égalités de normes » aux raccords et l'inclusion sur tout `x > 0`
demandent la même conservation radiale. -/
theorem transport_ratio_eq_at_two_points_iff (z w : TrueZero) {M₁ M₂ : ℝ} (h₁ : 0 < M₁) (h₁₂ : M₁ < M₂) :
    ‖zeroTerm w M₁‖ / ‖zeroTerm z M₁‖ = ‖zeroTerm w M₂‖ / ‖zeroTerm z M₂‖ ↔
      rZeroRadialPosition w.1 = rZeroRadialPosition z.1 := by
  have h₂ : 0 < M₂ := lt_trans h₁ h₁₂
  have hA := norm_zeroPoint_pos w
  have hB := norm_zeroPoint_pos z
  have hratio : ∀ {M : ℝ}, 0 < M →
      ‖zeroTerm w M‖ / ‖zeroTerm z M‖ = M ^ (rZeroRadialPosition w.1 - rZeroRadialPosition z.1) *
        (‖zeroPoint z‖ / ‖zeroPoint w‖) := by
    intro M hM
    rw [norm_zeroTerm_eq w hM, norm_zeroTerm_eq z hM, Real.rpow_sub hM]
    have := Real.rpow_pos_of_pos hM (rZeroRadialPosition z.1)
    field_simp
  rw [hratio h₁, hratio h₂]
  have hc : 0 < ‖zeroPoint z‖ / ‖zeroPoint w‖ := div_pos hB hA
  constructor
  · intro h
    have hpow := mul_right_cancel₀ hc.ne' h
    set c := rZeroRadialPosition w.1 - rZeroRadialPosition z.1
    by_contra hne
    have hc0 : c ≠ 0 := sub_ne_zero.mpr hne
    rcases lt_or_gt_of_ne hc0 with hneg | hpos
    · exact absurd hpow (ne_of_gt (Real.rpow_lt_rpow_of_neg h₁ h₁₂ hneg))
    · exact absurd hpow (ne_of_lt (Real.rpow_lt_rpow h₁.le h₁₂ hpos))
  · intro h
    rw [h, sub_self, Real.rpow_zero, Real.rpow_zero]


/-- **Les deux égalités de normes « manquantes » d'E116** (`‖u_e(q)‖ = ‖u_l(q)‖` en deux abscisses `q₁ < q₂`) ⟺ même partie réelle
ET même module de support. -/
theorem raccord_norm_equalities_iff (e l : TrueZero) {q₁ q₂ : ℝ} (h₁ : 0 < q₁) (h₁₂ : q₁ < q₂) :
    (‖zeroTerm e q₁‖ = ‖zeroTerm l q₁‖ ∧ ‖zeroTerm e q₂‖ = ‖zeroTerm l q₂‖) ↔
      rZeroRadialPosition l.1 = rZeroRadialPosition e.1 ∧ ‖zeroPoint e‖ = ‖zeroPoint l‖ := by
  have h₂ : 0 < q₂ := lt_trans h₁ h₁₂
  have hA := norm_zeroPoint_pos l
  have hB := norm_zeroPoint_pos e
  have hpos : ∀ {q : ℝ}, 0 < q → 0 < ‖zeroTerm e q‖ := fun hq => by
    rw [norm_zeroTerm_eq e hq]; exact div_pos (Real.rpow_pos_of_pos hq _) hB
  constructor
  · rintro ⟨e1, e2⟩
    have hβ : rZeroRadialPosition l.1 = rZeroRadialPosition e.1 := by
      rw [← transport_ratio_eq_at_two_points_iff e l h₁ h₁₂, ← e1, ← e2, div_self (hpos h₁).ne',
        div_self (hpos h₂).ne']
    refine ⟨hβ, ?_⟩
    rw [norm_zeroTerm_eq e h₁, norm_zeroTerm_eq l h₁, hβ] at e1
    have hx := Real.rpow_pos_of_pos h₁ (rZeroRadialPosition e.1)
    field_simp at e1
    nlinarith
  · rintro ⟨hβ, hρ⟩
    refine ⟨?_, ?_⟩
    · rw [norm_zeroTerm_eq e h₁, norm_zeroTerm_eq l h₁, hβ, hρ]
    · rw [norm_zeroTerm_eq e h₂, norm_zeroTerm_eq l h₂, hβ, hρ]

/-- **Sur tout passage qui monte, les deux égalités de normes d'E116 sont FAUSSES**, que l'arrivée soit ON ou non : même partie
réelle et même module forcent la même hauteur. Elles n'étaient pas une loi manquante mais un énoncé faux entre deux membres
distincts de hauteurs différentes (la version historique `energy_balance_two_primes_false` ne traitait que `β_e < β_l`). -/
theorem raccord_norm_equalities_false_of_vertical (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hV : VerticalPassage p) {q₁ q₂ : ℝ} (h₁ : 0 < q₁) (h₁₂ : q₁ < q₂) :
    ¬ (‖zeroTerm ⟨p.zEarlierMember, hE⟩ q₁‖ = ‖zeroTerm ⟨p.zLaterMember, lt_trans hE hV⟩ q₁‖ ∧
        ‖zeroTerm ⟨p.zEarlierMember, hE⟩ q₂‖ = ‖zeroTerm ⟨p.zLaterMember, lt_trans hE hV⟩ q₂‖) := by
  intro h
  obtain ⟨hβ, hρ⟩ := (raccord_norm_equalities_iff _ _ h₁ h₁₂).mp h
  have hsq : ‖zeroPoint ⟨p.zEarlierMember, hE⟩‖ ^ 2 = ‖zeroPoint ⟨p.zLaterMember, lt_trans hE hV⟩‖ ^ 2 := by rw [hρ]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply] at hsq
  have r1 := zeroPoint_re ⟨p.zEarlierMember, hE⟩
  have r2 := zeroPoint_re ⟨p.zLaterMember, lt_trans hE hV⟩
  have i1 := zeroPoint_im ⟨p.zEarlierMember, hE⟩
  have i2 := zeroPoint_im ⟨p.zLaterMember, lt_trans hE hV⟩
  simp only at hβ r1 r2 i1 i2
  rw [r1, r2, i1, i2, hβ] at hsq
  have hTl : 0 < rZeroHeight p.zLaterMember := lt_trans hE hV
  have : rZeroHeight p.zEarlierMember * rZeroHeight p.zEarlierMember <
      rZeroHeight p.zLaterMember * rZeroHeight p.zLaterMember := by
    have hlt : rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember := hV
    nlinarith
  linarith

#print axioms arrival_radial_le_fiber
#print axioms mixed_fiber_arrival_low
#print axioms arrival_onLine_iff_fiber_onLine
#print axioms arrival_onLine_iff_lineDefect_zero
#print axioms arrival_fiber_interval_equivalent
#print axioms inside_large_iff
#print axioms inside_small_iff
#print axioms passage_inclusion_split
#print axioms inside_primes_iff_at_two
#print axioms transport_ratio_eq_at_two_points_iff
#print axioms raccord_norm_equalities_iff
#print axioms raccord_norm_equalities_false_of_vertical

end RHV6Fresh
