/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.PointedPrimeComparison

/-!
# RHV6Fresh — l'enroulement des Tours à indice fixé (E151, auteur, 2026-10-02)

Demande de l'auteur : à indice de contact `k` fixé, les cellules des zéros successifs rapetissent ; un
zéro « s'enroule » à l'intérieur du précédent. Ce fichier écrit les conséquences exactes de ce régime,
pour toute position radiale `β > 0` (donc aussi dans les mondes témoins).

* **Emboîtement strict** (§1) : à `k ≥ 1` fixé, le contact `C_k(β, T) = exp((arctan(T/β) + kπ)/T)`
  décroît strictement quand la hauteur monte (`windingContact_strictAnti_height`) : les `k` premiers
  demi-tours d'un zéro plus haut sont contenus dans ceux du plus bas. À même hauteur, aucun
  enroulement : translation rigide, même facteur pour tout `k` (`windingContact_sameHeight`).
* **Fenêtre de hauteur** (§2) : un réel `q > 0` n'est dans la cellule `k` que si
  `kπ < T log q < (k + 1)π + π/2` (`cell_height_window`) ; au-delà de la hauteur
  `((k + 1)π + π/2)/log 2`, la cellule `k` ne contient aucun réel `≥ 2` (`cell_empty_above_height`).
  Pour `k = 4` : seuls les membres de hauteur `< 24,93`, c'est-à-dire `T_1` et `T_2` parmi tous les zéros.
* **Enfoncement de chaque premier** (§3) : dès que `T log q ≥ kπ + π/2`, `q` est au-dessus du contact `k`
  (`contact_below_of_height`) : tout premier traverse tout indice fixé et s'enfonce sans retour ; le contact
  `k` d'une Tour `(β', T')` lu dans la Tour `(β, T)` est à la position `T·(φ' + kπ)/T' − φ` sur `π`
  (`windingContact_position`), contraction `T/T'` de l'indice.

Borne : tout ce qui est écrit ici vaut pour tout `β > 0` ; l'enroulement est la contraction du pas
(régime vertical) lue à indice fixé ; il ne lit pas la position radiale. Aucun `sorry`, aucun axiome,
aucune prémisse.
-/

namespace RHV6Fresh

open Real

/-- Contact d'indice `k` (réel) de la Tour de paramètres `(β, T)`. -/
noncomputable def windingContact (β T k : ℝ) : ℝ :=
  Real.exp ((Real.arctan (T / β) + k * Real.pi) / T)

/-- En ligne, ce sont les contacts de la Tour de ligne. -/
theorem windingContact_half (T : ℝ) (k : ℤ) : windingContact (1 / 2) T k = lineContact T k := rfl

theorem windingContact_pos (β T k : ℝ) : 0 < windingContact β T k := Real.exp_pos _

theorem phase_pos {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) : 0 < Real.arctan (T / β) :=
  Real.arctan_pos.mpr (div_pos hT hβ)

/-! ## 1. Emboîtement strict à indice fixé -/

/-- La phase croît moins vite que la hauteur : `T·(arctan(T'/β) − arctan(T/β)) < (T' − T)/2`. -/
theorem phase_increment_lt {β T T' : ℝ} (hβ : 0 < β) (hT : 0 < T) (hTT' : T < T') :
    T * (Real.arctan (T' / β) - Real.arctan (T / β)) < (T' - T) / 2 := by
  set a := T / β with ha
  set a' := T' / β with ha'
  have hapos : 0 < a := div_pos hT hβ
  have haa' : a < a' := div_lt_div_of_pos_right hTT' hβ
  set y := (a' - a) / (1 + a * a') with hy
  have hden : 0 < 1 + a * a' := by nlinarith
  have hypos : 0 < y := div_pos (by linarith) hden
  have hay : a * y < 1 := by
    rw [hy, mul_div_assoc', div_lt_one hden]; nlinarith
  have hsum : Real.arctan a + Real.arctan y = Real.arctan a' := by
    rw [Real.arctan_add hay]
    congr 1
    have h1 : 1 - a * y = (1 + a ^ 2) / (1 + a * a') := by
      rw [hy]; field_simp; ring
    have h2 : a + y = a' * (1 + a ^ 2) / (1 + a * a') := by
      rw [hy]; field_simp; ring
    have : (0 : ℝ) < 1 + a ^ 2 := by positivity
    rw [h1, h2, div_div_div_cancel_right₀ hden.ne', mul_div_assoc, div_self this.ne', mul_one]
  have hlt : Real.arctan y < y := by
    have h0 : 0 < Real.arctan y := Real.arctan_pos.mpr hypos
    have := Real.lt_tan h0 (Real.arctan_lt_pi_div_two y)
    rwa [Real.tan_arctan] at this
  have hdiff : Real.arctan a' - Real.arctan a < y := by linarith
  -- `T·y = (T' − T)·Tβ/(β² + TT') ≤ (T' − T)/2`
  have hTy : T * y ≤ (T' - T) / 2 := by
    have hyeq : y = (T' - T) * β / (β ^ 2 + T * T') := by
      rw [hy, ha, ha']; field_simp
    rw [hyeq]
    have hpos : 0 < β ^ 2 + T * T' := by nlinarith [sq_nonneg β, mul_pos hT (hT.trans hTT')]
    rw [← mul_div_assoc, div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [sq_nonneg (β - T), mul_pos hT (sub_pos.mpr hTT')]
  calc T * (Real.arctan a' - Real.arctan a) < T * y := mul_lt_mul_of_pos_left hdiff hT
    _ ≤ (T' - T) / 2 := hTy

/-- **Enroulement** : à indice `k ≥ 1` fixé, le contact décroît strictement avec la hauteur, pour toute
position radiale `β > 0`. -/
theorem windingContact_strictAnti_height {β T T' k : ℝ} (hβ : 0 < β) (hT : 0 < T) (hTT' : T < T')
    (hk : 1 ≤ k) : windingContact β T' k < windingContact β T k := by
  unfold windingContact
  apply Real.exp_lt_exp.mpr
  have hT' : 0 < T' := hT.trans hTT'
  rw [div_lt_div_iff₀ hT' hT]
  have hinc := phase_increment_lt hβ hT hTT'
  have hφ := phase_pos hβ hT
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have hd : 0 < T' - T := sub_pos.mpr hTT'
  nlinarith [mul_le_mul_of_nonneg_left hk (le_of_lt (mul_pos hd Real.pi_pos))]

/-- **Initiales emboîtées** : la cellule `(1, C_k]` d'un membre plus haut est contenue dans celle du plus
bas. -/
theorem windingSegment_nested {β T T' k q : ℝ} (hβ : 0 < β) (hT : 0 < T) (hTT' : T < T')
    (hk : 1 ≤ k) (hq : q ≤ windingContact β T' k) : q < windingContact β T k :=
  hq.trans_lt (windingContact_strictAnti_height hβ hT hTT' hk)

/-- **À même hauteur, aucun enroulement** : deux positions radiales donnent des contacts dans un rapport
unique, le même pour tout indice. -/
theorem windingContact_sameHeight (β β' T k : ℝ) :
    windingContact β' T k =
      windingContact β T k * Real.exp ((Real.arctan (T / β') - Real.arctan (T / β)) / T) := by
  unfold windingContact
  rw [← Real.exp_add]
  congr 1
  ring

/-! ## 2. Fenêtre de hauteur d'une cellule fixée -/

/-- **Fenêtre de hauteur** : un réel `q > 0` dans la cellule `k` de la Tour `(β, T)` vérifie
`kπ < T log q < (k + 1)π + π/2`. -/
theorem cell_height_window {β T k q : ℝ} (hβ : 0 < β) (hT : 0 < T) (hq : 0 < q)
    (hlo : windingContact β T k < q) (hhi : q ≤ windingContact β T (k + 1)) :
    k * Real.pi < T * Real.log q ∧ T * Real.log q < (k + 1) * Real.pi + Real.pi / 2 := by
  have hφ := phase_pos hβ hT
  have hφ' := Real.arctan_lt_pi_div_two (T / β)
  unfold windingContact at hlo hhi
  have hl := (Real.lt_log_iff_exp_lt hq).mpr hlo
  have hh : Real.log q ≤ (Real.arctan (T / β) + (k + 1) * Real.pi) / T := by
    rw [← Real.log_exp ((Real.arctan (T / β) + (k + 1) * Real.pi) / T)]
    exact Real.log_le_log hq hhi
  rw [div_lt_iff₀ hT] at hl
  rw [le_div_iff₀ hT] at hh
  constructor <;> nlinarith

/-- **Cellule fixée, vide au-delà d'une hauteur** : dès que `T log 2 ≥ (k + 1)π + π/2`, la cellule `k`
ne contient aucun réel `≥ 2`, pour toute position radiale. -/
theorem cell_empty_above_height {β T k q : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (hH : (k + 1) * Real.pi + Real.pi / 2 ≤ T * Real.log 2) (hq : 2 ≤ q) :
    ¬ (windingContact β T k < q ∧ q ≤ windingContact β T (k + 1)) := by
  rintro ⟨hlo, hhi⟩
  have hw := (cell_height_window hβ hT (by linarith) hlo hhi).2
  have : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq
  nlinarith

/-! ## 3. Enfoncement de chaque premier -/

/-- **Tout réel traverse tout indice fixé** : dès que `T log q ≥ kπ + π/2`, `q` est au-dessus du
contact `k`. -/
theorem contact_below_of_height {β T k q : ℝ} (hT : 0 < T) (hq : 0 < q)
    (hH : k * Real.pi + Real.pi / 2 ≤ T * Real.log q) : windingContact β T k < q := by
  unfold windingContact
  rw [← Real.lt_log_iff_exp_lt hq, div_lt_iff₀ hT]
  have := Real.arctan_lt_pi_div_two (T / β)
  linarith

/-- **Le contact `k` d'une Tour lu dans une autre** : position `(T·(φ' + kπ)/T' − φ)/π` ; en
particulier l'indice se contracte du facteur `T/T'`. -/
theorem windingContact_position (β T β' T' k : ℝ) :
    pointedPosition β T (windingContact β' T' k) =
      (T * ((Real.arctan (T' / β') + k * Real.pi) / T') - Real.arctan (T / β)) / Real.pi := by
  unfold pointedPosition windingContact
  rw [Real.log_exp]

#print axioms windingContact_half
#print axioms phase_increment_lt
#print axioms windingContact_strictAnti_height
#print axioms windingSegment_nested
#print axioms windingContact_sameHeight
#print axioms cell_height_window
#print axioms cell_empty_above_height
#print axioms contact_below_of_height
#print axioms windingContact_position

end RHV6Fresh
