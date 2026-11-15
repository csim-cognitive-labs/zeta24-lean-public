/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ArrivalFiberHypotheses
import RHV6Fresh.Terminal.SynchronizationMatrix

/-!
# Le zéro suivant sous un demi : ce qu'il impose à sa fréquence et à son amplitude, après des zéros ON prouvés par comptage
(auteur, 2026-10-16)

Demande de l'auteur : « prouver la relation entre β < 1/2 pour le prochain zéro et ce que cela implique, après deux zéros ON
(prouvés par comptage), à propos de la fréquence potentielle de ce zéro et de son amplitude ; nous ne cherchons peut-être même
pas au bon endroit pour exclure β < 1/2 ».

Tout est démontré pour toute profondeur `d = 1/2 − β > 0`, sans fabriquer de zéro : chaque énoncé suppose un vrai zéro bas
et en tire ce qu'il impose.

1. **Fréquence : signature de comptage, discrète** (`low_arrival_count_jump`, `low_member_deficit_ge_two`,
   `low_after_on_band`) : un zéro bas de hauteur `T` partage sa fréquence avec son miroir ; la fréquence `T` porte donc deux
   signaux, le comptage saute d'au moins deux à cette seule hauteur (`N(T_l) ≥ N(T_e) + 2` sur le passage qui y arrive), le
   déficit `N − N₀` y vaut au moins deux. Après une bande ON certifiée `N(c) = k`, `W(c) = 0`, un zéro bas est au-dessus de `c`
   et `N(T) ≥ k + 2`. Ces sauts ne dépendent pas de `d` : ils valent deux pour `d = 10⁻¹⁰⁰` comme pour `d = 0,4`.
2. **Amplitude : signature propre le long des premiers, continue et nulle à la limite** (`own_amplitude_drift_le`,
   `own_amplitude_signature_vanishes`, `escape_horizon_unbounded`) : la dérive de l'amplitude du zéro lui-même entre deux
   abscisses de `[1, X]` est au plus `(1/2 − β)·log X` ; sur toute fenêtre finie elle passe sous tout `ε` dès que la profondeur
   est assez petite ; l'horizon où le miroir dépasse une Tour ON PLUS BASSE (autre fréquence), `r^{1/d}` avec `r > 1`, dépasse
   toute borne quand `d → 0`. Aucune comparaison avec un zéro ON de même fréquence (interdit, auteur, 2026-10-16).
3. **Où chercher** (`two_signatures`) : les deux ensemble. La signature de comptage d'un zéro bas est lisible à la hauteur
   finie `T` du zéro, d'une taille fixe, quelle que soit la profondeur ; la signature d'amplitude ne l'est qu'au-delà d'un
   horizon de premiers non borné. Une exclusion de `β < 1/2` qui ne dépend pas de `d` ne peut donc pas venir d'une
   comparaison d'amplitudes sur une fenêtre finie de premiers ; elle porte sur le comptage à la hauteur du zéro (deux unités
   à une seule fréquence, sans annulation correspondante de la fonction réelle sur la ligne).

Portée : identités et caractérisations ; aucune n'exclut un zéro bas. « Le déficit reste nul à toute hauteur » est déjà compilé
⟺ RH (`lineDefect_invariant_iff_riemannHypothesis`) ; ce module dit où la signature d'un zéro bas est finie, pas qu'elle est
absente.
-/

namespace RHV6Fresh

open RHV3Lean Filter Topology

/-! ## 1. Fréquence : la signature de comptage d'un zéro bas -/

/-- **Saut de comptage à l'arrivée basse** : sur un passage qui monte vers un zéro bas, le comptage gagne au moins deux à
la seule hauteur d'arrivée (le zéro et son miroir partagent la fréquence). Toute profondeur. -/
theorem low_arrival_count_jump (p : TZeroPassage) (hV : VerticalPassage p) (hL : 0 < rZeroHeight p.zLaterMember)
    (hβ : rZeroRadialPosition p.zLaterMember < 1 / 2) :
    upperCountWithMultiplicity (rZeroHeight p.zEarlierMember) + 2 ≤
      upperCountWithMultiplicity (rZeroHeight p.zLaterMember) := by
  have h1 := passage_count_step_eq_fiber p hV
  have h2 := two_le_fiberCount_of_low ⟨p.zLaterMember, hL⟩ hβ
  simp only at h2
  omega

/-- **Déficit à la hauteur d'un zéro bas** : `N(T) − N₀(T) ≥ 2`, quelle que soit la profondeur. -/
theorem low_member_deficit_ge_two (w : TrueZero) (hβ : rZeroRadialPosition w.1 < 1 / 2) :
    2 ≤ zeroCountDeficit (rZeroHeight w.1) := by
  rw [zeroCountDeficit_eq]
  have := one_le_lowCount_of_low w le_rfl hβ
  omega

/-- **Après une bande ON certifiée** : si `N(c) = k` et aucun membre bas jusqu'à `c` (`W(c) = 0`, ce que donnent les comptages
certifiés), un zéro bas est au-dessus de `c` et, à sa hauteur, `N ≥ k + 2` : sa fréquence est la première où le comptage gagne
deux unités que les zéros ON ne portent pas. -/
theorem low_after_on_band {c : ℝ} {k : ℕ} (hN : upperCountWithMultiplicity c = k) (hW : lowCount c = 0)
    (w : TrueZero) (hβ : rZeroRadialPosition w.1 < 1 / 2) :
    c < rZeroHeight w.1 ∧ k + 2 ≤ upperCountWithMultiplicity (rZeroHeight w.1) ∧
      2 ≤ zeroCountDeficit (rZeroHeight w.1) := by
  have hc : c < rZeroHeight w.1 := by
    by_contra hle
    exact (lowCount_eq_zero_iff c).mp hW w (not_lt.mp hle) hβ
  refine ⟨hc, ?_, low_member_deficit_ge_two w hβ⟩
  have h1 := upperCount_eq_on_add_two_low c
  have h2 := upperCount_eq_on_add_two_low (rZeroHeight w.1)
  have h3 := onCount_mono hc.le
  have h4 := one_le_lowCount_of_low w le_rfl hβ
  omega

/-! ## 2. Amplitude : la signature propre le long des premiers disparaît avec la profondeur

Aucune référence à un zéro ON de même fréquence (interdit, auteur 2026-10-16) : seule la dérive de l'amplitude du zéro lui-même,
à l'échelle de la ligne, entre deux abscisses de premiers. -/

/-- **Dérive propre sur une fenêtre finie** : pour `x, y ∈ [1, X]`, `|log(A_w(y)/A_w(x))| ≤ |β − 1/2|·log X`. -/
theorem own_amplitude_drift_le (w : TrueZero) {X x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hxX : x ≤ X) (hyX : y ≤ X) :
    |Real.log (pairAmplitude w y / pairAmplitude w x)| ≤ |rZeroRadialPosition w.1 - 1 / 2| * Real.log X := by
  rw [block_readjustment_log w (by linarith) (by linarith), abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have h1 := Real.log_nonneg hx
  have h2 := Real.log_nonneg hy
  have h3 := Real.log_le_log (by linarith) hxX
  have h4 := Real.log_le_log (by linarith) hyX
  rw [abs_le]; constructor <;> linarith

/-- **Sur toute fenêtre finie de premiers, la dérive propre d'amplitude passe sous toute tolérance dès que la profondeur est
assez petite** : la signature d'amplitude est continue et nulle en `β = 1/2`. -/
theorem own_amplitude_signature_vanishes {X : ℝ} (hX : 1 ≤ X) {ε : ℝ} (hε : 0 < ε) :
    ∃ d₀ > 0, ∀ w : TrueZero, |rZeroRadialPosition w.1 - 1 / 2| < d₀ →
      ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → x ≤ X → y ≤ X → |Real.log (pairAmplitude w y / pairAmplitude w x)| < ε := by
  have hL := Real.log_nonneg hX
  refine ⟨ε / (Real.log X + 1), div_pos hε (by linarith), fun w hw x y hx hy hxX hyX => ?_⟩
  have hb := own_amplitude_drift_le w hx hy hxX hyX
  have hk : |rZeroRadialPosition w.1 - 1 / 2| * Real.log X < ε := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < Real.log X + 1)).mp hw
    nlinarith [abs_nonneg (rZeroRadialPosition w.1 - 1 / 2)]
  linarith

/-- **L'horizon d'évasion n'est pas borné** : pour `r > 1` (rapport des modules du miroir et d'une Tour ON plus basse),
l'horizon `r^{1/d}` au-delà duquel le miroir la dépasse est plus grand que toute borne `H` dès que `d` est assez petit. -/
theorem escape_horizon_unbounded {r : ℝ} (hr : 1 < r) (H : ℝ) :
    ∃ d₀ > 0, ∀ d : ℝ, 0 < d → d < d₀ → H < r ^ (1 / d) := by
  have hlog : 0 < Real.log r := Real.log_pos hr
  set L := max (Real.log (max H 1)) 1 with hL
  have hLpos : 0 < L := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨Real.log r / L, div_pos hlog hLpos, fun d hd hdd => ?_⟩
  have hr0 : 0 < r := by linarith
  rw [Real.rpow_def_of_pos hr0]
  have hkey : L < Real.log r * (1 / d) := by
    rw [mul_one_div, lt_div_iff₀ hd]
    have := (lt_div_iff₀ hLpos).mp hdd
    linarith [mul_comm d L]
  have hH : H ≤ max H 1 := le_max_left _ _
  have h1 : 0 < max H 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  calc H ≤ max H 1 := hH
    _ = Real.exp (Real.log (max H 1)) := (Real.exp_log h1).symm
    _ ≤ Real.exp L := Real.exp_le_exp.mpr (le_max_left _ _)
    _ < Real.exp (Real.log r * (1 / d)) := Real.exp_lt_exp.mpr hkey

/-! ## 3. Les deux signatures ensemble -/

/-- **Les deux signatures d'un zéro bas** : à sa hauteur, le comptage gagne deux unités non portées par des zéros ON
(déficit `≥ 2`, fibre `≥ 2`), pour toute profondeur ; tandis que, sur toute fenêtre finie de premiers et pour toute tolérance,
il existe une profondeur sous laquelle la dérive propre de son amplitude est sous la tolérance. -/
theorem two_signatures (w : TrueZero) (hβ : rZeroRadialPosition w.1 < 1 / 2) {X : ℝ} (hX : 1 ≤ X) {ε : ℝ}
    (hε : 0 < ε) :
    2 ≤ zeroCountDeficit (rZeroHeight w.1) ∧ 2 ≤ fiberCountWithMultiplicity (rZeroHeight w.1) ∧
      ∃ d₀ > 0, ∀ v : TrueZero, |rZeroRadialPosition v.1 - 1 / 2| < d₀ →
        ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → x ≤ X → y ≤ X → |Real.log (pairAmplitude v y / pairAmplitude v x)| < ε :=
  ⟨low_member_deficit_ge_two w hβ, two_le_fiberCount_of_low w hβ, own_amplitude_signature_vanishes hX hε⟩

end RHV6Fresh
