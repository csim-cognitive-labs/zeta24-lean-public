/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.LocalPrimeGapSynchronization
import RHV6Fresh.Terminal.StageCell

/-!
# RHV6Fresh — audit contradictoire de la synchronisation locale et de sa queue (E301, 2026-10-14)

Objet : décider, par des énoncés compilés, si la synchronisation locale (C126) et le théorème de queue constituent une
contrainte INDÉPENDANTE sur le prochain zéro, et chercher une borne analytique de la queue uniforme en l'écart,
indépendante du zéro testé, sans RH. Aucune définition existante n'est modifiée ; la chaîne et le but `:399` non plus.

1. **Forme de la synchronisation, pour toute famille** (`gap_synchronization_any_family`) : pour TOUTE famille de points
   `r_i` et de poids `c_i` (sommabilité aux deux bornes), l'incrément de `F(x) = Σ c_i x^{r_i}` entre deux bornes est la
   somme des incréments individuels. La synchronisation par écart est donc la linéarité de la somme ; ce qui est propre
   à ζ dans `localSynchronization` est la seule formule explicite lissée (`smoothedRemainder_eq_tsum_residueTerm`), qui
   identifie `F` au reste des premiers. Elle est satisfaite par la famille authentique quelle que soit sa position radiale
   (`localSynchronization_from_explicit_formula`).
2. **La queue n'est pas une contrainte** (`residual_eq_tail_any_family`, `localResidual_eq_tail_of_sync`) : pour toute
   famille sommable, cible − somme finie = somme du complément ; `localResidual_eq_tail` découle de
   `localSynchronization` et de ce seul fait.
3. **Borne analytique de la queue sur un écart** (`localHeightResidual`, `localHeightResidual_eq_tail_increment`,
   `localHeightResidual_bound`) : après retrait de tous les zéros de hauteur `≤ H`, le résidu sur l'écart `[p_n, p_{n+1}]`
   est l'incrément de la queue au-dessus de `H`, et `‖résidu‖ ≤ budget(H)·(p_n + p_{n+1})` : constante indépendante de
   l'écart, de la position radiale de tout zéro, démontrée sans RH (par `Re ρ ≤ 1` seulement).
4. **Cette borne n'est pas discriminante** (`tail_bound_any_family`, `tail_bound_admits_offline_point`) : la même borne,
   d'exposant `1`, vaut pour toute famille de points de partie réelle `≤ 1` ; un point de partie réelle `1/4` la
   satisfait. Une borne d'exposant `θ < 1` uniforme en l'écart serait une bande sans zéro (déjà compilé :
   `prime_blocks_iff_zero_free`, `RemovalExponent`), de nature RH.
-/

namespace RHV6Fresh

open RHV3Lean Complex

/-! ## 1. La synchronisation par écart est la linéarité de la somme, pour toute famille -/

/-- **Synchronisation par écart pour TOUTE famille** : l'incrément de `Σ c_i x^{r_i}` est la somme des incréments. -/
theorem gap_synchronization_any_family {ι : Type*} (c r : ι → ℂ) (a b : ℝ)
    (ha : Summable fun i => c i * (a : ℂ) ^ (r i)) (hb : Summable fun i => c i * (b : ℂ) ^ (r i)) :
    (∑' i, c i * (b : ℂ) ^ (r i)) - (∑' i, c i * (a : ℂ) ^ (r i)) =
      ∑' i, c i * ((b : ℂ) ^ (r i) - (a : ℂ) ^ (r i)) := by
  rw [← hb.tsum_sub ha]
  exact tsum_congr fun i => by ring

/-- **Seule entrée propre à ζ** : la synchronisation locale est l'instance, pour la famille authentique et la cible
arithmétique, de la formule explicite lissée appliquée aux deux bornes de l'écart. Aucune position radiale n'y figure. -/
theorem localSynchronization_from_explicit_formula (I : PrimeGapInterval) :
    localArithmeticTarget I =
      (∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm I.upper ρ) -
        ∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm I.lower ρ := by
  unfold localArithmeticTarget
  rw [smoothedRemainder_eq_tsum_residueTerm I.one_lt_upper, smoothedRemainder_eq_tsum_residueTerm I.one_lt_lower]

/-! ## 2. Le théorème de queue n'ajoute rien à la synchronisation -/

/-- **Pour toute famille sommable**, cible − somme finie = somme sur le complément. -/
theorem residual_eq_tail_any_family {ι : Type*} (f : ι → ℂ) (hf : Summable f) (s : Finset ι) :
    (∑' i, f i) - ∑ i ∈ s, f i = ∑' i : ((s : Set ι)ᶜ : Set ι), f i := by
  rw [← hf.sum_add_tsum_compl (s := s)]
  ring

/-- `localResidual_eq_tail` redémontré depuis `localSynchronization` et le seul fait générique : la queue n'est pas une
contrainte supplémentaire. -/
theorem localResidual_eq_tail_of_sync (s : Finset ExplicitIndex) (I : PrimeGapInterval) :
    localReconstructionResidual s I =
      ∑' ρ : ((s : Set ExplicitIndex)ᶜ : Set ExplicitIndex), smoothedLocalContribution ρ.1 I := by
  unfold localReconstructionResidual
  rw [localSynchronization I]
  exact residual_eq_tail_any_family _ (smoothedLocalContribution_summable I) s

/-! ## 3. Borne analytique de la queue sur un écart premier, uniforme en l'écart, sans RH -/

/-- Résidu de l'écart `I` après retrait de TOUS les zéros de hauteur `≤ H` (coupure de hauteur). -/
noncomputable def localHeightResidual (H : ℝ) (I : PrimeGapInterval) : ℂ :=
  localArithmeticTarget I - (precedingSum H I.upper - precedingSum H I.lower)

/-- Le résidu à coupure de hauteur est l'incrément, sur l'écart, de la queue de tous les zéros au-dessus de `H`. -/
theorem localHeightResidual_eq_tail_increment (H : ℝ) (I : PrimeGapInterval) :
    localHeightResidual H I = followingSum H I.upper - followingSum H I.lower := by
  unfold localHeightResidual localArithmeticTarget
  rw [remainder_eq_preceding_add_following H I.one_lt_upper, remainder_eq_preceding_add_following H I.one_lt_lower]
  ring

/-- **Borne de la queue sur un écart** : `‖résidu_H(I)‖ ≤ budget(H)·(p_n + p_{n+1})`. Constante indépendante de l'écart et
de la position radiale de tout zéro ; démontrée sans RH (`Re ρ ≤ 1`). Exposant `1`. -/
theorem localHeightResidual_bound (H : ℝ) (I : PrimeGapInterval) :
    ‖localHeightResidual H I‖ ≤ followingBudget H * (I.lower + I.upper) := by
  rw [localHeightResidual_eq_tail_increment]
  exact tail_window_increment_bound H I.one_lt_lower I.one_lt_upper

/-! ## 4. La borne n'est pas discriminante : elle vaut pour toute famille de partie réelle `≤ 1` -/

/-- **Même borne pour TOUTE famille** de points de partie réelle `≤ 1` et de poids absolument sommables. -/
theorem tail_bound_any_family {ι : Type*} (c r : ι → ℂ) (hc : Summable fun i => ‖c i‖)
    (hr : ∀ i, (r i).re ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖∑' i, c i * (x : ℂ) ^ (r i)‖ ≤ (∑' i, ‖c i‖) * x := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hterm : ∀ i, ‖c i * (x : ℂ) ^ (r i)‖ ≤ ‖c i‖ * x := by
    intro i
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc x ^ (r i).re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (hr i)
      _ = x := Real.rpow_one x
  have hdom : Summable fun i => ‖c i‖ * x := hc.mul_right _
  have hs : Summable fun i => ‖c i * (x : ℂ) ^ (r i)‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hdom
  calc ‖∑' i, c i * (x : ℂ) ^ (r i)‖ ≤ ∑' i, ‖c i * (x : ℂ) ^ (r i)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' i, ‖c i‖ * x := Summable.tsum_le_tsum hterm hs hdom
    _ = (∑' i, ‖c i‖) * x := tsum_mul_right

/-- **Contre-modèle de discrimination** : un point unique de partie réelle `1/4`, de hauteur et de poids quelconques,
satisfait la borne d'exposant `1` ; aucune borne de cette forme n'exclut une arrivée basse. -/
theorem tail_bound_admits_offline_point (T : ℝ) (w : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖w * (x : ℂ) ^ ((1 / 4 : ℂ) + T * I)‖ ≤ ‖w‖ * x := by
  have h := tail_bound_any_family (ι := Unit) (fun _ => w) (fun _ => (1 / 4 : ℂ) + T * I)
    Summable.of_finite
    (fun _ => by simp; norm_num) hx
  simpa using h

#print axioms gap_synchronization_any_family
#print axioms localSynchronization_from_explicit_formula
#print axioms residual_eq_tail_any_family
#print axioms localResidual_eq_tail_of_sync
#print axioms localHeightResidual_eq_tail_increment
#print axioms localHeightResidual_bound
#print axioms tail_bound_any_family
#print axioms tail_bound_admits_offline_point

end RHV6Fresh
