/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FirstZeroDominance
import RHV6Fresh.Terminal.FirstTowerHorizon
import RHV6Fresh.Terminal.LocalRaccordCaptivity
import RHV6Fresh.Terminal.WholeWindingObligation
import RHV6Fresh.Terminal.FirstGainPremise
import RHV6Fresh.Terminal.EventHeightProgression
import RHV6Fresh.Direct.PairTowers

/-!
# Captivités et dominations compilées SANS supposer l'arrivée ON

Correction de l'auteur (2026-10-10), avant toute nouvelle tentative : il existe des captivités et des dominations
compilées sans supposer l'arrivée ON ; elles sont conservées et composées dans leur portée exacte.

| Build historique | Résultat exact | Ici |
|---|---|---|
| 43d5fbfd `RegimeCapture` (retiré en fb8b2508, ménage) | captivité par le premier partagé, encadrement du premier attendu par les contacts de la cellule | `regime_captive_of_prime` (restauré, partie inconditionnelle seulement ; les `def P…` de ce fichier ne sont pas restaurées) |
| e586d8dd `LocalRaccordCaptivity` | captivité énergétique au raccord premier, passage qui monte, hauteur `≥ 2` | `height_advance_local_budget` |
| 9aecca85 `FirstTowerHorizon` | domination par le premier zéro ON, toute position radiale, jusqu'à un horizon borné | `tower_inside_below_horizon`, `tower_inside_of_height` |
| même commit | un membre ou son miroir dans le champ sur tout l'horizon, sous condition de hauteur | `mirror_pair_has_prisoner`, `lower_member_prisoner` |
| 70c35dc0 `WholeWindingObligation` | enroulement des contacts à l'infini sur tout passage | `acquired_winding_all_passages` |
| 0cb8cd68 `FirstGainPremise` | domination individuelle sous gain collectif et contrôle d'interaction explicites | `norm_le_first_of_interaction` |

Composition (`captivity_without_on_arrival`) : sur un passage qui monte depuis un zéro ON, sous l'ancre, l'arrivée `l`
(rien supposé sur sa position radiale) est captive par le premier partagé, captive en énergie au raccord dès la hauteur 2,
dominée par le premier zéro jusqu'à l'horizon `√x·‖ρ₁‖ ≤ ‖ρ_l‖`, emboîtée à l'infini, et DANS LE CHAMP DU PREMIER ZÉRO
SUR TOUT `x ≥ 1` dès que son support atteint celui du premier (`β_l ≤ 1/2` est acquis sur un pas qui monte). Portée :
`InsideField` est sur `x ≥ 1` ; l'étage complet `DominanceStage` (axe entier, symétrie) reste équivalent à ON.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune `def P…`.
-/

namespace RHV6Fresh
open RHV3Lean

/-- **Captivité par le premier partagé, sans supposition ON** (restauration de 43d5fbfd, `RegimeCapture`, RC2) : le
successeur pointe sur le minimum attendu du précédent, et la cellule de sa propre Tour contient son propre minimum attendu. -/
theorem regime_captive_of_prime (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
      (firstTowerOf ⟨p.zLaterMember, hL⟩).entryContact <
          (expectedMinimumPrime ⟨p.zLaterMember, hL⟩ : ℝ) ∧
      (expectedMinimumPrime ⟨p.zLaterMember, hL⟩ : ℝ) ≤
          (firstTowerOf ⟨p.zLaterMember, hL⟩).lastRayContact :=
  ⟨(passage_event_increment p hE hL).2.1, firstTower_cell_contains_expected ⟨p.zLaterMember, hL⟩⟩

/-- Sous l'ancre, le support du premier est `√(1/4 + T₁²)`. -/
theorem firstZero_support_sq (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    ‖zeroPoint (canonicalZero 1)‖ ^ 2 = 1 / 4 + rZeroHeight (canonicalZero 1).1 ^ 2 := by
  rw [zeroPoint_norm_sq, h₁]; ring

/-- **Support atteint par la hauteur seule** : `T₁² + 1/4 ≤ T_w²` ⟹ `‖ρ₁‖ ≤ ‖ρ_w‖`, toute position radiale. -/
theorem support_ge_first_of_height (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) (w : TrueZero)
    (hT : rZeroHeight (canonicalZero 1).1 ^ 2 + 1 / 4 ≤ rZeroHeight w.1 ^ 2) :
    ‖zeroPoint (canonicalZero 1)‖ ≤ ‖zeroPoint w‖ := by
  have h1 := firstZero_support_sq h₁
  have h2 := zeroPoint_norm_sq w
  have hsq : ‖zeroPoint (canonicalZero 1)‖ ^ 2 ≤ ‖zeroPoint w‖ ^ 2 := by
    nlinarith [sq_nonneg (rZeroRadialPosition w.1)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- **Captivité du membre atteint dans le champ du premier, sans supposer l'arrivée ON** : sur un pas qui monte, `β_l ≤ 1/2`
est acquis (`passage_entry_radial_le_half`) ; sous l'ancre, dès que le support de `l` atteint celui du premier, `l` est dans
le champ du premier sur tout `x ≥ 1` (`lower_member_prisoner`). -/
theorem arrival_insideField_of_support (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (p : TZeroPassage) (hL : 0 < rZeroHeight p.zLaterMember) (hV : VerticalPassage p)
    (hρ : ‖zeroPoint (canonicalZero 1)‖ ≤ ‖zeroPoint ⟨p.zLaterMember, hL⟩‖) :
    InsideField (canonicalZero 1) ⟨p.zLaterMember, hL⟩ :=
  lower_member_prisoner h₁ (passage_entry_radial_le_half p hV) hρ

/-- **Composition, dans leur portée exacte, des captivités et dominations acquises sans supposer l'arrivée ON**, sur un
passage `p : e → l` qui monte depuis un zéro, sous l'ancre :
1. premier partagé et cellule (43d5fbfd) ;
2. captivité énergétique au raccord dès la hauteur 2 (e586d8dd) ;
3. domination par le premier jusqu'à l'horizon `√x·‖ρ₁‖ ≤ ‖ρ_l‖`, toute position radiale (9aecca85) ;
4. `l` ou son miroir dans le champ dès `‖ρ₁‖ ≤ T_l` (9aecca85) ;
5. `l` dans le champ sur tout `x ≥ 1` dès `‖ρ₁‖ ≤ ‖ρ_l‖`, et dès `T₁² + 1/4 ≤ T_l²` (composé) ;
6. emboîtement des contacts à l'infini (70c35dc0). -/
theorem captivity_without_on_arrival (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hV : VerticalPassage p) :
    (occurrence ⟨p.zLaterMember, hL⟩ = expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ ∧
      (firstTowerOf ⟨p.zLaterMember, hL⟩).entryContact <
          (expectedMinimumPrime ⟨p.zLaterMember, hL⟩ : ℝ) ∧
      (expectedMinimumPrime ⟨p.zLaterMember, hL⟩ : ℝ) ≤
          (firstTowerOf ⟨p.zLaterMember, hL⟩).lastRayContact) ∧
    (2 ≤ rZeroHeight p.zLaterMember → LocalCaptivity p hE hL) ∧
    (∀ x : ℝ, 1 ≤ x → Real.sqrt x * ‖zeroPoint (canonicalZero 1)‖ ≤ ‖zeroPoint ⟨p.zLaterMember, hL⟩‖ →
      ‖zeroTerm ⟨p.zLaterMember, hL⟩ x‖ ≤ firstField (canonicalZero 1) x) ∧
    (‖zeroPoint (canonicalZero 1)‖ ≤ rZeroHeight p.zLaterMember →
      InsideField (canonicalZero 1) ⟨p.zLaterMember, hL⟩ ∨
        InsideField (canonicalZero 1) (mirrorMember ⟨p.zLaterMember, hL⟩)) ∧
    (‖zeroPoint (canonicalZero 1)‖ ≤ ‖zeroPoint ⟨p.zLaterMember, hL⟩‖ →
      InsideField (canonicalZero 1) ⟨p.zLaterMember, hL⟩) ∧
    (rZeroHeight (canonicalZero 1).1 ^ 2 + 1 / 4 ≤ rZeroHeight p.zLaterMember ^ 2 →
      InsideField (canonicalZero 1) ⟨p.zLaterMember, hL⟩) ∧
    WindingNestedAtInfinity ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ :=
  ⟨regime_captive_of_prime p hE hL,
    fun h2 => ((height_advance_local_budget p hE hL hV).2 h2).2,
    fun _ hx hH => tower_inside_below_horizon h₁ hx hH,
    fun hH => mirror_pair_has_prisoner h₁ hH,
    fun hρ => arrival_insideField_of_support h₁ p hL hV hρ,
    fun hT => arrival_insideField_of_support h₁ p hL hV
      (support_ge_first_of_height h₁ ⟨p.zLaterMember, hL⟩ hT),
    acquired_winding_all_passages p hE hL⟩

#print axioms regime_captive_of_prime
#print axioms support_ge_first_of_height
#print axioms arrival_insideField_of_support
#print axioms captivity_without_on_arrival

end RHV6Fresh
