/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CaptivityWithoutOn
import RHV6Fresh.Terminal.MirrorGroupNonCompensation
import RHV6Fresh.Terminal.AmplitudeStableSynchronization
import RHV6Fresh.Terminal.GrammaticalRaccordJump
import RHV6Fresh.Terminal.OnRegimeInduction
import RHV6Fresh.Terminal.CountingDeficit
import RHV6Fresh.Terminal.RemainderRepresentation
import RHV6Fresh.Terminal.RayCapture

/-!
# Audit des trois forces de la contradiction « amplification miroir OFF » (auteur, 2026-10-19)

Texte collé : « régime ON du premier zéro + contraintes exactes des premiers + largeurs et fréquences des contacts
⟹ impossibilité de l'amplification miroir OFF » ; trois résultats de force différente à distinguer : une amplification OFF,
une incompatibilité individuelle, une impossibilité collective de compensation.

Ce module classe chacune des trois forces par ce que le compilateur établit, SANS zéro fabriqué et SANS prendre la fréquence
d'un zéro ON comme référence : la seule comparaison à même hauteur est celle du membre bas authentique `l` avec son propre
miroir `l*` (deux vrais zéros de la paire).

1. **Amplification OFF** (certificat, compilé) : `A_{l*}(x)/A_l(x) = x^{1 − 2β_l}·‖ρ_l‖/‖ρ_{l*}‖`, le miroir dépasse le champ
   du premier zéro au-delà de son horizon exact `(‖ρ_{l*}‖/‖ρ₁‖)^{1/(1/2 − β_l)}` ; les deux membres sont présents ensemble.
2. **Incompatibilité individuelle** : le membre bas est dans le champ (support) ; son miroir dans le champ ⟺ `β_l = 1/2`.
   Les obligations de contact (largeur, fréquence, facteur) sont satisfaites par toute `β ∈ ]0, 1/2]` : l'incompatibilité
   individuelle n'est pas dérivée des contacts, elle est une CARACTÉRISATION du but.
3. **Impossibilité collective** : la non-compensation par un groupe fini est compilée ; la reconstruction exacte admet la
   famille authentique pour toute position radiale ; l'impossibilité avec le complément infini ⟺ borne du reste d'exposant
   `< 1 − β_l` (bande sans zéro contenant le miroir), acquise à l'exposant `1` seulement.

Composition : les trois ingrédients du texte tiennent ensemble pour toute `β_l ∈ ]0, 1/2]` ; « aucun zéro ne dépasse le champ
du premier » ⟺ RH. La contrainte universelle manquante n'est pas dans leur composition.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Amplification OFF : certificat compilé sur la paire authentique -/

/-- **Rapport des enveloppes du miroir et du membre bas, même hauteur** : `A_{l*}(x)/A_l(x) = x^{1 − 2β_l}·‖ρ_l‖/‖ρ_{l*}‖`.
Pour `β_l < 1/2` l'exposant `1 − 2β_l` est strictement positif : la croissance du miroir est strictement plus forte que celle
du membre bas, dans le domaine des premiers. Fonction de `(β_l, T_l)` seuls : vraie dans tout monde. -/
theorem mirror_over_low_amplitude_ratio (l : TrueZero) {x : ℝ} (hx : 0 < x) :
    pairAmplitude (mirrorMember l) x / pairAmplitude l x =
      x ^ (1 - 2 * rZeroRadialPosition l.1) * (‖zeroPoint l‖ / ‖zeroPoint (mirrorMember l)‖) := by
  rw [pairAmplitude_ratio l (mirrorMember l) hx, mirrorMember_radial]
  ring_nf

/-- L'exposant de croissance relative du miroir est strictement positif sous un demi. -/
theorem mirror_relative_exponent_pos (l : TrueZero) (hβ : rZeroRadialPosition l.1 < 1 / 2) :
    0 < 1 - 2 * rZeroRadialPosition l.1 := by linarith

/-- **Les deux membres sont présents ensemble** : le miroir est un vrai zéro distinct, de même hauteur, au-dessus d'un demi. -/
theorem mirror_pair_both_present (l : TrueZero) (hβ : rZeroRadialPosition l.1 < 1 / 2) :
    mirrorMember l ≠ l ∧ rZeroHeight (mirrorMember l).1 = rZeroHeight l.1 ∧
      rZeroRadialPosition (mirrorMember l).1 = 1 / 2 + (1 / 2 - rZeroRadialPosition l.1) :=
  ⟨mirrorMember_ne hβ, mirrorMember_ordinate l, by rw [mirrorMember_radial]; ring⟩

/-- **Amplification OFF contre le champ du premier zéro** (sous l'ancre) : au-delà de l'horizon exact
`(‖ρ_{l*}‖/‖ρ₁‖)^{1/(1/2 − β_l)}`, l'amplitude du miroir dépasse strictement le champ du premier. C'est le certificat
d'amplification ; il est individuel et fonction de `(β_l, T_l)`. -/
theorem off_amplification_certificate {z₁ l : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hβ : rZeroRadialPosition l.1 < 1 / 2) {x : ℝ} (hx : 0 < x)
    (hfar : (‖zeroPoint (mirrorMember l)‖ / ‖zeroPoint z₁‖) ^ (1 / (1 / 2 - rZeroRadialPosition l.1)) < x) :
    firstField z₁ x < ‖zeroTerm (mirrorMember l) x‖ := by
  have hδ : 0 < 1 / 2 - rZeroRadialPosition l.1 := by linarith
  have hw : rZeroRadialPosition (mirrorMember l).1 = 1 / 2 + (1 / 2 - rZeroRadialPosition l.1) :=
    (mirror_pair_both_present l hβ).2.2
  have := (upper_member_exact_horizon h₁ hδ hw hx).not.mpr (not_le.mpr hfar)
  exact not_le.mp this

/-! ## 2. Incompatibilité individuelle : caractérisation du but -/

/-- **Le membre bas est captif du champ du premier** sur `x ≥ 1` dès que son support atteint celui du premier (géométrie
seule, aucune hypothèse sur sa partie réelle au-delà de `β_l ≤ 1/2`). -/
theorem low_member_captive {z₁ l : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) (hρ : ‖zeroPoint z₁‖ ≤ ‖zeroPoint l‖) : InsideField z₁ l :=
  lower_member_prisoner h₁ hβ hρ

/-- **Incompatibilité individuelle du miroir avec le champ du premier ⟺ membre en ligne.** Sous `β_l ≤ 1/2` et le support :
le miroir est dans le champ ⟺ `β_l = 1/2`. L'incompatibilité individuelle (« le miroir ne peut pas dépasser le champ »)
n'est donc pas un fait intermédiaire : elle est le but lui-même. -/
theorem mirror_insideField_iff_onLine {z₁ l : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) (hρ : ‖zeroPoint z₁‖ ≤ ‖zeroPoint l‖) :
    InsideField z₁ (mirrorMember l) ↔ rZeroRadialPosition l.1 = 1 / 2 := by
  constructor
  · intro hm
    exact inside_field_forces_line h₁ (low_member_captive h₁ hβ hρ) hm
  · intro hOn
    rw [(mirrorMember_eq_self_iff l).mpr hOn]
    exact low_member_captive h₁ hβ hρ

/-- **Les largeurs et fréquences des contacts n'imposent pas l'incompatibilité** : pour toute `β ∈ ]0, 1/2]`, fenêtre du
facteur et factorisation des contacts sont satisfaites (rappel de `grammar_contacts_admit_any_radial`). -/
theorem contact_constraints_admit_low {β T : ℝ} (hT : 0 < T) (hβ : 0 < β) (hβ2 : β ≤ 1 / 2) :
    1 ≤ paramFactor β T ∧ paramFactor β T < Real.exp (1 / (2 * T) / T) ∧
      ∀ k : ℤ, windingContact β T k = lineContact T k * paramFactor β T :=
  grammar_contacts_admit_any_radial hT hβ hβ2

/-! ## 3. Impossibilité collective : groupe fini compilé, complément infini = bande sans zéro -/

/-- **Non-compensation par un groupe fini** (rappel) : le miroir d'un membre bas de hauteur dans `]H, H'']` n'est compensé
par aucun groupe fini sous son exposant. -/
theorem finite_group_noncompensation {H H'' θ C : ℝ} (l : TrueZero) (hz : H < rZeroHeight l.1)
    (hz' : rZeroHeight l.1 ≤ H'') (hθ : θ < 1 - rZeroRadialPosition l.1) :
    ¬ ∀ x : ℝ, 1 < x → ‖nextFiberSum H H'' x‖ ≤ C * x ^ θ :=
  mirror_group_not_compensated l hz hz' hθ

/-- **Impossibilité collective avec le complément infini ⟺ borne du reste des premiers sous l'exposant du miroir.**
La forme fermante disponible exige `∃ θ < 1 − β_l, ∃ C, ‖R(x)‖ ≤ C·x^θ` (premiers seuls) ; c'est une bande sans zéro
contenant le miroir, et elle contredit l'existence même du membre bas. -/
theorem infinite_complement_closes (l : TrueZero)
    (h : ∃ θ C : ℝ, θ < 1 - rZeroRadialPosition l.1 ∧
      ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ θ) : False :=
  mirror_closes_of_remainder_growth l h

/-- **Ce qui est acquis sur le complément infini** : l'exposant `1` seulement, qui n'est jamais `< 1 − β_l`. -/
theorem acquired_exponent_not_below_mirror (l : TrueZero) :
    (∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 : ℝ)) ∧
      ¬ ((1 : ℝ) < 1 - rZeroRadialPosition l.1) :=
  ⟨smoothedRemainder_linear_growth, by have := thm_zeroRadialPosition_positive l.1; linarith⟩

/-- **La reconstruction exacte admet la famille authentique pour toute position radiale** : la représentation du reste lissé
ne mentionne aucune partie réelle (rappel). -/
theorem reconstruction_admits_any_radial (p : TZeroPassage) {x : ℝ} (hx : 1 < x) :
    smoothedRemainder x = ∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm x ρ :=
  (authentic_family_reconstructs_any_radial p hx).1

/-! ## 4. Composition des trois ingrédients du texte -/

/-- **Les trois ingrédients tiennent ensemble pour toute arrivée basse** : régime du premier zéro (ancre, membre bas captif
sur `x ≥ 1`), contraintes exactes des premiers (reconstruction exacte), largeurs et fréquences des contacts (fenêtre du
facteur). Aucun des trois ne lit `β_l` au-delà de `β_l ≤ 1/2` : leur composition ne peut exclure `β_l < 1/2`. -/
theorem three_ingredients_any_low_arrival (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (p : TZeroPassage) (hL : 0 < rZeroHeight p.zLaterMember) (hV : VerticalPassage p)
    (hρ : ‖zeroPoint (canonicalZero 1)‖ ≤ ‖zeroPoint ⟨p.zLaterMember, hL⟩‖) :
    InsideField (canonicalZero 1) ⟨p.zLaterMember, hL⟩ ∧
      (∀ x : ℝ, 1 < x → smoothedRemainder x = ∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm x ρ) ∧
      (1 ≤ paramFactor (rZeroRadialPosition p.zLaterMember) (rZeroHeight p.zLaterMember) ∧
        paramFactor (rZeroRadialPosition p.zLaterMember) (rZeroHeight p.zLaterMember) <
          Real.exp (1 / (2 * rZeroHeight p.zLaterMember) / rZeroHeight p.zLaterMember) ∧
        ∀ k : ℤ, windingContact (rZeroRadialPosition p.zLaterMember) (rZeroHeight p.zLaterMember) k =
          lineContact (rZeroHeight p.zLaterMember) k *
            paramFactor (rZeroRadialPosition p.zLaterMember) (rZeroHeight p.zLaterMember)) :=
  ⟨arrival_insideField_of_support h₁ p hL hV hρ,
    fun x hx => reconstruction_admits_any_radial p hx,
    contact_constraints_admit_low hL (thm_zeroRadialPosition_positive _) (passage_entry_radial_le_half p hV)⟩

/-- **Impossibilité universelle de l'amplification ⟺ RH** (sous l'ancre, premier zéro au bas de l'énumération) : « aucun
zéro ne dépasse le champ du premier » est exactement l'hypothèse de Riemann. La contradiction du texte, quantifiée sur
tous les zéros, est RH ; sur le seul membre atteint, elle est le but. -/
theorem universal_no_amplification_iff_riemannHypothesis
    (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    (∀ w : TrueZero, InsideField (canonicalZero 1) w) ↔ RiemannHypothesis :=
  first_field_iff_riemannHypothesis canonicalZero_one_bottom h₁

/-- **Fermeture par l'incompatibilité du miroir** : si le miroir du membre atteint est dans le champ du premier, le membre
est en ligne ; sous `β_l < 1/2`, contradiction. C'est l'antécédent qui manque, non la conséquence. -/
theorem mirror_captivity_closes {l : TrueZero} (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (hβ : rZeroRadialPosition l.1 < 1 / 2) (hρ : ‖zeroPoint (canonicalZero 1)‖ ≤ ‖zeroPoint l‖)
    (hm : InsideField (canonicalZero 1) (mirrorMember l)) : False := by
  have := (mirror_insideField_iff_onLine h₁ hβ.le hρ).mp hm
  linarith

/-! ## 5. Conservation de la domination du premier zéro au cours des événements premiers (auteur, 2026-10-19, huitième
message : « la question décisive est de savoir si la domination du premier zéro est une borne démontrée pour tous les
événements futurs et pour le signal pertinent, plutôt qu'une observation sur les fenêtres expérimentales ») -/

/-- **Domination conservée à un membre** : le premier zéro domine le membre ET son miroir (la paire entière que l'événement
engage), sur tout `x ≥ 1`. Aucune valeur de `β` n'y est présupposée. -/
def DominationConserved (z₁ w : TrueZero) : Prop := InsideField z₁ w ∧ InsideField z₁ (mirrorMember w)

/-- **(2) Les membres ON sont dominés par le premier à TOUT événement premier** (et à tout `x > 0`) : borne DÉMONTRÉE, pas
une observation de fenêtre. -/
theorem onLine_dominated_at_every_prime_event (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2) (n : ℕ) :
    pairAmplitude w (fnPrimeAtRank n : ℝ) ≤ pairAmplitude (canonicalZero 1) (fnPrimeAtRank n : ℝ) := by
  have hp : 0 < (fnPrimeAtRank n : ℝ) := by
    have := (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n).pos
    exact_mod_cast this
  exact pairAmplitude_onLine_le_of_height h₁ hw (firstZero_height_le w) hp

/-- **(2) bis, domination ON conservée** : pour un membre ON, le premier domine le membre et son miroir (qui est lui-même). -/
theorem dominationConserved_of_onLine (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2) : DominationConserved (canonicalZero 1) w := by
  have hIn : InsideField (canonicalZero 1) w := fun x hx =>
    (pairAmplitude_le_iff (canonicalZero 1) w (by linarith)).mp
      (pairAmplitude_onLine_le_of_height h₁ hw (firstZero_height_le w) (by linarith))
  exact ⟨hIn, by rw [(mirrorMember_eq_self_iff w).mpr hw]; exact hIn⟩

/-- **(4) La croissance du miroir dépasse nécessairement la domination à un événement premier** : pour toute arrivée basse,
il existe un NOMBRE PREMIER `q` au-delà de l'horizon exact où l'amplitude du miroir dépasse strictement le champ du premier.
Les premiers sont en nombre infini ; le dépassement persiste ensuite. Certificat compilé, fonction de `(β_l, T_l)`. -/
theorem mirror_exceeds_domination_at_prime {z₁ l : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hβ : rZeroRadialPosition l.1 < 1 / 2) :
    ∃ q : ℕ, Nat.Prime q ∧ firstField z₁ (q : ℝ) < ‖zeroTerm (mirrorMember l) (q : ℝ)‖ := by
  set Hz : ℝ := (‖zeroPoint (mirrorMember l)‖ / ‖zeroPoint z₁‖) ^ (1 / (1 / 2 - rZeroRadialPosition l.1)) with hHz
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (⌈Hz⌉₊ + 1)
  refine ⟨q, hprime, ?_⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hprime.pos
  have hfar : Hz < q := by
    have h1 : Hz ≤ ⌈Hz⌉₊ := Nat.le_ceil Hz
    have h2 : (⌈Hz⌉₊ : ℝ) + 1 ≤ q := by exact_mod_cast hq
    linarith
  exact off_amplification_certificate h₁ hβ hqpos hfar

/-- **(3)–(4) Domination conservée à l'arrivée ⟺ arrivée en ligne** (support du membre bas acquis) : sous `β_l ≤ 1/2`, le
premier domine la paire `l`, `l*` ⟺ `β_l = 1/2`. La conservation de la domination au premier événement OFF n'est pas une borne
disponible : elle est le but. -/
theorem dominationConserved_iff_onLine {z₁ l : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) (hρ : ‖zeroPoint z₁‖ ≤ ‖zeroPoint l‖) :
    DominationConserved z₁ l ↔ rZeroRadialPosition l.1 = 1 / 2 := by
  constructor
  · intro h; exact (mirror_insideField_iff_onLine h₁ hβ hρ).mp h.2
  · intro hOn
    refine ⟨low_member_captive h₁ hβ hρ, ?_⟩
    rw [(mirrorMember_eq_self_iff l).mpr hOn]; exact low_member_captive h₁ hβ hρ

/-- **(4) Première arrivée OFF impossible SOUS la conservation de la domination** : la contradiction du texte est compilée,
son antécédent (domination du premier sur la paire de l'arrivée) est ce qui manque. -/
theorem first_off_arrival_impossible_of_domination {z₁ l : TrueZero} (h₁ : rZeroRadialPosition z₁.1 = 1 / 2)
    (hβ : rZeroRadialPosition l.1 < 1 / 2) (hρ : ‖zeroPoint z₁‖ ≤ ‖zeroPoint l‖)
    (hDom : DominationConserved z₁ l) : False := by
  have := (dominationConserved_iff_onLine h₁ hβ.le hρ).mp hDom
  linarith

/-- **La domination conservée à tous les membres ⟺ RH** (sous l'ancre) : comme borne « pour tous les événements futurs »,
elle a exactement la force de l'hypothèse de Riemann. -/
theorem dominationConserved_all_iff_riemannHypothesis
    (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) :
    (∀ w : TrueZero, DominationConserved (canonicalZero 1) w) ↔ RiemannHypothesis := by
  rw [← universal_no_amplification_iff_riemannHypothesis h₁]
  exact ⟨fun h w => (h w).1, fun h w => ⟨h w, h (mirrorMember w)⟩⟩

/-- **Le signal pertinent (reste des premiers au-dessus du départ) : aucune domination par le premier n'est compilée** ;
la seule borne disponible de la somme des suivants est linéaire, et une borne `√x` ⟺ tous les suivants en ligne
(`followingSum_sqrt_iff_following_le_half`). Sous une telle borne, le membre atteint est en ligne. -/
theorem collective_signal_domination_closes (e l : TrueZero) (hlt : rZeroHeight e.1 < rZeroHeight l.1)
    (hβ : rZeroRadialPosition l.1 < 1 / 2)
    (h : ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖followingSum (rZeroHeight e.1) x‖ ≤ C * x ^ (1 / 2 : ℝ)) : False := by
  have := following_onLine_of_followingSum_sqrt e h l hlt
  linarith

#print axioms onLine_dominated_at_every_prime_event
#print axioms mirror_exceeds_domination_at_prime
#print axioms dominationConserved_iff_onLine
#print axioms dominationConserved_all_iff_riemannHypothesis
#print axioms collective_signal_domination_closes

#print axioms mirror_over_low_amplitude_ratio
#print axioms off_amplification_certificate
#print axioms mirror_insideField_iff_onLine
#print axioms three_ingredients_any_low_arrival
#print axioms universal_no_amplification_iff_riemannHypothesis
#print axioms mirror_captivity_closes

/-! ## §6 — Prémisse MINIMALE (auteur, 2026-10-19, neuvième message : « une prémisse très réduite, une compilation définitive »)

La prémisse retenue est la **conservation de la domination du premier zéro, au miroir du membre atteint, aux seuls
événements premiers** : sur un passage qui monte depuis un membre ON dont tout l'historique est ON, le terme du miroir du
membre atteint ne dépasse le champ du premier zéro à aucun nombre premier. Elle est réduite de trois façons :
(i) elle ne porte que sur les ABSCISSES PREMIÈRES (les événements), jamais sur tout l'axe ;
(ii) elle ne porte que sur le MIROIR du membre atteint, jamais sur le membre lui-même (captif par théorème) ;
(iii) elle ne porte que sur les passages d'HISTORIQUE ON (première rupture possible), jamais sur un passage quelconque.
Sur un membre ON atteint, elle est un THÉORÈME (`mirror_dominated_at_primes_of_onLine`) : elle ne demande rien aux ON.
Elle est impliquée par RH (`mirror_dominated_at_primes_of_riemannHypothesis`) : au plus aussi forte que RH.
Elle ferme le cas bas (`low_arrival_impossible_of_mirror_domination_at_primes`) par le dépassement compilé du miroir à un
premier (`mirror_exceeds_domination_at_prime`). Dans le contexte du cas bas, elle est donc ⟺ `β_l = 1/2`, et quantifiée
sur tous les passages d'historique ON elle est ⟺ RH (`DemonstrationChain.mirror_domination_premise_iff_riemannHypothesis`). -/

/-- **Vacuité sur les membres ON** : le miroir d'un membre ON est lui-même, dominé par le premier à tout nombre premier. -/
theorem mirror_dominated_at_primes_of_onLine (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2) (q : ℕ) (hq : Nat.Prime q) :
    ‖zeroTerm (mirrorMember w) (q : ℝ)‖ ≤ firstField (canonicalZero 1) (q : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  rw [(mirrorMember_eq_self_iff w).mpr hw]
  show ‖zeroTerm w (q : ℝ)‖ ≤ ‖zeroTerm (canonicalZero 1) (q : ℝ)‖
  exact (pairAmplitude_le_iff (canonicalZero 1) w hq0).mp
    (pairAmplitude_onLine_le_of_height h₁ hw (firstZero_height_le w) hq0)

/-- **Impliquée par RH** : sous RH tout membre est ON, la prémisse est vide. Elle est au plus aussi forte que RH. -/
theorem mirror_dominated_at_primes_of_riemannHypothesis (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (hRH : RiemannHypothesis) (w : TrueZero) (q : ℕ) (hq : Nat.Prime q) :
    ‖zeroTerm (mirrorMember w) (q : ℝ)‖ ≤ firstField (canonicalZero 1) (q : ℝ) :=
  mirror_dominated_at_primes_of_onLine h₁ w (thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1) q hq

/-- **Fermeture du cas bas** : si le miroir d'une arrivée basse restait dominé par le premier à tout nombre premier, le
dépassement compilé à un premier au-delà de l'horizon exact serait contredit. -/
theorem low_arrival_impossible_of_mirror_domination_at_primes {z₁ l : TrueZero}
    (h₁ : rZeroRadialPosition z₁.1 = 1 / 2) (hβ : rZeroRadialPosition l.1 < 1 / 2)
    (hDom : ∀ q : ℕ, Nat.Prime q → ‖zeroTerm (mirrorMember l) (q : ℝ)‖ ≤ firstField z₁ (q : ℝ)) : False := by
  obtain ⟨q, hq, hlt⟩ := mirror_exceeds_domination_at_prime h₁ hβ
  exact absurd (hDom q hq) (not_le.mpr hlt)

#print axioms mirror_dominated_at_primes_of_onLine
#print axioms mirror_dominated_at_primes_of_riemannHypothesis
#print axioms low_arrival_impossible_of_mirror_domination_at_primes

/-! ## 7. Réduction à UN SEUL premier au-delà de l'horizon exact (texte collé, point 19, 2026-10-19)

La fermeture du cas bas ne consomme la domination qu'à UN premier, situé au-delà de l'horizon exact du miroir
(`off_amplification_certificate` y donne le dépassement). La prémisse est donc réduite d'une forme universelle (tout
premier) à une forme existentielle (un seul premier au-delà de l'horizon, ce premier dépendant de l'arrivée : point 20).
L'horizon est une fonction des seuls paramètres du membre et du premier zéro ; sur un membre ON le miroir est lui-même et
l'exposant est nul, la condition est alors satisfaite par tout premier. -/

/-- **Horizon exact du miroir** `(‖ρ_{l*}‖/‖ρ₁‖)^{1/(1/2 − β_l)}` : un nombre réel, fonction des paramètres seuls. -/
noncomputable def mirrorHorizon (z₁ l : TrueZero) : ℝ :=
  (‖zeroPoint (mirrorMember l)‖ / ‖zeroPoint z₁‖) ^ (1 / (1 / 2 - rZeroRadialPosition l.1))

/-- **Fermeture du cas bas à un seul premier** : une arrivée basse dont le miroir est dominé par le premier à UN premier
au-delà de l'horizon exact est contredite par le dépassement compilé à ce premier. -/
theorem low_arrival_impossible_of_one_prime {z₁ l : TrueZero}
    (h₁ : rZeroRadialPosition z₁.1 = 1 / 2) (hβ : rZeroRadialPosition l.1 < 1 / 2)
    (hDom : ∃ q : ℕ, Nat.Prime q ∧ mirrorHorizon z₁ l < q ∧
      ‖zeroTerm (mirrorMember l) (q : ℝ)‖ ≤ firstField z₁ (q : ℝ)) : False := by
  obtain ⟨q, hq, hfar, hle⟩ := hDom
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  exact absurd hle (not_le.mpr (off_amplification_certificate h₁ hβ hqpos hfar))

/-- **La forme universelle entraîne la forme à un premier** : les premiers sont en nombre infini. -/
theorem one_prime_of_all_primes {z₁ l : TrueZero}
    (hDom : ∀ q : ℕ, Nat.Prime q → ‖zeroTerm (mirrorMember l) (q : ℝ)‖ ≤ firstField z₁ (q : ℝ)) :
    ∃ q : ℕ, Nat.Prime q ∧ mirrorHorizon z₁ l < q ∧
      ‖zeroTerm (mirrorMember l) (q : ℝ)‖ ≤ firstField z₁ (q : ℝ) := by
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (⌈mirrorHorizon z₁ l⌉₊ + 1)
  refine ⟨q, hprime, ?_, hDom q hprime⟩
  have h1 : mirrorHorizon z₁ l ≤ ⌈mirrorHorizon z₁ l⌉₊ := Nat.le_ceil _
  have h2 : (⌈mirrorHorizon z₁ l⌉₊ : ℝ) + 1 ≤ q := by exact_mod_cast hq
  linarith

/-- **Vacuité sur les membres ON** : le miroir est lui-même, dominé à tout premier ; un premier au-delà de l'horizon existe. -/
theorem one_prime_of_onLine (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2) :
    ∃ q : ℕ, Nat.Prime q ∧ mirrorHorizon (canonicalZero 1) w < q ∧
      ‖zeroTerm (mirrorMember w) (q : ℝ)‖ ≤ firstField (canonicalZero 1) (q : ℝ) :=
  one_prime_of_all_primes (mirror_dominated_at_primes_of_onLine h₁ w hw)

/-- **Impliquée par RH.** -/
theorem one_prime_of_riemannHypothesis (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (hRH : RiemannHypothesis) (w : TrueZero) :
    ∃ q : ℕ, Nat.Prime q ∧ mirrorHorizon (canonicalZero 1) w < q ∧
      ‖zeroTerm (mirrorMember w) (q : ℝ)‖ ≤ firstField (canonicalZero 1) (q : ℝ) :=
  one_prime_of_onLine h₁ w (thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1)

/-- **Ce que la forme à un premier n'affaiblit pas** : dans le contexte du cas bas (support acquis), elle reste ⟺ `β_l = 1/2`
(elle est fausse sous un demi par `low_arrival_impossible_of_one_prime`, vraie en ligne par `one_prime_of_onLine`). -/
theorem one_prime_iff_onLine (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) (l : TrueZero)
    (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) :
    (∃ q : ℕ, Nat.Prime q ∧ mirrorHorizon (canonicalZero 1) l < q ∧
      ‖zeroTerm (mirrorMember l) (q : ℝ)‖ ≤ firstField (canonicalZero 1) (q : ℝ)) ↔
    rZeroRadialPosition l.1 = 1 / 2 := by
  constructor
  · intro h
    by_contra hne
    exact low_arrival_impossible_of_one_prime h₁ (lt_of_le_of_ne hβ hne) h
  · intro hOn; exact one_prime_of_onLine h₁ l hOn

#print axioms low_arrival_impossible_of_one_prime
#print axioms one_prime_of_all_primes
#print axioms one_prime_of_onLine
#print axioms one_prime_iff_onLine

/-! ## 8. Réduction suivante : UN SEUL POINT au-delà de l'horizon, décalage authentique des contacts du miroir, trois
certificats (onzième message, 2026-10-19 : « continue la réduction, une seule prémisse, prouve la fermeture »)

La fermeture du cas bas ne lit la domination qu'en UN point au-delà de l'horizon exact ; rien n'exige que ce point soit un
nombre premier. La prémisse est donc réduite une seconde fois : d'une forme à un premier à une forme à un point réel
(la forme à un premier l'entraîne ; la forme universelle aussi). Le texte collé fournit en outre une signature géométrique
exacte de la paire OFF, compilée ici : à tout étage `k`, les contacts de l'arrivée et de son miroir sont décalés d'une
constante logarithmique `Δ_l = (arctan(T/β) − arctan(T/(1−β)))/T`, strictement positive sous un demi, nulle ⟺ ON. -/

/-- L'horizon exact est un réel positif ou nul (puissance réelle d'un quotient de normes). -/
theorem mirrorHorizon_nonneg (z₁ l : TrueZero) : 0 ≤ mirrorHorizon z₁ l :=
  Real.rpow_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)) _

/-- **Fermeture du cas bas en UN SEUL POINT** : une arrivée basse dont le miroir est dominé par le premier zéro en un
point réel au-delà de l'horizon exact est contredite par le dépassement compilé en ce point. -/
theorem low_arrival_impossible_of_one_point {z₁ l : TrueZero}
    (h₁ : rZeroRadialPosition z₁.1 = 1 / 2) (hβ : rZeroRadialPosition l.1 < 1 / 2)
    (hDom : ∃ x : ℝ, mirrorHorizon z₁ l < x ∧ ‖zeroTerm (mirrorMember l) x‖ ≤ firstField z₁ x) : False := by
  obtain ⟨x, hfar, hle⟩ := hDom
  have hxpos : 0 < x := lt_of_le_of_lt (mirrorHorizon_nonneg z₁ l) hfar
  exact absurd hle (not_le.mpr (off_amplification_certificate h₁ hβ hxpos hfar))

/-- **La forme à un premier entraîne la forme à un point.** -/
theorem one_point_of_one_prime {z₁ l : TrueZero}
    (h : ∃ q : ℕ, Nat.Prime q ∧ mirrorHorizon z₁ l < q ∧
      ‖zeroTerm (mirrorMember l) (q : ℝ)‖ ≤ firstField z₁ (q : ℝ)) :
    ∃ x : ℝ, mirrorHorizon z₁ l < x ∧ ‖zeroTerm (mirrorMember l) x‖ ≤ firstField z₁ x := by
  obtain ⟨q, _, hfar, hle⟩ := h
  exact ⟨q, hfar, hle⟩

/-- **Vacuité sur les membres ON.** -/
theorem one_point_of_onLine (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (w : TrueZero) (hw : rZeroRadialPosition w.1 = 1 / 2) :
    ∃ x : ℝ, mirrorHorizon (canonicalZero 1) w < x ∧
      ‖zeroTerm (mirrorMember w) x‖ ≤ firstField (canonicalZero 1) x :=
  one_point_of_one_prime (one_prime_of_onLine h₁ w hw)

/-- **Impliquée par RH.** -/
theorem one_point_of_riemannHypothesis (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2)
    (hRH : RiemannHypothesis) (w : TrueZero) :
    ∃ x : ℝ, mirrorHorizon (canonicalZero 1) w < x ∧
      ‖zeroTerm (mirrorMember w) x‖ ≤ firstField (canonicalZero 1) x :=
  one_point_of_onLine h₁ w (thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1)

/-- **Force exacte de la forme à un point** dans le contexte du cas bas : ⟺ `β_l = 1/2`. La réduction affaiblit la forme,
elle ne la dérive pas. -/
theorem one_point_iff_onLine (h₁ : rZeroRadialPosition (canonicalZero 1).1 = 1 / 2) (l : TrueZero)
    (hβ : rZeroRadialPosition l.1 ≤ 1 / 2) :
    (∃ x : ℝ, mirrorHorizon (canonicalZero 1) l < x ∧
      ‖zeroTerm (mirrorMember l) x‖ ≤ firstField (canonicalZero 1) x) ↔
    rZeroRadialPosition l.1 = 1 / 2 := by
  constructor
  · intro h
    by_contra hne
    exact low_arrival_impossible_of_one_point h₁ (lt_of_le_of_ne hβ hne) h
  · intro hOn; exact one_point_of_onLine h₁ l hOn

/-- **Décalage authentique des contacts du miroir** (texte collé, point 3) : à même hauteur, les contacts de `l` et de
`l*` sont décalés, à tout étage `k`, de la constante logarithmique
`Δ_l = (arctan(T_l/β_l) − arctan(T_l/(1 − β_l)))/T_l`. -/
theorem mirror_contact_shift (l : TrueZero) (k : ℤ) :
    Real.log (contactMinusAt l k) - Real.log (contactMinusAt (mirrorMember l) k) =
      (Real.arctan (rZeroHeight l.1 / rZeroRadialPosition l.1)
        - Real.arctan (rZeroHeight l.1 / (1 - rZeroRadialPosition l.1))) / rZeroHeight l.1 := by
  rw [contactMinusAt_eq_exp, contactMinusAt_eq_exp, Real.log_exp, Real.log_exp, mirrorMember_ordinate,
    mirrorMember_radial]
  ring

/-- Sous un demi, le décalage est strictement positif à tout étage : la paire OFF a une séparation de contacts non nulle
à tous les étages homologues. -/
theorem mirror_contact_shift_pos (l : TrueZero) (hβ : rZeroRadialPosition l.1 < 1 / 2) (k : ℤ) :
    0 < Real.log (contactMinusAt l k) - Real.log (contactMinusAt (mirrorMember l) k) := by
  rw [mirror_contact_shift]
  have hT : 0 < rZeroHeight l.1 := l.2
  have hb : 0 < rZeroRadialPosition l.1 := thm_zeroRadialPosition_positive l.1
  refine div_pos ?_ hT
  rw [sub_pos]
  exact Real.arctan_strictMono (div_lt_div_of_pos_left hT hb (by linarith))

/-- Le décalage est nul ⟺ ON (caractérisation : la signature géométrique de la paire est exactement le but). -/
theorem mirror_contact_shift_eq_zero_iff (l : TrueZero) (k : ℤ) :
    Real.log (contactMinusAt l k) - Real.log (contactMinusAt (mirrorMember l) k) = 0 ↔
      rZeroRadialPosition l.1 = 1 / 2 := by
  constructor
  · intro h
    rw [mirror_contact_shift, div_eq_zero_iff, sub_eq_zero] at h
    have hT : 0 < rZeroHeight l.1 := l.2
    rcases h with h | h
    · have hb : 0 < rZeroRadialPosition l.1 := thm_zeroRadialPosition_positive l.1
      have h1b : 0 < 1 - rZeroRadialPosition l.1 := by
        have := thm_zeroRadialPosition_positive (mirrorMember l).1
        rwa [mirrorMember_radial] at this
      have h2 := Real.arctan_strictMono.injective h
      rw [div_eq_div_iff hb.ne' h1b.ne'] at h2
      have h3 := mul_left_cancel₀ hT.ne' h2
      linarith
    · exact absurd h hT.ne'
  · intro hOn
    rw [(mirrorMember_eq_self_iff l).mpr hOn, sub_self]

/-- **Les trois certificats compilés d'une arrivée basse** (texte collé, point 7) : contacts du miroir décalés à tout
étage ; amplification du miroir au-delà de l'horizon exact, en tout point ; non-compensation par tout groupe fini contenant
le miroir sous l'exposant du miroir. Ils démontrent une déformation et une obstruction finie ; aucun ne contredit un fait
acquis : la contradiction exige encore la domination en un point au-delà de l'horizon (prémisse). -/
theorem off_three_certificates {z₁ l : TrueZero}
    (h₁ : rZeroRadialPosition z₁.1 = 1 / 2) (hβ : rZeroRadialPosition l.1 < 1 / 2) :
    (∀ k : ℤ, 0 < Real.log (contactMinusAt l k) - Real.log (contactMinusAt (mirrorMember l) k)) ∧
    (∀ x : ℝ, mirrorHorizon z₁ l < x → firstField z₁ x < ‖zeroTerm (mirrorMember l) x‖) ∧
    (∀ H H'' θ C : ℝ, H < rZeroHeight l.1 → rZeroHeight l.1 ≤ H'' → θ < 1 - rZeroRadialPosition l.1 →
      ¬ ∀ x : ℝ, 1 < x → ‖nextFiberSum H H'' x‖ ≤ C * x ^ θ) :=
  ⟨mirror_contact_shift_pos l hβ,
   fun x hfar => off_amplification_certificate h₁ hβ (lt_of_le_of_lt (mirrorHorizon_nonneg z₁ l) hfar) hfar,
   fun _ _ _ _ hz hz' hθ => mirror_group_not_compensated l hz hz' hθ⟩

#print axioms low_arrival_impossible_of_one_point
#print axioms one_point_iff_onLine
#print axioms mirror_contact_shift_pos
#print axioms mirror_contact_shift_eq_zero_iff
#print axioms off_three_certificates

end RHV6Fresh
