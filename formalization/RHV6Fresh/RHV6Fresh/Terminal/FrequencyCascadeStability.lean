/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CascadeContinuation
import RHV6Fresh.Terminal.FirstGainPremise
import RHV6Fresh.Terminal.DoubleRigidity
import RHV6Fresh.Terminal.OnRegimeInduction

/-!
# La cascade de fréquences : ensemble cohérent et stable (auteur, 2026-10-19)

Demande de l'auteur : « le zéro suivant est strictement supérieur en fréquence au précédent, et le suivant idem, à l'infini ;
les hauteurs augmentent sur la ligne » ; « le zéro suivant doit donc obligatoirement connaître la fréquence du zéro précédent et du zéro
suivant ; les zéros ne sont pas calculés au hasard et il n'existe pas d'ajustement » ; « les zéros forment un ensemble
cohérent et stable ; toute intrusion ou miroir détruit la stabilité ».

Compilé ici, axiomes standard, sur les vrais zéros seulement (énumération canonique) :
* la fréquence ne recule jamais le long de toute la suite (`frequency_never_decreases`) ;
* depuis un zéro ON atteint en montant, le pas suivant monte encore (`frequency_cascade_continues_from_engaged`) ;
* sur la ligne, la cascade STRICTE est démontrée : la fréquence du zéro suivant est strictement supérieure à celle du précédent
  (`strict_frequency_step_onLine`), et sur des zéros sur la ligne les fréquences augmentent à tout rang, à l'infini
  (`strict_frequency_cascade_onLine`) ; la même cascade écrite sur toute la suite, sans savoir les zéros sur la ligne, ⟺ RH
  (`strict_frequency_cascade_iff_riemannHypothesis`) : seul un miroir hors ligne pourrait la rompre ;
* le zéro du milieu est lié aux deux voisins : prédécesseur et successeur uniques (aucun ajustement), il lit la fréquence du
  précédent et le suivant se lit depuis la sienne (`zero_linked_to_both_neighbours`) ;
* un miroir détruit la stabilité : un seul zéro hors ligne force deux rangs consécutifs à la même fréquence
  (`mirror_breaks_frequency_cascade`) ; deux β miroirs n'ont jamais la même valeur hors ligne, l'un avant, l'autre après
  (`mirror_placed_unequally`), d'où l'instabilité (`mirror_creates_instability`) ; une intrusion détruit la reconstruction (`insertTwo_not_reconstruct`, déjà compilé).
Portée : la non-décroissance, la continuation depuis un zéro engagé, la liaison aux deux voisins et la rupture par un miroir
sont démontrées ; la cascade stricte à tout rang n'est pas démontrée : elle a la force de RH.
-/

namespace RHV6Fresh

open RHV3Lean

/-- **La fréquence ne recule jamais** le long de la suite des vrais zéros, toute position radiale. -/
theorem frequency_never_decreases {m n : ℕ} (h : m ≤ n) :
    rZeroHeight (canonicalZero m).1 ≤ rZeroHeight (canonicalZero n).1 :=
  canonicalZero_height_mono h

/-- Le pas canonique de rang `n ≥ 1` : du zéro de rang `n` au zéro de rang `n + 1`. -/
noncomputable def canonicalStep (n : ℕ) (hn : 1 ≤ n) : TZeroPassage :=
  ⟨(canonicalZero n).1, (canonicalZero (n + 1)).1, canonicalZero_consecutive hn⟩

/-- Tout passage dont le départ est un vrai zéro de hauteur positive est un pas canonique. -/
theorem passage_is_canonicalStep (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember) :
    ∃ n, ∃ _ : 1 ≤ n, (canonicalZero n).1 = p.zEarlierMember ∧
      (canonicalZero (n + 1)).1 = p.zLaterMember := by
  obtain ⟨n, hn, hw⟩ := canonicalZero_surjective ⟨p.zEarlierMember, hE⟩
  have hE' : (canonicalZero n).1 = p.zEarlierMember := congrArg Subtype.val hw
  exact ⟨n, hn, hE', (passage_successor_unique (p := canonicalStep n hn) (p' := p) hE')⟩

/-- **La cascade continue depuis un zéro engagé** : si le zéro de rang `n + 1` est ON et atteint en montant, le pas
suivant monte encore. -/
theorem frequency_cascade_continues_from_engaged {n : ℕ} (hn : 1 ≤ n)
    (hUp : rZeroHeight (canonicalZero n).1 < rZeroHeight (canonicalZero (n + 1)).1)
    (hOn : rZeroRadialPosition (canonicalZero (n + 1)).1 = 1 / 2) :
    rZeroHeight (canonicalZero (n + 1)).1 < rZeroHeight (canonicalZero (n + 2)).1 :=
  (engaged_regime_kept (p := canonicalStep n hn) (q := canonicalStep (n + 1) (by omega)) rfl hUp hOn).1

/-- **La cascade stricte à l'infini** (sur toute la suite, la fréquence du zéro suivant strictement supérieure, à tout rang) ⟺ RH. -/
theorem strict_frequency_cascade_iff_riemannHypothesis :
    (∀ n : ℕ, 1 ≤ n → rZeroHeight (canonicalZero n).1 < rZeroHeight (canonicalZero (n + 1)).1) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    refine no_sameHeight_iff_riemannHypothesis.mp fun p hE hH => ?_
    obtain ⟨n, hn, hEq, hLq⟩ := passage_is_canonicalStep p hE
    have := h n hn
    rw [hEq, hLq] at this
    exact absurd hH (ne_of_lt this)
  · intro hRH n hn
    exact passage_height_lt_of_riemannHypothesis hRH (canonicalStep n hn)

/-- **Le zéro du milieu est lié aux deux voisins** (`e → l → s`) : prédécesseur et successeur uniques (aucun ajustement),
il lit la fréquence du précédent, et la fréquence du suivant se lit depuis la sienne et l'accroissement des rencontres. -/
theorem zero_linked_to_both_neighbours {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hM : 0 < rZeroHeight q.zEarlierMember) (hS : 0 < rZeroHeight q.zLaterMember) :
    (∀ p' : TZeroPassage, p'.zLaterMember = p.zLaterMember → p'.zEarlierMember = p.zEarlierMember) ∧
    (∀ q' : TZeroPassage, q'.zEarlierMember = q.zEarlierMember → q'.zLaterMember = q.zLaterMember) ∧
    (∀ k : ℤ, rZeroHeight p.zEarlierMember =
      Real.pi / (Real.pi / rZeroHeight p.zLaterMember -
        cascadeIncrement ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ k)) ∧
    (∀ k : ℤ, rZeroHeight q.zLaterMember =
      Real.pi / (Real.pi / rZeroHeight p.zLaterMember +
        cascadeIncrement ⟨q.zEarlierMember, hM⟩ ⟨q.zLaterMember, hS⟩ k)) := by
  refine ⟨fun p' h => ?_, fun q' h => (passage_successor_unique h.symm).symm,
    (next_zero_reads_previous p hE hL).2.2.2, fun k => ?_⟩
  · by_contra hNe
    have h₂ : PZeroMembersConsecutive p'.zEarlierMember p.zLaterMember := by rw [← h]; exact p'.hConsecutive
    rcases thm_distinctZeroMembers_comparable hNe with hlt | hlt
    · exact h₂.2 ⟨p.zEarlierMember, hlt, p.hConsecutive.1⟩
    · exact p.hConsecutive.2 ⟨p'.zEarlierMember, hlt, h₂.1⟩
  · have h : cascadeIncrement ⟨q.zEarlierMember, hM⟩ ⟨q.zLaterMember, hS⟩ k =
        Real.pi / rZeroHeight q.zLaterMember - Real.pi / rZeroHeight q.zEarlierMember :=
      cascadeIncrement_eq _ _ k
    have hS' : rZeroHeight q.zLaterMember ≠ 0 := hS.ne'
    rw [hJ, h, add_sub_cancel, div_div_eq_mul_div, mul_div_cancel_left₀ _ Real.pi_ne_zero]

/-- **Un miroir détruit la stabilité** : un seul vrai zéro hors ligne force deux rangs consécutifs à la même fréquence ;
la cascade stricte est rompue. -/
theorem mirror_breaks_frequency_cascade (w : TrueZero) (hOff : rZeroRadialPosition w.1 ≠ 1 / 2) :
    ∃ n : ℕ, 1 ≤ n ∧ rZeroHeight (canonicalZero n).1 = rZeroHeight (canonicalZero (n + 1)).1 := by
  by_contra hNo
  push Not at hNo
  have hStrict : ∀ n : ℕ, 1 ≤ n → rZeroHeight (canonicalZero n).1 < rZeroHeight (canonicalZero (n + 1)).1 :=
    fun n hn => lt_of_le_of_ne (frequency_never_decreases (Nat.le_succ n)) (hNo n hn)
  exact hOff (thm_zeroRadialPosition_half_of_riemannHypothesis
    (strict_frequency_cascade_iff_riemannHypothesis.mp hStrict) w.1)

/-- **Deux β miroirs ne peuvent pas avoir la même valeur** : un zéro et son miroir ont la même fréquence, et la même partie
réelle seulement s'ils coïncident (zéro ON). Hors ligne, ils sont placés de manière inégale de part et d'autre : l'un avant,
l'autre après ; deux vrais zéros distincts occupent la même fréquence. -/
theorem mirror_placed_unequally (w : TrueZero) (hOff : rZeroRadialPosition w.1 ≠ 1 / 2) :
    rZeroHeight (mirrorMember w).1 = rZeroHeight w.1 ∧
    rZeroRadialPosition (mirrorMember w).1 ≠ rZeroRadialPosition w.1 ∧
    mirrorMember w ≠ w ∧
    ((rZeroRadialPosition w.1 < 1 / 2 ∧ 1 / 2 < rZeroRadialPosition (mirrorMember w).1) ∨
      (rZeroRadialPosition (mirrorMember w).1 < 1 / 2 ∧ 1 / 2 < rZeroRadialPosition w.1)) := by
  have hr := mirrorMember_radial w
  refine ⟨mirrorMember_ordinate w, fun h => hOff (by linarith), fun h => hOff ((mirrorMember_eq_self_iff w).mp h), ?_⟩
  rcases lt_or_gt_of_ne hOff with h | h
  · exact Or.inl ⟨h, by linarith⟩
  · exact Or.inr ⟨by linarith, h⟩

/-- **Un miroir crée forcément l'instabilité** : un zéro hors ligne et son miroir, placés de manière inégale à la même
fréquence, rompent la cascade stricte. -/
theorem mirror_creates_instability (w : TrueZero) (hOff : rZeroRadialPosition w.1 ≠ 1 / 2) :
    rZeroRadialPosition (mirrorMember w).1 ≠ rZeroRadialPosition w.1 ∧
    ∃ n : ℕ, 1 ≤ n ∧ rZeroHeight (canonicalZero n).1 = rZeroHeight (canonicalZero (n + 1)).1 :=
  ⟨(mirror_placed_unequally w hOff).2.1, mirror_breaks_frequency_cascade w hOff⟩

/-- **Sur la ligne, la fréquence augmente strictement** : la fréquence (hauteur) du zéro suivant est strictement supérieure à
celle du précédent. -/
theorem strict_frequency_step_onLine {n : ℕ} (hn : 1 ≤ n)
    (hOn : rZeroRadialPosition (canonicalZero n).1 = 1 / 2)
    (hOn' : rZeroRadialPosition (canonicalZero (n + 1)).1 = 1 / 2) :
    rZeroHeight (canonicalZero n).1 < rZeroHeight (canonicalZero (n + 1)).1 :=
  passage_height_lt_of_onLine (canonicalStep n hn) hOn hOn'

/-- **La cascade stricte à l'infini sur la ligne** : sur des zéros sur la ligne, la fréquence du zéro suivant est strictement
supérieure, et celle du suivant encore, à tout rang, à l'infini. -/
theorem strict_frequency_cascade_onLine
    (hOn : ∀ n : ℕ, 1 ≤ n → rZeroRadialPosition (canonicalZero n).1 = 1 / 2) :
    ∀ n : ℕ, 1 ≤ n → rZeroHeight (canonicalZero n).1 < rZeroHeight (canonicalZero (n + 1)).1 :=
  fun n hn => strict_frequency_step_onLine hn (hOn n hn) (hOn (n + 1) (by omega))

end RHV6Fresh

#print axioms RHV6Fresh.strict_frequency_cascade_iff_riemannHypothesis
#print axioms RHV6Fresh.zero_linked_to_both_neighbours
#print axioms RHV6Fresh.mirror_breaks_frequency_cascade
#print axioms RHV6Fresh.frequency_cascade_continues_from_engaged
#print axioms RHV6Fresh.mirror_creates_instability
#print axioms RHV6Fresh.strict_frequency_cascade_onLine
