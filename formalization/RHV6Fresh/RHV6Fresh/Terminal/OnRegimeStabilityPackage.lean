/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CascadeContinuation
import RHV6Fresh.Terminal.LowNextZeroSignatures
import RHV6Fresh.Terminal.AuthenticPassageProfile
import RHV6Fresh.Terminal.CountingDeficit
import RHV6Fresh.Terminal.BoxCountHeight
import RHV6Fresh.Terminal.ZetaBox.Final
import RHV6Fresh.Terminal.RegimeChange
import RHV6Fresh.Terminal.RaccordDetector
import RHV6Fresh.Direct.MirrorCount

/-!
# Paquet de stabilité du régime ON engagé et profil obligé d'une première rupture

Module de CONSOLIDATION : tout est démontré depuis des théorèmes compilés, aucune hypothèse nouvelle, aucun `sorry`.
Composition pure, sauf trois théorèmes nouveaux sur la fibre de hauteur d'un membre bas
(`fiber_top_member_high`, `fiber_exit_from_high`, `cascade_resumes_after_fiber`).

Portée (vocabulaire du dépôt) : ces énoncés CARACTÉRISENT le régime engagé et la forme d'une rupture ; ils ne sont pas une
dérivation de la conservation du régime. Le profil d'une rupture est DÉMONTRÉ ; aucune de ses lignes n'est une contradiction,
elles tiennent dans le monde témoin. Le module n'importe pas `DemonstrationChain` (non compilable en l'état) : la minoration
`15 < T` d'un membre bas est redémontrée ici (`low_member_above_15`) depuis les certificats de rectangles de `ζ`.
-/

namespace RHV6Fresh

open RHV3Lean Complex

/-- Le certificat de la première bande : `N(15) = 1` (rectangles de `ζ`), donc aucun membre bas de hauteur `≤ 15`
(`saturation_of_count_one`). Depuis le 2026-10-27, seule la première bande est dans le build par défaut ; les bandes 22 et 28
(`28 < T`) sont dans la cible optionnelle `RHV6FreshCertificates` (`FirstThreeZerosCertified.lean`). -/
theorem low_member_above_15 (w : TrueZero) (hβ : rZeroRadialPosition w.1 < 1 / 2) :
    15 < rZeroHeight w.1 := by
  obtain ⟨hZ₁₀, hZ₂₀, hW₁₀, hW₂₀⟩ := ZB.Cert.zeta_box_certificate
  have h15 : upperCountWithMultiplicity 15 = 1 :=
    upperCount_of_zeta_boxes (σ₀ := 1 / 4) (t₁ := 1) (T₀ := 15) (T := 15) (K := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hZ₁₀ hZ₂₀ hW₁₀ hW₂₀ hZ₁₀ hZ₂₀
      (by rw [hW₁₀]; norm_num) hW₂₀
  have hW : lowCount 15 = 0 := (saturation_iff_lowCount_zero 15).mp (saturation_of_count_one h15)
  by_contra hle
  exact (lowCount_eq_zero_iff 15).mp hW w (not_lt.mp hle) hβ

/-- **1. Stabilité du régime ON engagé** (composition). Sur deux passages joints `o` puis `p`, `o` vertical, départ de `p`
en ligne, hauteurs positives : (i) `p` monte ; (ii) l'arrivée n'est pas au-dessus de la ligne ; (iii) le miroir du départ est
le départ ; (iv) tout passage `q` qui quitte l'arrivée monte ⟺ l'arrivée est en ligne (caractérisation, pas dérivation) ;
(v) les décalages d'entrelacement de `p` décroissent strictement à tout indice. -/
theorem engaged_on_regime_stability (o p : TZeroPassage) (hJ : o.zLaterMember = p.zEarlierMember)
    (ho : VerticalPassage o) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    VerticalPassage p ∧ rZeroRadialPosition p.zLaterMember ≤ 1 / 2 ∧
    mirrorMember ⟨p.zEarlierMember, hE⟩ = ⟨p.zEarlierMember, hE⟩ ∧
    (∀ q : TZeroPassage, p.zLaterMember = q.zEarlierMember →
      (VerticalPassage q ↔ rZeroRadialPosition p.zLaterMember = 1 / 2)) ∧
    (∀ k : ℤ, interlacingOffset ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ (k + 1) <
      interlacingOffset ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ k) := by
  have hV : VerticalPassage p := (engaged_regime_kept hJ ho (hJ ▸ hOn)).1
  refine ⟨hV, passage_entry_radial_le_half p hV, (mirror_annulled_iff_onLine _).mpr hOn, ?_, ?_⟩
  · intro q hq
    constructor
    · exact fun hqv => junction_vertical_vertical hq hV hqv
    · intro h
      exact (engaged_regime_kept hq hV h).1
  · exact fun k => interlacingOffset_strictAnti ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hV k

/-- **2. Le dernier de la fibre d'un membre bas est haut.** Si `β_l < 1/2`, tout membre `s` de même hauteur sans
successeur de même hauteur a `β_s > 1/2` : le miroir de `l` est à la même hauteur avec `β = 1 − β_l > 1/2`, et `s` ne
peut pas le précéder (ordre lexicographique hauteur puis position radiale). -/
theorem fiber_top_member_high (l : TrueZero) (hβ : rZeroRadialPosition l.1 < 1 / 2)
    (s : TNonTrivialZetaZero) (hs : rZeroHeight s = rZeroHeight l.1)
    (hTop : ∀ v : TNonTrivialZetaZero, rZeroHeight v = rZeroHeight l.1 → ¬ PZeroMemberPrecedes s v) :
    1 / 2 < rZeroRadialPosition s := by
  have hm := mirror_radial_gt hβ
  rw [mirrorMember_radial] at hm
  by_contra hle
  push Not at hle
  apply hTop (mirrorMember l).1 (mirrorMember_ordinate l)
  rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
  right
  refine ⟨hs.trans (mirrorMember_ordinate l).symm, ?_⟩
  rw [mirrorMember_radial]; linarith

/-- **3. Sortie vers le haut depuis la fibre d'un membre bas.** Un passage qui monte et dont le départ est à la hauteur
d'un membre bas part d'un membre `β > 1/2` (par consécutivité : un successeur de même hauteur précéderait l'arrivée). -/
theorem fiber_exit_from_high (l : TrueZero) (hβ : rZeroRadialPosition l.1 < 1 / 2) (q : TZeroPassage)
    (hH : rZeroHeight q.zEarlierMember = rZeroHeight l.1) (hV : VerticalPassage q) :
    1 / 2 < rZeroRadialPosition q.zEarlierMember := by
  refine fiber_top_member_high l hβ q.zEarlierMember hH ?_
  intro v hv hpre
  apply q.hConsecutive.2
  refine ⟨v, hpre, ?_⟩
  rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
  left
  have : rZeroHeight q.zEarlierMember < rZeroHeight q.zLaterMember := hV
  linarith

/-- **4. Profil démontré de toute perturbation OFF (première rupture).** Pour un membre bas `l` arrivé par un passage
vertical `p` : (i) `15 < T_l` ; (ii) le miroir est distinct, de même hauteur, `β > 1/2`, et `l` le précède ; (iii) la fibre de
hauteur est finie et contient `l` et son miroir ; (iv) il existe un passage sortant horizontal depuis `l`, aux décalages
d'entrelacement constants ; (v) le déficit de comptage à `T_l` est `≥ 2` ; (vi) tout passage qui monte depuis la hauteur
`T_l` part d'un membre `β > 1/2`. PROFIL DÉMONTRÉ ; aucune de ces lignes n'est une contradiction, elles tiennent dans le
monde témoin. -/
theorem off_disturbance_profile (l : TrueZero) (hβ : rZeroRadialPosition l.1 < 1 / 2)
    (p : TZeroPassage) (hJ : p.zLaterMember = l.1) (hV : VerticalPassage p) :
    15 < rZeroHeight l.1 ∧
    (mirrorMember l ≠ l ∧ rZeroHeight (mirrorMember l).1 = rZeroHeight l.1 ∧
      1 / 2 < rZeroRadialPosition (mirrorMember l).1 ∧ PZeroMemberPrecedes l.1 (mirrorMember l).1) ∧
    ((sZeroHeightFiber (rZeroHeight l.1)).Finite ∧ l.1 ∈ sZeroHeightFiber (rZeroHeight l.1) ∧
      (mirrorMember l).1 ∈ sZeroHeightFiber (rZeroHeight l.1)) ∧
    (∃ q : TZeroPassage, q.zEarlierMember = l.1 ∧ HorizontalPassage q ∧
      ∃ (hE : 0 < rZeroHeight q.zEarlierMember) (hL : 0 < rZeroHeight q.zLaterMember),
        ∀ k : ℤ, interlacingOffset ⟨q.zEarlierMember, hE⟩ ⟨q.zLaterMember, hL⟩ (k + 1) =
          interlacingOffset ⟨q.zEarlierMember, hE⟩ ⟨q.zLaterMember, hL⟩ k) ∧
    2 ≤ zeroCountDeficit (rZeroHeight l.1) ∧
    (∀ q : TZeroPassage, rZeroHeight q.zEarlierMember = rZeroHeight l.1 → VerticalPassage q →
      1 / 2 < rZeroRadialPosition q.zEarlierMember) := by
  refine ⟨low_member_above_15 l hβ, ⟨?_, mirrorMember_ordinate l, ?_, mirror_precedes hβ⟩,
    ⟨thm_zeroHeightFiber_finite _, rfl, mirrorMember_ordinate l⟩, ?_, low_member_deficit_ge_two l hβ,
    fun q hH hq => fiber_exit_from_high l hβ q hH hq⟩
  · intro h
    have := mirror_radial_gt hβ
    rw [h] at this
    exact lt_irrefl _ this
  · have := mirror_radial_gt hβ
    rw [mirrorMember_radial] at this ⊢
    linarith
  · obtain ⟨q, hq, hH, hL⟩ := low_arrival_outgoing_exists l hβ
    have hEq : 0 < rZeroHeight q.zEarlierMember := by rw [hq]; exact l.2
    have hJ' : p.zLaterMember = q.zEarlierMember := hJ.trans hq.symm
    have hβ' : rZeroRadialPosition p.zLaterMember < 1 / 2 := by rw [hJ]; exact hβ
    exact ⟨q, hq, hH, hEq, hL, (low_arrival_freezes_cascade hJ' hV hβ' hEq hL).2⟩

/-- **5. Seul mode de reprise après la fibre.** Après une première rupture en `l`, tout passage `q` qui quitte la hauteur
`T_l` en montant part d'un membre `β > 1/2` et arrive à un membre `β ≤ 1/2`, strictement plus haut : le régime « vertical
depuis un membre haut » est le seul mode de reprise (composition de 3 et de `passage_entry_radial_le_half`). -/
theorem cascade_resumes_after_fiber (l : TrueZero) (hβ : rZeroRadialPosition l.1 < 1 / 2) (q : TZeroPassage)
    (hH : rZeroHeight q.zEarlierMember = rZeroHeight l.1) (hV : VerticalPassage q) :
    rZeroHeight l.1 < rZeroHeight q.zLaterMember ∧ 1 / 2 < rZeroRadialPosition q.zEarlierMember ∧
      rZeroRadialPosition q.zLaterMember ≤ 1 / 2 :=
  ⟨hH ▸ hV, fiber_exit_from_high l hβ q hH hV, passage_entry_radial_le_half q hV⟩

#print axioms low_member_above_15
#print axioms engaged_on_regime_stability
#print axioms fiber_top_member_high
#print axioms fiber_exit_from_high
#print axioms off_disturbance_profile
#print axioms cascade_resumes_after_fiber

end RHV6Fresh
