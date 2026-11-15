/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RegimeTrigger

/-!
# RHV6Fresh — le tout en ligne et le paquet de contraintes, pris ensemble (auteur, 2026-09-30)

Correction de méthode demandée par l'auteur : ne plus regarder chaque contrainte isolément. La
liaison avec le zéro suivant est admise ; la liaison avec l'ensemble des zéros en ligne, qui
forment un tout, doit l'être aussi. Ce tout raffine le lissage et retrouve les écarts ; chaque
contribution ne peut y être ni remplacée ni déviée, parce qu'elle est liée dans le même temps à la
reproduction exacte de la grammaire première et au fait de pointer sur un zéro.

Ce fichier pose les contraintes sur **un seul objet** et les utilise en même temps :

* **§1 Le tout en ligne, décrit par la hauteur seule.** `lineWhole` : les indices de la formule
  explicite situés sur la ligne. Il est en bijection avec les hauteurs où la fonction réelle
  `lineValue` s'annule (`lineWholeEquiv`), et sa contribution au canal est une somme sur ces seules
  hauteurs (`lineWhole_channel_by_height`).
* **§2 L'écart.** `lineDeviation` : ce que le canal contient en dehors du tout. Le reste
  arithmétique est exactement le tout plus l'écart (`remainder_eq_lineWhole_add_deviation`) ;
  l'écart est donc fixé par le seul côté arithmétique et par la fonction réelle de la hauteur
  (`lineDeviation_arithmetic`).
* **§3 Ni remplacée, ni déviée.** L'écart ne peut être imité par aucune repondération des membres
  en ligne, finie ou infinie (`lineDeviation_not_absorbed`) ; un membre hors ligne rend l'écart non
  nul (`off_member_deviates`).
* **§4 Le paquet au passage diagonal.** Sur une entrée en régime horizontal depuis une chaîne verticale,
  toutes les contraintes tiennent en même temps sur les mêmes objets, et l'entrée est enregistrée :
  le départ est dans le tout (la fonction réelle s'annule à sa hauteur), l'arrivée et son miroir
  sont hors du tout dans un même paquet de hauteur, la grammaire première est reproduite
  exactement au même événement, le reste arithmétique reste le reste spectral, et l'écart est non
  nul (`regime_entry_packet`). Dans toute représentation du canal l'arrivée figure avec son
  exposant `β < 1/2`, sa hauteur et un poids non nul (`regime_entry_recorded`).

Bornes compilées : « l'écart est nul pour tout `x > 1` » ⟺ RH (`lineDeviation_vanishes_iff`) ;
« le reste arithmétique est la somme sur les hauteurs où la fonction réelle s'annule » ⟺ RH
(`riemannHypothesis_iff_remainder_eq_lineWhole`). Le paquet enregistre un changement de régime ;
ces théorèmes ne l'interdisent pas.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean Complex Set

/-! ## 1. Le tout en ligne, décrit par la hauteur seule -/

/-- **Le tout en ligne** : les indices de la formule explicite situés sur la ligne. -/
def lineWhole : Set ExplicitIndex := {ρ | (ρ : ℂ).re = 1 / 2}

/-- Un membre typé est dans le tout si et seulement s'il est en ligne. -/
theorem memberIndex_mem_lineWhole_iff (z : TrueZero) :
    memberIndex z ∈ lineWhole ↔ rZeroRadialPosition z.1 = 1 / 2 := Iff.rfl

/-- Un indice du tout est le point de la ligne à sa hauteur. -/
theorem lineWhole_point {ρ : ExplicitIndex} (h : ρ ∈ lineWhole) :
    (ρ : ℂ) = linePoint (ρ : ℂ).im := Complex.ext h rfl

/-- La fonction réelle de la hauteur s'annule à la hauteur de tout indice du tout. -/
theorem lineWhole_lineValue {ρ : ExplicitIndex} (h : ρ ∈ lineWhole) :
    lineValue (ρ : ℂ).im = 0 := by
  have hre : (ρ : ℂ).re = 1 / 2 := h
  have hz : PIsNonTrivialZetaZero (linePoint (ρ : ℂ).im) := by
    rw [← lineWhole_point h]
    exact ⟨ρ.property.1, by rw [hre]; norm_num, by rw [hre]; norm_num⟩
  exact (onLine_zero_iff_lineValue _).mp hz

/-- Une hauteur où la fonction réelle s'annule porte un indice de la formule explicite. -/
theorem linePoint_isNontrivial {t : ℝ} (h : lineValue t = 0) :
    IsNontrivialZetaZero (linePoint t) := by
  have hz := (onLine_zero_iff_lineValue t).mpr h
  refine ⟨hz.1, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp only [linePoint_re, Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.natCast_re,
      Complex.one_re, Complex.neg_im, Complex.add_im, Complex.natCast_im, Complex.one_im] at hre
    norm_num at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · intro h1
    have hre := congrArg Complex.re h1
    simp only [linePoint_re, Complex.one_re] at hre
    norm_num at hre

/-- **Le tout en ligne est engendré par la hauteur seule** : il est en bijection avec les hauteurs
où la fonction réelle `lineValue` s'annule. -/
noncomputable def lineWholeEquiv : lineWhole ≃ {t : ℝ // lineValue t = 0} where
  toFun ρ := ⟨((ρ : ExplicitIndex) : ℂ).im, lineWhole_lineValue ρ.2⟩
  invFun t := ⟨⟨linePoint t, linePoint_isNontrivial t.2⟩, rfl⟩
  left_inv ρ := Subtype.ext (Subtype.ext (lineWhole_point ρ.2).symm)
  right_inv _ := Subtype.ext rfl

/-- **La contribution du tout est une somme sur les hauteurs où la fonction réelle s'annule.** -/
theorem lineWhole_channel_by_height (x : ℝ) :
    channelOn lineWhole x =
      ∑' t : {t : ℝ // lineValue t = 0},
        -(zetaZeroMultiplicity (linePoint t) : ℂ) * Perron.f x (linePoint t) :=
  (lineWholeEquiv.symm.tsum_eq
    (fun ρ : lineWhole => nontrivialZeroResidueTerm x (ρ : ExplicitIndex))).symm

/-! ## 2. L'écart : ce que le canal contient en dehors du tout -/

/-- **L'écart** : la contribution au canal des indices hors du tout en ligne. -/
noncomputable def lineDeviation (x : ℝ) : ℂ := channelOn lineWholeᶜ x

/-- **Le reste arithmétique est le tout en ligne plus l'écart**, pour tout `x > 1`. -/
theorem remainder_eq_lineWhole_add_deviation {x : ℝ} (hx : 1 < x) :
    smoothedVonMangoldtSum x - smoothedZeroBackground x =
      channelOn lineWhole x + lineDeviation x := by
  rw [← channel_eq_arithmetic hx]
  exact channel_eq_packet_add_complement lineWhole hx

/-- **L'écart est fixé par le côté arithmétique et par la fonction réelle de la hauteur** : le
reste arithmétique moins la somme sur les hauteurs où `lineValue` s'annule. -/
theorem lineDeviation_arithmetic {x : ℝ} (hx : 1 < x) :
    lineDeviation x =
      smoothedVonMangoldtSum x - smoothedZeroBackground x -
        ∑' t : {t : ℝ // lineValue t = 0},
          -(zetaZeroMultiplicity (linePoint t) : ℂ) * Perron.f x (linePoint t) := by
  rw [remainder_eq_lineWhole_add_deviation hx, lineWhole_channel_by_height]
  ring

open Classical in
/-- Le poids d'un indice dans l'écart : sa multiplicité hors ligne, zéro en ligne. -/
noncomputable def offWeight (ρ : ExplicitIndex) : ℂ :=
  if (ρ : ℂ).re = 1 / 2 then 0 else -(zetaZeroMultiplicity (ρ : ℂ) : ℂ)

theorem lineDeviation_eq_tsum (x : ℝ) :
    lineDeviation x = ∑' ρ : ExplicitIndex, offWeight ρ * Perron.f x (ρ : ℂ) := by
  unfold lineDeviation channelOn
  rw [tsum_subtype lineWholeᶜ (fun ρ : ExplicitIndex => nontrivialZeroResidueTerm x ρ)]
  refine tsum_congr fun ρ => ?_
  by_cases h : (ρ : ℂ).re = 1 / 2
  · have hm : ρ ∉ lineWholeᶜ := fun hc => hc h
    rw [Set.indicator_of_notMem hm]
    unfold offWeight
    rw [if_pos h, zero_mul]
  · have hm : ρ ∈ lineWholeᶜ := h
    rw [Set.indicator_of_mem hm]
    unfold offWeight
    rw [if_neg h]
    rfl

theorem offWeight_summable :
    Summable fun ρ : ExplicitIndex => ‖offWeight ρ / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => ?_)
    multiplicity_weight_summable
  unfold offWeight
  split_ifs
  · rw [zero_div, norm_zero]
    exact norm_nonneg _
  · rw [neg_div, norm_neg]

/-- Une série de poids sommables sur les indices est sommable en tout `x > 1`. -/
theorem weighted_profiles_summable (w : ExplicitIndex → ℂ)
    (hw : Summable fun ρ : ExplicitIndex => ‖w ρ / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖) {x : ℝ}
    (hx : 1 < x) : Summable fun ρ : ExplicitIndex => w ρ * Perron.f x (ρ : ℂ) := by
  refine (summable_profiles (fun ρ : ExplicitIndex => (ρ : ℂ))
    (fun ρ => w ρ / ((ρ : ℂ) * ((ρ : ℂ) + 1))) explicitIndex_re_le_one hw hx).congr fun ρ => ?_
  change w ρ / ((ρ : ℂ) * ((ρ : ℂ) + 1)) * (x : ℂ) ^ (ρ : ℂ) =
    w ρ * ((x : ℂ) ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1)))
  ring

/-! ## 3. Ni remplacée, ni déviée -/

/-- **L'écart n'est absorbé par aucune repondération du tout en ligne.** Si des poids portés par
les seuls indices en ligne, finis ou infinis, redonnent l'écart pour tout `x > 1`, alors ces poids
sont tous nuls et il n'y a aucun zéro hors ligne. Une contribution hors ligne ne peut donc être
ni remplacée par des membres en ligne, ni compensée par une déviation de leurs poids. -/
theorem lineDeviation_not_absorbed (v : ExplicitIndex → ℂ)
    (hv : Summable fun ρ : ExplicitIndex => ‖v ρ / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖)
    (hSupp : ∀ ρ : ExplicitIndex, ρ ∉ lineWhole → v ρ = 0)
    (h : ∀ x : ℝ, 1 < x → lineDeviation x = ∑' ρ : ExplicitIndex, v ρ * Perron.f x (ρ : ℂ)) :
    (∀ ρ, v ρ = 0) ∧ RiemannHypothesis := by
  have hsum : Summable fun ρ : ExplicitIndex =>
      ‖(offWeight ρ - v ρ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => ?_)
      (offWeight_summable.add hv)
    rw [sub_div]
    exact norm_sub_le _ _
  have hzero : ∀ ρ, offWeight ρ - v ρ = 0 := by
    refine spectral_weights_unique _ hsum fun x hx => ?_
    have h1 := weighted_profiles_summable offWeight offWeight_summable hx
    have h2 := weighted_profiles_summable v hv hx
    have hsplit : ∑' ρ : ExplicitIndex, (offWeight ρ - v ρ) * Perron.f x (ρ : ℂ) =
        ∑' ρ : ExplicitIndex, offWeight ρ * Perron.f x (ρ : ℂ) -
          ∑' ρ : ExplicitIndex, v ρ * Perron.f x (ρ : ℂ) := by
      rw [← Summable.tsum_sub h1 h2]
      exact tsum_congr fun ρ => sub_mul _ _ _
    rw [hsplit, ← lineDeviation_eq_tsum, h x hx, sub_self]
  have hOn : ∀ ρ : ExplicitIndex, (ρ : ℂ).re = 1 / 2 := by
    intro ρ
    by_contra hre
    have hvρ : v ρ = 0 := hSupp ρ hre
    have hw : offWeight ρ = -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) := if_neg hre
    have h0 := hzero ρ
    rw [hvρ, sub_zero, hw, neg_eq_zero] at h0
    exact (zetaZeroMultiplicity_pos ρ.property.1).ne' (by exact_mod_cast h0)
  refine ⟨fun ρ => ?_, fun s hs htriv hne => hOn ⟨s, hs, htriv, hne⟩⟩
  have hw : offWeight ρ = 0 := if_pos (hOn ρ)
  have h0 := hzero ρ
  rw [hw, zero_sub, neg_eq_zero] at h0
  exact h0

/-- **Borne** : « l'écart est nul pour tout `x > 1` » est l'hypothèse de Riemann. -/
theorem lineDeviation_vanishes_iff :
    (∀ x : ℝ, 1 < x → lineDeviation x = 0) ↔ RiemannHypothesis := by
  constructor
  · intro h
    refine (lineDeviation_not_absorbed (fun _ => 0) ?_ (fun _ _ => rfl) fun x hx => ?_).2
    · simp only [zero_div, norm_zero]
      exact summable_zero
    · rw [h x hx]
      simp only [zero_mul, tsum_zero]
  · intro hRH x _
    rw [lineDeviation_eq_tsum]
    have hz : ∀ ρ : ExplicitIndex, offWeight ρ * Perron.f x (ρ : ℂ) = 0 := fun ρ => by
      have hw : offWeight ρ = 0 :=
        if_pos (hRH (ρ : ℂ) ρ.property.1 ρ.property.2.1 ρ.property.2.2)
      rw [hw, zero_mul]
    rw [tsum_congr hz, tsum_zero]

/-- **Un membre hors ligne dévie** : s'il existe un zéro hors ligne, l'écart entre le reste
arithmétique et le tout en ligne est non nul en un `x > 1`. -/
theorem off_member_deviates {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    ∃ x : ℝ, 1 < x ∧ lineDeviation x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hOff (thm_zeroRadialPosition_half_of_riemannHypothesis
    (lineDeviation_vanishes_iff.mp hcon) z.1)

/-- **Borne, toutes les contraintes dans une seule égalité** : RH équivaut à « le reste
arithmétique (lissage et écarts des premiers) est, pour tout `x > 1`, la somme sur les seules
hauteurs où la fonction réelle `lineValue` s'annule ». -/
theorem riemannHypothesis_iff_remainder_eq_lineWhole :
    RiemannHypothesis ↔
      ∀ x : ℝ, 1 < x → smoothedVonMangoldtSum x - smoothedZeroBackground x =
        ∑' t : {t : ℝ // lineValue t = 0},
          -(zetaZeroMultiplicity (linePoint t) : ℂ) * Perron.f x (linePoint t) := by
  rw [← lineDeviation_vanishes_iff]
  constructor
  · intro h x hx
    rw [remainder_eq_lineWhole_add_deviation hx, h x hx, add_zero, lineWhole_channel_by_height]
  · intro h x hx
    rw [lineDeviation_arithmetic hx, h x hx, sub_self]

/-! ## 4. Le paquet de contraintes au passage diagonal qui précède l'entrée -/

/-- **Le paquet au passage diagonal, toutes les contraintes en même temps.** Sur trois passages
consécutifs vertical, vertical, horizontal, le passage du milieu `p` porte à la fois :

1. la liaison avec le suivant : il part d'un membre en ligne, fait avancer la hauteur et arrive
   strictement sous la ligne ;
2. le tout en ligne : le départ est dans le tout et la fonction réelle s'annule à sa hauteur ;
   l'arrivée et son miroir sont deux indices distincts, hors du tout, dans le même paquet de
   hauteur ;
3. la grammaire première, au même événement : le raccord grammatical existe, son événement est
   celui que les zéros reconstruisent, et l'histoire première gagne exactement cet événement ;
4. le reste : le reste arithmétique reste égal au reste spectral à chaque entier `N ≥ 2` ;
5. l'enregistrement : l'écart entre le reste arithmétique et le tout en ligne est non nul. -/
theorem regime_entry_packet {o p q : TZeroPassage} (hJ₁ : o.zLaterMember = p.zEarlierMember)
    (hJ₂ : p.zLaterMember = q.zEarlierMember) (ho : VerticalPassage o) (hp : VerticalPassage p)
    (hq : HorizontalPassage q) (hE : 0 < rZeroHeight p.zEarlierMember)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    (rZeroRadialPosition p.zEarlierMember = 1 / 2 ∧
      rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
      rZeroRadialPosition p.zLaterMember < 1 / 2) ∧
    (memberIndex ⟨p.zEarlierMember, hE⟩ ∈ lineWhole ∧
      lineValue (rZeroHeight p.zEarlierMember) = 0 ∧
      memberIndex ⟨p.zLaterMember, hL⟩ ∉ lineWhole ∧
      memberIndex (mirrorMember ⟨p.zLaterMember, hL⟩) ∉ lineWhole ∧
      memberIndex (mirrorMember ⟨p.zLaterMember, hL⟩) ≠ memberIndex ⟨p.zLaterMember, hL⟩ ∧
      memberIndex ⟨p.zLaterMember, hL⟩ ∈ heightPacket (rZeroHeight p.zLaterMember) ∧
      memberIndex (mirrorMember ⟨p.zLaterMember, hL⟩) ∈
        heightPacket (rZeroHeight p.zLaterMember)) ∧
    (∃ G : GrammaticalRaccord ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩,
      G.event = reconstructedEventAt (nZeroSourceIndex p.zLaterMember) ∧
      primalHistory (nZeroSourceIndex p.zLaterMember) =
        primalHistory (nZeroSourceIndex p.zEarlierMember) ++ [G.event]) ∧
    (∀ N : ℕ, 2 ≤ N → exactRemainder N = spectralRemainder N) ∧
    (∃ x : ℝ, 1 < x ∧ lineDeviation x ≠ 0) := by
  obtain ⟨hOnE, hT, hLow, _⟩ := regime_entry_from_line hJ₁ hJ₂ ho hp hq
  have hOffL : PIsOffCriticalLine (⟨p.zLaterMember, hL⟩ : TrueZero).1 := ne_of_lt hLow
  obtain ⟨G, _, hRec, hHist⟩ := globalRigidSystem.raccord p hE hL
  refine ⟨⟨hOnE, hT, hLow⟩, ⟨hOnE, lineValue_member_onLine _ hOnE, hOffL, ?_,
    off_packet_mirror_distinct hOffL, memberIndex_mem_heightPacket ⟨p.zLaterMember, hL⟩,
    mirrorMember_mem_heightPacket ⟨p.zLaterMember, hL⟩⟩, ⟨G, hRec, hHist⟩,
    fun N hN => arithmetic_eq_spectral hN, off_member_deviates hOffL⟩
  intro hm
  have hm' : rZeroRadialPosition (mirrorMember ⟨p.zLaterMember, hL⟩).1 = 1 / 2 := hm
  have hr := mirrorMember_radial ⟨p.zLaterMember, hL⟩
  have hLow' : rZeroRadialPosition (⟨p.zLaterMember, hL⟩ : TrueZero).1 < 1 / 2 := hLow
  linarith

/-- **L'entrée en régime horizontal est enregistrée dans toute représentation du canal** : le
membre d'arrivée y figure avec son exposant `β < 1/2`, sa hauteur et un poids non nul. Aucune
représentation du reste arithmétique ne le remplace ni ne le déplace. -/
theorem regime_entry_recorded {ι : Type*} (Rep : SpectralRepresentation ι) {p q : TZeroPassage}
    (hJ : p.zLaterMember = q.zEarlierMember) (hp : VerticalPassage p) (hq : HorizontalPassage q)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    ∃ i, (Rep.point i).re < 1 / 2 ∧ (Rep.point i).im = rZeroHeight p.zLaterMember ∧
      Rep.weight i ≠ 0 := by
  obtain ⟨i, hre, him, _, hne⟩ := Rep.recovers_member ⟨p.zLaterMember, hL⟩
  refine ⟨i, ?_, him, hne⟩
  rw [hre]
  exact junction_vertical_horizontal hJ hp hq

#print axioms lineWholeEquiv
#print axioms lineWhole_channel_by_height
#print axioms remainder_eq_lineWhole_add_deviation
#print axioms lineDeviation_arithmetic
#print axioms lineDeviation_not_absorbed
#print axioms lineDeviation_vanishes_iff
#print axioms off_member_deviates
#print axioms riemannHypothesis_iff_remainder_eq_lineWhole
#print axioms regime_entry_packet
#print axioms regime_entry_recorded

end RHV6Fresh
