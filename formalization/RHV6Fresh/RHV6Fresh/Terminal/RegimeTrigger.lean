/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.SpectralUniqueness
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# RHV6Fresh — le changement de régime lu par la hauteur : caractérisation et certificat
(auteur, 2026-09-30)

Demande de l'auteur : le régime `β = 1/2` est engagé par l'annulation du miroir ; un zéro pris
dans ce régime n'en sort pas sans un événement ; seule la hauteur évolue ; extraire les règles et
les événements qui justifient un changement de régime.

Portée exacte (correction de l'auteur, 2026-09-30) : ce fichier **caractérise** et **certifie** ; il
ne produit ni le membre suivant ni la cause du déplacement radial. « Annulation du miroir » se lit
ici : la ligne `β = 1/2` est le lieu fixe de la réflexion `β ↦ 1 − β`.

Ce qui est compilé ici, sans prémisse :

* **§1 Le régime engagé est gardé sur la ligne.** Un membre en ligne atteint par un passage
  vertical est quitté par un passage vertical, jamais horizontal (`engaged_regime_kept`). La
  composante radiale n'apparaît donc jamais sur un membre en ligne : elle apparaît *pendant* un
  passage vertical. Sur un passage vertical, `β_l ≤ 1/2 ≤ β_e` ; il est pur (`Δβ = 0`) si et
  seulement si ses deux membres sont en ligne (`vertical_pure_iff_onLine`), sinon diagonal
  (`DiagonalPassage`, `ΔT > 0` et `Δβ < 0`). La position radiale d'arrivée caractérise le régime
  du passage suivant, déjà donné : vertical ⟺ `β_l = 1/2`, horizontal ⟺ `β_l < 1/2`
  (`vertical_arrival_characterizes`) ; elle ne construit pas ce passage. Toute entrée en
  régime horizontal est précédée d'un passage diagonal (`regime_entry_diagonal`), et après deux
  passages verticaux ce passage diagonal part de la ligne (`regime_entry_from_line`).
* **§2 Le certificat, lu par la hauteur seule : la fibre.** À une hauteur donnée il y a au plus un
  membre en ligne (`fibre_onLine_unique`) ; une fibre est multiple si et seulement si elle contient
  un membre hors ligne (`fibre_multiple_iff_off`) ; à l'arrivée d'un passage vertical,
  `β_l = 1/2` ⟺ la fibre de la nouvelle hauteur est réduite à `l`
  (`vertical_arrival_onLine_iff_fibre_singleton`), et de même au départ
  (`vertical_departure_onLine_iff_fibre_singleton`). La fibre multiple est un certificat de la
  présence d'un hors-ligne à cette hauteur, pas sa cause : elle est multiple parce qu'un hors-ligne
  y existe déjà.
* **§3 Le détecteur en `T` seul sur la ligne.** `Λ(1 − s̄) = conj Λ(s)` : le miroir échange deux
  points et conjugue la valeur ; sur la ligne les deux points coïncident, donc `Λ` y est réelle
  (`completedZeta_real_onLine`). Un zéro en ligne est une seule équation réelle en la seule
  variable `T` (`onLine_zero_iff_lineValue`), et un changement de signe de cette fonction réelle
  entre deux hauteurs garantit l'existence d'un membre en ligne entre elles, par le théorème des
  valeurs intermédiaires (`onLine_member_of_sign_change`). Ce n'est pas un générateur du membre
  suivant : il ne donne ni la hauteur suivante, ni l'unicité, ni la consécutivité, ni
  l'exhaustivité des zéros. C'est la partie
  inconditionnelle de l'ancien `FixedLocusParity.lean` (retiré au ménage), sans sa prémisse.

Bornes compilées : « toute fibre est réduite à un membre » ⟺ RH
(`riemannHypothesis_iff_fibres_singleton`) ; « aucun passage diagonal, et le plus bas membre ne
porte pas de passage horizontal » ⟺ RH (`riemannHypothesis_iff_no_diagonal`). Le détecteur en
`T` certifie des membres en ligne ; il n'interdit pas une fibre multiple à une hauteur où la
fonction réelle ne s'annule pas (`lineValue_ne_zero_fibre_off`). Non démontré : l'impossibilité du
passage vertical `(T, 1/2) → (T', β' < 1/2)`.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean Complex Set
open scoped ComplexConjugate

/-! ## 1. Le régime engagé est gardé sur la ligne ; l'entrée est précédée d'un passage diagonal -/

/-- **Passage diagonal** : la hauteur avance et la position radiale recule strictement. -/
def DiagonalPassage (p : TZeroPassage) : Prop :=
  VerticalPassage p ∧
    rZeroRadialPosition p.zLaterMember < rZeroRadialPosition p.zEarlierMember

/-- Sur un passage vertical, la position radiale ne peut que reculer. -/
theorem vertical_radial_step (p : TZeroPassage) (hV : VerticalPassage p) :
    rZeroRadialPosition p.zLaterMember ≤ rZeroRadialPosition p.zEarlierMember :=
  le_trans (passage_entry_radial_le_half p hV) (passage_exit_radial_ge_half p hV)

/-- **Passage vertical pur** : `Δβ = 0` si et seulement si les deux membres sont en ligne. -/
theorem vertical_pure_iff_onLine (p : TZeroPassage) (hV : VerticalPassage p) :
    rZeroRadialPosition p.zLaterMember = rZeroRadialPosition p.zEarlierMember ↔
      rZeroRadialPosition p.zEarlierMember = 1 / 2 ∧
        rZeroRadialPosition p.zLaterMember = 1 / 2 := by
  have h1 := passage_entry_radial_le_half p hV
  have h2 := passage_exit_radial_ge_half p hV
  constructor
  · intro h
    constructor <;> linarith
  · rintro ⟨a, b⟩
    rw [a, b]

/-- Un passage vertical est diagonal si et seulement si l'un de ses membres est hors ligne. -/
theorem diagonal_iff_off (p : TZeroPassage) (hV : VerticalPassage p) :
    DiagonalPassage p ↔
      (PIsOffCriticalLine p.zEarlierMember ∨ PIsOffCriticalLine p.zLaterMember) := by
  constructor
  · rintro ⟨_, hlt⟩
    by_contra hcon
    rw [not_or] at hcon
    have he : rZeroRadialPosition p.zEarlierMember = 1 / 2 := not_not.mp hcon.1
    have hl : rZeroRadialPosition p.zLaterMember = 1 / 2 := not_not.mp hcon.2
    rw [he, hl] at hlt
    exact lt_irrefl _ hlt
  · intro h
    refine ⟨hV, lt_of_le_of_ne (vertical_radial_step p hV) ?_⟩
    intro heq
    have hon := (vertical_pure_iff_onLine p hV).mp heq
    rcases h with h | h
    · exact h hon.1
    · exact h hon.2

/-- **La position radiale d'arrivée d'un passage vertical caractérise le régime du passage
suivant** : vertical si et seulement si le membre d'arrivée est en ligne, horizontal si et seulement
s'il est sous la ligne. Le passage suivant `q` est donné ; ce théorème le classe, il ne le construit
pas. -/
theorem vertical_arrival_characterizes {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hp : VerticalPassage p) :
    (VerticalPassage q ↔ rZeroRadialPosition p.zLaterMember = 1 / 2) ∧
      (HorizontalPassage q ↔ rZeroRadialPosition p.zLaterMember < 1 / 2) := by
  refine ⟨⟨fun hq => junction_vertical_vertical hJ hp hq,
    fun h => (onLine_keeps_regime hJ h).mp hp⟩,
    ⟨fun hq => junction_vertical_horizontal hJ hp hq, fun h => ?_⟩⟩
  rcases passage_regime_dichotomy q with ⟨hq, _⟩ | ⟨hq, _⟩
  · exact absurd (junction_vertical_vertical hJ hp hq) (ne_of_lt h)
  · exact hq

/-- **Le régime engagé est gardé** : un membre en ligne atteint par un passage vertical est quitté
par un passage vertical, jamais horizontal. -/
theorem engaged_regime_kept {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hp : VerticalPassage p) (hOn : rZeroRadialPosition p.zLaterMember = 1 / 2) :
    VerticalPassage q ∧ ¬ HorizontalPassage q := by
  have hq : VerticalPassage q := (onLine_keeps_regime hJ hOn).mp hp
  exact ⟨hq, fun hH => absurd hH (ne_of_lt hq)⟩

/-- **Toute entrée en régime horizontal est précédée d'un passage diagonal** : la composante
radiale apparaît pendant le passage vertical qui arrive, pas sur un membre en ligne. -/
theorem regime_entry_diagonal {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hp : VerticalPassage p) (hq : HorizontalPassage q) :
    DiagonalPassage p ∧ rZeroRadialPosition p.zLaterMember < 1 / 2 ∧
      1 / 2 ≤ rZeroRadialPosition p.zEarlierMember := by
  have hl := junction_vertical_horizontal hJ hp hq
  have he := passage_exit_radial_ge_half p hp
  exact ⟨⟨hp, lt_of_lt_of_le hl he⟩, hl, he⟩

/-- **Depuis une chaîne verticale, le passage diagonal part de la ligne** : sur trois passages
consécutifs vertical, vertical, horizontal, le passage du milieu part d'un membre en ligne, fait
avancer la hauteur, et arrive strictement sous la ligne. -/
theorem regime_entry_from_line {o p q : TZeroPassage} (hJ₁ : o.zLaterMember = p.zEarlierMember)
    (hJ₂ : p.zLaterMember = q.zEarlierMember) (ho : VerticalPassage o) (hp : VerticalPassage p)
    (hq : HorizontalPassage q) :
    rZeroRadialPosition p.zEarlierMember = 1 / 2 ∧
      rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
      rZeroRadialPosition p.zLaterMember < 1 / 2 ∧ DiagonalPassage p :=
  ⟨hJ₁ ▸ junction_vertical_vertical hJ₁ ho hp, hp, junction_vertical_horizontal hJ₂ hp hq,
    (regime_entry_diagonal hJ₂ hp hq).1⟩

/-! ## 2. Le certificat lu par la hauteur seule : la fibre -/

/-- À une hauteur donnée, il y a au plus un membre en ligne. -/
theorem fibre_onLine_unique {z w : TNonTrivialZetaZero} (hT : rZeroHeight z = rZeroHeight w)
    (hz : rZeroRadialPosition z = 1 / 2) (hw : rZeroRadialPosition w = 1 / 2) : z = w :=
  Subtype.ext (Complex.ext (hz.trans hw.symm) hT)

/-- **Une fibre est multiple si et seulement si elle contient un membre hors ligne.** -/
theorem fibre_multiple_iff_off (T : ℝ) :
    (∃ z w : TNonTrivialZetaZero, z ≠ w ∧ rZeroHeight z = T ∧ rZeroHeight w = T) ↔
      ∃ z : TNonTrivialZetaZero, rZeroHeight z = T ∧ PIsOffCriticalLine z := by
  constructor
  · rintro ⟨z, w, hne, hz, hw⟩
    by_cases hzOn : rZeroRadialPosition z = 1 / 2
    · refine ⟨w, hw, fun hwOn => hne (fibre_onLine_unique (hz.trans hw.symm) hzOn hwOn)⟩
    · exact ⟨z, hz, hzOn⟩
  · rintro ⟨z, hz, hOff⟩
    refine ⟨z, zMirrorZero z, ?_, hz, (thm_mirror_sameHeight z).trans hz⟩
    intro h
    have hr := thm_mirror_radialPosition z
    rw [← h] at hr
    exact hOff (by linarith)

/-- **Arrivée verticale** : le membre d'arrivée est en ligne si et seulement si la fibre de la
nouvelle hauteur est réduite à lui. -/
theorem vertical_arrival_onLine_iff_fibre_singleton (p : TZeroPassage) (hV : VerticalPassage p) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ↔
      ∀ w : TNonTrivialZetaZero, rZeroHeight w = rZeroHeight p.zLaterMember →
        w = p.zLaterMember := by
  constructor
  · intro hOn w hw
    by_contra hne
    have hwOff : rZeroRadialPosition w ≠ 1 / 2 := fun h => hne (fibre_onLine_unique hw h hOn)
    have key : ∀ u : TNonTrivialZetaZero, rZeroHeight u = rZeroHeight p.zLaterMember →
        rZeroRadialPosition u < 1 / 2 → False := by
      intro u hu hβ
      apply p.hConsecutive.2
      refine ⟨u, ?_, ?_⟩
      · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
        left
        rw [hu]
        exact hV
      · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
        right
        exact ⟨hu, by rw [hOn]; exact hβ⟩
    rcases lt_or_gt_of_ne hwOff with h | h
    · exact key w hw h
    · exact key (zMirrorZero w) ((thm_mirror_sameHeight w).trans hw)
        (by rw [thm_mirror_radialPosition]; linarith)
  · intro h
    have hm := h (zMirrorZero p.zLaterMember) (thm_mirror_sameHeight _)
    have hr := thm_mirror_radialPosition p.zLaterMember
    rw [hm] at hr
    linarith

/-- **Départ vertical** : le membre de départ est en ligne si et seulement si la fibre de sa
hauteur est réduite à lui. -/
theorem vertical_departure_onLine_iff_fibre_singleton (p : TZeroPassage)
    (hV : VerticalPassage p) :
    rZeroRadialPosition p.zEarlierMember = 1 / 2 ↔
      ∀ w : TNonTrivialZetaZero, rZeroHeight w = rZeroHeight p.zEarlierMember →
        w = p.zEarlierMember := by
  constructor
  · intro hOn w hw
    by_contra hne
    have hwOff : rZeroRadialPosition w ≠ 1 / 2 := fun h => hne (fibre_onLine_unique hw h hOn)
    have key : ∀ u : TNonTrivialZetaZero, rZeroHeight u = rZeroHeight p.zEarlierMember →
        1 / 2 < rZeroRadialPosition u → False := by
      intro u hu hβ
      apply p.hConsecutive.2
      refine ⟨u, ?_, ?_⟩
      · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
        right
        exact ⟨hu.symm, by rw [hOn]; exact hβ⟩
      · rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
        left
        rw [hu]
        exact hV
    rcases lt_or_gt_of_ne hwOff with h | h
    · exact key (zMirrorZero w) ((thm_mirror_sameHeight w).trans hw)
        (by rw [thm_mirror_radialPosition]; linarith)
    · exact key w hw h
  · intro h
    have hm := h (zMirrorZero p.zEarlierMember) (thm_mirror_sameHeight _)
    have hr := thm_mirror_radialPosition p.zEarlierMember
    rw [hm] at hr
    linarith

/-- **Borne** : « toute fibre est réduite à un membre » est l'hypothèse de Riemann. -/
theorem riemannHypothesis_iff_fibres_singleton :
    RiemannHypothesis ↔
      ∀ z w : TrueZero, rZeroHeight z.1 = rZeroHeight w.1 → z = w := by
  constructor
  · intro hRH z w hT
    exact trueZero_ext
      ((thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1).trans
        (thm_zeroRadialPosition_half_of_riemannHypothesis hRH w.1).symm) hT
  · intro h
    apply riemannHypothesis_of_noOff
    intro z hOff
    have hm := h z (mirrorMember z) (mirrorMember_ordinate z).symm
    have hr := mirrorMember_radial z
    rw [← hm] at hr
    exact hOff (by linarith)

/-- **Borne** : « aucun passage diagonal, et le plus bas membre ne porte pas de passage
horizontal » est l'hypothèse de Riemann. -/
theorem riemannHypothesis_iff_no_diagonal :
    RiemannHypothesis ↔
      (∀ p : TZeroPassage, ¬ DiagonalPassage p) ∧
      (¬ ∃ q : TZeroPassage, 0 < rZeroHeight q.zEarlierMember ∧
        sUpperZerosBelow q.zEarlierMember = ∅ ∧ HorizontalPassage q) := by
  constructor
  · intro hRH
    refine ⟨?_, (riemannHypothesis_iff_no_regimeEntry.mp hRH).2⟩
    rintro p ⟨_, hlt⟩
    rw [thm_zeroRadialPosition_half_of_riemannHypothesis hRH,
      thm_zeroRadialPosition_half_of_riemannHypothesis hRH] at hlt
    exact lt_irrefl _ hlt
  · rintro ⟨h, hBottom⟩
    refine riemannHypothesis_iff_no_regimeEntry.mpr ⟨?_, hBottom⟩
    rintro ⟨p, q, hJ, hp, hq⟩
    exact h p (regime_entry_diagonal hJ hp hq).1

/-! ## 3. Le détecteur en `T` seul : la ligne est le lieu fixe de la réflexion, `Λ` y est réelle -/

/-- `Λ = ζ · Γ_ℝ` sur `re s > 0`. -/
theorem completedZeta_eq_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
  have hne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  rw [riemannZeta_def_of_ne_zero hs0, div_mul_cancel₀ _ hne]

/-- Le facteur gamma commute à la conjugaison. -/
theorem Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  unfold Gammaℝ
  have hπ : ((Real.pi : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_pos.ne
  have hpow := Complex.conj_cpow (Real.pi : ℂ) (-s / 2) hπ
  rw [Complex.conj_ofReal] at hpow
  have h2 : conj (-s / 2) = -(conj s) / 2 := by rw [map_div₀, map_neg, map_ofNat]
  have h3 : conj (s / 2) = conj s / 2 := by rw [map_div₀, map_ofNat]
  rw [h2] at hpow
  rw [map_mul, ← Complex.Gamma_conj, ← h3, hpow, Complex.conj_conj]

/-- `Λ(s̄) = conj Λ(s)` sur `re s > 0`. -/
theorem completedZeta_conj {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hs' : 0 < (conj s).re := by simpa using hs
  rw [completedZeta_eq_mul hs', completedZeta_eq_mul hs, _root_.riemannZeta_conj, Gammaℝ_conj,
    map_mul]

/-- **Le miroir agit sur `Λ` par conjugaison** : `Λ(1 − s̄) = conj Λ(s)`. Hors de la ligne, il
relie les valeurs en deux points distincts. -/
theorem completedZeta_mirror {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta (1 - conj s) = conj (completedRiemannZeta s) := by
  rw [completedRiemannZeta_one_sub, completedZeta_conj hs]

/-- Le point de la ligne à la hauteur `t`. -/
noncomputable def linePoint (t : ℝ) : ℂ := ⟨1 / 2, t⟩

@[simp] theorem linePoint_re (t : ℝ) : (linePoint t).re = 1 / 2 := rfl
@[simp] theorem linePoint_im (t : ℝ) : (linePoint t).im = t := rfl

/-- Sur la ligne, le miroir est le point lui-même. -/
theorem mirror_linePoint (t : ℝ) : 1 - conj (linePoint t) = linePoint t := by
  apply Complex.ext
  · simp
    norm_num
  · simp

/-- **Sur la ligne, `Λ` est réelle** : le miroir y est l'identité, donc la valeur est égale à sa
conjuguée. La ligne est le lieu fixe de la réflexion `β ↦ 1 − β` : c'est ce point fixe qui réduit la
condition complexe de zéro à une seule équation réelle. -/
theorem completedZeta_real_onLine (t : ℝ) : (completedRiemannZeta (linePoint t)).im = 0 := by
  have h := completedZeta_mirror (s := linePoint t) (by simp)
  rw [mirror_linePoint] at h
  have him := congrArg Complex.im h
  rw [Complex.conj_im] at him
  linarith

/-- **La fonction réelle de la hauteur** : `T ↦ Λ(1/2 + iT)`. -/
noncomputable def lineValue (t : ℝ) : ℝ := (completedRiemannZeta (linePoint t)).re

theorem completedZeta_linePoint (t : ℝ) :
    completedRiemannZeta (linePoint t) = (lineValue t : ℂ) := by
  apply Complex.ext
  · simp [lineValue]
  · simp [completedZeta_real_onLine]

/-- **Sur la ligne, un zéro est une seule équation réelle en `T`.** -/
theorem onLine_zero_iff_lineValue (t : ℝ) :
    PIsNonTrivialZetaZero (linePoint t) ↔ lineValue t = 0 := by
  have h0 : 0 < (linePoint t).re := by simp
  have hz : riemannZeta (linePoint t) = 0 ↔ lineValue t = 0 := by
    rw [← Complex.ofReal_eq_zero, ← completedZeta_linePoint, completedZeta_eq_mul h0, mul_eq_zero,
      or_iff_left (Gammaℝ_ne_zero_of_re_pos h0)]
  constructor
  · intro h
    exact hz.mp h.1
  · intro h
    exact ⟨hz.mpr h, h0, by simp; norm_num⟩

/-- Un membre en ligne annule la fonction réelle à sa hauteur. -/
theorem lineValue_member_onLine (z : TNonTrivialZetaZero)
    (hβ : rZeroRadialPosition z = 1 / 2) : lineValue (rZeroHeight z) = 0 := by
  rw [← onLine_zero_iff_lineValue]
  have hpt : linePoint (rZeroHeight z) = z.1 := Complex.ext hβ.symm rfl
  rw [hpt]
  exact z.2

/-- **La fibre d'une hauteur contient un membre en ligne si et seulement si la fonction réelle
s'y annule.** -/
theorem fibre_has_onLine_member_iff (T : ℝ) :
    (∃ z : TNonTrivialZetaZero, rZeroHeight z = T ∧ rZeroRadialPosition z = 1 / 2) ↔
      lineValue T = 0 := by
  constructor
  · rintro ⟨z, hT, hβ⟩
    rw [← hT]
    exact lineValue_member_onLine z hβ
  · intro h
    exact ⟨⟨linePoint T, (onLine_zero_iff_lineValue T).mpr h⟩, rfl, rfl⟩

/-- **Borne** : à une hauteur où la fonction réelle ne s'annule pas, tout membre est hors ligne.
Le détecteur en `T` ne dit rien d'autre de ces hauteurs. -/
theorem lineValue_ne_zero_fibre_off {T : ℝ} (hT : lineValue T ≠ 0) (z : TNonTrivialZetaZero)
    (hz : rZeroHeight z = T) : PIsOffCriticalLine z := by
  intro hβ
  exact hT (hz ▸ lineValue_member_onLine z hβ)

theorem linePoint_eq (t : ℝ) : linePoint t = (1 / 2 : ℂ) + I * (t : ℂ) := by
  apply Complex.ext
  · simp
  · simp

/-- La fonction réelle de la hauteur est continue. -/
theorem continuous_lineValue : Continuous lineValue := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have h0 : linePoint t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have h1 : linePoint t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have hd := (differentiableAt_completedZeta h0 h1).continuousAt
  have hc : ContinuousAt (fun τ : ℝ => linePoint τ) t := by
    simp only [linePoint_eq]
    fun_prop
  exact Complex.continuous_re.continuousAt.comp (hd.comp hc)

/-- **Détection en `T` seul** : un changement de signe de la fonction réelle entre deux hauteurs
garantit l'existence d'un zéro sur la ligne entre elles (valeurs intermédiaires). -/
theorem onLine_zero_of_sign_change {t₁ t₂ : ℝ} (h12 : t₁ < t₂)
    (h : lineValue t₁ * lineValue t₂ < 0) :
    ∃ t ∈ Ioo t₁ t₂, PIsNonTrivialZetaZero (linePoint t) := by
  have hcont : ContinuousOn lineValue (Icc t₁ t₂) := continuous_lineValue.continuousOn
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨t, ht, hv⟩ := intermediate_value_Ioo' h12.le hcont ⟨hb, ha⟩
    exact ⟨t, ht, (onLine_zero_iff_lineValue t).mpr hv⟩
  · obtain ⟨t, ht, hv⟩ := intermediate_value_Ioo h12.le hcont ⟨ha, hb⟩
    exact ⟨t, ht, (onLine_zero_iff_lineValue t).mpr hv⟩

/-- **Le détecteur certifie un membre en ligne** : entre deux hauteurs positives où la fonction
réelle change de signe, il y a un vrai zéro supérieur sur la ligne. Existence seule : ni la hauteur,
ni l'unicité, ni la consécutivité, ni l'absence d'une fibre hors ligne entre les deux. -/
theorem onLine_member_of_sign_change {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ < t₂)
    (h : lineValue t₁ * lineValue t₂ < 0) :
    ∃ z : TrueZero, rZeroRadialPosition z.1 = 1 / 2 ∧ t₁ < rZeroHeight z.1 ∧
      rZeroHeight z.1 < t₂ := by
  obtain ⟨t, ht, hz⟩ := onLine_zero_of_sign_change h12 h
  exact ⟨⟨⟨linePoint t, hz⟩, lt_of_le_of_lt h0 ht.1⟩, rfl, ht.1, ht.2⟩

#print axioms vertical_pure_iff_onLine
#print axioms diagonal_iff_off
#print axioms vertical_arrival_characterizes
#print axioms engaged_regime_kept
#print axioms regime_entry_diagonal
#print axioms regime_entry_from_line
#print axioms fibre_onLine_unique
#print axioms fibre_multiple_iff_off
#print axioms vertical_arrival_onLine_iff_fibre_singleton
#print axioms vertical_departure_onLine_iff_fibre_singleton
#print axioms riemannHypothesis_iff_fibres_singleton
#print axioms riemannHypothesis_iff_no_diagonal
#print axioms completedZeta_mirror
#print axioms completedZeta_real_onLine
#print axioms onLine_zero_iff_lineValue
#print axioms fibre_has_onLine_member_iff
#print axioms lineValue_ne_zero_fibre_off
#print axioms continuous_lineValue
#print axioms onLine_zero_of_sign_change
#print axioms onLine_member_of_sign_change

end RHV6Fresh
