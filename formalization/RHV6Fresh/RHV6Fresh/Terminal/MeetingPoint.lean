/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.DemonstrationChain
import RHV6Fresh.Terminal.LocalPrimeGapSynchronization

/-!
# Point de rencontre et prémisse unique sur la fréquence (module isolé, non importé par la chaîne)

Objets de l'auteur (2026-10-28) écrits en Lean à partir des seuls faits compilés :

1. **Fréquence d'un membre** : le paramètre de fréquence de son terme conjoint (`residueTerm_joint`).
   Elle vaut la partie imaginaire du zéro, ce que la chaîne appelle « hauteur » : les deux mots désignent
   le même nombre compilé (`memberFrequency_eq_height`). La prémisse de la chaîne est donc déjà une
   prémisse sur la fréquence.
2. **Point de rencontre d'un écart** : unique, à la fin de l'écart (le premier suivant).
3. **Obligation de rencontre** : à ce point, la demande de l'écart est la somme des parts de tous les
   zéros, et la part de chacun est imposée. Ce n'est pas une prémisse : c'est compilé
   (`localSynchronization`, `imposed_joint_gap`).
4. **Prémisse unique** : la fréquence attendue monte à chaque passage, lue au point de rencontre. Elle
   entraîne la prémisse de la chaîne, donc RH. Elle est exactement « aucun passage n'a ses deux
   membres à la même fréquence » (`expectedFrequency_iff_no_shared_frequency`).

Aucun axiome, aucun `sorry`. Rien ici ne touche la chaîne.
-/

namespace RHV6Fresh

open Complex RHV3Lean

/-! ## 1. Fréquence d'un membre -/

/-- Fréquence d'un zéro non trivial : la partie imaginaire de son point, qui est le paramètre `T` de
son terme conjoint (`memberJoint_frequency`). -/
noncomputable def zeroFrequency (z : TNonTrivialZetaZero) : ℝ := (cZeroSupport z).im

/-- La fréquence est le nombre que la chaîne appelle « hauteur ». -/
theorem zeroFrequency_eq_height (z : TNonTrivialZetaZero) : zeroFrequency z = rZeroHeight z := rfl

/-- Fréquence d'un membre (vrai zéro) : le paramètre `T` de son terme conjoint. -/
noncomputable def memberFrequency (z : TrueZero) : ℝ := ((memberIndex z : ExplicitIndex) : ℂ).im

theorem memberFrequency_eq_zeroFrequency (z : TrueZero) : memberFrequency z = zeroFrequency z.1 :=
  zeroPoint_im z

/-- Le terme conjoint d'un membre est porté par sa fréquence (lecture compilée de `memberJoint`). -/
theorem memberJoint_frequency (z : TrueZero) (x : ℝ) :
    memberJoint (memberIndex z) x =
      jointTerm (zetaZeroMultiplicity (zeroPoint z)) (rZeroRadialPosition z.1) (memberFrequency z)
        (smoothingPhase (zeroPoint z)) (‖zeroPoint z‖ * ‖zeroPoint z + 1‖) x := by
  unfold memberJoint memberFrequency memberIndex
  rfl

/-! ## 2. Point de rencontre d'un écart -/

/-- Point de rencontre d'un écart : unique, à la fin de l'écart (le premier suivant). -/
noncomputable def meetingPoint (I : PrimeGapInterval) : ℝ := I.upper

theorem meetingPoint_eq_upper (I : PrimeGapInterval) : meetingPoint I = fnPrimeAtRank (I.rank + 1) := rfl

theorem meetingPoint_gt_lower (I : PrimeGapInterval) : I.lower < meetingPoint I := I.lower_lt_upper

theorem one_lt_meetingPoint (I : PrimeGapInterval) : 1 < meetingPoint I := I.one_lt_upper

/-- Unicité : le point de rencontre d'un écart est déterminé par l'écart. -/
theorem meetingPoint_unique (I J : PrimeGapInterval) (h : I.rank = J.rank) : meetingPoint I = meetingPoint J := by
  unfold meetingPoint PrimeGapInterval.upper; rw [h]

/-! ## 3. Obligation de rencontre (compilée, pas une prémisse) -/

/-- Part imposée d'un membre sur un écart : incrément de son terme conjoint entre le début de l'écart et
le point de rencontre. -/
noncomputable def imposedShare (w : TrueZero) (I : PrimeGapInterval) : ℂ :=
  memberJoint (memberIndex w) (meetingPoint I) - memberJoint (memberIndex w) I.lower

/-- **Chaque zéro connaît sa part exacte** : la part imposée est l'incrément de la courbe des premiers sur
l'écart moins l'incrément des autres (compilé : `imposed_joint_gap`). -/
theorem imposedShare_eq (w : TrueZero) (I : PrimeGapInterval) :
    imposedShare w I =
      (smoothedRemainder (meetingPoint I) - smoothedRemainder I.lower) -
        (othersSum w (meetingPoint I) - othersSum w I.lower) :=
  imposed_joint_gap w I.rank

/-- **Tous les signaux se rencontrent au point de rencontre** : la demande de l'écart est la somme des
parts de tous les zéros (compilé : `localSynchronization`). -/
theorem all_signals_meet (I : PrimeGapInterval) :
    localArithmeticTarget I = ∑' ρ : ExplicitIndex, smoothedLocalContribution ρ I :=
  localSynchronization I

/-! ## 4. Prémisse unique sur la fréquence -/

/-- **Prémisse unique (auteur)** : la fréquence attendue monte à chaque passage. -/
def ExpectedFrequencyRisesAtMeetings : Prop :=
  ∀ p : TZeroPassage, zeroFrequency p.zEarlierMember < zeroFrequency p.zLaterMember

/-- La prémisse unique entraîne la prémisse de la chaîne. -/
theorem expectedFrequencyRises_of_meetings (h : ExpectedFrequencyRisesAtMeetings) :
    ExpectedFrequencyRises := h

/-- Et réciproquement : les deux prémisses sont le même énoncé, lu en fréquence ou en hauteur. -/
theorem expectedFrequencyRisesAtMeetings_iff :
    ExpectedFrequencyRisesAtMeetings ↔ ExpectedFrequencyRises := Iff.rfl

/-- Sur les membres (hauteur positive), la prémisse se lit sur la fréquence du terme conjoint. -/
theorem memberFrequency_lt_of_meetings (h : ExpectedFrequencyRisesAtMeetings) (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    memberFrequency ⟨p.zEarlierMember, hE⟩ < memberFrequency ⟨p.zLaterMember, hL⟩ :=
  (memberFrequency_eq_zeroFrequency ⟨p.zEarlierMember, hE⟩).trans_lt
    ((h p).trans_eq (memberFrequency_eq_zeroFrequency ⟨p.zLaterMember, hL⟩).symm)

/-- **La prémisse unique entraîne RH** (par la chaîne, inchangée). Conditionnel : la prémisse est posée. -/
theorem riemannHypothesis_of_meetings (h : ExpectedFrequencyRisesAtMeetings) : RiemannHypothesis :=
  riemannHypothesis_terminal (expectedFrequencyRises_of_meetings h)

/-- **Ce qui reste exactement à dériver** : la prémisse unique équivaut à « aucun passage n'a ses deux
membres à la même fréquence ». Sur un passage, l'ordre canonique donne soit la fréquence qui monte, soit
la même fréquence avec la position radiale qui monte ; seul le second cas la met en échec. -/
theorem expectedFrequency_iff_no_shared_frequency :
    ExpectedFrequencyRisesAtMeetings ↔
      ∀ p : TZeroPassage, rZeroHeight p.zEarlierMember ≠ rZeroHeight p.zLaterMember := by
  constructor
  · intro h p
    exact ne_of_lt (h p)
  · intro h p
    rcases (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mp p.precedes with hlt | ⟨heq, _⟩
    · exact hlt
    · exact absurd heq (h p)

/-- Un passage à fréquence partagée est un passage dont le membre postérieur est strictement plus à droite
radialement : le seul cas qui échappe à la prémisse. -/
theorem shared_frequency_passage_profile (p : TZeroPassage)
    (h : rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember) :
    rZeroRadialPosition p.zEarlierMember < rZeroRadialPosition p.zLaterMember := by
  rcases (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mp p.precedes with hlt | ⟨_, hr⟩
  · exact absurd h (ne_of_lt hlt)
  · exact hr

/-! ## 5. Le cas restant lu sur le calage (compilé) -/

/-- À fréquence fixée, le calage lissé décroît strictement avec la position radiale. -/
theorem smoothingPhase_strictAnti_radial {β β' T : ℝ} (hβ : 0 < β) (h : β < β') (hT : 0 < T) :
    smoothingPhase ⟨β', T⟩ < smoothingPhase ⟨β, T⟩ := by
  unfold smoothingPhase
  apply add_lt_add <;> apply Real.arctan_strictMono <;> apply div_lt_div_of_pos_left hT <;> simp <;> linarith

/-- **Même fréquence et même calage ⇒ même position radiale** : à fréquence partagée, le calage sépare. -/
theorem radial_eq_of_shared_frequency_phase {β β' T : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (hT : 0 < T)
    (h : smoothingPhase ⟨β, T⟩ = smoothingPhase ⟨β', T⟩) : β = β' := by
  rcases lt_trichotomy β β' with hlt | heq | hgt
  · exact absurd h (ne_of_gt (smoothingPhase_strictAnti_radial hβ hlt hT))
  · exact heq
  · exact absurd h (ne_of_lt (smoothingPhase_strictAnti_radial hβ' hgt hT))

/-- **Profil complet du seul cas restant** : deux membres à la même fréquence, le second strictement
plus à droite (c'est le profil d'un passage à fréquence partagée, `shared_frequency_passage_profile`),
ont des calages distincts : celui du second est strictement plus petit. À fréquence égale, parmi
amplitude, fréquence et calage, le calage sépare toujours les deux membres. -/
theorem shared_frequency_members_phase (e l : TrueZero)
    (h : rZeroHeight e.1 = rZeroHeight l.1)
    (hr : rZeroRadialPosition e.1 < rZeroRadialPosition l.1) :
    smoothingPhase (zeroPoint l) < smoothingPhase (zeroPoint e) := by
  rw [smoothingPhase_zeroPoint, smoothingPhase_zeroPoint, ← h]
  exact smoothingPhase_strictAnti_radial (thm_zeroRadialPosition_positive _) hr e.2

/-! ## 6. Rencontres d'un membre et fréquence partagée -/

/-- Le calage lissé d'un point de hauteur positive est strictement positif. -/
theorem smoothingPhase_pos {β T : ℝ} (hβ : 0 < β) (hT : 0 < T) : 0 < smoothingPhase ⟨β, T⟩ := by
  show 0 < Real.arctan (T / β) + Real.arctan (T / (β + 1))
  have h1 : 0 < Real.arctan (T / β) := by
    rw [← Real.arctan_zero]; exact Real.arctan_strictMono (div_pos hT hβ)
  have h2 : 0 < Real.arctan (T / (β + 1)) := by
    rw [← Real.arctan_zero]; exact Real.arctan_strictMono (div_pos hT (by linarith))
  linarith

/-- Le calage lissé est strictement inférieur à `π`. -/
theorem smoothingPhase_lt_pi (β T : ℝ) : smoothingPhase ⟨β, T⟩ < Real.pi := by
  show Real.arctan (T / β) + Real.arctan (T / (β + 1)) < Real.pi
  linarith [Real.arctan_lt_pi_div_two (T / β), Real.arctan_lt_pi_div_two (T / (β + 1))]

/-- **Deux membres à la même fréquence ne partagent aucune rencontre** : leurs réseaux de rencontres
lissées, de même pas `π/T`, sont décalés d'une fraction strictement positive et strictement inférieure
à un pas (le décalage des calages, dans `]0, π[`). -/
theorem shared_frequency_no_common_meeting (e l : TrueZero)
    (h : rZeroHeight e.1 = rZeroHeight l.1)
    (hr : rZeroRadialPosition e.1 < rZeroRadialPosition l.1) (k k' : ℤ) :
    smoothedMeeting (zeroPoint e) k ≠ smoothedMeeting (zeroPoint l) k' := by
  intro heq
  have hT : 0 < (zeroPoint e).im := by rw [zeroPoint_im]; exact e.2
  have hIm : (zeroPoint l).im = (zeroPoint e).im := by rw [zeroPoint_im, zeroPoint_im, h]
  unfold smoothedMeeting at heq
  rw [hIm] at heq
  have h' := Real.exp_injective heq
  rw [div_left_inj' hT.ne'] at h'
  have hlt := shared_frequency_members_phase e l h hr
  have hpos : 0 < smoothingPhase (zeroPoint l) := by
    rw [smoothingPhase_zeroPoint]; exact smoothingPhase_pos (thm_zeroRadialPosition_positive _) l.2
  have hpi : smoothingPhase (zeroPoint e) < Real.pi := by
    rw [smoothingPhase_zeroPoint]; exact smoothingPhase_lt_pi _ _
  have hn : smoothingPhase (zeroPoint e) - smoothingPhase (zeroPoint l) = ((k' - k : ℤ) : ℝ) * Real.pi := by
    push_cast; linarith
  have hπ := Real.pi_pos
  have h0 : (0 : ℝ) < ((k' - k : ℤ) : ℝ) := by
    by_contra hc
    push_neg at hc
    have := mul_nonpos_of_nonpos_of_nonneg hc hπ.le
    linarith
  have h1 : ((k' - k : ℤ) : ℝ) < 1 := by
    by_contra hc
    push_neg at hc
    have := mul_le_mul_of_nonneg_right hc hπ.le
    linarith
  have h0' : (0 : ℤ) < k' - k := by exact_mod_cast h0
  have h1' : k' - k < 1 := by exact_mod_cast h1
  omega

/-- Part d'un membre au point de rencontre d'un écart, lue sur ses trois paramètres : amplitude
`x^β/N`, fréquence `T`, calage `θ`, au point `x = ` premier suivant (`memberJoint_frequency`). -/
theorem imposedShare_at_meeting (w : TrueZero) (I : PrimeGapInterval) :
    imposedShare w I =
      jointTerm (zetaZeroMultiplicity (zeroPoint w)) (rZeroRadialPosition w.1) (memberFrequency w)
          (smoothingPhase (zeroPoint w)) (‖zeroPoint w‖ * ‖zeroPoint w + 1‖) (meetingPoint I) -
        jointTerm (zetaZeroMultiplicity (zeroPoint w)) (rZeroRadialPosition w.1) (memberFrequency w)
          (smoothingPhase (zeroPoint w)) (‖zeroPoint w‖ * ‖zeroPoint w + 1‖) I.lower := by
  unfold imposedShare
  rw [memberJoint_frequency, memberJoint_frequency]

/-! ## 7. Ancrage : depuis un membre ON, la fréquence ne peut pas être partagée -/

/-- Sur un passage à fréquence partagée dont le membre antérieur est ON, le postérieur `l` est au-dessus
d'un demi, donc son miroir (même fréquence, sous un demi) précède le membre antérieur. -/
theorem mirror_precedes_earlier_of_shared_frequency (p : TZeroPassage) (l : TrueZero)
    (hl : l.1 = p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (h : rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember) :
    PZeroMemberPrecedes (mirrorMember l).1 p.zEarlierMember := by
  have hr := shared_frequency_passage_profile p h
  have hr' : 1 / 2 < rZeroRadialPosition p.zLaterMember := hOn ▸ hr
  rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
  right
  refine ⟨?_, ?_⟩
  · rw [mirrorMember_ordinate, hl]; exact h.symm
  · rw [mirrorMember_radial, hl, hOn]; linarith

/-- Le miroir du postérieur précède aussi le postérieur lui-même. -/
theorem mirror_precedes_later_of_shared_frequency (p : TZeroPassage) (l : TrueZero)
    (hl : l.1 = p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (h : rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember) :
    PZeroMemberPrecedes (mirrorMember l).1 p.zLaterMember := by
  have hr := shared_frequency_passage_profile p h
  have hr' : 1 / 2 < rZeroRadialPosition p.zLaterMember := hOn ▸ hr
  rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
  right
  refine ⟨?_, ?_⟩
  · rw [mirrorMember_ordinate, hl]
  · rw [mirrorMember_radial, hl]; linarith

/-- **Historique ON ⇒ fréquence non partagée** : si l'antérieur est ON et si tout membre précédant le
postérieur est ON, les deux membres n'ont pas la même fréquence. C'est, sur ce passage, la prémisse
unique dérivée des seuls faits compilés. -/
theorem no_shared_frequency_of_history_onLine (p : TZeroPassage) (l : TrueZero)
    (hl : l.1 = p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hHist : ∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) :
    rZeroHeight p.zEarlierMember ≠ rZeroHeight p.zLaterMember := by
  intro h
  have hm := hHist _ (mirror_precedes_later_of_shared_frequency p l hl hOn h)
  rw [mirrorMember_radial, hl] at hm
  have hr := shared_frequency_passage_profile p h
  rw [hOn] at hr
  linarith

/-- **Ancrage** : le premier passage, depuis le premier zéro canonique (ON, rien en dessous), ne partage
pas sa fréquence. Le premier zéro démarre le régime : la fréquence monte dès le premier passage. -/
theorem first_passage_no_shared_frequency (p : TZeroPassage) (l : TrueZero)
    (hl : l.1 = p.zLaterMember) (hFirst : p.zEarlierMember = (canonicalZero 1).1) :
    rZeroHeight p.zEarlierMember ≠ rZeroHeight p.zLaterMember := by
  intro h
  have hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2 := by rw [hFirst]; exact anchor_canonical_one
  have hpre := mirror_precedes_earlier_of_shared_frequency p l hl hOn h
  have hmem : (mirrorMember l).1 ∈ sUpperZerosBelow (canonicalZero 1).1 := by
    refine ⟨(mirrorMember l).2, ?_⟩
    rw [← hFirst]; exact hpre
  rw [anchor_bottom] at hmem
  exact hmem

/-- Sur un passage dont l'antérieur est ON et l'historique ON, la fréquence monte strictement. -/
theorem frequency_rises_of_history_onLine (p : TZeroPassage) (l : TrueZero)
    (hl : l.1 = p.zLaterMember)
    (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hHist : ∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) :
    zeroFrequency p.zEarlierMember < zeroFrequency p.zLaterMember := by
  rcases (thm_zeroMemberPrecedes_iff_height_radial_lex _ _).mp p.precedes with hlt | ⟨heq, _⟩
  · exact hlt
  · exact absurd heq (no_shared_frequency_of_history_onLine p l hl hOn hHist)

/-! ## 8. Ce que l'ordre seul impose à l'arrivée, et ce qu'il laisse ouvert -/

/-- **Historique ON ⇒ l'arrivée n'est jamais au-dessus d'un demi** : si elle l'était, son miroir (même
fréquence, sous un demi) la précéderait et serait ON, ce qui la mettrait sur la ligne. -/
theorem later_le_half_of_history_onLine (p : TZeroPassage) (l : TrueZero) (hl : l.1 = p.zLaterMember)
    (hHist : ∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) :
    rZeroRadialPosition p.zLaterMember ≤ 1 / 2 := by
  by_contra hgt
  push_neg at hgt
  have hpre : PZeroMemberPrecedes (mirrorMember l).1 p.zLaterMember := by
    rw [thm_zeroMemberPrecedes_iff_height_radial_lex]
    right
    refine ⟨?_, ?_⟩
    · rw [mirrorMember_ordinate, hl]
    · rw [mirrorMember_radial, hl]; linarith
  have hm := hHist _ hpre
  rw [mirrorMember_radial, hl] at hm
  linarith

/-- **Dichotomie de l'arrivée** : sous historique ON, l'arrivée est sur la ligne ou strictement en
dessous. Le cas « sur la ligne » relance la montée de fréquence au pas suivant (`frequency_rises_of_history_onLine`)
dès que l'historique s'étend ; le cas « en dessous » est l'arrivée basse, dont le pas suivant vers son
miroir est, par l'ordre même, un passage à fréquence partagée. C'est le seul point ouvert. -/
theorem arrival_onLine_or_low (p : TZeroPassage) (l : TrueZero) (hl : l.1 = p.zLaterMember)
    (hHist : ∀ w : TrueZero, PZeroMemberPrecedes w.1 p.zLaterMember → rZeroRadialPosition w.1 = 1 / 2) :
    rZeroRadialPosition p.zLaterMember = 1 / 2 ∨ rZeroRadialPosition p.zLaterMember < 1 / 2 :=
  (lt_or_eq_of_le (later_le_half_of_history_onLine p l hl hHist)).elim Or.inr Or.inl

/-- Une arrivée basse et son miroir ont la même fréquence : le passage de l'une à l'autre, s'il est un
passage, partage sa fréquence. Rien dans l'ordre ne l'exclut ; c'est ce que la prémisse unique affirme. -/
theorem low_arrival_mirror_shares_frequency (l : TrueZero) :
    zeroFrequency (mirrorMember l).1 = zeroFrequency l.1 :=
  mirrorMember_ordinate l

/-! ## 9. Amplitude relative d'une part entre rencontres : constante si et seulement si sur la ligne

Lecture E393 (2026-10-28) : lu comme un seul ON, le couple « arrivée basse + miroir » retombe sur sa
fréquence, garde un calage petit, mais son amplitude dérive d'une rencontre à l'autre. L'objet exact est
ici : l'amplitude d'un membre rapportée à l'amplitude de référence de la ligne, `x^(1/2)`, lue aux points
de rencontre. Elle est constante entre rencontres si et seulement si la position radiale est un demi. -/

/-- Module du terme conjoint : `|m| · |x^β / N|`. -/
theorem jointTerm_norm_eq (m β T θ N x : ℝ) :
    ‖jointTerm m β T θ N x‖ = |m| * |x ^ β / N| := by
  unfold jointTerm
  simp only [norm_neg, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs,
    mul_one]

theorem memberDenominator_pos (w : TrueZero) : 0 < ‖zeroPoint w‖ * ‖zeroPoint w + 1‖ :=
  mul_pos (norm_zeroPoint_pos w) (norm_pos_iff.mpr (zeroPoint_add_one_ne_zero w))

theorem memberMultiplicity_pos (w : TrueZero) : (0 : ℝ) < zetaZeroMultiplicity (zeroPoint w) := by
  exact_mod_cast zetaZeroMultiplicity_pos w.1.2.1

/-- Amplitude d'un membre au point `x` : le module de son terme conjoint. -/
noncomputable def memberAmplitude (w : TrueZero) (x : ℝ) : ℝ := ‖memberJoint (memberIndex w) x‖

/-- L'amplitude d'un membre est `m · x^β / N` (lecture compilée du terme conjoint). -/
theorem memberAmplitude_eq (w : TrueZero) {x : ℝ} (hx : 0 < x) :
    memberAmplitude w x =
      (zetaZeroMultiplicity (zeroPoint w) : ℝ) * x ^ rZeroRadialPosition w.1 /
        (‖zeroPoint w‖ * ‖zeroPoint w + 1‖) := by
  unfold memberAmplitude
  rw [memberJoint_frequency, jointTerm_norm_eq]
  have hm : (0 : ℝ) ≤ zetaZeroMultiplicity (zeroPoint w) := Nat.cast_nonneg _
  have hq : 0 < x ^ rZeroRadialPosition w.1 / (‖zeroPoint w‖ * ‖zeroPoint w + 1‖) :=
    div_pos (Real.rpow_pos_of_pos hx _) (memberDenominator_pos w)
  rw [abs_of_nonneg hm, abs_of_pos hq]
  ring

/-- Amplitude relative d'un membre au point `x` : son amplitude rapportée à l'amplitude de référence de
la ligne, `x^(1/2)`. -/
noncomputable def relativeAmplitude (w : TrueZero) (x : ℝ) : ℝ :=
  memberAmplitude w x / x ^ (1 / 2 : ℝ)

/-- L'amplitude relative vaut `(m/N) · x^(β − 1/2)` : elle ne dépend de `x` que par l'écart de la
position radiale à un demi. -/
theorem relativeAmplitude_eq (w : TrueZero) {x : ℝ} (hx : 0 < x) :
    relativeAmplitude w x =
      ((zetaZeroMultiplicity (zeroPoint w) : ℝ) / (‖zeroPoint w‖ * ‖zeroPoint w + 1‖)) *
        x ^ (rZeroRadialPosition w.1 - 1 / 2) := by
  unfold relativeAmplitude
  rw [memberAmplitude_eq w hx, Real.rpow_sub hx]
  have h1 : x ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have hN : ‖zeroPoint w‖ * ‖zeroPoint w + 1‖ ≠ 0 := (memberDenominator_pos w).ne'
  field_simp

/-- **Amplitude relative constante entre rencontres** : la part d'un membre a la même amplitude relative
à tous les points de rencontre. -/
def ConstantRelativeAmplitudeAtMeetings (w : TrueZero) : Prop :=
  ∀ I J : PrimeGapInterval, relativeAmplitude w (meetingPoint I) = relativeAmplitude w (meetingPoint J)

/-- Deux points de rencontre distincts : ceux des écarts de rang 0 et 1. -/
theorem meetingPoint_zero_lt_one : meetingPoint ⟨0⟩ < meetingPoint ⟨1⟩ := by
  unfold meetingPoint PrimeGapInterval.upper
  exact_mod_cast thm_primeAtRank_strictMono (show 0 + 1 < 1 + 1 by norm_num)

/-- Sur deux positions `0 < x₁ < x₂`, `x₁^c = x₂^c` force `c = 0`. -/
theorem exponent_zero_of_rpow_eq {c x₁ x₂ : ℝ} (h₁ : 0 < x₁) (h : x₁ < x₂) (heq : x₁ ^ c = x₂ ^ c) :
    c = 0 := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · exact absurd heq (ne_of_gt (Real.rpow_lt_rpow_of_neg h₁ h hc))
  · exact hc
  · exact absurd heq (ne_of_lt (Real.rpow_lt_rpow h₁.le h hc))

/-- **Théorème** : la part d'un membre a une amplitude relative constante entre rencontres si et
seulement si sa position radiale est un demi. Deux rencontres suffisent à le lire. -/
theorem constantRelativeAmplitude_iff_onLine (w : TrueZero) :
    ConstantRelativeAmplitudeAtMeetings w ↔ rZeroRadialPosition w.1 = 1 / 2 := by
  constructor
  · intro h
    have h01 := h ⟨0⟩ ⟨1⟩
    have hx0 : 0 < meetingPoint ⟨0⟩ := by linarith [one_lt_meetingPoint ⟨0⟩]
    have hx1 : 0 < meetingPoint ⟨1⟩ := by linarith [one_lt_meetingPoint ⟨1⟩]
    rw [relativeAmplitude_eq w hx0, relativeAmplitude_eq w hx1] at h01
    have hK : 0 < (zetaZeroMultiplicity (zeroPoint w) : ℝ) / (‖zeroPoint w‖ * ‖zeroPoint w + 1‖) :=
      div_pos (memberMultiplicity_pos w) (memberDenominator_pos w)
    have hc := exponent_zero_of_rpow_eq hx0 meetingPoint_zero_lt_one (mul_left_cancel₀ hK.ne' h01)
    linarith
  · intro h I J
    have hI : 0 < meetingPoint I := by linarith [one_lt_meetingPoint I]
    have hJ : 0 < meetingPoint J := by linarith [one_lt_meetingPoint J]
    rw [relativeAmplitude_eq w hI, relativeAmplitude_eq w hJ, h, sub_self, Real.rpow_zero, Real.rpow_zero]

/-- **Sens de la dérive, arrivée basse** : sous un demi, l'amplitude relative décroît strictement d'une
position à la suivante. -/
theorem relativeAmplitude_strictAnti_of_low (w : TrueZero) (hlow : rZeroRadialPosition w.1 < 1 / 2)
    {x₁ x₂ : ℝ} (h₁ : 0 < x₁) (h : x₁ < x₂) : relativeAmplitude w x₂ < relativeAmplitude w x₁ := by
  rw [relativeAmplitude_eq w h₁, relativeAmplitude_eq w (h₁.trans h)]
  have hK : 0 < (zetaZeroMultiplicity (zeroPoint w) : ℝ) / (‖zeroPoint w‖ * ‖zeroPoint w + 1‖) :=
    div_pos (memberMultiplicity_pos w) (memberDenominator_pos w)
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg h₁ h (by linarith)) hK

/-- **Sens de la dérive, membre au-dessus d'un demi (le miroir)** : l'amplitude relative croît strictement. -/
theorem relativeAmplitude_strictMono_of_high (w : TrueZero) (hhigh : 1 / 2 < rZeroRadialPosition w.1)
    {x₁ x₂ : ℝ} (h₁ : 0 < x₁) (h : x₁ < x₂) : relativeAmplitude w x₁ < relativeAmplitude w x₂ := by
  rw [relativeAmplitude_eq w h₁, relativeAmplitude_eq w (h₁.trans h)]
  have hK : 0 < (zetaZeroMultiplicity (zeroPoint w) : ℝ) / (‖zeroPoint w‖ * ‖zeroPoint w + 1‖) :=
    div_pos (memberMultiplicity_pos w) (memberDenominator_pos w)
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow h₁.le h (by linarith)) hK

/-- **Le couple à fréquence partagée n'a pas cette propriété, membre par membre** : l'arrivée basse
(position radiale strictement sous un demi) n'a pas d'amplitude relative constante entre rencontres. -/
theorem low_arrival_not_constantRelativeAmplitude (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2) :
    ¬ ConstantRelativeAmplitudeAtMeetings l :=
  fun h => absurd ((constantRelativeAmplitude_iff_onLine l).mp h) (ne_of_lt hlow)

/-- Son miroir (même fréquence, position un moins l'autre) non plus. -/
theorem mirror_not_constantRelativeAmplitude (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2) :
    ¬ ConstantRelativeAmplitudeAtMeetings (mirrorMember l) := by
  intro h
  have := (constantRelativeAmplitude_iff_onLine _).mp h
  rw [mirrorMember_radial] at this
  linarith

/-- Part conjointe du couple (arrivée basse et miroir) au point `x`. -/
noncomputable def pairJoint (l : TrueZero) (x : ℝ) : ℂ :=
  memberJoint (memberIndex l) x + memberJoint (memberIndex (mirrorMember l)) x

/-- Amplitude relative du couple : le module de sa part conjointe rapporté à `x^(1/2)`. -/
noncomputable def pairRelativeAmplitude (l : TrueZero) (x : ℝ) : ℝ := ‖pairJoint l x‖ / x ^ (1 / 2 : ℝ)

/-- L'amplitude relative du couple domine celle du miroir moins celle de l'arrivée basse. -/
theorem pairRelativeAmplitude_ge (l : TrueZero) {x : ℝ} (hx : 0 < x) :
    relativeAmplitude (mirrorMember l) x - relativeAmplitude l x ≤ pairRelativeAmplitude l x := by
  unfold pairRelativeAmplitude pairJoint relativeAmplitude memberAmplitude
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ (Real.rpow_pos_of_pos hx _).le
  have := norm_sub_le (memberJoint (memberIndex l) x + memberJoint (memberIndex (mirrorMember l)) x)
    (memberJoint (memberIndex l) x)
  rw [add_sub_cancel_left] at this
  linarith

/-- **Le couple lui-même n'a pas d'amplitude relative bornée aux rencontres** : pour toute borne, un point
de rencontre la dépasse. En particulier l'amplitude relative du couple n'est constante sur aucune lecture
« comme un ON ». C'est la dérive mesurée en E393, ici compilée. -/
theorem pairRelativeAmplitude_unbounded (l : TrueZero) (hlow : rZeroRadialPosition l.1 < 1 / 2) (c : ℝ) :
    ∃ I : PrimeGapInterval, c < pairRelativeAmplitude l (meetingPoint I) := by
  set δ : ℝ := 1 / 2 - rZeroRadialPosition l.1 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set Kp : ℝ := (zetaZeroMultiplicity (zeroPoint (mirrorMember l)) : ℝ) /
    (‖zeroPoint (mirrorMember l)‖ * ‖zeroPoint (mirrorMember l) + 1‖) with hKp
  set Km : ℝ := (zetaZeroMultiplicity (zeroPoint l) : ℝ) / (‖zeroPoint l‖ * ‖zeroPoint l + 1‖) with hKm
  have hKp0 : 0 < Kp := div_pos (memberMultiplicity_pos _) (memberDenominator_pos _)
  have hKm0 : 0 < Km := div_pos (memberMultiplicity_pos _) (memberDenominator_pos _)
  -- les points de rencontre tendent vers l'infini, donc leur puissance `δ` aussi
  have hP : Filter.Tendsto (fun n : ℕ => (fnPrimeAtRank (n + 1) : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop.comp thm_primeAtRank_strictMono.tendsto_atTop).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hR : Filter.Tendsto (fun n : ℕ => (fnPrimeAtRank (n + 1) : ℝ) ^ δ) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hδpos).comp hP
  obtain ⟨n, hn⟩ := (hR.eventually_gt_atTop ((c + Km) / Kp)).exists
  refine ⟨⟨n⟩, ?_⟩
  have hx1 : 1 < meetingPoint ⟨n⟩ := one_lt_meetingPoint ⟨n⟩
  have hx : 0 < meetingPoint ⟨n⟩ := by linarith
  have hmeet : meetingPoint ⟨n⟩ = (fnPrimeAtRank (n + 1) : ℝ) := rfl
  refine lt_of_lt_of_le ?_ (pairRelativeAmplitude_ge l hx)
  rw [relativeAmplitude_eq _ hx, relativeAmplitude_eq _ hx, mirrorMember_radial]
  have e1 : 1 - rZeroRadialPosition l.1 - 1 / 2 = δ := by rw [hδ]; ring
  have e2 : rZeroRadialPosition l.1 - 1 / 2 = -δ := by rw [hδ]; ring
  rw [e1, e2, ← hKp, ← hKm]
  have hlow1 : meetingPoint ⟨n⟩ ^ (-δ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
  have hbig : (c + Km) / Kp < meetingPoint ⟨n⟩ ^ δ := by rw [hmeet]; exact hn
  have hbig' : c + Km < Kp * meetingPoint ⟨n⟩ ^ δ := by
    rwa [div_lt_iff₀ hKp0, mul_comm] at hbig
  nlinarith [mul_le_mul_of_nonneg_left hlow1 hKm0.le]

end RHV6Fresh

#print axioms RHV6Fresh.riemannHypothesis_of_meetings
#print axioms RHV6Fresh.expectedFrequency_iff_no_shared_frequency
#print axioms RHV6Fresh.imposedShare_eq
#print axioms RHV6Fresh.shared_frequency_members_phase
#print axioms RHV6Fresh.shared_frequency_no_common_meeting
#print axioms RHV6Fresh.imposedShare_at_meeting
#print axioms RHV6Fresh.no_shared_frequency_of_history_onLine
#print axioms RHV6Fresh.first_passage_no_shared_frequency
#print axioms RHV6Fresh.frequency_rises_of_history_onLine
#print axioms RHV6Fresh.later_le_half_of_history_onLine
#print axioms RHV6Fresh.constantRelativeAmplitude_iff_onLine
#print axioms RHV6Fresh.low_arrival_not_constantRelativeAmplitude
#print axioms RHV6Fresh.mirror_not_constantRelativeAmplitude
#print axioms RHV6Fresh.pairRelativeAmplitude_unbounded
