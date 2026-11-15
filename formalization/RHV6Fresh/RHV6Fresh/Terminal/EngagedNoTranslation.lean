/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.EngagedRadialFloor
import RHV6Fresh.Terminal.TowerWinding
import RHV6Fresh.Terminal.FirstZeroField
import RHV6Fresh.Terminal.OneZeroOnePrime
import RHV6Fresh.Terminal.TowerGrid
import RHV6Fresh.Terminal.RegimeTower
import RHV6Fresh.Terminal.DoubleRigidity
import RHV6Fresh.Terminal.FixedExponentField

/-!
# RHV6Fresh — enroulement imposé, captivité au raccord, succession : la translation de la grille d'arrivée
(réalignement de l'auteur, 2026-10-04)

Réalignement de l'auteur : il n'y a aucune « diagonale » dans zêta. Un membre n'a que deux coordonnées, la
position radiale `β` et la hauteur `T`. Sur un pas parti de l'état engagé, la hauteur avance : c'est un
enroulement (pas contracté, contacts qui se referment). Une position radiale différente n'est pas un second
mouvement : c'est une translation rigide de toute la grille d'arrivée, par un facteur unique `λ` (le facteur
radial). La flèche à certifier est

    enroulement imposé + captivité énergétique au raccord + succession EV + 1  ⟹  λ = 1,

et `λ = 1` ⟺ grille non translatée ⟺ `β_l = 1/2` (`onLine_iff_no_grid_translation`).

Ce module COMPOSE les théorèmes déjà compilés (aucun n'est redémontré) :

* succession : `eventIndex_succ_of_passage`, `expectedMinimumPrime_succ_of_passage` ;
* hauteur et position radiale : `passage_entry_radial_le_half` ;
* enroulement : `vertical_iff_pitch_contracts`, `windingContact_strictAnti_height`,
  `prime_axis_nesting_any_depth` ;
* captivité au raccord exact : `height_advance_local_budget` ;
* translation rigide : `contact_eq_line_mul_radial`, `radialFactor_eq_one_iff`,
  `towerPosition_eq_line_add_residue`, `onLine_iff_no_grid_translation` ;
* sinus et cosinus : `zeroTerm_real_iff_ray` (les contacts sont les annulations de la partie imaginaire).

* **§1 Les trois lectures de la translation** (`grid_translation_readings`).
* **§2 L'enroulement entre deux Tours** : `WindingNested e l`, contacts d'indice `k ≥ 1` de la Tour
  d'arrivée strictement en deçà de ceux de la Tour de départ. Deux Tours en ligne : emboîtées dès que la
  hauteur avance (`windingNested_of_onLine`). Départ en ligne : emboîtement ⟺ la translation est sous le
  rapport des contacts de ligne, indice par indice (`windingNested_iff_translation_bound`) ; l'emboîtement
  n'est donc PAS indépendant de la translation : il la borne. Emboîtement perdu ⟹ grille translatée
  (`translation_of_not_nested`). Profondeur de hauteur suffisante : emboîtement à cet indice pour toutes
  positions radiales (`windingNested_index_of_depth`).
* **§3 Le pas engagé, tout ensemble** (`engaged_step_combined`) et la fenêtre de la translation capturée
  (`engaged_nested_translation_window`) : `1 ≤ λ` et `λ·C_1^{ligne}(T_l) < C_1^{ligne}(T_e)`.
* **§4 La cible, découpée** : loi locale de conservation ⟺ (emboîtement sur tout pas engagé) ∧ (pas engagé
  + succession + captivité + emboîtement ⟹ grille non translatée)
  (`conservation_iff_nested_and_noTranslation`).

* **§5 La place de la Tour suivante, et de toutes les autres** (paramètre de l'auteur : la Tour s'enroule en
  laissant la place à la suivante, jusqu'à l'infini) : plancher commun `1` (`contact_gt_one`), emboîtement
  transmis (`windingNested_trans`), espace d'une Tour borné des deux côtés (`tower_room_two_sided`,
  `translation_room_two_sided`) ; la Tour suivante s'enroule (pas strictement contracté) ⟺ la grille n'est pas
  translatée (`no_translation_iff_next_winds`) ; deux enroulements successifs ⟹ grille non translatée
  (`next_winding_forces_no_translation`) ; une Tour de même hauteur prend sa place par translation, tous ses
  contacts en deçà, sans enroulement (`sameHeight_successor_translates_inward`) ; l'obligation d'enroulement
  à tous les pas ⟺ RH (`winding_to_infinity_iff_riemannHypothesis`).

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse `def P… : Prop`. Borne : avec la seule Tour
précédente, `λ` est enfermé dans une fenêtre ; l'enroulement de la Tour suivante est SUPPOSÉ dans la section 5,
il n'y est pas dérivé ; `P_b < P_l ⟺ λ_l = 1` est une équivalence dont aucun côté n'est démontré. Flèche à
démontrer : contraction acquise au pas `n` ⟹ contraction au pas `n + 1`.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Les trois lectures de la translation -/

/-- **La translation de la grille, lue de trois façons.** Facteur radial égal à `1` ⟺ en ligne ⟺ tout réel
est à sa position de ligne ⟺ tout contact est le contact de la Tour de ligne à la même hauteur. -/
theorem grid_translation_readings (z : TrueZero) :
    (radialFactor z = 1 ↔ rZeroRadialPosition z.1 = 1 / 2) ∧
      (rZeroRadialPosition z.1 = 1 / 2 ↔
        ∀ q : ℝ, towerPosition z q = linePosition (rZeroHeight z.1) q) ∧
      (rZeroRadialPosition z.1 = 1 / 2 ↔
        ∀ k : ℤ, contactMinusAt z k = lineContact (rZeroHeight z.1) k) := by
  refine ⟨radialFactor_eq_one_iff z, onLine_iff_no_grid_translation z, ?_, ?_⟩
  · intro h k
    rw [contact_eq_line_mul_radial, (radialFactor_eq_one_iff z).mpr h, mul_one]
  · intro h
    have h0 := h 0
    rw [contact_eq_line_mul_radial] at h0
    have hp := lineContact_pos (rZeroHeight z.1) 0
    exact (radialFactor_eq_one_iff z).mp (mul_left_cancel₀ hp.ne' (h0.trans (mul_one _).symm))

/-! ## 2. L'enroulement entre deux Tours -/

/-- Les contacts de la Tour de ligne, à indice `k ≥ 1` fixé, décroissent strictement avec la hauteur. -/
theorem lineContact_strictAnti_height {T T' : ℝ} (hT : 0 < T) (hTT' : T < T') {k : ℤ} (hk : 1 ≤ k) :
    lineContact T' k < lineContact T k := by
  have h := windingContact_strictAnti_height (β := 1 / 2) (k := (k : ℝ)) (by norm_num) hT hTT'
    (by exact_mod_cast hk)
  rw [windingContact_half, windingContact_half] at h
  exact h

/-- **Enroulement de la Tour `l` dans la Tour `e`** : à tout indice `k ≥ 1`, le contact de `l` est
strictement en deçà du contact de `e`. -/
def WindingNested (e l : TrueZero) : Prop :=
  ∀ k : ℤ, 1 ≤ k → contactMinusAt l k < contactMinusAt e k

/-- **Depuis un départ en ligne, l'emboîtement borne la translation.** Indice par indice, le contact de
l'arrivée est en deçà de celui du départ ⟺ le contact de ligne à la hauteur d'arrivée, translaté par le
facteur radial de l'arrivée, est en deçà du contact de ligne à la hauteur de départ. -/
theorem windingNested_iff_translation_bound (e l : TrueZero)
    (he : rZeroRadialPosition e.1 = 1 / 2) :
    WindingNested e l ↔
      ∀ k : ℤ, 1 ≤ k →
        lineContact (rZeroHeight l.1) k * radialFactor l < lineContact (rZeroHeight e.1) k := by
  have hEq : ∀ k : ℤ, contactMinusAt e k = lineContact (rZeroHeight e.1) k := fun k => by
    rw [contact_eq_line_mul_radial, (radialFactor_eq_one_iff e).mpr he, mul_one]
  constructor
  · intro h k hk
    have hk' := h k hk
    rw [contact_eq_line_mul_radial l, hEq] at hk'
    exact hk'
  · intro h k hk
    rw [contact_eq_line_mul_radial l, hEq]
    exact h k hk

/-- **Deux Tours en ligne sont emboîtées dès que la hauteur avance.** -/
theorem windingNested_of_onLine (e l : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2)
    (hl : rZeroRadialPosition l.1 = 1 / 2) (hT : rZeroHeight e.1 < rZeroHeight l.1) :
    WindingNested e l := by
  rw [windingNested_iff_translation_bound e l he]
  intro k hk
  rw [(radialFactor_eq_one_iff l).mpr hl, mul_one]
  exact lineContact_strictAnti_height e.2 hT hk

/-- **Emboîtement perdu ⟹ grille translatée.** Départ en ligne, la hauteur avance : si la Tour d'arrivée
n'est pas emboîtée dans la Tour de départ, l'arrivée n'est pas en ligne. -/
theorem translation_of_not_nested (e l : TrueZero) (he : rZeroRadialPosition e.1 = 1 / 2)
    (hT : rZeroHeight e.1 < rZeroHeight l.1) (hN : ¬ WindingNested e l) :
    rZeroRadialPosition l.1 ≠ 1 / 2 :=
  fun hl => hN (windingNested_of_onLine e l he hl hT)

/-- **Profondeur de hauteur suffisante : emboîtement à cet indice pour toutes positions radiales.** -/
theorem windingNested_index_of_depth (e l : TrueZero) (k : ℤ)
    (hgap : rZeroHeight e.1 * (Real.pi / 2 + (k : ℝ) * Real.pi) ≤
      rZeroHeight l.1 * ((k : ℝ) * Real.pi)) :
    contactMinusAt l k < contactMinusAt e k := by
  have h := prime_axis_nesting_any_depth (β := rZeroRadialPosition e.1)
    (β' := rZeroRadialPosition l.1) (thm_zeroRadialPosition_positive e.1) e.2 l.2 hgap
  unfold windingContact at h
  rw [contactMinusAt_eq_exp, contactMinusAt_eq_exp]
  exact h

/-! ## 3. Le pas engagé, tout ensemble -/

/-- **Le pas parti de l'état engagé, toutes les liaisons sur les mêmes objets.** Départ en ligne, la
hauteur avance, hauteur d'arrivée au moins `2`. Alors, ensemble : succession (rang `+ 1`, premier de
référence strictement plus grand), hauteur qui avance, position radiale d'arrivée `≤ 1/2`, pas contracté
(enroulement), captivité énergétique au raccord exact, translation `λ ≥ 1`, tout contact de l'arrivée =
contact de ligne × `λ`, toute position = position de ligne + résidu constant, et les contacts sont
exactement les annulations de la partie imaginaire du terme de la Tour d'arrivée. -/
theorem engaged_step_combined (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hV : VerticalPassage p) (_hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hT2 : 2 ≤ rZeroHeight p.zLaterMember) :
    nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 ∧
      expectedMinimumPrime ⟨p.zEarlierMember, hE⟩ < expectedMinimumPrime ⟨p.zLaterMember, hL⟩ ∧
      rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember ∧
      rZeroRadialPosition p.zLaterMember ≤ 1 / 2 ∧
      towerPitch ⟨p.zLaterMember, hL⟩ < towerPitch ⟨p.zEarlierMember, hE⟩ ∧
      LocalCaptivity p hE hL ∧
      1 ≤ radialFactor ⟨p.zLaterMember, hL⟩ ∧
      (∀ k : ℤ, contactMinusAt ⟨p.zLaterMember, hL⟩ k =
        lineContact (rZeroHeight p.zLaterMember) k * radialFactor ⟨p.zLaterMember, hL⟩) ∧
      (∀ q : ℝ, towerPosition ⟨p.zLaterMember, hL⟩ q =
        linePosition (rZeroHeight p.zLaterMember) q + changeResidue p.zLaterMember / Real.pi) ∧
      (∀ q : ℝ, 0 < q →
        ((zeroTerm ⟨p.zLaterMember, hL⟩ q).im = 0 ↔
          ∃ k : ℤ, q = contactMinusAt ⟨p.zLaterMember, hL⟩ k)) := by
  have hLe := passage_entry_radial_le_half p hV
  have hLam : 1 ≤ radialFactor ⟨p.zLaterMember, hL⟩ := by
    rcases hLe.lt_or_eq with hlt | heq
    · exact ((radialFactor_gt_one_iff ⟨p.zLaterMember, hL⟩).mpr hlt).le
    · exact ((radialFactor_eq_one_iff ⟨p.zLaterMember, hL⟩).mpr heq).ge
  exact ⟨eventIndex_succ_of_passage p hE, expectedMinimumPrime_succ_of_passage p hE hL, hV, hLe,
    (vertical_iff_pitch_contracts p hE hL).mp hV,
    ((height_advance_local_budget p hE hL hV).2 hT2).2, hLam,
    fun k => contact_eq_line_mul_radial ⟨p.zLaterMember, hL⟩ k,
    fun q => towerPosition_eq_line_add_residue ⟨p.zLaterMember, hL⟩ q,
    fun _ hq => zeroTerm_real_iff_ray hq⟩

/-- **La fenêtre de la translation capturée.** Pas parti de l'état engagé, Tour d'arrivée emboîtée dans la
Tour de départ : la translation `λ` de la grille d'arrivée vérifie `1 ≤ λ` et, à tout indice `k ≥ 1`,
`C_k^{ligne}(T_l)·λ < C_k^{ligne}(T_e)`. L'enroulement et l'ordre enferment la translation ; ils ne
l'annulent pas. -/
theorem engaged_nested_translation_window (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hV : VerticalPassage p) (hOn : rZeroRadialPosition p.zEarlierMember = 1 / 2)
    (hN : WindingNested ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩) :
    1 ≤ radialFactor ⟨p.zLaterMember, hL⟩ ∧
      ∀ k : ℤ, 1 ≤ k →
        lineContact (rZeroHeight p.zLaterMember) k * radialFactor ⟨p.zLaterMember, hL⟩ <
          lineContact (rZeroHeight p.zEarlierMember) k := by
  have hLe := passage_entry_radial_le_half p hV
  refine ⟨?_, (windingNested_iff_translation_bound ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hOn).mp hN⟩
  rcases hLe.lt_or_eq with hlt | heq
  · exact ((radialFactor_gt_one_iff ⟨p.zLaterMember, hL⟩).mpr hlt).le
  · exact ((radialFactor_eq_one_iff ⟨p.zLaterMember, hL⟩).mpr heq).ge

/-! ## 4. La cible, découpée -/

/-- **La loi locale de conservation, découpée selon la flèche de l'auteur.** Sur les pas partis de la
ligne où la hauteur avance (hauteur d'arrivée au moins `2`) : « l'arrivée est en ligne » ⟺
(a) la Tour d'arrivée est emboîtée dans la Tour de départ, et
(b) succession + captivité énergétique au raccord + emboîtement ⟹ la grille d'arrivée n'est pas translatée.
La succession et la captivité sont des théorèmes sur ces pas ; (a) et (b) portent ensemble la loi. -/
theorem conservation_iff_nested_and_noTranslation :
    (∀ (p : TZeroPassage) (_hE : 0 < rZeroHeight p.zEarlierMember)
        (_hL : 0 < rZeroHeight p.zLaterMember), VerticalPassage p →
        rZeroRadialPosition p.zEarlierMember = 1 / 2 → 2 ≤ rZeroHeight p.zLaterMember →
        rZeroRadialPosition p.zLaterMember = 1 / 2) ↔
      (∀ (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
          (hL : 0 < rZeroHeight p.zLaterMember), VerticalPassage p →
          rZeroRadialPosition p.zEarlierMember = 1 / 2 → 2 ≤ rZeroHeight p.zLaterMember →
          WindingNested ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩) ∧
        (∀ (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
          (hL : 0 < rZeroHeight p.zLaterMember), VerticalPassage p →
          rZeroRadialPosition p.zEarlierMember = 1 / 2 → 2 ≤ rZeroHeight p.zLaterMember →
          nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1 →
          LocalCaptivity p hE hL →
          WindingNested ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ →
          ∀ q : ℝ, towerPosition ⟨p.zLaterMember, hL⟩ q =
            linePosition (rZeroHeight p.zLaterMember) q) := by
  constructor
  · intro h
    refine ⟨fun p hE hL hV hOn hT2 =>
      windingNested_of_onLine ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ hOn
        (h p hE hL hV hOn hT2) hV, ?_⟩
    intro p hE hL hV hOn hT2 _ _ _
    exact (onLine_iff_no_grid_translation ⟨p.zLaterMember, hL⟩).mp (h p hE hL hV hOn hT2)
  · rintro ⟨hA, hB⟩ p hE hL hV hOn hT2
    exact (onLine_iff_no_grid_translation ⟨p.zLaterMember, hL⟩).mpr
      (hB p hE hL hV hOn hT2 (eventIndex_succ_of_passage p hE)
        ((height_advance_local_budget p hE hL hV).2 hT2).2 (hA p hE hL hV hOn hT2))

/-! ## 5. La place de la Tour suivante, et de toutes les autres jusqu'à l'infini

Paramètre de l'auteur (2026-10-04) : la Tour doit s'enrouler en laissant la place à la suivante ; l'espace
réservé à une Tour est limité par la précédente ET par la suivante et toutes les autres.

Portée exacte (revue de l'auteur, 2026-10-04) : dans cette section l'enroulement de la Tour suivante est une
HYPOTHÈSE des énoncés (`WindingNested l b`, ou le passage suivant vertical), jamais une conclusion. Rien ici ne
dérive « la place laissée à la suivante ». La flèche à démontrer est la transmission de la contraction :
contraction acquise au pas `n` ⟹ contraction au pas `n + 1`
(`experiments/contraction_transmission_probe/`, un but ouvert, EXIT=1). -/

/-- **Le plancher commun de toutes les Tours** : tout contact d'indice `k ≥ 0` est strictement au-delà
de `1`. Les Tours suivantes s'accumulent vers `1` sans l'atteindre. -/
theorem contact_gt_one (z : TrueZero) {k : ℤ} (hk : 0 ≤ k) : 1 < contactMinusAt z k := by
  rw [contactMinusAt_eq_exp, Real.one_lt_exp_iff]
  have hφ : 0 < Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) :=
    Real.arctan_pos.mpr (div_pos z.2 (thm_zeroRadialPosition_positive z.1))
  have hkπ : (0 : ℝ) ≤ (k : ℝ) * Real.pi := mul_nonneg (by exact_mod_cast hk) Real.pi_pos.le
  exact div_pos (by linarith) z.2

/-- L'emboîtement se transmet : toute Tour emboîtée dans la suivante d'une Tour est emboîtée dans celle-ci. -/
theorem windingNested_trans {e l b : TrueZero} (h₁ : WindingNested e l) (h₂ : WindingNested l b) :
    WindingNested e b :=
  fun k hk => (h₂ k hk).trans (h₁ k hk)

/-- **Encadrement sous deux emboîtements supposés.** Les deux emboîtements sont des hypothèses ; l'énoncé ne
dérive pas la place de la Tour suivante. Trois Tours successives emboîtées : à tout
indice `k ≥ 1`, le contact de la Tour du milieu est strictement entre celui de la suivante et celui de la
précédente, et celui de la suivante reste au-delà de `1`. -/
theorem tower_room_two_sided {e l b : TrueZero} (h₁ : WindingNested e l) (h₂ : WindingNested l b)
    {k : ℤ} (hk : 1 ≤ k) :
    1 < contactMinusAt b k ∧ contactMinusAt b k < contactMinusAt l k ∧
      contactMinusAt l k < contactMinusAt e k :=
  ⟨contact_gt_one b (by omega), h₂ k hk, h₁ k hk⟩

/-- **La fenêtre de la translation, bornée des deux côtés.** Départ en ligne, trois Tours successives
emboîtées : la translation de la Tour du milieu est bornée au-dessus par la Tour précédente et en dessous
par la Tour suivante, `C_k^{ligne}(T_b)·λ_b < C_k^{ligne}(T_l)·λ_l < C_k^{ligne}(T_e)`. -/
theorem translation_room_two_sided {e l b : TrueZero} (he : rZeroRadialPosition e.1 = 1 / 2)
    (h₁ : WindingNested e l) (h₂ : WindingNested l b) {k : ℤ} (hk : 1 ≤ k) :
    lineContact (rZeroHeight b.1) k * radialFactor b < lineContact (rZeroHeight l.1) k * radialFactor l ∧
      lineContact (rZeroHeight l.1) k * radialFactor l < lineContact (rZeroHeight e.1) k := by
  refine ⟨?_, (windingNested_iff_translation_bound e l he).mp h₁ k hk⟩
  have h := h₂ k hk
  rw [contact_eq_line_mul_radial b, contact_eq_line_mul_radial l] at h
  exact h

/-- **Contraction du pas suivant ⟺ non-translation (équivalence, aucun des deux côtés n'est dérivé).** La hauteur
avance sur le pas `e → l` ; `l → b` est le pas suivant. Alors la Tour `b` s'enroule (son pas est strictement
contracté par rapport à celui de `l`) si et seulement si la grille de `l` n'est pas translatée. -/
theorem no_translation_iff_next_winds {p q : TZeroPassage} (hJ : p.zLaterMember = q.zEarlierMember)
    (hp : VerticalPassage p) (hL : 0 < rZeroHeight p.zLaterMember)
    (hE' : 0 < rZeroHeight q.zEarlierMember) (hB : 0 < rZeroHeight q.zLaterMember) :
    towerPitch ⟨q.zLaterMember, hB⟩ < towerPitch ⟨q.zEarlierMember, hE'⟩ ↔
      radialFactor ⟨p.zLaterMember, hL⟩ = 1 := by
  exact (vertical_iff_pitch_contracts q hE' hB).symm.trans
    ((vertical_arrival_characterizes hJ hp).1.trans (radialFactor_eq_one_iff ⟨p.zLaterMember, hL⟩).symm)

/-- **Deux contractions successives ⟹ grille non translatée.** La contraction du pas suivant est une
hypothèse (`hq`). Si la hauteur avance aux deux pas `e → l` et `l → b`, la grille de `l` n'est pas
translatée : tout réel y est à sa position de ligne. -/
theorem next_winding_forces_no_translation {p q : TZeroPassage}
    (hJ : p.zLaterMember = q.zEarlierMember) (hp : VerticalPassage p) (hq : VerticalPassage q)
    (hL : 0 < rZeroHeight p.zLaterMember) :
    radialFactor ⟨p.zLaterMember, hL⟩ = 1 ∧
      ∀ x : ℝ, towerPosition ⟨p.zLaterMember, hL⟩ x = linePosition (rZeroHeight p.zLaterMember) x := by
  have hOn := junction_vertical_vertical hJ hp hq
  exact ⟨(radialFactor_eq_one_iff ⟨p.zLaterMember, hL⟩).mpr hOn,
    (onLine_iff_no_grid_translation ⟨p.zLaterMember, hL⟩).mp hOn⟩

/-- **Borne : une Tour de même hauteur prend sa place par translation, pas par enroulement.** Sur un pas de
même hauteur, le pas de la Tour d'arrivée est celui de la Tour de départ, et TOUS ses contacts (tout indice,
positif ou négatif) sont strictement en deçà : l'emboîtement des contacts d'indice `k ≥ 1` tient. L'emboîtement
des contacts seul ne porte donc pas l'obligation d'enroulement ; c'est la contraction du pas qui la porte. -/
theorem sameHeight_successor_translates_inward (q : TZeroPassage)
    (hE : 0 < rZeroHeight q.zEarlierMember) (hL : 0 < rZeroHeight q.zLaterMember)
    (hH : HorizontalPassage q) :
    towerPitch ⟨q.zLaterMember, hL⟩ = towerPitch ⟨q.zEarlierMember, hE⟩ ∧
      (∀ k : ℤ, contactMinusAt ⟨q.zLaterMember, hL⟩ k < contactMinusAt ⟨q.zEarlierMember, hE⟩ k) ∧
      WindingNested ⟨q.zEarlierMember, hE⟩ ⟨q.zLaterMember, hL⟩ := by
  have hT : rZeroHeight q.zEarlierMember = rZeroHeight q.zLaterMember := hH
  have hβ := (horizontal_regime q hE hL hH).1
  have hAll : ∀ k : ℤ, contactMinusAt ⟨q.zLaterMember, hL⟩ k < contactMinusAt ⟨q.zEarlierMember, hE⟩ k := by
    intro k
    refine lt_of_eq_of_lt (contactMinusAt_eq_exp ⟨q.zLaterMember, hL⟩ k)
      (lt_of_lt_of_eq ?_ (contactMinusAt_eq_exp ⟨q.zEarlierMember, hE⟩ k).symm)
    change Real.exp ((Real.arctan (rZeroHeight q.zLaterMember / rZeroRadialPosition q.zLaterMember) +
        (k : ℝ) * Real.pi) / rZeroHeight q.zLaterMember) <
      Real.exp ((Real.arctan (rZeroHeight q.zEarlierMember / rZeroRadialPosition q.zEarlierMember) +
        (k : ℝ) * Real.pi) / rZeroHeight q.zEarlierMember)
    rw [← hT]
    have hlt : Real.arctan (rZeroHeight q.zEarlierMember / rZeroRadialPosition q.zLaterMember) <
        Real.arctan (rZeroHeight q.zEarlierMember / rZeroRadialPosition q.zEarlierMember) :=
      Real.arctan_strictMono ((div_lt_div_iff_of_pos_left hE
        (thm_zeroRadialPosition_positive q.zLaterMember)
        (thm_zeroRadialPosition_positive q.zEarlierMember)).mpr hβ)
    exact Real.exp_lt_exp.mpr (div_lt_div_of_pos_right (by linarith) hE)
  refine ⟨?_, hAll, fun k _ => hAll k⟩
  unfold towerPitch
  change Real.pi / rZeroHeight q.zLaterMember = Real.pi / rZeroHeight q.zEarlierMember
  rw [hT]

/-- **L'obligation d'enroulement jusqu'à l'infini.** « Chaque Tour s'enroule dans la précédente : à tout
pas de la moitié supérieure, le pas de la Tour d'arrivée est strictement contracté » ⟺ hypothèse de Riemann. -/
theorem winding_to_infinity_iff_riemannHypothesis :
    (∀ (p : TZeroPassage) (hE : 0 < rZeroHeight p.zEarlierMember)
        (hL : 0 < rZeroHeight p.zLaterMember),
        towerPitch ⟨p.zLaterMember, hL⟩ < towerPitch ⟨p.zEarlierMember, hE⟩) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_height_always_advances fun p hE =>
      (vertical_iff_pitch_contracts p hE (hE.trans_le (passage_height_le p))).mpr
        (h p hE (hE.trans_le (passage_height_le p)))
  · intro hRH p hE hL
    exact (vertical_iff_pitch_contracts p hE hL).mp
      (lt_of_le_of_ne (passage_height_le p)
        (fun hEq => (no_sameHeight_iff_riemannHypothesis.mpr hRH) p hE hEq))

#print axioms grid_translation_readings
#print axioms lineContact_strictAnti_height
#print axioms windingNested_iff_translation_bound
#print axioms windingNested_of_onLine
#print axioms translation_of_not_nested
#print axioms windingNested_index_of_depth
#print axioms engaged_step_combined
#print axioms engaged_nested_translation_window
#print axioms conservation_iff_nested_and_noTranslation
#print axioms contact_gt_one
#print axioms windingNested_trans
#print axioms tower_room_two_sided
#print axioms translation_room_two_sided
#print axioms no_translation_iff_next_winds
#print axioms next_winding_forces_no_translation
#print axioms sameHeight_successor_translates_inward
#print axioms winding_to_infinity_iff_riemannHypothesis

end RHV6Fresh
