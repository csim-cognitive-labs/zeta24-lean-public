/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TrueZero
import Mathlib.Data.Prod.Lex

/-!
# RHV3Lean — O7, la grammaire des écarts de zéros

    TRACE_ID              : RHV3-O7
    SEMANTIC_OBJECT       : O7 — la grammaire des écarts de zéros
    SEMANTIC_STATEMENT    : la grammaire des écarts de zéros est la même
                            grammaire retrouvée côté zéro — fibre de hauteur,
                            ordre membre-sensible, consécutivité, écart de
                            hauteur — construite sur les vrais zéros et non sur
                            les premiers.
    MATHEMATICAL_STATEMENT: l'ordre membre-sensible est la hauteur puis, à
                            hauteur égale, la position radiale ; l'écart est la
                            différence des hauteurs ; il est toujours >= 0 sur
                            un couple ordonné, et nul si et seulement si les
                            deux membres sont dans la même fibre.
    MATHEMATICAL_PARENT   : O1 — le vrai zéro.
    PROOF_STRATEGY        : l'ordre est l'ordre lexicographique sur le couple
                            (hauteur, position radiale) ; sa clé est injective
                            parce que ces deux coordonnées sont les deux parties
                            du support, donc déterminent le membre (O1) ; la
                            positivité de l'écart se lit sur la disjonction
                            lexicographique.
    REQUIRED_LEMMAS       : Prod.Lex.toLex_lt_toLex, Complex.ext,
                            thm_zero_identity_of_sameSupport
    WHY_EACH_LEMMA_EXISTS : le premier expose l'ordre exactement comme
                            « hauteur puis position radiale » ; les deux autres
                            donnent l'injectivité de la clé, sans laquelle deux
                            membres distincts pourraient être incomparables.
    LEAN_DEFINITION       : sZeroHeightFiber, fnZeroOrderKey,
                            PZeroMemberPrecedes, PZeroMembersConsecutive,
                            rZeroPairHeightGap
    LEAN_THEOREM          : thm_zeroMemberPrecedes_iff_height_radial_lex,
                            thm_zeroOrderKey_injective,
                            thm_zeroPairHeightGap_nonnegative,
                            thm_zeroPairHeightGap_zero_iff_sameFiber
    SAME_MEMBER_CHECK     : l'ordre est membre-sensible : à hauteur égale il
                            sépare encore par la position radiale, donc il ne
                            confond jamais deux membres distincts de la même
                            fibre.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau — le passage est O8.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre ici.
    FORBIDDEN_PREMISES    : tout ordre par la seule hauteur, qui confondrait
                            deux membres de la même fibre ; toute mention d'un
                            premier, d'une Tour, d'un contact ou d'un comptage ;
                            toute prémisse de positivité stricte des écarts.
    NEXT_CONSUMER         : O8 (le passage).
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

/-! ## 1. La fibre de hauteur -/

/-- **La fibre de hauteur** : les vrais zéros situés exactement à une hauteur
donnée.  Elle peut porter plusieurs membres distincts ; c'est précisément ce que
l'ordre membre-sensible doit continuer à séparer. -/
def sZeroHeightFiber (rHeight : ℝ) : Set TNonTrivialZetaZero :=
  {zZero | rZeroHeight zZero = rHeight}

theorem thm_mem_zeroHeightFiber_iff
    (rHeight : ℝ) (zZero : TNonTrivialZetaZero) :
    zZero ∈ sZeroHeightFiber rHeight ↔ rZeroHeight zZero = rHeight := Iff.rfl

/-- Deux membres sont dans la même fibre exactement quand leurs hauteurs
coïncident. -/
theorem thm_sameFiber_iff_sameHeight
    (zLeftZero zRightZero : TNonTrivialZetaZero) :
    (∃ rHeight : ℝ,
        zLeftZero ∈ sZeroHeightFiber rHeight ∧
          zRightZero ∈ sZeroHeightFiber rHeight) ↔
      rZeroHeight zLeftZero = rZeroHeight zRightZero := by
  constructor
  · rintro ⟨rHeight, hLeft, hRight⟩
    exact hLeft.trans hRight.symm
  · intro hSameHeight
    exact ⟨rZeroHeight zRightZero, hSameHeight, rfl⟩

/-! ## 2. L'ordre membre-sensible -/

/-- **La clé d'ordre membre-sensible** : la hauteur d'abord, la position
radiale ensuite.  Les deux coordonnées du membre entrent, jamais une seule. -/
def fnZeroOrderKey (zZero : TNonTrivialZetaZero) : Lex (ℝ × ℝ) :=
  toLex (rZeroHeight zZero, rZeroRadialPosition zZero)

/-- **L'ordre membre-sensible des membres.** -/
def PZeroMemberPrecedes (zEarlier zLater : TNonTrivialZetaZero) : Prop :=
  fnZeroOrderKey zEarlier < fnZeroOrderKey zLater

/-- **L'ordre est exactement « hauteur d'abord, position radiale ensuite ».**
C'est la clause membre-sensible : à hauteur égale l'ordre ne s'effondre pas, il
sépare encore par la position radiale. -/
theorem thm_zeroMemberPrecedes_iff_height_radial_lex
    (zEarlier zLater : TNonTrivialZetaZero) :
    PZeroMemberPrecedes zEarlier zLater ↔
      rZeroHeight zEarlier < rZeroHeight zLater ∨
        (rZeroHeight zEarlier = rZeroHeight zLater ∧
          rZeroRadialPosition zEarlier < rZeroRadialPosition zLater) :=
  Prod.Lex.toLex_lt_toLex

/-- **La clé d'ordre est injective.**  Les deux coordonnées lues sont les deux
parties du support, donc elles déterminent le membre (O1).  Aucun couple de
membres distincts n'est incomparable. -/
theorem thm_zeroOrderKey_injective : Function.Injective fnZeroOrderKey := by
  intro zLeftZero zRightZero hSameKey
  have hPair :
      (rZeroHeight zLeftZero, rZeroRadialPosition zLeftZero) =
        (rZeroHeight zRightZero, rZeroRadialPosition zRightZero) := by
    simpa [fnZeroOrderKey] using congrArg ofLex hSameKey
  have hHeight : rZeroHeight zLeftZero = rZeroHeight zRightZero :=
    congrArg Prod.fst hPair
  have hRadial :
      rZeroRadialPosition zLeftZero = rZeroRadialPosition zRightZero :=
    congrArg Prod.snd hPair
  exact thm_zero_identity_of_sameSupport (Complex.ext hRadial hHeight)

theorem thm_zeroMemberPrecedes_irreflexive (zZero : TNonTrivialZetaZero) :
    ¬ PZeroMemberPrecedes zZero zZero := lt_irrefl _

theorem thm_zeroMemberPrecedes_transitive
    {zFirst zSecond zThird : TNonTrivialZetaZero}
    (hFirstSecond : PZeroMemberPrecedes zFirst zSecond)
    (hSecondThird : PZeroMemberPrecedes zSecond zThird) :
    PZeroMemberPrecedes zFirst zThird := lt_trans hFirstSecond hSecondThird

theorem thm_zeroMemberPrecedes_asymmetric
    {zEarlier zLater : TNonTrivialZetaZero}
    (hPrecedes : PZeroMemberPrecedes zEarlier zLater) :
    ¬ PZeroMemberPrecedes zLater zEarlier := LT.lt.asymm hPrecedes

/-- **Deux membres distincts sont toujours comparables.** -/
theorem thm_distinctZeroMembers_comparable
    {zLeftZero zRightZero : TNonTrivialZetaZero}
    (hDistinct : zLeftZero ≠ zRightZero) :
    PZeroMemberPrecedes zLeftZero zRightZero ∨
      PZeroMemberPrecedes zRightZero zLeftZero :=
  lt_or_gt_of_ne (fun hSameKey => hDistinct (thm_zeroOrderKey_injective hSameKey))

/-! ## 3. La consécutivité -/

/-- **La consécutivité membre-sensible** : précéder, sans aucun membre
strictement interposé. -/
def PZeroMembersConsecutive (zEarlier zLater : TNonTrivialZetaZero) : Prop :=
  PZeroMemberPrecedes zEarlier zLater ∧
    ¬ ∃ zBetween : TNonTrivialZetaZero,
      PZeroMemberPrecedes zEarlier zBetween ∧
        PZeroMemberPrecedes zBetween zLater

theorem thm_consecutive_precedes
    {zEarlier zLater : TNonTrivialZetaZero}
    (hConsecutive : PZeroMembersConsecutive zEarlier zLater) :
    PZeroMemberPrecedes zEarlier zLater := hConsecutive.1

theorem thm_consecutive_members_distinct
    {zEarlier zLater : TNonTrivialZetaZero}
    (hConsecutive : PZeroMembersConsecutive zEarlier zLater) :
    zEarlier ≠ zLater := by
  intro hSame
  exact thm_zeroMemberPrecedes_irreflexive zLater (hSame ▸ hConsecutive.1)

/-! ## 4. L'écart de hauteur, et la rigidité de O7 -/

/-- **L'écart de hauteur d'un couple ordonné de membres.** -/
def rZeroPairHeightGap (zEarlier zLater : TNonTrivialZetaZero) : ℝ :=
  rZeroHeight zLater - rZeroHeight zEarlier

/-- **RIGIDITE — l'écart est toujours non négatif.**  Sur un couple ordonné par
l'ordre membre-sensible, l'écart de hauteur ne peut pas être négatif : c'est la
première moitié de la rigidité de O7, et elle est acquise ici, une fois pour
toutes, sans aucune hypothèse. -/
theorem thm_zeroPairHeightGap_nonnegative
    {zEarlier zLater : TNonTrivialZetaZero}
    (hPrecedes : PZeroMemberPrecedes zEarlier zLater) :
    0 ≤ rZeroPairHeightGap zEarlier zLater := by
  rw [thm_zeroMemberPrecedes_iff_height_radial_lex] at hPrecedes
  unfold rZeroPairHeightGap
  rcases hPrecedes with hStrict | hSameHeight
  · linarith
  · rw [hSameHeight.1]
    linarith

/-- **RIGIDITE — l'écart est nul exactement dans la même fibre.**  C'est la
seconde moitié : un écart nul ne dit rien d'autre que « même hauteur », et il
n'exclut nullement que les deux membres soient distincts. -/
theorem thm_zeroPairHeightGap_zero_iff_sameFiber
    (zEarlier zLater : TNonTrivialZetaZero) :
    rZeroPairHeightGap zEarlier zLater = 0 ↔
      rZeroHeight zEarlier = rZeroHeight zLater := by
  unfold rZeroPairHeightGap
  exact sub_eq_zero.trans eq_comm

/-- **La configuration qui portera la contradiction terminale existe déjà dans
la grammaire.**  Deux membres distincts de la même fibre sont comparables, donc
ordonnés, et leur écart de hauteur est nul.  Rien ici ne la refuse : c'est la
loi locale du transport, bien plus tard, qui la refusera. -/
theorem thm_distinctSameFiberMembers_haveNullGap
    {zLeftZero zRightZero : TNonTrivialZetaZero}
    (hDistinct : zLeftZero ≠ zRightZero)
    (hSameHeight : rZeroHeight zLeftZero = rZeroHeight zRightZero) :
    (PZeroMemberPrecedes zLeftZero zRightZero ∨
        PZeroMemberPrecedes zRightZero zLeftZero) ∧
      rZeroPairHeightGap zLeftZero zRightZero = 0 :=
  ⟨thm_distinctZeroMembers_comparable hDistinct,
    (thm_zeroPairHeightGap_zero_iff_sameFiber zLeftZero zRightZero).mpr hSameHeight⟩

end RHV3Lean
