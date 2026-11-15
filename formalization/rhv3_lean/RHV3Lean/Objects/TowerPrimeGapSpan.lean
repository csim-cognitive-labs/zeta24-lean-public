/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TowerTransition
import RHV3Lean.Objects.PrimeGapGrammar

/-!
# RHV3Lean — la portée de Tour d'une arête première canonique

    TRACE_ID              : RHV3-TOWER-PRIME-GAP-SPAN
    SEMANTIC_OBJECT       : la lecture, par la hauteur d'un membre, de la
                            largeur logarithmique d'une arête déjà produite par
                            la grammaire première O6 — jamais une estimation de
                            densité, jamais un PNT.
    SEMANTIC_STATEMENT    : pour une place `Theta_n = p_n -> p_(n+1)` de
                            l'unique histoire première, la hauteur `T` d'un
                            membre donne une portée réelle exacte, dont la
                            variation entre deux membres est linéaire en
                            l'écart de hauteur, et dont l'inversion restitue
                            exactement l'écart premier `g_n` — sans
                            approximation, sans hypothèse de croissance.
    MATHEMATICAL_STATEMENT: TowerPrimeGapSpan z n := T(z)/pi * log(p_(n+1)/p_n)
                            = T(z)/pi * log(1 + g_n/p_n) ;
                            D_(i+1)(n) - D_i(n)
                              = (T_(i+1)-T_i)/pi * log(1+g_n/p_n) ;
                            D_(i+1)(n) = D_i(n) <-> T_(i+1) = T_i ;
                            D_(i+1)(n) > D_i(n) <-> T_(i+1) > T_i ;
                            T_(i+1)-T_i
                              = pi*(D_(i+1)(n)-D_i(n)) / log(1+g_n/p_n) ;
                            g_n = p_n * (exp(pi*D_i(n)/T_i) - 1).
    MATHEMATICAL_PARENT   : O6 — la grammaire des écarts premiers
                            (`PrimeGapGrammar.lean`) ; O3 — la Tour harmonique
                            (`HarmonicTower.lean`, `rTowerHeight`).
    PROOF_STRATEGY        : `fnPrimeSuccessor n = fnPrimeAtRank n + nPrimeGap n`
                            (arithmétique ℕ, puis coercion) donne
                            `p_(n+1)/p_n = 1 + g_n/p_n` par algèbre de corps
                            pure ; la portée est alors `T/pi` fois une quantité
                            STRICTEMENT POSITIVE et INDEPENDANTE du membre,
                            d'où la linéarité en `T` et toutes les équivalences
                            de signe ; l'inversion du gap vient de
                            `Real.exp_log` sur `p_(n+1)/p_n > 0`.
    REQUIRED_LEMMAS       : thm_primeAtRank_lt_successor, thm_primeGap_positive,
                            thm_primeAtRank_isPrime, Real.log_pos, Real.exp_log,
                            Real.pi_pos, thm_rTowerHeight_positive
    WHY_EACH_LEMMA_EXISTS : les trois premiers donnent l'ordre et la
                            positivité qui rendent le logarithme strictement
                            positif ; les deux suivants ferment l'inversion
                            exponentielle exacte ; le dernier autorise la
                            division par la hauteur dans le sens inverse.
    LEAN_DEFINITION       : rPrimeGapLogRatio, TowerPrimeGapSpan
    LEAN_THEOREM          : thm_primeSuccessor_eq_add_gap,
                            thm_primeGapLogRatio_pos,
                            thm_primeGapLogRatio_eq_log_one_add,
                            thm_towerPrimeGapSpan_eq_log_one_add,
                            thm_towerPrimeGapSpan_diff,
                            thm_towerPrimeGapSpan_eq_iff_height_eq,
                            thm_towerPrimeGapSpan_gt_iff_height_gt,
                            thm_towerPrimeGapSpan_heightGap_formula,
                            thm_primeGap_recovered_from_span
    SAME_MEMBER_CHECK     : `TowerPrimeGapSpan` lit exclusivement la hauteur du
                            SEUL membre `z` reçu ; aucune substitution n'est
                            exprimable.
    SAME_PASSAGE_CHECK    : les théorèmes de différence portent sur LA MÊME
                            place `n`, évaluée aux deux hauteurs d'un même
                            passage.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau — la place `n` commune à
                            deux passages est l'objet du module suivant
                            (`TowerGrammarMorphism.lean`).
    SAME_HISTORY_CHECK    : `p_n`, `p_(n+1)`, `g_n` viennent exclusivement de
                            `fnPrimeAtRank`/`fnPrimeSuccessor`/`nPrimeGap`, donc
                            de l'unique histoire première de O6.
    FORBIDDEN_PREMISES    : PNT, densité, approximation, hypothèse de
                            croissance ; l'égalité `DeltaT = g_n` (interdite
                            explicitement — la relation vraie est
                            logarithmique/multiplicative, jamais additive) ;
                            tout rang cible choisi hors de `n` reçu en
                            paramètre.
    NEXT_CONSUMER         : `TowerGrammarMorphism.lean` — le rang `n` cessera
                            d'être un paramètre libre et sera PRODUIT par le
                            passage lui-même.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

/-! ## 1. Le ratio logarithmique d'une place, indépendant de tout membre -/

/-- **Le ratio logarithmique d'une place** `log(p_(n+1)/p_n)`, fonction du seul
rang `n` — jamais d'un zéro, d'une hauteur ou d'une Tour. -/
noncomputable def rPrimeGapLogRatio (nRank : ℕ) : ℝ :=
  Real.log ((fnPrimeSuccessor nRank : ℝ) / (fnPrimeAtRank nRank : ℝ))

theorem thm_primeAtRank_pos (nRank : ℕ) : 0 < fnPrimeAtRank nRank :=
  (thm_primeAtRank_isPrime nRank).pos

/-- **`p_(n+1) = p_n + g_n`**, l'écart entier restitué en addition exacte —
valide parce que `p_n < p_(n+1)` rend la soustraction ℕ de `nPrimeGap` sans
troncature. -/
theorem thm_primeSuccessor_eq_add_gap (nRank : ℕ) :
    fnPrimeSuccessor nRank = fnPrimeAtRank nRank + nPrimeGap nRank := by
  have hLt := thm_primeAtRank_lt_successor nRank
  unfold nPrimeGap
  omega

/-- **Le ratio logarithmique d'une place est strictement positif.** -/
theorem thm_primeGapLogRatio_pos (nRank : ℕ) : 0 < rPrimeGapLogRatio nRank := by
  unfold rPrimeGapLogRatio
  apply Real.log_pos
  have hPosAt : (0 : ℝ) < (fnPrimeAtRank nRank : ℝ) := by
    exact_mod_cast thm_primeAtRank_pos nRank
  rw [lt_div_iff₀ hPosAt, one_mul]
  have hLt := thm_primeAtRank_lt_successor nRank
  exact_mod_cast hLt

/-- **Le ratio logarithmique d'une place vaut exactement `log(1+g_n/p_n)`.**
Algèbre de corps pure sur `p_(n+1) = p_n + g_n`. -/
theorem thm_primeGapLogRatio_eq_log_one_add (nRank : ℕ) :
    rPrimeGapLogRatio nRank =
      Real.log (1 + (nPrimeGap nRank : ℝ) / (fnPrimeAtRank nRank : ℝ)) := by
  unfold rPrimeGapLogRatio
  have hPosAt : (fnPrimeAtRank nRank : ℝ) ≠ 0 := by
    exact_mod_cast (thm_primeAtRank_pos nRank).ne'
  have hSum : (fnPrimeSuccessor nRank : ℝ) =
      (fnPrimeAtRank nRank : ℝ) + (nPrimeGap nRank : ℝ) := by
    exact_mod_cast thm_primeSuccessor_eq_add_gap nRank
  rw [hSum]
  congr 1
  field_simp

/-! ## 2. La portée de Tour d'une place -/

/-- **La portée de Tour d'une place**, pour un membre donné : `T(z)/pi` fois
son ratio logarithmique. Aucune approximation, aucun PNT : c'est une lecture
algébrique exacte de deux objets déjà produits séparément (la Tour, la
grammaire première). -/
noncomputable def TowerPrimeGapSpan (z : TUpperNonTrivialZetaZero) (nRank : ℕ) : ℝ :=
  rTowerHeight z / Real.pi * rPrimeGapLogRatio nRank

/-- **`TowerPrimeGapSpan z n = T(z)/pi * log(1+g_n/p_n)`.** -/
theorem thm_towerPrimeGapSpan_eq_log_one_add
    (z : TUpperNonTrivialZetaZero) (nRank : ℕ) :
    TowerPrimeGapSpan z nRank =
      rTowerHeight z / Real.pi *
        Real.log (1 + (nPrimeGap nRank : ℝ) / (fnPrimeAtRank nRank : ℝ)) := by
  unfold TowerPrimeGapSpan
  rw [thm_primeGapLogRatio_eq_log_one_add]

/-! ## 3. Deux hauteurs sur la même arête -/

/-- **La différence de portée sur la même place est exactement linéaire dans
l'écart de hauteur.** -/
theorem thm_towerPrimeGapSpan_diff
    (zLeft zRight : TUpperNonTrivialZetaZero) (nRank : ℕ) :
    TowerPrimeGapSpan zRight nRank - TowerPrimeGapSpan zLeft nRank =
      (rTowerHeight zRight - rTowerHeight zLeft) / Real.pi *
        rPrimeGapLogRatio nRank := by
  unfold TowerPrimeGapSpan
  ring

/-- Un fait de signe générique : un produit par un facteur strictement positif
préserve la stricte positivité, dans les deux sens. Utilisé uniquement pour
lire le signe de l'écart de portée depuis celui de l'écart de hauteur. -/
private theorem thm_mul_pos_iff_of_pos_right {a c : ℝ} (hc : 0 < c) :
    0 < a * c ↔ 0 < a := by
  constructor
  · intro hProd
    by_contra hNot
    push_neg at hNot
    nlinarith
  · intro hPos
    exact mul_pos hPos hc

/-- **La portée coïncide sur la même place exactement quand les deux hauteurs
coïncident.** -/
theorem thm_towerPrimeGapSpan_eq_iff_height_eq
    (zLeft zRight : TUpperNonTrivialZetaZero) (nRank : ℕ) :
    TowerPrimeGapSpan zRight nRank = TowerPrimeGapSpan zLeft nRank ↔
      rTowerHeight zRight = rTowerHeight zLeft := by
  have hRatioPos := thm_primeGapLogRatio_pos nRank
  have hRatioNe : rPrimeGapLogRatio nRank ≠ 0 := ne_of_gt hRatioPos
  have hPiNe : Real.pi ≠ 0 := Real.pi_ne_zero
  constructor
  · intro hEq
    have hDiffZero :
        (rTowerHeight zRight - rTowerHeight zLeft) / Real.pi *
            rPrimeGapLogRatio nRank = 0 := by
      have := thm_towerPrimeGapSpan_diff zLeft zRight nRank
      rw [hEq] at this
      linarith
    rcases mul_eq_zero.mp hDiffZero with hDiv | hRatio
    · have : rTowerHeight zRight - rTowerHeight zLeft = 0 := by
        field_simp at hDiv
        linarith
      linarith
    · exact absurd hRatio hRatioNe
  · intro hEq
    unfold TowerPrimeGapSpan
    rw [hEq]

/-- **La portée croît sur la même place exactement quand la hauteur croît.** -/
theorem thm_towerPrimeGapSpan_gt_iff_height_gt
    (zLeft zRight : TUpperNonTrivialZetaZero) (nRank : ℕ) :
    TowerPrimeGapSpan zLeft nRank < TowerPrimeGapSpan zRight nRank ↔
      rTowerHeight zLeft < rTowerHeight zRight := by
  have hRatioPos := thm_primeGapLogRatio_pos nRank
  rw [← sub_pos, thm_towerPrimeGapSpan_diff, ← sub_pos (a := rTowerHeight zRight)]
  have hDivIff :
      0 < (rTowerHeight zRight - rTowerHeight zLeft) / Real.pi ↔
        0 < rTowerHeight zRight - rTowerHeight zLeft :=
    ⟨fun h => by
        by_contra hNot; push_neg at hNot
        exact absurd h (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg
          (by linarith) (le_of_lt Real.pi_pos))),
      fun h => div_pos h Real.pi_pos⟩
  rw [thm_mul_pos_iff_of_pos_right hRatioPos, hDivIff]

/-- **L'inversion exacte de l'écart de hauteur** depuis l'écart de portée sur
la même place. -/
theorem thm_towerPrimeGapSpan_heightGap_formula
    (zLeft zRight : TUpperNonTrivialZetaZero) (nRank : ℕ) :
    rTowerHeight zRight - rTowerHeight zLeft =
      Real.pi * (TowerPrimeGapSpan zRight nRank - TowerPrimeGapSpan zLeft nRank) /
        rPrimeGapLogRatio nRank := by
  have hRatioNe : rPrimeGapLogRatio nRank ≠ 0 :=
    ne_of_gt (thm_primeGapLogRatio_pos nRank)
  have hPiNe : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [thm_towerPrimeGapSpan_diff]
  field_simp

/-! ## 4. Récupération exacte de l'écart premier -/

/-- **L'écart premier est récupéré exactement depuis la portée d'un seul
membre.** `g_n = p_n * (exp(pi*D(n)/T) - 1)`, où `D(n) = TowerPrimeGapSpan z n`
et `T = rTowerHeight z`. Inversion exponentielle exacte, sans troncature. -/
theorem thm_primeGap_recovered_from_span
    (z : TUpperNonTrivialZetaZero) (nRank : ℕ) :
    (nPrimeGap nRank : ℝ) =
      (fnPrimeAtRank nRank : ℝ) *
        (Real.exp (Real.pi * TowerPrimeGapSpan z nRank / rTowerHeight z) - 1) := by
  have hHeightNe : rTowerHeight z ≠ 0 := ne_of_gt (thm_rTowerHeight_positive z)
  have hPiNe : Real.pi ≠ 0 := Real.pi_ne_zero
  have hArg :
      Real.pi * TowerPrimeGapSpan z nRank / rTowerHeight z = rPrimeGapLogRatio nRank := by
    unfold TowerPrimeGapSpan
    field_simp
  rw [hArg]
  have hPosAt : (0 : ℝ) < (fnPrimeAtRank nRank : ℝ) := by
    exact_mod_cast thm_primeAtRank_pos nRank
  have hRatioPos : (0:ℝ) < (fnPrimeSuccessor nRank : ℝ) / (fnPrimeAtRank nRank : ℝ) := by
    apply div_pos
    · have : 0 < fnPrimeSuccessor nRank := by
        unfold fnPrimeSuccessor; exact thm_primeAtRank_pos (nRank + 1)
      exact_mod_cast this
    · exact hPosAt
  unfold rPrimeGapLogRatio
  rw [Real.exp_log hRatioPos]
  have hSum : (fnPrimeSuccessor nRank : ℝ) =
      (fnPrimeAtRank nRank : ℝ) + (nPrimeGap nRank : ℝ) := by
    exact_mod_cast thm_primeSuccessor_eq_add_gap nRank
  rw [hSum]
  field_simp
  ring

/-! ## 5. Passage à écart de hauteur nul — la même lecture, sur toute arête -/

/-- **Un passage d'écart de hauteur nul lit la MÊME portée que son extrémité
gauche, sur N'IMPORTE QUELLE place `n`.**  Reformulation directe de
`thm_towerPrimeGapSpan_eq_iff_height_eq` au niveau d'un `TTowerMemberTransition`
(`TowerTransition.lean`) plutôt que de deux membres nus : c'est le pont exact
entre l'écart de hauteur d'un passage et l'égalité de sa portée première, sur
toute arête, pas seulement celle que le passage produit lui-même. -/
theorem thm_towerPrimeGapSpan_eq_of_heightGap_zero
    (Tr : TTowerMemberTransition) (hZero : Tr.heightGap = 0) (nRank : ℕ) :
    TowerPrimeGapSpan Tr.zRight nRank = TowerPrimeGapSpan Tr.zLeft nRank := by
  rw [thm_towerPrimeGapSpan_eq_iff_height_eq]
  unfold TTowerMemberTransition.heightGap at hZero
  unfold rTowerHeight
  linarith

/-! Surface audit. -/

#check TowerPrimeGapSpan
#check thm_towerPrimeGapSpan_eq_log_one_add
#check thm_towerPrimeGapSpan_diff
#check thm_towerPrimeGapSpan_eq_iff_height_eq
#check thm_towerPrimeGapSpan_gt_iff_height_gt
#check thm_towerPrimeGapSpan_heightGap_formula
#check thm_primeGap_recovered_from_span
#check thm_towerPrimeGapSpan_eq_of_heightGap_zero

end RHV3Lean
