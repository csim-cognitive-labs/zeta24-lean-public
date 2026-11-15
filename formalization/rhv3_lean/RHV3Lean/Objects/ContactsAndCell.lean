/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.HarmonicTower
import RHV3Lean.Objects.AlgebraicAxis

/-!
# RHV3Lean — O4, les contacts et la cellule terminale

    TRACE_ID              : RHV3-O4
    SEMANTIC_OBJECT       : O4 — les contacts et la cellule terminale
    SEMANTIC_STATEMENT    : les contacts sont les deux points où la Tour
                            rencontre l'axe algébrique, orientés l'un par
                            rapport à l'autre, et la cellule qu'ils délimitent
                            contient l'intervalle algébrique et l'ensemble
                            ordonné, en général pluriel, des nombres trouvés.
    MATHEMATICAL_STATEMENT: C- = x_kappa, C+ = x_(kappa+m), 0 < C- < C+,
                            I_C = (C-, C+], log(C+/C-) = m*pi/T, et
                            (C-, C+, m, orientation) -> (T, beta) -> rho est une
                            application, jamais multivaluée.
    MATHEMATICAL_PARENT   : O3 — la Tour harmonique ; O2 — l'axe algébrique.
    PROOF_STRATEGY        : les deux contacts sont deux incidences de la Tour du
                            MÊME membre, aux adresses kappa et kappa+m ; l'ordre
                            strict vient de l'ordre strict des incidences ; le
                            diamètre vient du décalage d'adresse ; l'inversion
                            RETROUVE la hauteur depuis le diamètre, puis la
                            position radiale depuis le contact d'entrée par la
                            formule tangentielle, donc le membre lui-même.
    REQUIRED_LEMMAS       : thm_rTowerIncidence_strictOrder,
                            thm_rTowerLogIncidence_shift,
                            thm_rTowerLogIncidence_phaseEquation,
                            Real.tan_arctan, Real.tan_periodic
    WHY_EACH_LEMMA_EXISTS : les trois premiers donnent l'ordre, le diamètre et
                            l'équation d'incidence ; les deux derniers ramènent
                            la tangente de la phase décalée d'un multiple entier
                            de pi à la tangente de la phase, ce qui rend la
                            position radiale depuis le seul contact d'entrée.
    LEAN_DEFINITION       : TTowerWindow, rContactMinus, rContactPlus,
                            sCellCarrier, tCellAlgebraicInterval,
                            rCellLogDiameter
    LEAN_THEOREM          : thm_contacts_strictOrder, thm_cellCarrier_eq_Ioc,
                            thm_cellLogDiameter_formula,
                            thm_inversion_recovers_height,
                            thm_inversion_recovers_radialPosition,
                            thm_sameContactData_sameMember
    SAME_MEMBER_CHECK     : thm_sameContactData_sameMember — même donnée
                            complète de contacts implique le même membre ;
                            l'inversion est une application, jamais
                            multivaluée.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre dans ce module ;
                            la cellule est produite AVANT tout comptage.
    FORBIDDEN_PREMISES    : choisir l'adresse d'entrée ou le nombre d'étages à
                            partir d'un premier, d'un rang, d'un comptage ou
                            d'une histoire première ; reconstruire la provenance
                            du membre après coup au lieu de la porter par
                            l'inversion.
    NEXT_CONSUMER         : O10 (la rigidité de comptage), puis O5
                            (l'occurrence première).
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiom` nouveau.
-/

namespace RHV3Lean

/-! ## 1. La fenêtre de Tour, et ses deux contacts -/

/-- **La fenêtre de la Tour d'un membre** : son adresse d'entrée et son nombre
d'étages.  Ce sont les deux coordonnées discrètes lues sur la Tour ; rien ici
ne les choisit à partir d'un premier ou d'un comptage. -/
structure TTowerWindow where
  /-- Adresse d'entrée `kappa`. -/
  kEntryAddress : ℤ
  /-- Nombre d'étages `m`. -/
  nSpan : ℕ
  /-- Le nombre d'étages est strictement positif. -/
  hSpanPositive : 0 < nSpan

variable (zUpperZero : TUpperNonTrivialZetaZero) (tWindow : TTowerWindow)

/-- L'adresse terminale `kappa + m`. -/
def kTerminalAddress : ℤ := tWindow.kEntryAddress + (tWindow.nSpan : ℤ)

/-- **Le contact d'entrée** `C- = x_kappa`. -/
noncomputable def rContactMinus : ℝ :=
  rTowerIncidence zUpperZero tWindow.kEntryAddress

/-- **Le contact terminal** `C+ = x_(kappa+m)`. -/
noncomputable def rContactPlus : ℝ :=
  rTowerIncidence zUpperZero (kTerminalAddress tWindow)

theorem thm_contactMinus_positive : 0 < rContactMinus zUpperZero tWindow :=
  thm_rTowerIncidence_positive _ _

theorem thm_contactPlus_positive : 0 < rContactPlus zUpperZero tWindow :=
  thm_rTowerIncidence_positive _ _

/-- **L'orientation des deux contacts** : `C- < C+`, parce que le nombre
d'étages est strictement positif et que les incidences croissent strictement
avec l'adresse. -/
theorem thm_contacts_strictOrder :
    rContactMinus zUpperZero tWindow < rContactPlus zUpperZero tWindow := by
  apply thm_rTowerIncidence_strictOrder
  have hSpan : (0 : ℤ) < (tWindow.nSpan : ℤ) := by exact_mod_cast tWindow.hSpanPositive
  unfold kTerminalAddress
  omega

/-! ## 2. La cellule terminale -/

/-- **La cellule terminale** `I_C = (C-, C+]`. -/
noncomputable def sCellCarrier : Set ℝ :=
  Set.Ioc (rContactMinus zUpperZero tWindow) (rContactPlus zUpperZero tWindow)

theorem thm_cellCarrier_eq_Ioc :
    sCellCarrier zUpperZero tWindow =
      Set.Ioc (rContactMinus zUpperZero tWindow)
        (rContactPlus zUpperZero tWindow) := rfl

/-- **La cellule EST un intervalle algébrique** au sens de O2 : elle porte donc
un ensemble de nombres trouvés fini, ordonné, déterminé, et en général
pluriel. -/
noncomputable def tCellAlgebraicInterval : TAlgebraicInterval where
  rLeftEndpoint := rContactMinus zUpperZero tWindow
  rRightEndpoint := rContactPlus zUpperZero tWindow
  hLeftPositive := thm_contactMinus_positive zUpperZero tWindow
  hOrdered := thm_contacts_strictOrder zUpperZero tWindow

/-- L'appartenance à la cellule est exactement l'appartenance à l'intervalle
algébrique qu'elle porte. -/
theorem thm_mem_cellCarrier_iff (rPoint : ℝ) :
    rPoint ∈ sCellCarrier zUpperZero tWindow ↔
      (tCellAlgebraicInterval zUpperZero tWindow).rLeftEndpoint < rPoint ∧
        rPoint ≤ (tCellAlgebraicInterval zUpperZero tWindow).rRightEndpoint :=
  Iff.rfl

/-! ## 3. Le diamètre, et l'inversion qui RETROUVE le membre -/

/-- **Le diamètre logarithmique de la cellule.** -/
noncomputable def rCellLogDiameter : ℝ :=
  Real.log (rContactPlus zUpperZero tWindow) -
    Real.log (rContactMinus zUpperZero tWindow)

/-- **Le diamètre vaut exactement `m*pi/T`.** -/
theorem thm_cellLogDiameter_formula :
    rCellLogDiameter zUpperZero tWindow =
      (tWindow.nSpan : ℝ) * Real.pi / rTowerHeight zUpperZero := by
  unfold rCellLogDiameter rContactPlus rContactMinus rTowerIncidence
  rw [Real.log_exp, Real.log_exp]
  simpa [kTerminalAddress] using
    thm_rTowerLogIncidence_shift zUpperZero tWindow.kEntryAddress
      (tWindow.nSpan : ℤ)

theorem thm_cellLogDiameter_positive :
    0 < rCellLogDiameter zUpperZero tWindow := by
  rw [thm_cellLogDiameter_formula]
  have hSpan : (0 : ℝ) < (tWindow.nSpan : ℝ) := by exact_mod_cast tWindow.hSpanPositive
  exact div_pos (mul_pos hSpan Real.pi_pos) (thm_rTowerHeight_positive zUpperZero)

/-- **L'INVERSION — la hauteur est RETROUVEE depuis les contacts.**

`T = m*pi / (log C+ - log C-)`.  La hauteur du membre n'est pas conservée à
côté de la cellule : elle est lisible dans la cellule elle-même.  C'est ce qui
fait que la provenance du membre est portée par l'inversion, et non
reconstruite après coup. -/
theorem thm_inversion_recovers_height :
    rTowerHeight zUpperZero =
      (tWindow.nSpan : ℝ) * Real.pi / rCellLogDiameter zUpperZero tWindow := by
  have hHeight : 0 < rTowerHeight zUpperZero := thm_rTowerHeight_positive zUpperZero
  have hSpan : (0 : ℝ) < (tWindow.nSpan : ℝ) := by exact_mod_cast tWindow.hSpanPositive
  rw [thm_cellLogDiameter_formula]
  field_simp

/-- **L'INVERSION — la position radiale est RETROUVEE depuis le contact
d'entrée.**

`beta = T / tan(T * log C-)`.  L'équation d'incidence donne
`T*log C- = phi + kappa*pi`, et la tangente est invariante par un multiple
entier de `pi`, donc `tan(T*log C-) = tan(phi) = T/beta`. -/
theorem thm_inversion_recovers_radialPosition :
    rTowerRadialPosition zUpperZero =
      rTowerHeight zUpperZero /
        Real.tan (rTowerHeight zUpperZero *
          Real.log (rContactMinus zUpperZero tWindow)) := by
  have hRadial : 0 < rTowerRadialPosition zUpperZero :=
    thm_rTowerRadialPosition_positive zUpperZero
  have hHeight : rTowerHeight zUpperZero ≠ 0 :=
    ne_of_gt (thm_rTowerHeight_positive zUpperZero)
  have hLogContact :
      Real.log (rContactMinus zUpperZero tWindow) =
        rTowerLogIncidence zUpperZero tWindow.kEntryAddress := by
    unfold rContactMinus rTowerIncidence
    exact Real.log_exp _
  have hPhase :
      rTowerHeight zUpperZero * Real.log (rContactMinus zUpperZero tWindow) =
        rTowerPhase zUpperZero + (tWindow.kEntryAddress : ℝ) * Real.pi := by
    rw [hLogContact]
    exact thm_rTowerLogIncidence_phaseEquation zUpperZero tWindow.kEntryAddress
  rw [hPhase, (Real.tan_periodic.int_mul tWindow.kEntryAddress) (rTowerPhase zUpperZero),
    rTowerPhase, Real.tan_arctan]
  field_simp

/-- **RIGIDITE — même donnée complète de contacts, même membre.**

L'inversion `(C-, C+, m) -> (T, beta) -> rho` est une application, jamais une
correspondance à plusieurs valeurs.  Deux membres dont les fenêtres ont le même
nombre d'étages et produisent les deux mêmes contacts sont le même membre. -/
theorem thm_sameContactData_sameMember
    {zLeftZero zRightZero : TUpperNonTrivialZetaZero}
    {tLeftWindow tRightWindow : TTowerWindow}
    (hSameSpan : tLeftWindow.nSpan = tRightWindow.nSpan)
    (hSameContactMinus :
      rContactMinus zLeftZero tLeftWindow = rContactMinus zRightZero tRightWindow)
    (hSameContactPlus :
      rContactPlus zLeftZero tLeftWindow = rContactPlus zRightZero tRightWindow) :
    zLeftZero = zRightZero := by
  have hSameDiameter :
      rCellLogDiameter zLeftZero tLeftWindow =
        rCellLogDiameter zRightZero tRightWindow := by
    unfold rCellLogDiameter
    rw [hSameContactMinus, hSameContactPlus]
  have hSameHeight : rTowerHeight zLeftZero = rTowerHeight zRightZero := by
    rw [thm_inversion_recovers_height zLeftZero tLeftWindow,
      thm_inversion_recovers_height zRightZero tRightWindow, hSameDiameter,
      hSameSpan]
  have hSameRadial :
      rTowerRadialPosition zLeftZero = rTowerRadialPosition zRightZero := by
    rw [thm_inversion_recovers_radialPosition zLeftZero tLeftWindow,
      thm_inversion_recovers_radialPosition zRightZero tRightWindow,
      hSameHeight, hSameContactMinus]
  have hSameMember : zLeftZero.1 = zRightZero.1 :=
    thm_zero_identity_of_sameSupport (Complex.ext hSameRadial hSameHeight)
  exact Subtype.ext hSameMember

end RHV3Lean
