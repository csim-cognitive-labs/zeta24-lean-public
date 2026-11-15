/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TrueTowerState
import RHV3Lean.Objects.ContactsAndCell
import RHV3Lean.Objects.TrueTowerCarrier
import RHV3Lean.Objects.CountingRigidity
import Mathlib.NumberTheory.Bertrand

/-!
# RHV3Lean — le producteur causal de l'état propre canonique

    TRACE_ID              : RHV3-S4-CANONICAL-PRODUCER
    SEMANTIC_OBJECT       : la Tour propre canonique du même membre
    SEMANTIC_STATEMENT    : `TTrueHarmonicTowerState z` reçoit une paire de
                            contacts satisfaisant largeur+loi tangentielle,
                            mais ces deux équations seules sont périodiques :
                            tout décalage entier de l'adresse d'entrée produit
                            un second habitant valide. Ce module ne cherche pas
                            une adresse à partir d'un premier, d'un rang ou
                            d'un comptage : il calcule, en forme close, à
                            partir des seules coordonnées propres du membre
                            (T, phi), la PLUS PETITE adresse dont l'incidence
                            entre dans la région de comptage `x >= 2`, et
                            construit l'état propre à cette adresse.
    MATHEMATICAL_STATEMENT: kappa*(z) = ceil(max(0, (T*log 2 - phi)/pi)) ;
                            C-(z) = x_(kappa*(z)) ; C+(z) = x_(kappa*(z)+1) ;
                            2 <= C-(z).
    MATHEMATICAL_PARENT   : O3 la Tour harmonique ; O4 les contacts et la
                            cellule ; historique `rh_gap_criterion` /
                            `RHV2TrueContacts.lean::canonicalContactAddress`,
                            retrouvé par recherche exhaustive de l'historique
                            Git et porté ici SANS ses coordonnées retirées
                            (aucun champ `kappa`/`m` n'est exposé publiquement :
                            l'adresse reste interne à la définition).
    PROOF_STRATEGY        : la largeur et la loi tangentielle sont déjà
                            prouvées pour TOUTE adresse par les théorèmes
                            génériques de `ContactsAndCell.lean` ; ce module
                            ne fait qu'instancier ces théorèmes génériques à
                            l'adresse calculée, puis borner cette adresse par
                            la même inégalité de plancher que l'historique.
    REQUIRED_LEMMAS       : thm_cellLogDiameter_formula,
                            thm_inversion_recovers_radialPosition,
                            Nat.le_ceil, Real.exp_le_exp, Real.exp_log
    WHY_EACH_LEMMA_EXISTS : les deux premiers portent les deux lois de l'état
                            pour une adresse quelconque ; les trois derniers
                            bornent l'adresse calculée par en dessous et
                            replacent le contact d'entrée au-dessus de deux.
    LEAN_DEFINITION       : rCanonicalContactThreshold, kCanonicalContactAddress,
                            canonicalTrueTowerState, tCanonicalTrueTowerCarrier
    LEAN_THEOREM          : thm_canonicalContactMinus_ge_two,
                            thm_canonicalTrueTowerState_injective
    SAME_MEMBER_CHECK     : thm_canonicalTrueTowerState_injective — spécialise
                            la rigidité générique `thm_same_true_contacts_same_member`
                            au SEUL état canonique, donc deux membres distincts
                            ne peuvent jamais partager cet état.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : sans objet — aucun premier n'entre dans ce module.
    FORBIDDEN_PREMISES    : premier, rang, comptage, N_P, C3 ; toute adresse
                            choisie pour faire correspondre un premier à la
                            cellule.
    NEXT_CONSUMER         : `thm_canonicalCell_foundCount_eq_one` (T1) — mais
                            ce module NE LE PRODUIT PAS et n'y prétend pas.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS            : CONTROL_ONLY / LEGACY.  `kCanonicalContactAddress`
                             est un sélecteur d'adresse entière `k` en forme
                             close : exactement l'objet que le maître
                             mathématique exclut comme objet public de la
                             démonstration (§0, règle 13 : « Aucun `branch`,
                             `k`, `contactIndex`, sélecteur périodique ... ne
                             constitue un objet mathématique public »).  Ce
                             module ne représente donc PAS les vrais contacts
                             du régime réel, qui obéissent à l'inventaire
                             complet des quatre-vingt-dix-neuf contraintes
                             historiques (§0, règle 15) jamais encodées ici.
                             Tout résultat de ce module — y compris sa propre
                             réfutation ci-dessous — porte UNIQUEMENT sur cet
                             objet hors-régime, jamais sur T1 lui-même.

## Avertissement honnête, à lire avant tout réemploi

Ce module ferme exactement une obligation : « aucun producteur canonique des
contacts n'existe » est RÉFUTÉ.  Il n'en ferme aucune autre.

En particulier, `thm_canonicalContactMinus_ge_two` seul n'implique NI que la
cellule `(C-,C+]` contient un premier, NI qu'elle en contient exactement un.
Le corpus historique `rh_gap_criterion` (`RHV2ContactPrimeReadout.lean`)
construit exactement CE calcul de seuil et déclare explicitement, dans son
propre commentaire :

    « Local contact count, with no claim that its value is universally 1 or
      3. »

et garde l'énoncé correspondant (`EveryCanonicalCenterHitsPrime`) comme une
PROPOSITION non prouvée, précisément pour ne jamais la faire passer pour un
théorème.  Ce module fait le même choix : aucun theorem `= 1` n'est énoncé
ici.

De plus, la largeur de la cellule à cette adresse est `pi/T`, qui tend vers
`0` quand `T` croît, alors que le contact d'entrée reste borné près de `2`
(c'est exactement ce que `thm_canonicalContactMinus_ge_two` fixe : l'adresse
est la PLUS PETITE qui atteint `2`, donc `C-` ne s'éloigne pas de `2`).  Une
cellule dont le diamètre logarithmique tend vers `0` autour d'un point fixe
ne peut pas contenir un premier pour la plupart des hauteurs : ceci est un
avertissement mathématique, PAS un theorem Lean de ce module, et il n'est pas
utilisé pour conclure quoi que ce soit ici.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

variable (zUpperZero : TUpperNonTrivialZetaZero)

/-! ## 1. Le seuil de forme close, et l'adresse canonique -/

/-- **Le seuil de forme close** `(T*log 2 - phi)/pi`, fonction des seules
coordonnées propres du membre. -/
noncomputable def rCanonicalContactThreshold : ℝ :=
  (rTowerHeight zUpperZero * Real.log 2 - rTowerPhase zUpperZero) / Real.pi

/-- **L'adresse canonique** : la plus petite adresse entière non négative dont
l'incidence atteint la région de comptage `x >= 2`. Forme close, jamais une
recherche sur les premiers. -/
noncomputable def kCanonicalContactAddress : ℤ :=
  (⌈max 0 (rCanonicalContactThreshold zUpperZero)⌉₊ : ℕ)

/-! ## 2. Les deux lois, instanciées à l'adresse canonique -/

/-- La largeur consécutive à l'adresse canonique, par instanciation du
théorème générique de largeur à `nSpan = 1`. -/
theorem thm_canonicalContact_consecutive_width :
    Real.log (rTowerIncidence zUpperZero (kCanonicalContactAddress zUpperZero + 1)) -
        Real.log (rTowerIncidence zUpperZero (kCanonicalContactAddress zUpperZero)) =
      Real.pi / rZeroHeight zUpperZero.1 := by
  have hStep := thm_rTowerLogIncidence_successor zUpperZero
    (kCanonicalContactAddress zUpperZero)
  unfold rTowerIncidence
  rw [Real.log_exp, Real.log_exp]
  simpa [rTowerHeight] using hStep

/-- La loi tangentielle à l'adresse canonique, par instanciation du théorème
générique d'inversion radiale à cette même adresse. -/
theorem thm_canonicalContact_tangent_law :
    rZeroRadialPosition zUpperZero.1 *
        Real.tan (rZeroHeight zUpperZero.1 *
          Real.log (rTowerIncidence zUpperZero (kCanonicalContactAddress zUpperZero))) =
      rZeroHeight zUpperZero.1 := by
  have hDiv := thm_inversion_recovers_radialPosition zUpperZero
    (⟨kCanonicalContactAddress zUpperZero, 1, by norm_num⟩ : TTowerWindow)
  have hContactMinus :
      rContactMinus zUpperZero
          (⟨kCanonicalContactAddress zUpperZero, 1, by norm_num⟩ : TTowerWindow) =
        rTowerIncidence zUpperZero (kCanonicalContactAddress zUpperZero) := rfl
  rw [hContactMinus] at hDiv
  have hTan :
      Real.tan (rTowerHeight zUpperZero *
          Real.log (rTowerIncidence zUpperZero (kCanonicalContactAddress zUpperZero))) ≠ 0 := by
    intro hz
    rw [hz, div_zero] at hDiv
    exact (ne_of_gt (thm_rTowerRadialPosition_positive zUpperZero)) hDiv
  have hProd := (eq_div_iff hTan).1 hDiv
  simpa [rTowerRadialPosition, rTowerHeight, mul_comm] using hProd

/-! ## 3. L'état propre canonique -/

/-- **L'ETAT PROPRE CANONIQUE.**  Un producteur réel, calculé en forme close
depuis le seul membre, jamais un habitant quelconque du type. -/
noncomputable def canonicalTrueTowerState :
    TTrueHarmonicTowerState zUpperZero where
  contactMinus := rTowerIncidence zUpperZero (kCanonicalContactAddress zUpperZero)
  contactPlus := rTowerIncidence zUpperZero (kCanonicalContactAddress zUpperZero + 1)
  contactMinus_pos := thm_rTowerIncidence_positive zUpperZero _
  contactPlus_pos := thm_rTowerIncidence_positive zUpperZero _
  ordered := thm_rTowerIncidence_strictOrder zUpperZero (by omega)
  consecutive_width := thm_canonicalContact_consecutive_width zUpperZero
  tangent_law := thm_canonicalContact_tangent_law zUpperZero

theorem thm_canonicalTrueTowerState_contactMinus :
    (canonicalTrueTowerState zUpperZero).contactMinus =
      rTowerIncidence zUpperZero (kCanonicalContactAddress zUpperZero) := rfl

/-! ## 4. Admissibilité : le contact d'entrée atteint la région de comptage -/

/-- **Le contact d'entrée canonique est au-dessus de deux.**  L'adresse est la
plus petite qui atteint `x = 2` ; elle ne s'en éloigne donc jamais par choix
d'une adresse plus grande. -/
theorem thm_canonicalContactMinus_ge_two :
    2 ≤ (canonicalTrueTowerState zUpperZero).contactMinus := by
  set t : ℝ := rCanonicalContactThreshold zUpperZero with ht
  set n : ℕ := ⌈max 0 t⌉₊ with hn
  have hmax : max 0 t ≤ (n : ℝ) := Nat.le_ceil _
  have htn : t ≤ (n : ℝ) := le_trans (le_max_right 0 t) hmax
  have hHeight : 0 < rTowerHeight zUpperZero := thm_rTowerHeight_positive zUpperZero
  have hPi : 0 < Real.pi := Real.pi_pos
  have hscaled :
      rTowerHeight zUpperZero * Real.log 2 - rTowerPhase zUpperZero ≤
        (n : ℝ) * Real.pi := by
    have := (div_le_iff₀ hPi).mp htn
    simpa [t, rCanonicalContactThreshold, mul_comm] using this
  have hexponent :
      Real.log 2 ≤
        (rTowerPhase zUpperZero + (n : ℝ) * Real.pi) / rTowerHeight zUpperZero := by
    apply (le_div_iff₀ hHeight).2
    linarith
  have hExp :
      (2 : ℝ) ≤ rTowerIncidence zUpperZero (n : ℤ) := by
    rw [show (2 : ℝ) = Real.exp (Real.log 2) by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]]
    unfold rTowerIncidence rTowerLogIncidence
    apply Real.exp_le_exp.mpr
    push_cast
    exact hexponent
  simpa [canonicalTrueTowerState, kCanonicalContactAddress, n, t] using hExp

/-! ## 5. Rigidité SAME_MEMBER, spécialisée à l'état canonique -/

/-- **Même paire de contacts canoniques, même membre.**  Spécialisation de la
rigidité générique de `TrueTowerState.lean` au seul état canonique. -/
theorem thm_canonicalTrueTowerState_injective
    {zLeft zRight : TUpperNonTrivialZetaZero}
    (hMinus :
      (canonicalTrueTowerState zLeft).contactMinus =
        (canonicalTrueTowerState zRight).contactMinus)
    (hPlus :
      (canonicalTrueTowerState zLeft).contactPlus =
        (canonicalTrueTowerState zRight).contactPlus) :
    zLeft = zRight :=
  TTrueHarmonicTowerState.thm_same_true_contacts_same_member
    (canonicalTrueTowerState zLeft) (canonicalTrueTowerState zRight) hMinus hPlus

/-! ## 6. Le porteur canonique threadé -/

/-- **LE PORTEUR CANONIQUE.**  Un seul état par membre, calculé en forme
close, jamais posé. Ferme la ligne de registre « porteur CANONIQUE déterminé
par les vrais contacts consécutifs ». -/
noncomputable def tCanonicalTrueTowerCarrier : TTrueTowerCarrier where
  fnState := canonicalTrueTowerState

theorem thm_canonicalTrueTowerCarrier_state (zUpperZero : TUpperNonTrivialZetaZero) :
    tCanonicalTrueTowerCarrier.fnState zUpperZero = canonicalTrueTowerState zUpperZero := rfl

/-! ## 7. Ce que ce module ne prétend pas -/

/-- **T1 sur l'état canonique — PROPOSITION SEULE.**
Gardée comme énoncé nommé pour ne jamais être confondue avec un theorem. -/
def PCanonicalCellFoundCountOne : Prop :=
  ∀ zUpperZero : TUpperNonTrivialZetaZero,
    nCellFoundCount (canonicalTrueTowerState zUpperZero).terminalCell = 1

/-! ## 8. Contrôle sur l'adresse hors-régime -- SANS PORTÉE SUR T1

`kCanonicalContactAddress` est un sélecteur d'adresse entière — exactement
l'objet que le maître mathématique exclut comme objet public de la
démonstration (§0, règle 13 ; registre des 99 contraintes, C56/C57/C59).  Ce
qui suit est une preuve valide sur CET objet précis et rien d'autre : ce
n'est ni une fermeture de T1, ni une réfutation de T1.  T1 pour les vrais
contacts du régime réel (verrouillé par von Mangoldt, C48-C52) reste
exactement ce qu'il était : un fait reçu du maître sémantique, non formalisé
ici, ni infirmé ici. -/

theorem thm_canonicalTrueTowerState_contactPlus :
    (canonicalTrueTowerState zUpperZero).contactPlus =
      rTowerIncidence zUpperZero (kCanonicalContactAddress zUpperZero + 1) := rfl

/-- **L'incidence terminale canonique reste bornée par `2*exp(2*pi/T)`.**
Conséquence pure de la minimalité de l'adresse canonique
(`Nat.ceil_lt_add_one`) et de la borne `phi < pi/2` déjà produite
(`thm_rTowerPhase_lt_piDivTwo`) : AUCUNE propriété première n'intervient ici,
seulement la géométrie de l'adresse de forme close. -/
theorem thm_canonicalContactPlus_lt_two_mul_exp_twicePi :
    (canonicalTrueTowerState zUpperZero).contactPlus <
      2 * Real.exp (2 * Real.pi / rTowerHeight zUpperZero) := by
  have hHeight : 0 < rTowerHeight zUpperZero := thm_rTowerHeight_positive zUpperZero
  have hPi : 0 < Real.pi := Real.pi_pos
  have hPhiUpper : rTowerPhase zUpperZero < Real.pi / 2 :=
    thm_rTowerPhase_lt_piDivTwo zUpperZero
  have hCeil :
      ((⌈max 0 (rCanonicalContactThreshold zUpperZero)⌉₊ : ℕ) : ℝ) <
        max 0 (rCanonicalContactThreshold zUpperZero) + 1 :=
    Nat.ceil_lt_add_one (le_max_left 0 _)
  have hKey :
      rTowerPhase zUpperZero +
          (((⌈max 0 (rCanonicalContactThreshold zUpperZero)⌉₊ : ℕ) : ℝ) + 1) * Real.pi <
        rTowerHeight zUpperZero * Real.log 2 + 2 * Real.pi := by
    by_cases ht : 0 ≤ rCanonicalContactThreshold zUpperZero
    · rw [max_eq_right ht] at hCeil ⊢
      have htpi :
          rCanonicalContactThreshold zUpperZero * Real.pi =
            rTowerHeight zUpperZero * Real.log 2 - rTowerPhase zUpperZero := by
        unfold rCanonicalContactThreshold; field_simp
      nlinarith [hCeil, htpi]
    · push_neg at ht
      rw [max_eq_left (le_of_lt ht)] at hCeil ⊢
      simp only [Nat.ceil_zero, Nat.cast_zero] at hCeil ⊢
      have hTlog2pos : 0 < rTowerHeight zUpperZero * Real.log 2 :=
        mul_pos hHeight (Real.log_pos (by norm_num))
      nlinarith [hCeil, hPhiUpper, hTlog2pos]
  have hDivT :
      (rTowerPhase zUpperZero +
          (((⌈max 0 (rCanonicalContactThreshold zUpperZero)⌉₊ : ℕ) : ℝ) + 1) * Real.pi) /
        rTowerHeight zUpperZero <
      Real.log 2 + 2 * Real.pi / rTowerHeight zUpperZero := by
    rw [div_lt_iff₀ hHeight]
    have hExpand :
        (Real.log 2 + 2 * Real.pi / rTowerHeight zUpperZero) * rTowerHeight zUpperZero =
          rTowerHeight zUpperZero * Real.log 2 + 2 * Real.pi := by
      field_simp
    rw [hExpand]
    exact hKey
  have hContactPlus :
      (canonicalTrueTowerState zUpperZero).contactPlus =
        Real.exp
          ((rTowerPhase zUpperZero +
              (((⌈max 0 (rCanonicalContactThreshold zUpperZero)⌉₊ : ℕ) : ℝ) + 1) * Real.pi) /
            rTowerHeight zUpperZero) := by
    rw [thm_canonicalTrueTowerState_contactPlus]
    unfold rTowerIncidence rTowerLogIncidence kCanonicalContactAddress
    push_cast
    congr 1
  rw [hContactPlus, show 2 * Real.exp (2 * Real.pi / rTowerHeight zUpperZero) =
      Real.exp (Real.log 2 + 2 * Real.pi / rTowerHeight zUpperZero) by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]]
  exact Real.exp_lt_exp.mpr hDivT

/-- **Contrôle, sur l'adresse hors-régime uniquement.**  Dès que la hauteur du
membre satisfait la seule borne réelle `2*pi <= log(3/2)*T`, la cellule de
CET état non légitime (§8) ne contient aucun premier -- pas un, zéro. La
fonction de comptage n'est jamais en cause : elle lit fidèlement que les deux
bords tombent dans le même intervalle entier `(2,3)`, qui n'en contient
aucun. Cela ne concerne que `PCanonicalCellFoundCountOne` sur cet objet
précis, jamais T1. -/
theorem thm_canonicalCell_foundCount_eq_zero_of_height_large
    (hT : 2 * Real.pi ≤ Real.log (3 / 2) * rTowerHeight zUpperZero) :
    nCellFoundCount (canonicalTrueTowerState zUpperZero).terminalCell = 0 := by
  have hHeight : 0 < rTowerHeight zUpperZero := thm_rTowerHeight_positive zUpperZero
  have hContactMinusGeTwo : 2 ≤ (canonicalTrueTowerState zUpperZero).contactMinus :=
    thm_canonicalContactMinus_ge_two zUpperZero
  have hWidthPos : 0 < Real.pi / rTowerHeight zUpperZero := div_pos Real.pi_pos hHeight
  have hContactOrder :
      (canonicalTrueTowerState zUpperZero).contactMinus <
        (canonicalTrueTowerState zUpperZero).contactPlus := by
    have hLog := thm_canonicalContact_consecutive_width zUpperZero
    have hWidthPos : 0 < Real.pi / rZeroHeight zUpperZero.1 := div_pos Real.pi_pos zUpperZero.2
    have hLogLt :
        Real.log (rTowerIncidence zUpperZero (kCanonicalContactAddress zUpperZero)) <
          Real.log (rTowerIncidence zUpperZero (kCanonicalContactAddress zUpperZero + 1)) := by
      linarith
    have hExpLt := Real.exp_lt_exp.mpr hLogLt
    rw [Real.exp_log (thm_rTowerIncidence_positive zUpperZero _),
      Real.exp_log (thm_rTowerIncidence_positive zUpperZero _)] at hExpLt
    rwa [thm_canonicalTrueTowerState_contactMinus, thm_canonicalTrueTowerState_contactPlus]
  have hUpperBound := thm_canonicalContactPlus_lt_two_mul_exp_twicePi zUpperZero
  have hExpBound : Real.exp (2 * Real.pi / rTowerHeight zUpperZero) ≤ 3 / 2 := by
    rw [show (3 / 2 : ℝ) = Real.exp (Real.log (3 / 2)) by
      rw [Real.exp_log (by norm_num : (0:ℝ) < 3 / 2)]]
    exact Real.exp_le_exp.mpr ((div_le_iff₀ hHeight).mpr (by linarith [hT]))
  have hContactPlusLtThree : (canonicalTrueTowerState zUpperZero).contactPlus < 3 := by
    nlinarith [hUpperBound, hExpBound]
  have hContactMinusLtThree : (canonicalTrueTowerState zUpperZero).contactMinus < 3 :=
    lt_trans hContactOrder hContactPlusLtThree
  have hFloorMinus :
      ⌊(canonicalTrueTowerState zUpperZero).contactMinus⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by linarith [hContactMinusGeTwo])]
    constructor
    · push_cast; linarith [hContactMinusGeTwo]
    · push_cast; linarith [hContactMinusLtThree]
  have hFloorPlus :
      ⌊(canonicalTrueTowerState zUpperZero).contactPlus⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by linarith [hContactMinusGeTwo, hContactOrder])]
    constructor
    · push_cast; linarith [hContactMinusGeTwo, hContactOrder]
    · push_cast; linarith [hContactPlusLtThree]
  have hRankEq :
      nCellLeftEdgeRank (canonicalTrueTowerState zUpperZero).terminalCell =
        nCellRightEdgeRank (canonicalTrueTowerState zUpperZero).terminalCell := by
    unfold nCellLeftEdgeRank nCellRightEdgeRank nEdgePrimeRank
    rw [show (canonicalTrueTowerState zUpperZero).terminalCell.rLeftEndpoint =
        (canonicalTrueTowerState zUpperZero).contactMinus from rfl,
      show (canonicalTrueTowerState zUpperZero).terminalCell.rRightEndpoint =
        (canonicalTrueTowerState zUpperZero).contactPlus from rfl,
      hFloorMinus, hFloorPlus]
  rw [thm_cellFoundCount_eq_edgeRankDifference, hRankEq, Nat.sub_self]

/-- **`PCanonicalCellFoundCountOne` est FAUSSE.**  Il existe un régime de
hauteur — explicite, réel, non vide — où la cellule canonique ne contient
aucun premier.  Le comptage de Von Mangoldt/Chebyshev est ici innocent : il
mesure fidèlement un intervalle qui, par construction de l'adresse, ne
rencontre aucun entier. -/
theorem thm_PCanonicalCellFoundCountOne_is_false
    (zUpperZero : TUpperNonTrivialZetaZero)
    (hT : 2 * Real.pi ≤ Real.log (3 / 2) * rTowerHeight zUpperZero) :
    ¬ PCanonicalCellFoundCountOne := by
  intro hAll
  have h1 := hAll zUpperZero
  have h0 := thm_canonicalCell_foundCount_eq_zero_of_height_large zUpperZero hT
  omega

/-! ## 9. LE COMPTAGE, sur DEUX fenêtres du MÊME contact d'entrée, pour le
MÊME membre -- `T` et `Beta` ne déterminent PAS le compte

Ce module répond directement à l'objection : « `C+` et `C-` ne sont pas des
chiffres au hasard, les formules tangentielles les lient à `T` et `Beta` ».
C'est vrai -- et c'est exactement pour cela que ce qui suit tient : les DEUX
fenêtres ci-dessous partagent EXACTEMENT le même contact d'entrée `C-`
(donc partagent `T`, `Beta`, et l'adresse d'entrée), pour le MÊME membre, et
satisfont TOUTES DEUX les mêmes deux lois (largeur, loi tangentielle) déjà
produites de façon générique pour toute fenêtre (`ContactsAndCell.lean`).
Elles ne diffèrent QUE par le nombre d'étages -- lui aussi un paramètre
réel de la fenêtre, non fixé par `(T,Beta)`. Le comptage, exécuté par la
fonction de comptage déjà en place (`nCellFoundCount`), donne alors des
cardinaux DIFFÉRENTS : `0` sur l'une, `>= 1` sur l'autre. Le compte n'est
donc pas une fonction de `(T,Beta)` seuls -- il dépend aussi du nombre
d'étages, qui est un DEGRÉ DE LIBERTÉ non résolu par les deux équations. -/

/-- **La fenêtre à un seul étage**, identique à celle de `canonicalTrueTowerState`. -/
noncomputable def tWindowSpanOne (zUpperZero : TUpperNonTrivialZetaZero) : TTowerWindow where
  kEntryAddress := kCanonicalContactAddress zUpperZero
  nSpan := 1
  hSpanPositive := Nat.one_pos

/-- **Le nombre d'étages nécessaire pour doubler le contact d'entrée**, calculé
depuis la seule hauteur -- jamais depuis un premier, un rang ou un comptage. -/
noncomputable def nSpanDoubling (zUpperZero : TUpperNonTrivialZetaZero) : ℕ :=
  ⌈rTowerHeight zUpperZero * Real.log 2 / Real.pi⌉₊

theorem thm_nSpanDoubling_pos (zUpperZero : TUpperNonTrivialZetaZero) :
    0 < nSpanDoubling zUpperZero := by
  unfold nSpanDoubling
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos (thm_rTowerHeight_positive zUpperZero) (Real.log_pos (by norm_num)))
    Real.pi_pos

/-- **La fenêtre qui double le contact d'entrée**, même adresse d'entrée que
`tWindowSpanOne`, même membre, seul le nombre d'étages diffère. -/
noncomputable def tWindowSpanDoubling (zUpperZero : TUpperNonTrivialZetaZero) : TTowerWindow where
  kEntryAddress := kCanonicalContactAddress zUpperZero
  nSpan := nSpanDoubling zUpperZero
  hSpanPositive := thm_nSpanDoubling_pos zUpperZero

theorem thm_sameEntryContact (zUpperZero : TUpperNonTrivialZetaZero) :
    rContactMinus zUpperZero (tWindowSpanOne zUpperZero) =
      rContactMinus zUpperZero (tWindowSpanDoubling zUpperZero) := rfl

/-- **Le rapport des contacts atteint deux** dès que le nombre d'étages atteint
`nSpanDoubling`. Conséquence directe du décalage logarithmique générique déjà
produit (`thm_rTowerLogIncidence_shift`), jamais d'une nouvelle primitive. -/
theorem thm_contactPlus_doubling_ge_twice_contactMinus (zUpperZero : TUpperNonTrivialZetaZero) :
    2 * rContactMinus zUpperZero (tWindowSpanOne zUpperZero) ≤
      rContactPlus zUpperZero (tWindowSpanDoubling zUpperZero) := by
  have hHeight : 0 < rTowerHeight zUpperZero := thm_rTowerHeight_positive zUpperZero
  have hShift :
      rTowerLogIncidence zUpperZero
          (kTerminalAddress (tWindowSpanDoubling zUpperZero)) -
        rTowerLogIncidence zUpperZero (kCanonicalContactAddress zUpperZero) =
        (nSpanDoubling zUpperZero : ℝ) * Real.pi / rTowerHeight zUpperZero := by
    have := thm_rTowerLogIncidence_shift zUpperZero (kCanonicalContactAddress zUpperZero)
      (nSpanDoubling zUpperZero : ℤ)
    unfold kTerminalAddress tWindowSpanDoubling
    push_cast at this ⊢
    linarith [this]
  have hNge : rTowerHeight zUpperZero * Real.log 2 / Real.pi ≤
      (nSpanDoubling zUpperZero : ℝ) := Nat.le_ceil _
  have hRatio :
      Real.log 2 ≤ (nSpanDoubling zUpperZero : ℝ) * Real.pi / rTowerHeight zUpperZero := by
    rw [le_div_iff₀ hHeight]
    rw [div_le_iff₀ Real.pi_pos] at hNge
    nlinarith [hNge]
  have hLogGe :
      rTowerLogIncidence zUpperZero (kCanonicalContactAddress zUpperZero) + Real.log 2 ≤
        rTowerLogIncidence zUpperZero (kTerminalAddress (tWindowSpanDoubling zUpperZero)) := by
    linarith [hShift, hRatio]
  have hExp :
      Real.exp (rTowerLogIncidence zUpperZero (kCanonicalContactAddress zUpperZero)) *
          Real.exp (Real.log 2) ≤
        Real.exp
          (rTowerLogIncidence zUpperZero (kTerminalAddress (tWindowSpanDoubling zUpperZero))) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hLogGe
  rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at hExp
  unfold rContactMinus rContactPlus rTowerIncidence tWindowSpanOne
  show 2 * Real.exp (rTowerLogIncidence zUpperZero (kCanonicalContactAddress zUpperZero)) ≤
    Real.exp (rTowerLogIncidence zUpperZero (kTerminalAddress (tWindowSpanDoubling zUpperZero)))
  linarith [hExp]

/-- **LE COMPTAGE, exécuté.**  Sur la fenêtre doublante, la cellule contient AU
MOINS un premier -- par le postulat de Bertrand (`Nat.exists_prime_lt_and_le_two_mul`),
appliqué au seul plancher entier du contact d'entrée, déjà connu `>= 2`. Aucun
premier n'est choisi ni ciblé : le témoin vient de Bertrand, jamais d'une
adresse. -/
theorem thm_tWindowSpanDoubling_foundCount_ge_one (zUpperZero : TUpperNonTrivialZetaZero) :
    1 ≤ nCellFoundCount (tCellAlgebraicInterval zUpperZero (tWindowSpanDoubling zUpperZero)) := by
  set tInterval := tCellAlgebraicInterval zUpperZero (tWindowSpanDoubling zUpperZero) with hIdef
  have hCMinusGeTwo : 2 ≤ rContactMinus zUpperZero (tWindowSpanOne zUpperZero) :=
    thm_canonicalContactMinus_ge_two zUpperZero
  set n0 : ℕ := ⌊rContactMinus zUpperZero (tWindowSpanOne zUpperZero)⌋₊ with hn0def
  have hn0Pos : n0 ≠ 0 := by
    have : 2 ≤ n0 := by
      rw [hn0def]
      exact Nat.le_floor (by exact_mod_cast hCMinusGeTwo)
    omega
  obtain ⟨p, hp, hpLower, hpUpper⟩ := Nat.exists_prime_lt_and_le_two_mul n0 hn0Pos
  have hFloorLt : (n0 : ℝ) ≤ rContactMinus zUpperZero (tWindowSpanOne zUpperZero) :=
    Nat.floor_le (le_trans (by norm_num) hCMinusGeTwo)
  have hLtCell : rContactMinus zUpperZero (tWindowSpanOne zUpperZero) < (p : ℝ) := by
    have hp1 : (n0 : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hpLower
    have hFloorLt' :
        rContactMinus zUpperZero (tWindowSpanOne zUpperZero) < (n0 : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    linarith
  have hLeCell : (p : ℝ) ≤ rContactPlus zUpperZero (tWindowSpanDoubling zUpperZero) := by
    have hp2 : (p : ℝ) ≤ 2 * (n0 : ℝ) := by exact_mod_cast hpUpper
    have h2n0 : 2 * (n0 : ℝ) ≤ 2 * rContactMinus zUpperZero (tWindowSpanOne zUpperZero) := by
      linarith [hFloorLt]
    linarith [hp2, h2n0, thm_contactPlus_doubling_ge_twice_contactMinus zUpperZero]
  have hMem : p ∈ sAlgebraicIntervalFoundPrimes tInterval :=
    (thm_mem_foundPrimes_iff tInterval p).mpr
      ⟨hp,
        by
          show rContactMinus zUpperZero (tWindowSpanDoubling zUpperZero) < (p : ℝ)
          rw [← thm_sameEntryContact]; exact hLtCell,
        by show (p : ℝ) ≤ rContactPlus zUpperZero (tWindowSpanDoubling zUpperZero)
           exact hLeCell⟩
  unfold nCellFoundCount
  exact Finset.card_pos.mpr ⟨p, hMem⟩

/-- **LE THÉORÈME DEMANDÉ.**  Pour le MÊME membre -- même `T`, même `Beta`,
même contact d'entrée -- deux fenêtres légitimes (satisfaisant toutes deux les
mêmes lois de largeur et de tangente) donnent des comptages DIFFÉRENTS. `T` et
`Beta` déterminent bien `C-` et la LOI que satisfait `C+`, mais pas le nombre
d'étages -- donc pas le compte. Ce n'est pas une hypothèse ajoutée : c'est le
résultat du comptage lui-même, exécuté sur les deux fenêtres. -/
theorem thm_count_not_determined_by_T_beta_alone
    (zUpperZero : TUpperNonTrivialZetaZero)
    (hT : 2 * Real.pi ≤ Real.log (3 / 2) * rTowerHeight zUpperZero) :
    nCellFoundCount (canonicalTrueTowerState zUpperZero).terminalCell = 0 ∧
      1 ≤ nCellFoundCount (tCellAlgebraicInterval zUpperZero (tWindowSpanDoubling zUpperZero)) :=
  ⟨thm_canonicalCell_foundCount_eq_zero_of_height_large zUpperZero hT,
    thm_tWindowSpanDoubling_foundCount_ge_one zUpperZero⟩

/-! ## 10. CORRECTION : le degré de liberté n'est pas `m` (fixé à un dans la
cellule élémentaire), c'est `k` -- exactement l'entier libre des formules
convenues

`C- = exp((phi+k*pi)/T)`, `C+ = exp((phi+(k+1)*pi)/T)` : `k` apparaît, libre,
DANS les formules elles-mêmes. La section précédente faisait varier `m` (le
nombre d'étages) ; dans la cellule élémentaire (`m=1` toujours), ce n'était
pas le bon paramètre. Cette section refait EXACTEMENT la même démonstration
avec `m=1` fixé partout, en ne faisant varier QUE `k` -- le seul degré de
liberté que les formules convenues elles-mêmes exhibent. -/

/-- **Le prédécesseur de l'adresse canonique reste sous deux.**  Conséquence
directe de la minimalité de `kCanonicalContactAddress` (le plus petit `k`
atteignant `x>=2`) : `k-1` ne l'atteint pas encore. Aucune propriété première
n'intervient. -/
theorem thm_canonicalContactMinus_pred_lt_two
    (hT : 2 * Real.pi ≤ Real.log (3 / 2) * rTowerHeight zUpperZero) :
    rTowerIncidence zUpperZero (kCanonicalContactAddress zUpperZero - 1) < 2 := by
  have hHeight : 0 < rTowerHeight zUpperZero := thm_rTowerHeight_positive zUpperZero
  have hPhiUpper : rTowerPhase zUpperZero < Real.pi / 2 := thm_rTowerPhase_lt_piDivTwo zUpperZero
  have hlog23 : Real.log (3 / 2 : ℝ) < Real.log 2 := Real.log_lt_log (by norm_num) (by norm_num)
  have htPos : 0 < rCanonicalContactThreshold zUpperZero := by
    unfold rCanonicalContactThreshold
    rw [lt_div_iff₀ Real.pi_pos]
    have hTlog2_gt :
        rTowerHeight zUpperZero * Real.log (3 / 2) < rTowerHeight zUpperZero * Real.log 2 :=
      mul_lt_mul_of_pos_left hlog23 hHeight
    have hTlog23_ge : 2 * Real.pi ≤ rTowerHeight zUpperZero * Real.log (3 / 2) := by
      rw [mul_comm (rTowerHeight zUpperZero) (Real.log (3 / 2 : ℝ))]; exact hT
    linarith [hPhiUpper, Real.pi_pos]
  set n : ℕ := ⌈max 0 (rCanonicalContactThreshold zUpperZero)⌉₊ with hndef
  have hmaxEq : max 0 (rCanonicalContactThreshold zUpperZero) =
      rCanonicalContactThreshold zUpperZero := max_eq_right (le_of_lt htPos)
  have hnPos : 0 < n := by
    rw [hndef, hmaxEq]
    exact Nat.ceil_pos.mpr htPos
  have hCeilEq : n = ⌈rCanonicalContactThreshold zUpperZero⌉₊ := by rw [hndef, hmaxEq]
  have hPredLt : ((n : ℝ) - 1) < rCanonicalContactThreshold zUpperZero := by
    have hlt_nat : n - 1 < ⌈rCanonicalContactThreshold zUpperZero⌉₊ := by
      rw [← hCeilEq]; omega
    have hlt_real := Nat.lt_ceil.mp hlt_nat
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
    rwa [hcast] at hlt_real
  have htpi :
      rCanonicalContactThreshold zUpperZero * Real.pi =
        rTowerHeight zUpperZero * Real.log 2 - rTowerPhase zUpperZero := by
    unfold rCanonicalContactThreshold; field_simp
  have hKey :
      rTowerPhase zUpperZero + ((n : ℝ) - 1) * Real.pi <
        rTowerHeight zUpperZero * Real.log 2 := by
    nlinarith [hPredLt, htpi, Real.pi_pos]
  have hDivT :
      (rTowerPhase zUpperZero + ((n : ℝ) - 1) * Real.pi) / rTowerHeight zUpperZero <
        Real.log 2 := by
    rw [div_lt_iff₀ hHeight]; linarith [hKey]
  have hCast : ((kCanonicalContactAddress zUpperZero - 1 : ℤ) : ℝ) = (n : ℝ) - 1 := by
    unfold kCanonicalContactAddress
    push_cast
    ring
  change Real.exp (rTowerLogIncidence zUpperZero (kCanonicalContactAddress zUpperZero - 1)) < 2
  unfold rTowerLogIncidence
  rw [hCast]
  rw [show (2:ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]]
  exact Real.exp_lt_exp.mpr hDivT

/-- **La fenêtre AU MÊME `m=1`, décalée d'UN SEUL pas de `k`.** -/
noncomputable def tWindowPred (zUpperZero : TUpperNonTrivialZetaZero) : TTowerWindow where
  kEntryAddress := kCanonicalContactAddress zUpperZero - 1
  nSpan := 1
  hSpanPositive := Nat.one_pos

theorem thm_tWindowPred_contactPlus_eq_canonicalContactMinus
    (zUpperZero : TUpperNonTrivialZetaZero) :
    rContactPlus zUpperZero (tWindowPred zUpperZero) =
      (canonicalTrueTowerState zUpperZero).contactMinus := by
  change rTowerIncidence zUpperZero (kTerminalAddress (tWindowPred zUpperZero)) =
    rTowerIncidence zUpperZero (kCanonicalContactAddress zUpperZero)
  congr 1
  unfold kTerminalAddress tWindowPred
  push_cast
  ring

/-- **LE COMPTAGE CORRIGÉ.**  Même `T`, même `Beta`, même `m=1` (la cellule
élémentaire convenue) -- SEUL `k` diffère d'un pas.  Le premier `2` tombe
exactement dans la cellule décalée : le compte y est `>=1`, jamais `0`. -/
theorem thm_tWindowPred_foundCount_ge_one
    (hT : 2 * Real.pi ≤ Real.log (3 / 2) * rTowerHeight zUpperZero) :
    1 ≤ nCellFoundCount (tCellAlgebraicInterval zUpperZero (tWindowPred zUpperZero)) := by
  have hLt : rContactMinus zUpperZero (tWindowPred zUpperZero) < 2 := by
    exact thm_canonicalContactMinus_pred_lt_two zUpperZero hT
  have hLe : (2:ℝ) ≤ rContactPlus zUpperZero (tWindowPred zUpperZero) := by
    rw [thm_tWindowPred_contactPlus_eq_canonicalContactMinus]
    exact thm_canonicalContactMinus_ge_two zUpperZero
  have hMem : (2:ℕ) ∈
      sAlgebraicIntervalFoundPrimes (tCellAlgebraicInterval zUpperZero (tWindowPred zUpperZero)) :=
    (thm_mem_foundPrimes_iff _ 2).mpr ⟨Nat.prime_two, by exact_mod_cast hLt, by exact_mod_cast hLe⟩
  unfold nCellFoundCount
  exact Finset.card_pos.mpr ⟨2, hMem⟩

/-- **LE THÉORÈME DEMANDÉ, CORRIGÉ.**  Dans la cellule élémentaire convenue
(`m=1` fixé partout, jamais varié), pour le MÊME membre -- même `T`, même
`Beta` -- deux valeurs de l'entier `k` des formules `C- = exp((phi+k*pi)/T)`
donnent des comptages DIFFÉRENTS : `0` à l'adresse canonique, `>=1` à
l'adresse immédiatement précédente. `T` et `Beta` fixent bien `C-` et la loi
de `C+` UNE FOIS `k` choisi -- mais ne fixent pas `k` lui-même, qui reste le
degré de liberté périodique déjà documenté dans ce module (§ ouverture) et
exclu comme objet public par le maître mathématique (règle 13). -/
theorem thm_count_not_determined_by_T_beta_alone_v2
    (zUpperZero : TUpperNonTrivialZetaZero)
    (hT : 2 * Real.pi ≤ Real.log (3 / 2) * rTowerHeight zUpperZero) :
    nCellFoundCount (canonicalTrueTowerState zUpperZero).terminalCell = 0 ∧
      1 ≤ nCellFoundCount (tCellAlgebraicInterval zUpperZero (tWindowPred zUpperZero)) :=
  ⟨thm_canonicalCell_foundCount_eq_zero_of_height_large zUpperZero hT,
    thm_tWindowPred_foundCount_ge_one zUpperZero hT⟩

end RHV3Lean
