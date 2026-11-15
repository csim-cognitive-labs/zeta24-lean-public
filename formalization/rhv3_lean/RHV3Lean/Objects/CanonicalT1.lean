/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TrueTowerCarrier

/-!
# RHV3Lean — T1, le vrai producteur, sur un porteur générique opaque

    TRACE_ID              : RHV3-T1
    SEMANTIC_OBJECT       : T1 — localisation première unique de la cellule du
                            même membre.
    SEMANTIC_STATEMENT    : la géométrie du régime fixe un centre unique C_Z de
                            la cellule (maître sémantique §4/§9) ; ce centre est
                            occupé par un vrai premier canonique, lu par la
                            seule fonction de comptage de Von Mangoldt sur
                            l'intervalle algébrique produit par les deux vrais
                            contacts du même membre — jamais par une borne de
                            largeur comparée à un écart premier.
    MATHEMATICAL_STATEMENT: a=pi(C-), b=pi(C+), N_P=b-a ; le régime de centre
                            unique donne N_P=1, d'où P_Z=C_Z=C3 comme unique
                            premier de l'intervalle (C-,C+].
    MATHEMATICAL_PARENT   : O4 (contacts et cellule), O10 (comptage), §9 et
                            §13.1 (composition événementielle, ACQUIS) du
                            maître mathématique.
    PROOF_STRATEGY        : `TTrueTowerCarrier` reste OPAQUE — ses deux
                            équations (largeur, loi tangentielle) ne sont
                            JAMAIS analysées pour en tirer une unicité de
                            branche, exactement comme le maître Lean §4
                            l'interdit ("T1 ne doit pas être recherché sous la
                            forme largeur -> gaps -> N_P=1"). Le régime de
                            centre unique est reçu comme un fait ACQUIS et
                            nommé, discuté et confirmé explicitement par
                            l'utilisateur (préalable, "1 zéro non trivial = 1
                            et un seul premier", "utiliser la fonction de
                            comptage de Von Mangoldt et rien d'autre") ; ce
                            module consomme uniquement `thm_cellFoundCount_eq_
                            one_iff_existsUniquePrime` (CountingRigidity.lean)
                            et `thm_carrierCentralPrime_is_C3`
                            (TrueTowerCarrier.lean), tous deux déjà produits.
    REQUIRED_LEMMAS       : thm_cellFoundCount_eq_one_iff_existsUniquePrime,
                            thm_carrierCentralPrime_is_C3,
                            thm_carrierCentralPrime_isPrime,
                            thm_carrierCentralPrime_in_cell
    WHY_EACH_LEMMA_EXISTS : le premier transcrit N_P=1 en existence-et-unicité
                            du premier de la cellule ; les trois autres lisent
                            C3 sur cette même cellule sans nouvelle preuve.
    LEAN_DEFINITION       : PUniqueCenterRegime
    LEAN_THEOREM          : thm_T1_existsUniquePrime,
                            thm_T1_centralPrime_eq_C3,
                            thm_T1_centralPrime_unique
    SAME_MEMBER_CHECK     : hérité de `TTrueTowerCarrier` — toutes les lectures
                            restent fonctions du seul membre
                            (thm_carrierReadings_are_functions_of_member).
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : le premier unique est lu dans l'unique histoire
                            première de O6, par O10 seul.
    FORBIDDEN_PREMISES    : analyser les deux équations de `TTrueHarmonicTowerState`
                            pour en tirer une unicité de branche ; substituer
                            `tRatioFourOperator` ou `tPrincipalBranchCarrier`
                            au porteur générique `tCarrier` ; recevoir un
                            premier, un rang ou C3 comme hypothèse libre.
    NEXT_CONSUMER         : le rang canonique, l'occurrence complète, T2.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED pour la composition ; `PUniqueCenterRegime`
                            reste un Prop nommé, non prouvé ici — reçu comme
                            fait ACQUIS par le maître sémantique (§9), jamais
                            comme raccourci circulaire (il n'apparaît dans
                            aucun champ de structure et n'est jamais confondu
                            avec sa propre conclusion).

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau. `PUniqueCenterRegime`
n'est jamais utilisé silencieusement : il figure explicitement comme
hypothèse de chaque theorem qui en dépend.
-/

namespace RHV3Lean

namespace TTrueTowerCarrier

variable (tCarrier : TTrueTowerCarrier)

/-! ## 1. Le régime de centre unique, reçu comme acquis, jamais dérivé d'une
largeur -/

/-- **Le régime de centre unique** : pour tout membre, la cellule de son propre
état porte exactement un premier canonique. C'est le contenu du théorème de
composition événementielle (maître mathématique §13.1, ACQUIS) une fois la
reconstruction zéro-source disponible ; il n'est PAS dérivé ici d'une
comparaison de largeur à un écart premier (interdit par le maître Lean §4). -/
def PUniqueCenterRegime : Prop :=
  ∀ zUpperZero : TUpperNonTrivialZetaZero,
    nCellFoundCount (tCarrier.tCarrierCell zUpperZero) = 1

/-- **T1, sous sa forme de rangs de bord.**  Le régime de centre unique est
exactement l'égalité `R = L + 1` entre les deux rangs de comptage aux bords de
la cellule du membre — jamais une comparaison de largeur à un écart premier.
Transcription pure de `thm_cellFoundCount_eq_edgeRankDifference`
(CountingRigidity.lean), sans aucune hypothèse ni construction nouvelle : ce
n'est pas un second énoncé de T1, c'est le même `PUniqueCenterRegime` relu à
travers une égalité déjà prouvée entre `nCellFoundCount` et la différence des
deux rangs de bord. -/
theorem thm_T1_iff_rightEdgeRank_eq_leftEdgeRank_succ :
    tCarrier.PUniqueCenterRegime ↔
      ∀ zUpperZero : TUpperNonTrivialZetaZero,
        nCellRightEdgeRank (tCarrier.tCarrierCell zUpperZero) =
          nCellLeftEdgeRank (tCarrier.tCarrierCell zUpperZero) + 1 := by
  unfold PUniqueCenterRegime
  constructor
  · intro hRegime zUpperZero
    have hDiff := thm_cellFoundCount_eq_edgeRankDifference
      (tCarrier.tCarrierCell zUpperZero)
    have hFound := hRegime zUpperZero
    omega
  · intro hEdges zUpperZero
    rw [thm_cellFoundCount_eq_edgeRankDifference, hEdges zUpperZero]
    omega

/-- Un rang entier tombe dans la fenêtre de bord de la cellule si et seulement
si le premier qu'il porte y atterrit réellement — ni plus ni moins que la
lecture ponctuelle de `thm_foundPrime_iff_rank_between` (déjà prouvée),
recombinée avec `thm_mem_foundPrimes_iff` pour effacer la primalité, toujours
vraie de `fnPrimeAtRank`. Aucune construction nouvelle. -/
private theorem thm_landing_iff_rankWindow
    (tInterval : TAlgebraicInterval) (nRank : ℕ) :
    (tInterval.rLeftEndpoint < (fnPrimeAtRank nRank : ℝ) ∧
      (fnPrimeAtRank nRank : ℝ) ≤ tInterval.rRightEndpoint) ↔
    (nCellLeftEdgeRank tInterval ≤ nRank ∧ nRank < nCellRightEdgeRank tInterval) := by
  rw [← thm_foundPrime_iff_rank_between, thm_mem_foundPrimes_iff]
  exact ⟨fun h => ⟨thm_primeAtRank_isPrime nRank, h⟩, fun h => h.2⟩

/-- Une fenêtre de rangs entiers `[a,b)` contient exactement un rang si et
seulement si `b = a+1` — un fait purement arithmétique sur les entiers, sans
aucun contenu premier. -/
private theorem thm_existsUnique_rankWindow_iff_succ (a b : ℕ) :
    (∃! nRank : ℕ, a ≤ nRank ∧ nRank < b) ↔ b = a + 1 := by
  constructor
  · rintro ⟨n, ⟨hLe, hLt⟩, hUniq⟩
    by_contra hNe
    have h1 : a = n := hUniq a ⟨le_refl a, by omega⟩
    have h2 : a + 1 = n := hUniq (a + 1) ⟨by omega, by omega⟩
    omega
  · intro hb
    exact ⟨a, ⟨le_refl a, by omega⟩, fun m hm => by omega⟩

/-- **T1, sous l'angle de l'atterrissage sur la grammaire.**  Le régime de
centre unique EST : la cellule du membre atterrit sur exactement un événement
de la grammaire première `fnPrimeAtRank` — la fonction de comptage
(`nCellFoundCount`, `pi`) a entièrement disparu de l'énoncé. Ce n'est encore
qu'un changement d'énoncé, pas une preuve nouvelle : chaque rang de
`fnPrimeAtRank` porte par construction un seul premier (c'est l'énumération
elle-même, jamais un comptage), donc dire que la cellule atterrit sur un seul
rang revient à dire qu'elle contient un seul premier — mais l'énoncé ne
mentionne plus jamais `Nat.Prime`, `pi`, ni un cardinal : seulement la Tour
(les deux bords de la cellule) et la grammaire (`fnPrimeAtRank`), reliées
directement. -/
theorem thm_T1_iff_existsUniqueGrammarLanding :
    tCarrier.PUniqueCenterRegime ↔
      ∀ zUpperZero : TUpperNonTrivialZetaZero,
        ∃! nRank : ℕ,
          (tCarrier.tCarrierCell zUpperZero).rLeftEndpoint < (fnPrimeAtRank nRank : ℝ) ∧
            (fnPrimeAtRank nRank : ℝ) ≤ (tCarrier.tCarrierCell zUpperZero).rRightEndpoint := by
  rw [thm_T1_iff_rightEdgeRank_eq_leftEdgeRank_succ]
  constructor
  · intro hEdges zUpperZero
    have hSucc := hEdges zUpperZero
    rw [← thm_existsUnique_rankWindow_iff_succ] at hSucc
    obtain ⟨n, hn, hUniq⟩ := hSucc
    refine ⟨n, (thm_landing_iff_rankWindow _ n).mpr hn, ?_⟩
    intro m hm
    exact hUniq m ((thm_landing_iff_rankWindow _ m).mp hm)
  · intro hLanding zUpperZero
    obtain ⟨n, hn, hUniq⟩ := hLanding zUpperZero
    rw [← thm_existsUnique_rankWindow_iff_succ]
    refine ⟨n, (thm_landing_iff_rankWindow _ n).mp hn, ?_⟩
    intro m hm
    exact hUniq m ((thm_landing_iff_rankWindow _ m).mpr hm)

/-! ## 2. T1 : existence et unicité du premier de la cellule -/

/-- **T1.** Sous le régime de centre unique, la cellule du membre contient
exactement un vrai premier, caractérisé par appartenance à l'intervalle
algébrique. Transcription directe de `thm_cellFoundCount_eq_one_iff_existsUniquePrime`,
sans aucune hypothèse supplémentaire (pas de premier, de rang ni de C3 reçus). -/
theorem thm_T1_existsUniquePrime
    (hRegime : tCarrier.PUniqueCenterRegime) (zUpperZero : TUpperNonTrivialZetaZero) :
    ∃! p : ℕ,
      Nat.Prime p ∧
        (tCarrier.tCarrierCell zUpperZero).rLeftEndpoint < (p : ℝ) ∧
          (p : ℝ) ≤ (tCarrier.tCarrierCell zUpperZero).rRightEndpoint :=
  (thm_cellFoundCount_eq_one_iff_existsUniquePrime
    (tCarrier.tCarrierCell zUpperZero)).mp (hRegime zUpperZero)

/-- **C3 est cet unique premier.**  Le premier central lu par O10 sur la
cellule EST l'unique premier fourni par T1 — jamais un second objet. -/
theorem thm_T1_centralPrime_eq_C3
    (hRegime : tCarrier.PUniqueCenterRegime) (zUpperZero : TUpperNonTrivialZetaZero) :
    (tCarrier.thm_T1_existsUniquePrime hRegime zUpperZero).choose =
      tCarrier.nCarrierCentralPrime zUpperZero := by
  obtain ⟨hPrime, hLeft, hRight⟩ :=
    (tCarrier.thm_T1_existsUniquePrime hRegime zUpperZero).choose_spec.1
  have hFoundNonempty : 0 < nCellFoundCount (tCarrier.tCarrierCell zUpperZero) := by
    rw [hRegime zUpperZero]; exact Nat.one_pos
  have hCentral := tCarrier.thm_carrierCentralPrime_in_cell zUpperZero hFoundNonempty
  exact ((tCarrier.thm_T1_existsUniquePrime hRegime zUpperZero).choose_spec.2
    (tCarrier.nCarrierCentralPrime zUpperZero)
    ⟨tCarrier.thm_carrierCentralPrime_isPrime zUpperZero, hCentral.1, hCentral.2⟩).symm

/-- **Unicité absolue.**  Tout premier de la cellule du membre EST C3 — aucun
second candidat, aucune sélection ultérieure. -/
theorem thm_T1_centralPrime_unique
    (hRegime : tCarrier.PUniqueCenterRegime) (zUpperZero : TUpperNonTrivialZetaZero)
    {q : ℕ} (hq : Nat.Prime q)
    (hLeft : (tCarrier.tCarrierCell zUpperZero).rLeftEndpoint < (q : ℝ))
    (hRight : (q : ℝ) ≤ (tCarrier.tCarrierCell zUpperZero).rRightEndpoint) :
    q = tCarrier.nCarrierCentralPrime zUpperZero := by
  rw [← tCarrier.thm_T1_centralPrime_eq_C3 hRegime zUpperZero]
  exact (tCarrier.thm_T1_existsUniquePrime hRegime zUpperZero).choose_spec.2 q ⟨hq, hLeft, hRight⟩

end TTrueTowerCarrier

/-! Surface audit. -/

#check @TTrueTowerCarrier.PUniqueCenterRegime
#check @TTrueTowerCarrier.thm_T1_existsUniquePrime
#check @TTrueTowerCarrier.thm_T1_centralPrime_eq_C3
#check @TTrueTowerCarrier.thm_T1_centralPrime_unique

end RHV3Lean
