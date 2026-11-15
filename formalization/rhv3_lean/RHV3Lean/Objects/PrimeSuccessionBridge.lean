/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.CountingRigidity
import RHV3Lean.Objects.PrimeTransitionGrammar

/-!
# RHV3Lean — le pont : écart de comptage un ⟺ succession première canonique

    TRACE_ID              : RHV3-T2-BRIDGE
    SEMANTIC_OBJECT       : le pont entre l'écart de comptage `pi(q)-pi(p)=1`
                            et la succession première canonique complète
                            (ordre, séparation, corridor vide).
    SEMANTIC_STATEMENT    : T2 a jusqu'ici porté trop de structure à la fois
                            (ordre, voisinage, passage, nullité, même membre,
                            grammaire).  Une fois T1 acquis pour deux membres
                            (donc `p` et `q` DEJA de vrais premiers), TOUT le
                            contenu de la succession canonique — l'ordre
                            strict, la séparation, et l'absence de tout
                            premier entre les deux — est une pure conséquence
                            de la SEULE différence de comptage
                            `pi(q)-pi(p)=1`.  Ce module produit ce pont comme
                            un theorem, jamais comme une `Prop` reçue.
    MATHEMATICAL_STATEMENT: pour p, q premiers, pi(q)-pi(p)=1 implique
                            p<q, p!=q, et aucun premier r avec p<r<q.
                            Réciproquement, p<q et aucun premier strictement
                            entre les deux et q premier implique pi(q)-pi(p)=1.
    MATHEMATICAL_PARENT   : O10 (rigidité de comptage), déjà produit dans
                            `CountingRigidity.lean` — ce module n'ajoute AUCUNE
                            nouvelle primitive de comptage, il recompose les
                            théorèmes déjà là sur DEUX rangs de bord au lieu
                            d'un.
    PROOF_STRATEGY        : `pi(q)-pi(p)=1` est instancié sur l'intervalle
                            algébrique `(p,q]` via `nCellFoundCount` et
                            `thm_cellFoundCount_eq_edgeRankDifference`
                            (déjà produits).  L'ordre `p<q` sort de la seule
                            monotonie de `nEdgePrimeRank` (`Nat.count_monotone`)
                            combinée à la trichotomie de `≤` sur `ℕ` : aucune
                            hypothèse d'ordre n'est reçue séparément.
                            L'absence de premier intermédiaire, et l'unicité de
                            `q` comme témoin, sortent de
                            `thm_cellFoundCount_eq_one_iff_existsUniquePrime`
                            (déjà produit), appliqué à cet intervalle avec `q`
                            comme candidat (puisque `q` est déjà connu premier
                            et `p<q<=q`).
    REQUIRED_LEMMAS       : Nat.count_monotone, Nat.floor_natCast,
                            thm_cellFoundCount_eq_edgeRankDifference,
                            thm_cellFoundCount_eq_one_iff_existsUniquePrime
    WHY_EACH_LEMMA_EXISTS : la première donne la monotonie qui force l'ordre ;
                            la deuxième aligne `nEdgePrimeRank` d'un naturel
                            avec le comptage `pi` usuel ; les deux dernières
                            transcrivent le cardinal un en existence-et-unicité
                            sur l'intervalle `(p,q]`.
    LEAN_DEFINITION       : nPrimeCountRank, PIsNextPrime
    LEAN_THEOREM          : thm_nPrimeCountRank_eq_count,
                            thm_nPrimeCountRank_mono,
                            thm_order_of_countDiff_one,
                            thm_isNextPrime_of_countDiff_one,
                            thm_countDiff_one_of_isNextPrime,
                            thm_isNextPrime_iff_countDiff_one
    SAME_MEMBER_CHECK     : sans objet — ce module ne parle que de deux
                            naturels premiers `p`, `q`, jamais de membre ou de
                            Tour ; le raccord au porteur (T2 proprement dit)
                            est une application immédiate laissée à
                            `CanonicalT2.lean`.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : l'unique histoire première de O6 est celle lue par
                            `nEdgePrimeRank`, jamais une seconde énumération.
    FORBIDDEN_PREMISES    : recevoir l'ordre `p<q`, la séparation `p!=q`, ou
                            l'absence de premier intermédiaire comme hypothèse
                            libre ; recevoir `PCanonicalSuccession` comme
                            prémisse d'un theorem de ce module.
    NEXT_CONSUMER         : `CanonicalT2.lean`, pour relier ce pont aux deux
                            premiers centraux d'un passage réel (`p =
                            fnCarrierMemberCentralPrime zEarlierMember`,
                            `q = fnCarrierMemberCentralPrime zLaterMember`).
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

/-! ## 1. Le rang de comptage d'un naturel, et sa monotonie -/

/-- **Le rang de comptage d'un naturel** : relecture de `nEdgePrimeRank` sur un
naturel plutôt que sur un réel quelconque, exactement `pi(n)` du maître. -/
noncomputable def nPrimeCountRank (n : ℕ) : ℕ := nEdgePrimeRank (n : ℝ)

theorem thm_nPrimeCountRank_eq_count (n : ℕ) :
    nPrimeCountRank n = Nat.count Nat.Prime (n + 1) := by
  unfold nPrimeCountRank nEdgePrimeRank
  rw [Nat.floor_natCast]

/-- **La monotonie du rang de comptage.**  Conséquence directe de
`Nat.count_monotone` : jamais dérivée d'un ordre supposé sur les premiers. -/
theorem thm_nPrimeCountRank_mono : Monotone nPrimeCountRank := by
  intro m n hmn
  rw [thm_nPrimeCountRank_eq_count, thm_nPrimeCountRank_eq_count]
  exact Nat.count_monotone Nat.Prime (by omega)

/-! ## 2. L'ORDRE sort de la seule différence de comptage, jamais reçu -/

/-- **L'écart de comptage un force l'ordre strict.**  Aucune hypothèse d'ordre
n'est reçue : la seule monotonie du comptage, combinée à la trichotomie de `≤`
sur `ℕ`, suffit. -/
theorem thm_order_of_countDiff_one {p q : ℕ}
    (hDiff : nPrimeCountRank q - nPrimeCountRank p = 1) : p < q := by
  rcases lt_or_ge p q with hlt | hge
  · exact hlt
  · have hle : nPrimeCountRank q ≤ nPrimeCountRank p := thm_nPrimeCountRank_mono hge
    omega

/-! ## 3. La succession canonique complète, comme conséquence -/

/-- **La succession canonique**, formulée sans aucune référence à un porteur ou
à une Tour : `q` est strictement au-dessus de `p`, et aucun premier ne se
glisse strictement entre les deux. -/
def PIsNextPrime (p q : ℕ) : Prop :=
  p < q ∧ ∀ r : ℕ, Nat.Prime r → p < r → r < q → False

/-- **L'intervalle algébrique `(p,q]`, construit uniquement depuis l'ordre déjà
obtenu — jamais choisi pour faire correspondre un premier. -/
noncomputable def tPrimeGapInterval {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    TAlgebraicInterval where
  rLeftEndpoint := (p : ℝ)
  rRightEndpoint := (q : ℝ)
  hLeftPositive := by exact_mod_cast hp
  hOrdered := by exact_mod_cast hpq

/-- **LE PONT, sens direct.**  Deux premiers dont l'écart de comptage vaut un
sont automatiquement en succession canonique complète : ordre ET absence de
tout premier intermédiaire, sans qu'aucun des deux ne soit reçu séparément. -/
theorem thm_isNextPrime_of_countDiff_one {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hDiff : nPrimeCountRank q - nPrimeCountRank p = 1) :
    PIsNextPrime p q := by
  have hOrder : p < q := thm_order_of_countDiff_one hDiff
  refine ⟨hOrder, ?_⟩
  set tInterval : TAlgebraicInterval := tPrimeGapInterval hp.pos hOrder with hIdef
  have hFoundCount : nCellFoundCount tInterval = 1 := by
    rw [thm_cellFoundCount_eq_edgeRankDifference]
    show nEdgePrimeRank (q : ℝ) - nEdgePrimeRank (p : ℝ) = 1
    exact hDiff
  have hUnique := (thm_cellFoundCount_eq_one_iff_existsUniquePrime tInterval).mp hFoundCount
  have hqMem : q = hUnique.choose := by
    apply hUnique.choose_spec.2
    exact ⟨hq, by simpa [hIdef, tPrimeGapInterval] using hOrder,
      by simpa [hIdef, tPrimeGapInterval]⟩
  intro r hr hLeft hRight
  have hrMem : r = hUnique.choose := by
    apply hUnique.choose_spec.2
    refine ⟨hr, ?_, ?_⟩
    · simpa [hIdef, tPrimeGapInterval] using hLeft
    · simpa [hIdef, tPrimeGapInterval] using le_of_lt hRight
  have : r = q := hrMem.trans hqMem.symm
  omega

/-- **LE PONT, sens réciproque.**  La succession canonique complète force en
retour l'écart de comptage un — aucune direction n'est un raccourci sur
l'autre. -/
theorem thm_countDiff_one_of_isNextPrime {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hSucc : PIsNextPrime p q) :
    nPrimeCountRank q - nPrimeCountRank p = 1 := by
  obtain ⟨hOrder, hNone⟩ := hSucc
  set tInterval : TAlgebraicInterval := tPrimeGapInterval hp.pos hOrder with hIdef
  have hqMem : q ∈ sAlgebraicIntervalFoundPrimes tInterval :=
    (thm_mem_foundPrimes_iff tInterval q).mpr
      ⟨hq, by simpa [hIdef, tPrimeGapInterval] using hOrder,
        by simpa [hIdef, tPrimeGapInterval]⟩
  have hCard : nCellFoundCount tInterval = 1 := by
    apply (thm_cellFoundCount_eq_one_iff_existsUniquePrime tInterval).mpr
    refine ⟨q, ⟨hq, by simpa [hIdef, tPrimeGapInterval] using hOrder,
      by simpa [hIdef, tPrimeGapInterval]⟩, ?_⟩
    intro s hs
    obtain ⟨hsPrime, hsLeft, hsRight⟩ := hs
    by_contra hne
    have hsLt : (s : ℝ) < (q : ℝ) := lt_of_le_of_ne hsRight (by exact_mod_cast hne)
    have hsLtNat : s < q := by exact_mod_cast hsLt
    have hsLeftNat : p < s := by simpa [hIdef, tPrimeGapInterval] using hsLeft
    exact hNone s hsPrime hsLeftNat hsLtNat
  rw [thm_cellFoundCount_eq_edgeRankDifference] at hCard
  exact hCard

/-- **LE PONT COMPLET.**  L'écart de comptage un et la succession canonique
complète sont EXACTEMENT LA MÊME INFORMATION, pour deux premiers déjà connus.
C'est le théorème que la mission demande : tout ce qui entourait T2 — ordre,
voisinage, passage, nullité, grammaire — se réduit à cette seule équivalence
arithmétique. -/
theorem thm_isNextPrime_iff_countDiff_one {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) :
    PIsNextPrime p q ↔ nPrimeCountRank q - nPrimeCountRank p = 1 :=
  ⟨thm_countDiff_one_of_isNextPrime hp hq,
    thm_isNextPrime_of_countDiff_one hp hq⟩

/-! ## 4. Promotion vers la grammaire première canonique DÉJÀ produite

La relation locale `pi(q)-pi(p)=1` (ou `PIsNextPrime`) est réelle, mais
isolée : elle ne dit encore rien sur l'ordre global, le voisinage, les
transitions ou la nullité/non-nullité dans l'unique histoire première. Cette
section produit le raccord EXACT entre les deux premiers `p`, `q` et le rang
`nRank` de la grammaire déjà certifiée (`PrimeGapGrammar.lean`,
`PrimeTransitionGrammar.lean`) : une fois `p = fnPrimeAtRank nRank` et
`q = fnPrimeSuccessor nRank` établis, TOUTE la machinerie de grammaire
existante s'applique directement, sans qu'aucun nouvel objet de grammaire ne
soit inventé ici. -/

/-- **Le rang de `p`, et sa relecture comme rang de `q`.**  Aucune adresse
choisie : `Nat.count Nat.Prime p` est le rang zéro-basé exact de `p` dans
l'histoire première, par la seule surjectivité déjà produite de
`fnPrimeAtRank` sur les premiers. -/
theorem thm_nPrimeCountRank_eq_succ_count {p : ℕ} (hp : Nat.Prime p) :
    nPrimeCountRank p = Nat.count Nat.Prime p + 1 := by
  rw [thm_nPrimeCountRank_eq_count]
  exact Nat.count_succ_eq_succ_count hp

/-- **LE RACCORD.**  Deux premiers en succession canonique complète occupent
EXACTEMENT le rang `nRank = Nat.count Nat.Prime p` et son successeur : `p` est
`fnPrimeAtRank nRank`, `q` est `fnPrimeSuccessor nRank`. C'est le pont qui
transporte le fait local de comptage vers un objet consommable par la
grammaire déjà certifiée. -/
theorem thm_isNextPrime_gives_rank {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hSucc : PIsNextPrime p q) :
    fnPrimeAtRank (Nat.count Nat.Prime p) = p ∧
      fnPrimeSuccessor (Nat.count Nat.Prime p) = q := by
  refine ⟨thm_primeAtRank_surjective_onPrimes hp, ?_⟩
  have hCount := thm_countDiff_one_of_isNextPrime hp hq hSucc
  have hMono : nPrimeCountRank p ≤ nPrimeCountRank q :=
    thm_nPrimeCountRank_mono (le_of_lt hSucc.1)
  have hpEq := thm_nPrimeCountRank_eq_succ_count hp
  have hqEq := thm_nPrimeCountRank_eq_succ_count hq
  have hqCount : Nat.count Nat.Prime q = Nat.count Nat.Prime p + 1 := by omega
  unfold fnPrimeSuccessor
  rw [← hqCount]
  exact thm_primeAtRank_surjective_onPrimes hq

/-- **LA PROMOTION.**  Une fois le raccord de rang établi, la grammaire des
transitions DÉJÀ CERTIFIÉE (`thm_transition_exhaustive`,
`PrimeTransitionGrammar.lean`) s'applique directement : `(p,q)` porte
exactement l'une des quatre transitions modulo 6 de l'unique histoire
première. Aucun nouvel objet grammatical n'est introduit ; celui-ci est
consommé tel quel. -/
theorem thm_grammar_promotion_of_isNextPrime {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hGtThree : 3 < p)
    (hSucc : PIsNextPrime p q) :
    PPrimeTransitionAtRank .keep11 (Nat.count Nat.Prime p) ∨
      PPrimeTransitionAtRank .switch15 (Nat.count Nat.Prime p) ∨
      PPrimeTransitionAtRank .switch51 (Nat.count Nat.Prime p) ∨
      PPrimeTransitionAtRank .keep55 (Nat.count Nat.Prime p) := by
  obtain ⟨hAtRank, _⟩ := thm_isNextPrime_gives_rank hp hq hSucc
  have hGtRank : 3 < fnPrimeAtRank (Nat.count Nat.Prime p) := by rw [hAtRank]; exact hGtThree
  exact thm_transition_exhaustive hGtRank

/-- **La classe de gap modulo 6 est elle aussi promue**, par la même
relecture de rang, vers `thm_class_projection_complete` déjà certifié. -/
theorem thm_grammar_gapClass_of_isNextPrime {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hGtThree : 3 < p)
    (hSucc : PIsNextPrime p q) :
    (nPrimeGap (Nat.count Nat.Prime p) % 6 = 0 ↔
      fnPrimeSuccessor (Nat.count Nat.Prime p) % 6 =
        fnPrimeAtRank (Nat.count Nat.Prime p) % 6) ∧
    (nPrimeGap (Nat.count Nat.Prime p) % 6 = 2 ↔
      (fnPrimeAtRank (Nat.count Nat.Prime p) % 6 = 5 ∧
        fnPrimeSuccessor (Nat.count Nat.Prime p) % 6 = 1)) ∧
    (nPrimeGap (Nat.count Nat.Prime p) % 6 = 4 ↔
      (fnPrimeAtRank (Nat.count Nat.Prime p) % 6 = 1 ∧
        fnPrimeSuccessor (Nat.count Nat.Prime p) % 6 = 5)) := by
  obtain ⟨hAtRank, _⟩ := thm_isNextPrime_gives_rank hp hq hSucc
  have hGtRank : 3 < fnPrimeAtRank (Nat.count Nat.Prime p) := by rw [hAtRank]; exact hGtThree
  exact thm_class_projection_complete hGtRank

/-! Surface audit. -/

#check @nPrimeCountRank
#check @thm_nPrimeCountRank_eq_count
#check @thm_nPrimeCountRank_mono
#check @thm_order_of_countDiff_one
#check @PIsNextPrime
#check @thm_isNextPrime_of_countDiff_one
#check @thm_countDiff_one_of_isNextPrime
#check @thm_isNextPrime_iff_countDiff_one
#check @thm_nPrimeCountRank_eq_succ_count
#check @thm_isNextPrime_gives_rank
#check @thm_grammar_promotion_of_isNextPrime
#check @thm_grammar_gapClass_of_isNextPrime

end RHV3Lean
