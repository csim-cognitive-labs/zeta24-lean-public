/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.FrequencyCap
import RHV6Fresh.Terminal.OffCarrier
import RHV6Fresh.Terminal.FrequencyCascadeStability
import RHV6Fresh.Terminal.Universalization
import RHV6Fresh.Terminal.GeneratedFrequency

/-!
# La composition « comptage exact + occurrences premières + lecture des fréquences » (§19.17, 2026-10-30)

Module isolé (non ajouté à `RHV6Fresh.lean`). Demande de l'auteur (texte collé, §19.17.1) : ne plus chercher à montrer
que la paire OFF « consomme trop de places » (elle en consomme exactement deux, §19.16), mais déterminer si la
composition `FrequencyCap` (comptage exact) + `OffCarrier` (occurrences premières) + `GeneratedFrequency` (lecture des
fréquences) produit une inégalité STRICTE entre les hauteurs de deux membres consécutifs, c'est-à-dire si
« occurrences premières distinctes ⟹ hauteurs distinctes ».

Ce que ce module compile, sans rien supposer :

* **§1** l'occurrence est injective : deux membres distincts portent deux premiers distincts.
* **§2** la cible du texte, « occurrences distinctes ⟹ hauteurs distinctes », est ÉQUIVALENTE à RH
  (`distinctOccurrencesDistinctHeights_iff_riemannHypothesis`) ; sa forme consécutive aussi
  (`consecutive_heights_distinct_iff_riemannHypothesis`). Elle ne peut donc être ni posée ni déduite d'un théorème
  « indépendant du régime ON » sans que ce théorème soit lui-même RH.
* **§3** la composition est AVEUGLE sur le porteur : la paire (zéro OFF, membre sortant) porte les deux occurrences
  consécutives `p_n`, `p_{n+1}` (`outgoing_occurrence_eq_expected`), lit tout écart premier par le même nombre de
  cellules (`pair_reads_gaps_identically`, en particulier son propre pas `p_n → p_{n+1}`,
  `pair_reads_own_step_identically`), témoigne de la même fréquence engendrée par les premiers
  (`pair_same_generated_frequency`) et occupe deux places du comptage à cette hauteur (`pair_two_counting_places`).
  Aucun de ces énoncés ne voit la position radiale : ils ne séparent pas les hauteurs.
* **§4** ce qui, au voisinage de la composition, EST sensible à la position radiale : le transport d'énergie au
  premier partagé `p_{n+1}` est renversé (`outgoingRaccord_not_oriented`), et dans le cas miroir sa valeur exacte est
  `p_{n+1}^{2d} · ‖ρ‖/‖ρ*‖` avec `d = 1/2 − β` (`pair_transport_at_occurrence`), alors que sur tout passage vertical
  le transport est `≤ 1` (`towerRaccord_oriented_of_vertical`, déjà compilé). La frontière est donc : un théorème
  ARITHMÉTIQUE fixant le transport au premier partagé. Il n'est pas dans le corpus et n'est pas posé ici.

Aucun `sorry`, aucun axiome nouveau, aucune hypothèse équivalente à RH posée comme prouvée.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. L'occurrence est injective -/

/-- **Deux membres distincts portent deux premiers distincts** : l'occurrence est l'image du rang par
l'énumération des premiers, et le rang détermine le membre. -/
theorem occurrence_injective : Function.Injective occurrence := by
  intro a b h
  rw [occurrence_eq_primeAtRank, occurrence_eq_primeAtRank] at h
  exact thm_zeroSourceIndex_injective (thm_primeAtRank_injective h)

/-! ## 2. La cible du texte est RH -/

/-- **La cible du texte collé** : deux occurrences premières distinctes imposent deux hauteurs distinctes. -/
def DistinctOccurrencesDistinctHeights : Prop :=
  ∀ a b : TrueZero, occurrence a ≠ occurrence b → rZeroHeight a.1 ≠ rZeroHeight b.1

/-- **« Occurrences distinctes ⟹ hauteurs distinctes » ⟺ RH.** Sens ⟹ : un zéro OFF et son miroir sont deux membres
distincts (occurrences distinctes) de même hauteur. Sens ⟸ : sous RH, deux membres de même hauteur sont sur la ligne,
donc comparables seulement par la hauteur, donc égaux. -/
theorem distinctOccurrencesDistinctHeights_iff_riemannHypothesis :
    DistinctOccurrencesDistinctHeights ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_noOff
    intro z hOff
    have hne : mirrorMember z ≠ z := by
      intro heq
      have hr := mirrorMember_radial z
      rw [heq] at hr
      exact hOff (by linarith)
    have hocc : occurrence (mirrorMember z) ≠ occurrence z := fun h' => hne (occurrence_injective h')
    exact h _ _ hocc (mirrorMember_ordinate z)
  · intro hRH a b hocc hT
    apply hocc
    by_cases hab : a = b
    · rw [hab]
    · exfalso
      have ha := thm_zeroRadialPosition_half_of_riemannHypothesis hRH a.1
      have hb := thm_zeroRadialPosition_half_of_riemannHypothesis hRH b.1
      rcases thm_distinctZeroMembers_comparable (fun h => hab (Subtype.ext h)) with h | h <;>
        rw [thm_zeroMemberPrecedes_iff_height_radial_lex] at h <;>
        rcases h with h | ⟨_, h⟩ <;> linarith

/-- **Forme consécutive** : « deux membres consécutifs n'ont jamais la même hauteur » ⟺ RH (la cascade stricte de
§19.14, écrite avec `≠` au lieu de `<`, la hauteur étant croissante au sens large). -/
theorem consecutive_heights_distinct_iff_riemannHypothesis :
    (∀ n : ℕ, 1 ≤ n → rZeroHeight (canonicalZero n).1 ≠ rZeroHeight (canonicalZero (n + 1)).1) ↔
      RiemannHypothesis := by
  rw [← strict_frequency_cascade_iff_riemannHypothesis]
  constructor
  · intro h n hn
    refine lt_of_le_of_ne ?_ (h n hn)
    unfold canonicalZero
    exact canonicalMember_height_mono (by omega)
  · intro h n hn
    exact (h n hn).ne

/-! ## 3. La composition est aveugle sur le porteur -/

namespace OffCarrier

variable (C : OffCarrier)

/-- L'occurrence du membre sortant est `p_{n+1}`. -/
theorem outgoing_occurrence : occurrence C.outgoingMember = fnPrimeAtRank (C.n + 1) := by
  rw [occurrence_eq_primeAtRank]
  exact congrArg fnPrimeAtRank (canonicalMember_index (C.n + 1))

/-- **Les deux occurrences de la paire sont consécutives** : celle du membre sortant est le premier minimal attendu
du zéro OFF. -/
theorem outgoing_occurrence_eq_expected : occurrence C.outgoingMember = expectedMinimumPrime C.zero := by
  rw [C.outgoing_occurrence, C.zero_expectedMinimumPrime]

/-- La hauteur du membre sortant, écrite sur le vrai zéro. -/
theorem outgoingMember_height : rZeroHeight C.outgoingMember.1 = rZeroHeight C.zero.1 :=
  C.outgoing_same_height

/-- **Même lecture de tout écart** : la paire lit tout intervalle `[q, q']` par le même nombre de cellules (la lecture
d'un écart ne dépend que de la hauteur, `gap_reading_height_only`). -/
theorem pair_reads_gaps_identically (q q' : ℝ) :
    towerPosition C.outgoingMember q' - towerPosition C.outgoingMember q =
      towerPosition C.zero q' - towerPosition C.zero q := by
  rw [gap_reading_height_only, gap_reading_height_only, C.outgoingMember_height]

/-- **Même lecture de son propre pas** : le pas `p_n → p_{n+1}` est lu par le zéro OFF et par le membre sortant par le
même nombre de cellules `T · log(p_{n+1}/p_n) / π`. -/
theorem pair_reads_own_step_identically :
    towerPosition C.outgoingMember (fnPrimeAtRank (C.n + 1) : ℝ) -
        towerPosition C.outgoingMember (fnPrimeAtRank C.n : ℝ) =
      rZeroHeight C.zero.1 * (Real.log (fnPrimeAtRank (C.n + 1) : ℝ) - Real.log (fnPrimeAtRank C.n : ℝ)) /
        Real.pi ∧
    towerPosition C.zero (fnPrimeAtRank (C.n + 1) : ℝ) - towerPosition C.zero (fnPrimeAtRank C.n : ℝ) =
      rZeroHeight C.zero.1 * (Real.log (fnPrimeAtRank (C.n + 1) : ℝ) - Real.log (fnPrimeAtRank C.n : ℝ)) /
        Real.pi := by
  refine ⟨?_, gap_reading_height_only _ _ _⟩
  rw [gap_reading_height_only, C.outgoingMember_height]

/-- **Même fréquence engendrée** : la hauteur de la paire est une seule fréquence engendrée par les premiers, dont
chacun des deux membres est un témoin. -/
theorem pair_same_generated_frequency :
    ArithmeticFrequency (rZeroHeight C.zero.1) ∧
    GeneratedFrequency (rZeroHeight C.zero.1) ∧
    GeneratedFrequency (rZeroHeight C.outgoingMember.1) ∧
    rZeroHeight C.outgoingMember.1 = rZeroHeight C.zero.1 :=
  ⟨arithmeticFrequency_of_zero _, generatedFrequency_of_zero _, generatedFrequency_of_zero _,
    C.outgoingMember_height⟩

/-- **Deux places du comptage** : les rangs `n` et `n+1` sont tous deux sous la hauteur de la paire, le comptage à
cette hauteur compte donc au moins `n+2` points. -/
theorem pair_two_counting_places : C.n + 2 ≤ (upperWindow (rZeroHeight C.zero.1)).card :=
  card_ge_of_height_le (k := C.n + 1) (le_of_eq C.outgoing_same_height)

/-- **Même lecture du comptage** : les deux membres sont dans la fenêtre de comptage de la même hauteur. -/
theorem pair_in_same_window :
    zeroPoint C.zero ∈ upperWindow (rZeroHeight C.zero.1) ∧
    zeroPoint C.outgoingMember ∈ upperWindow (rZeroHeight C.zero.1) :=
  ⟨mem_upperWindow_iff.mpr ⟨C.zero, rfl, le_rfl⟩,
    mem_upperWindow_iff.mpr ⟨C.outgoingMember, rfl, le_of_eq C.outgoingMember_height⟩⟩

/-! ## 4. Ce qui est sensible à la position radiale au premier partagé -/

/-- **Le raccord sortant n'est pas orienté** : au premier partagé `p_{n+1}`, le membre sortant lit strictement plus
d'énergie que le zéro OFF (dès la hauteur `2`). Sur tout passage vertical, le raccord est orienté
(`towerRaccord_oriented_of_vertical`). -/
theorem outgoingRaccord_not_oriented (hT2 : 2 ≤ rZeroHeight C.zero.1) : ¬ C.outgoingRaccord.Oriented :=
  not_le.mpr (C.outgoing_signature.2.1 hT2)

/-- Dans le cas miroir, le membre sortant est le miroir, comme vrai zéro. -/
theorem outgoingMember_eq_mirror (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    C.outgoingMember = mirrorMember C.zero :=
  Subtype.ext h

/-- Dans le cas miroir, l'occurrence du miroir est `p_{n+1}`. -/
theorem mirror_occurrence_of_mirror_case (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1) :
    occurrence (mirrorMember C.zero) = fnPrimeAtRank (C.n + 1) := by
  rw [← C.outgoingMember_eq_mirror h]
  exact C.outgoing_occurrence

/-- **Valeur exacte du transport au premier partagé, cas miroir** : `p_{n+1}^{2d} · ‖ρ‖ / ‖ρ*‖` avec `d = 1/2 − β`.
C'est la seule quantité de la composition qui lit la position radiale ; le comptage, les occurrences et la lecture
des écarts (§3) ne la voient pas. -/
theorem pair_transport_at_occurrence :
    energyRatio C.zero (mirrorMember C.zero) (fnPrimeAtRank (C.n + 1) : ℝ) =
      (fnPrimeAtRank (C.n + 1) : ℝ) ^ (2 * C.radialShift) *
        (‖zeroPoint C.zero‖ / ‖zeroPoint (mirrorMember C.zero)‖) := by
  have hp : (0 : ℝ) < (fnPrimeAtRank (C.n + 1) : ℝ) := by exact_mod_cast (thm_primeAtRank_isPrime _).pos
  rw [energyRatio_eq _ _ hp, C.mirror_radial_eq, C.zero_radial_eq]
  congr 2
  ring

/-! ## 5. Le motif des trois raccords du porteur (étude sur trois zéros, cas miroir) -/

/-- Le passage après le miroir est vertical, et son membre d'arrivée est à hauteur `≥ 2` dès que la paire l'est. -/
theorem postPassage_height_advance (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1)
    (hT2 : 2 ≤ rZeroHeight C.zero.1) : 2 ≤ rZeroHeight C.postPassage.zLaterMember := by
  have hv : rZeroHeight C.postPassage.zEarlierMember < rZeroHeight C.postPassage.zLaterMember :=
    C.post_mirror_vertical h
  have he := C.postPassage_earlier_height
  linarith

/-- **Le motif des trois raccords** (dernier ON → zéro OFF → miroir → membre suivant), cas miroir, hauteur `≥ 2` :
hiérarchie à l'arrivée (passage vertical), hiérarchie BRISÉE à la sortie (passage horizontal : transport renversé
au premier partagé `p_{n+1}`), hiérarchie RÉTABLIE après le miroir (passage vertical). C'est la lecture radialement
sensible des trois événements de §19.16 ; le comptage, les occurrences et la lecture des écarts (§3) ne la voient pas. -/
theorem three_raccords_pattern (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1)
    (hT2 : 2 ≤ rZeroHeight C.zero.1) :
    RaccordHierarchy C.arrival C.arrival_earlier_pos C.arrival_later_pos ∧
    ¬ RaccordHierarchy C.outgoing C.outgoing_earlier_pos C.outgoing_later_pos ∧
    RaccordHierarchy C.postPassage C.postPassage_earlier_pos C.postPassage_later_pos :=
  ⟨C.arrival_hierarchy hT2, C.outgoing_signature.2.2,
    raccordHierarchy_of_height_advance _ _ _ (C.post_mirror_vertical h) (C.postPassage_height_advance h hT2)⟩

/-- **Le motif des trois transports** : orienté, renversé, orienté. -/
theorem three_transports_pattern (h : C.outgoing.zLaterMember = (mirrorMember C.zero).1)
    (hT2 : 2 ≤ rZeroHeight C.zero.1) :
    C.arrivalRaccord.Oriented ∧ ¬ C.outgoingRaccord.Oriented ∧
    (towerRaccordOf C.postPassage C.postPassage_earlier_pos C.postPassage_later_pos).Oriented :=
  ⟨(C.arrival_hierarchy hT2).1, C.outgoingRaccord_not_oriented hT2, (C.three_raccords_pattern h hT2).2.2.1⟩

end OffCarrier

#print axioms occurrence_injective
#print axioms distinctOccurrencesDistinctHeights_iff_riemannHypothesis
#print axioms consecutive_heights_distinct_iff_riemannHypothesis
#print axioms OffCarrier.outgoing_occurrence_eq_expected
#print axioms OffCarrier.pair_reads_gaps_identically
#print axioms OffCarrier.pair_reads_own_step_identically
#print axioms OffCarrier.pair_same_generated_frequency
#print axioms OffCarrier.pair_two_counting_places
#print axioms OffCarrier.pair_in_same_window
#print axioms OffCarrier.outgoingRaccord_not_oriented
#print axioms OffCarrier.mirror_occurrence_of_mirror_case
#print axioms OffCarrier.pair_transport_at_occurrence
#print axioms OffCarrier.three_raccords_pattern
#print axioms OffCarrier.three_transports_pattern

end RHV6Fresh
