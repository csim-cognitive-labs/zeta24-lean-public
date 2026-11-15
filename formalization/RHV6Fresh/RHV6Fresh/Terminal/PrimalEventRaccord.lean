/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RaccordDetector
import RHV6Fresh.Terminal.ShiftedWorld
import RHV6Fresh.Grammar.Mod6Rigidity
import RHV3Lean.Objects.PrimeTransitionGrammar

/-!
# RHV6Fresh — l'événement premier complet au raccord (auteur, 2026-09-30)

Le raccord `TowerRaccord e l` recevait le premier partagé `M`, c'est-à-dire une adresse. Ce fichier
lui rend le certificat grammatical complet de `M`, sans rien retirer de la géométrie ni de l'énergie.

* **L'événement premier** (`PrimalEvent`, `primalEventAt`) : rang, premier, prédécesseur, successeur,
  écart entrant, écart sortant, état modulo 6, classes des deux écarts, poids `log p`. Côté
  arithmétique seul : aucun zéro n'entre dans sa définition.
* **Le même événement reconstruit depuis les zéros** (`reconstructedEventAt`,
  `reconstructedEvent_eq_primalEvent`) : le foncteur de reconstruction de la base, appliqué au canal
  `ψ` issu de la source des zéros, redonne l'événement complet, poids compris. Inconditionnel.
* **L'histoire cumulative** (`primalHistory`, `primalHistory_succ`, `passage_history_step`) : sur tout
  passage, le préfixe spectral gagne exactement un membre et l'histoire première exactement un
  événement complet.
* **Le raccord grammatical** (`GrammaticalRaccord`, `grammaticalRaccordOf`, `grammaticalRaccord_eq`) :
  le raccord entre Tours, tous ses champs conservés, plus l'événement complet de `M`. Existence sur
  tout passage, unicité.
* **Ce que l'énergie lit de l'événement** (`memberStep`, `two_raccord_transport`,
  `history_transport_product`, `historyCharge_succ`) : dans le produit cumulé des transports, chaque
  membre pèse par `(Occ / p_min)^{β − 1/2}`, l'écart de son propre événement porté à la puissance de
  son écart à la ligne. Ce pas est neutre si et seulement si le membre est en ligne, parce que
  l'écart premier est strictement positif.
* **Test hors ligne** (`off_grammaticalRaccord_complete_and_reversed`) : sur le passage horizontal
  d'un zéro hors ligne, le raccord grammatical existe avec le certificat complet, reconstruit depuis
  les zéros, et le transport est renversé. Le certificat complet indexé par le rang n'exclut pas le
  hors-ligne.
* **Préfixes analytiques** (`passage_separated_by_window_iff`) : les préfixes de la formule explicite
  sont les fenêtres de hauteur. Une fenêtre sépare les deux membres d'un passage si et seulement si
  la hauteur avance. À hauteur de sortie `≥ 2`, c'est exactement l'orientation du raccord
  (`towerRaccord_oriented_iff_window_separates`).
* **Monde témoin** (`shiftedWorld_reconstructs_no_prime`) : le canal de `ζ(s−d)ζ(s+d)` a pour poids
  `Λ(n)(n^d + n^{−d})` ; le foncteur de reconstruction n'y reconnaît aucun premier, pour tout `d`,
  `d = 0` compris (monde `ζ²`, zéros doublés sur place).

* **L'organisme spectral** (`spectral_organism_member`, `spectral_organism_reconstructs`) : le membre
  qui porte la Tour est le terme sommé par la formule explicite, et la somme de tous ces termes
  redonne `ψ`, chaque événement complet, toute l'histoire et tout descripteur de l'histoire.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse nouvelle.
-/

open ArithmeticFunction

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. L'événement premier complet -/

/-- **L'événement premier complet** : le premier avec son histoire locale. -/
structure PrimalEvent where
  /-- Rang dans l'unique histoire première (`p_0 = 2`). -/
  rank : ℕ
  prime : ℕ
  predecessor : ℕ
  successor : ℕ
  /-- Écart entrant `p_n − p_{n−1}`. -/
  inGap : ℕ
  /-- Écart sortant `p_{n+1} − p_n`. -/
  outGap : ℕ
  /-- État modulo 6. -/
  state : ℕ
  /-- Classe de l'écart entrant modulo 6. -/
  inClass : ℕ
  /-- Classe de l'écart sortant modulo 6. -/
  outClass : ℕ
  /-- Poids du premier dans le canal `ψ`. -/
  weight : ℝ

/-- L'événement premier de rang `n`, défini côté arithmétique seul. -/
noncomputable def primalEventAt (n : ℕ) : PrimalEvent where
  rank := n
  prime := fnPrimeAtRank n
  predecessor := fnPrimeAtRank (n - 1)
  successor := fnPrimeSuccessor n
  inGap := fnPrimeAtRank n - fnPrimeAtRank (n - 1)
  outGap := nPrimeGap n
  state := fnPrimeAtRank n % 6
  inClass := (fnPrimeAtRank n - fnPrimeAtRank (n - 1)) % 6
  outClass := nPrimeGap n % 6
  weight := Real.log (fnPrimeAtRank n)

/-- Le même événement, lu par le foncteur de reconstruction sur le canal issu des zéros. -/
noncomputable def reconstructedEventAt (n : ℕ) : PrimalEvent where
  rank := n
  prime := (fnReconstructGrammar rPsiZeroChannel).primeAt n
  predecessor := (fnReconstructGrammar rPsiZeroChannel).primeAt (n - 1)
  successor := (fnReconstructGrammar rPsiZeroChannel).primeAt (n + 1)
  inGap := (fnReconstructGrammar rPsiZeroChannel).primeAt n -
    (fnReconstructGrammar rPsiZeroChannel).primeAt (n - 1)
  outGap := (fnReconstructGrammar rPsiZeroChannel).gapAt n
  state := (fnReconstructGrammar rPsiZeroChannel).primeAt n % 6
  inClass := ((fnReconstructGrammar rPsiZeroChannel).primeAt n -
    (fnReconstructGrammar rPsiZeroChannel).primeAt (n - 1)) % 6
  outClass := (fnReconstructGrammar rPsiZeroChannel).gapAt n % 6
  weight := (fnReconstructGrammar rPsiZeroChannel).weight
    ((fnReconstructGrammar rPsiZeroChannel).primeAt n)

/-- Le poids reconstruit depuis les zéros en un premier est exactement `log p`. -/
theorem reconstructed_weight_at_prime (n : ℕ) :
    (fnReconstructGrammar rPsiZeroChannel).weight (fnPrimeAtRank n) =
      Real.log (fnPrimeAtRank n) := by
  have h1 : 1 ≤ fnPrimeAtRank n := by have := thm_primeAtRank_ge_two n; omega
  show fnWeightFromPsi rPsiZeroChannel (fnPrimeAtRank n) = _
  rw [thm_weightFromPsi_eq_of_agree_on_naturals thm_M9aChannelIdentityOnNaturals_proved h1,
    thm_weightFromPsi_chebyshev h1, vonMangoldt_apply_prime (thm_primeAtRank_isPrime n)]

/-- **La grammaire complète reconstruite depuis les zéros est la grammaire première** : l'événement
reconstruit égale l'événement premier, champ par champ, poids compris. Inconditionnel. -/
theorem reconstructedEvent_eq_primalEvent (n : ℕ) :
    reconstructedEventAt n = primalEventAt n := by
  obtain ⟨_, hAt, _, hGap, _⟩ := thm_M9a_M9b_components_unconditional
  unfold reconstructedEventAt primalEventAt
  simp only [hAt, hGap, reconstructed_weight_at_prime]
  rfl

/-- L'écart sortant n'est jamais nul. -/
theorem primalEvent_outGap_pos (n : ℕ) : 0 < (primalEventAt n).outGap :=
  thm_primeGap_positive n

/-- L'écart entrant n'est jamais nul (rang `≥ 1`). -/
theorem primalEvent_inGap_pos {n : ℕ} (hn : 0 < n) : 0 < (primalEventAt n).inGap :=
  Nat.sub_pos_of_lt (thm_primeAtRank_strictMono (by omega))

/-- Le prédécesseur plus l'écart entrant donne le premier. -/
theorem primalEvent_predecessor_add_inGap {n : ℕ} (hn : 0 < n) :
    (primalEventAt n).predecessor + (primalEventAt n).inGap = (primalEventAt n).prime := by
  have h : fnPrimeAtRank (n - 1) < fnPrimeAtRank n := thm_primeAtRank_strictMono (by omega)
  show fnPrimeAtRank (n - 1) + (fnPrimeAtRank n - fnPrimeAtRank (n - 1)) = fnPrimeAtRank n
  omega

/-- Le premier plus l'écart sortant donne le successeur. -/
theorem primalEvent_prime_add_outGap (n : ℕ) :
    (primalEventAt n).prime + (primalEventAt n).outGap = (primalEventAt n).successor := by
  have h := thm_primeAtRank_lt_successor n
  show fnPrimeAtRank n + nPrimeGap n = fnPrimeSuccessor n
  unfold nPrimeGap
  omega

/-- L'écart entrant de l'événement `n` est l'écart sortant de l'événement `n − 1`. -/
theorem primalEvent_inGap_eq_prev_outGap {n : ℕ} (hn : 0 < n) :
    (primalEventAt n).inGap = (primalEventAt (n - 1)).outGap := by
  show fnPrimeAtRank n - fnPrimeAtRank (n - 1) = nPrimeGap (n - 1)
  unfold nPrimeGap fnPrimeSuccessor
  rw [Nat.sub_add_cancel hn]

/-- **Certificat grammatical de l'événement** (prédécesseur `> 3`) : l'état est `1` ou `5` ; chaque
écart est de classe `0`, `2` ou `4` ; la transition entrante et la transition sortante existent et
sont uniques parmi les quatre ; deux classes non nulles successives sont différentes (alternance). -/
theorem primalEvent_certificate {n : ℕ} (hn : 0 < n) (h3 : 3 < fnPrimeAtRank (n - 1)) :
    ((primalEventAt n).state = 1 ∨ (primalEventAt n).state = 5) ∧
      ((primalEventAt n).inClass = 0 ∨ (primalEventAt n).inClass = 2 ∨
        (primalEventAt n).inClass = 4) ∧
      ((primalEventAt n).outClass = 0 ∨ (primalEventAt n).outClass = 2 ∨
        (primalEventAt n).outClass = 4) ∧
      (∃! t : TPrimeTransition, PPrimeTransitionAtRank t (n - 1)) ∧
      (∃! t : TPrimeTransition, PPrimeTransitionAtRank t n) ∧
      ((primalEventAt n).inClass ≠ 0 → (primalEventAt n).outClass ≠ 0 →
        (primalEventAt n).inClass ≠ (primalEventAt n).outClass) := by
  have hlt : fnPrimeAtRank (n - 1) < fnPrimeAtRank n := thm_primeAtRank_strictMono (by omega)
  have h3n : 3 < fnPrimeAtRank n := h3.trans hlt
  have h3s : 3 < fnPrimeSuccessor n := thm_primeSuccessor_gt_three h3n
  have gP := prime_goodMod6 _ (thm_primeAtRank_isPrime (n - 1)) h3
  have gN := prime_goodMod6 _ (thm_primeAtRank_isPrime n) h3n
  have gS : GoodMod6 (fnPrimeSuccessor n) :=
    prime_goodMod6 _ (thm_primeAtRank_isPrime (n + 1)) h3s
  have hOutEq : (primalEventAt n).outClass = gapClass6 (fnPrimeAtRank n) (fnPrimeSuccessor n) := rfl
  have hInEq : (primalEventAt n).inClass = gapClass6 (fnPrimeAtRank (n - 1)) (fnPrimeAtRank n) := rfl
  have hle2 : fnPrimeAtRank n ≤ fnPrimeSuccessor n := (thm_primeAtRank_lt_successor n).le
  refine ⟨thm_primeAtRank_mod6_state h3n, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hInEq]; exact gapClass6_mem gP gN hlt.le
  · rw [hOutEq]; exact gapClass6_mem gN gS hle2
  · rcases thm_transition_exhaustive h3 with h | h | h | h
    all_goals exact ⟨_, h, fun t ht => thm_transition_unique ht h⟩
  · rcases thm_transition_exhaustive h3n with h | h | h | h
    all_goals exact ⟨_, h, fun t ht => thm_transition_unique ht h⟩
  · rw [hInEq, hOutEq]
    exact gapClass6_alternates gP gN gS hlt.le hle2

/-! ## 2. L'histoire cumulative -/

/-- L'histoire première jusqu'au rang `n` : la liste de ses événements complets. -/
noncomputable def primalHistory (n : ℕ) : List PrimalEvent :=
  (List.range (n + 1)).map primalEventAt

/-- L'histoire reconstruite depuis les zéros jusqu'au rang `n`. -/
noncomputable def reconstructedHistory (n : ℕ) : List PrimalEvent :=
  (List.range (n + 1)).map reconstructedEventAt

/-- **Deux états cumulatifs successifs diffèrent d'exactement un événement complet.** -/
theorem primalHistory_succ (n : ℕ) :
    primalHistory (n + 1) = primalHistory n ++ [primalEventAt (n + 1)] := by
  simp [primalHistory, List.range_succ]

theorem primalHistory_length (n : ℕ) : (primalHistory n).length = n + 1 := by
  simp [primalHistory]

/-- **L'histoire reconstruite depuis les zéros est l'histoire première**, à tout rang. -/
theorem reconstructedHistory_eq_primalHistory (n : ℕ) :
    reconstructedHistory n = primalHistory n := by
  unfold reconstructedHistory primalHistory
  exact List.map_congr_left fun k _ => reconstructedEvent_eq_primalEvent k

/-! ## 3. Le raccord grammatical -/

/-- **Le raccord grammatical** : le raccord entre Tours (premier partagé, deux cellules, deux
encadrements énergétiques, transport), plus l'événement premier complet du premier partagé. -/
structure GrammaticalRaccord (e l : TrueZero) extends TowerRaccord e l where
  /-- Le rang avance d'exactement un cran. -/
  rank_succ : nZeroSourceIndex l.1 = nZeroSourceIndex e.1 + 1
  /-- L'événement premier complet du raccord. -/
  event : PrimalEvent
  event_eq : event = primalEventAt (nZeroSourceIndex l.1)

/-- **Rigidité** : deux raccords grammaticaux entre les mêmes Tours sont égaux. -/
theorem grammaticalRaccord_eq {e l : TrueZero} (R S : GrammaticalRaccord e l) : R = S := by
  obtain ⟨R0, _, E, hE⟩ := R
  obtain ⟨S0, _, F, hF⟩ := S
  obtain rfl := towerRaccord_eq R0 S0
  subst hE hF
  rfl

/-- **Existence** : sur tout passage, le raccord grammatical existe. -/
noncomputable def grammaticalRaccordOf (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    GrammaticalRaccord ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ where
  toTowerRaccord := towerRaccordOf p hE hL
  rank_succ := thm_zeroSourceIndex_succ_of_passage p hE
  event := primalEventAt (nZeroSourceIndex p.zLaterMember)
  event_eq := rfl

namespace GrammaticalRaccord

variable {e l : TrueZero}

/-- Le premier de l'événement est le premier partagé. -/
theorem event_prime (G : GrammaticalRaccord e l) : G.event.prime = G.M := by
  rw [G.event_eq, G.entry_eq, occurrence_eq_primeAtRank]
  rfl

/-- Le prédécesseur de l'événement est l'occurrence de la Tour de sortie. -/
theorem event_predecessor (G : GrammaticalRaccord e l) : G.event.predecessor = occurrence e := by
  rw [G.event_eq, occurrence_eq_primeAtRank]
  show fnPrimeAtRank (nZeroSourceIndex l.1 - 1) = _
  rw [G.rank_succ, Nat.add_sub_cancel]

/-- Le successeur de l'événement est le premier attendu de la Tour d'entrée. -/
theorem event_successor (G : GrammaticalRaccord e l) : G.event.successor = expectedMinimumPrime l := by
  rw [G.event_eq]
  rfl

/-- Le rang de l'événement est strictement positif : il a un prédécesseur. -/
theorem rank_pos (G : GrammaticalRaccord e l) : 0 < nZeroSourceIndex l.1 := by
  rw [G.rank_succ]; omega

/-- L'écart entrant de l'événement est strictement positif. -/
theorem event_inGap_pos (G : GrammaticalRaccord e l) : 0 < G.event.inGap := by
  rw [G.event_eq]; exact primalEvent_inGap_pos G.rank_pos

/-- L'écart sortant de l'événement est strictement positif. -/
theorem event_outGap_pos (G : GrammaticalRaccord e l) : 0 < G.event.outGap := by
  rw [G.event_eq]; exact primalEvent_outGap_pos _

/-- `Occ(e) + écart entrant = M`. -/
theorem occurrence_add_inGap (G : GrammaticalRaccord e l) : occurrence e + G.event.inGap = G.M := by
  rw [← G.event_predecessor, ← G.event_prime, G.event_eq]
  exact primalEvent_predecessor_add_inGap G.rank_pos

/-- `M + écart sortant = p_min(l)`. -/
theorem M_add_outGap (G : GrammaticalRaccord e l) : G.M + G.event.outGap = expectedMinimumPrime l := by
  rw [← G.event_successor, ← G.event_prime, G.event_eq]
  exact primalEvent_prime_add_outGap _

/-- **L'événement du raccord est celui que les zéros reconstruisent.** -/
theorem event_reconstructed (G : GrammaticalRaccord e l) : G.event = reconstructedEventAt (nZeroSourceIndex l.1) := by
  rw [G.event_eq, reconstructedEvent_eq_primalEvent]

/-- **L'histoire première gagne exactement l'événement du raccord.** -/
theorem history_step (G : GrammaticalRaccord e l) :
    primalHistory (nZeroSourceIndex l.1) = primalHistory (nZeroSourceIndex e.1) ++ [G.event] := by
  rw [G.event_eq, G.rank_succ]
  exact primalHistory_succ _

end GrammaticalRaccord

/-- **Le diagramme des deux histoires sur un passage** : le préfixe spectral de `l` est celui de `e`
augmenté du seul membre `e` ; l'histoire première de `l` est celle de `e` augmentée du seul
événement du raccord ; l'histoire reconstruite depuis les zéros est cette même histoire. -/
theorem passage_history_step (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    sUpperZerosBelow p.zLaterMember = insert p.zEarlierMember (sUpperZerosBelow p.zEarlierMember) ∧
      p.zEarlierMember ∉ sUpperZerosBelow p.zEarlierMember ∧
      primalHistory (nZeroSourceIndex p.zLaterMember) =
        primalHistory (nZeroSourceIndex p.zEarlierMember) ++ [(grammaticalRaccordOf p hE hL).event] ∧
      reconstructedHistory (nZeroSourceIndex p.zLaterMember) =
        primalHistory (nZeroSourceIndex p.zLaterMember) :=
  ⟨thm_upperZerosBelow_of_consecutive hE p.hConsecutive,
    fun h => thm_zeroMemberPrecedes_irreflexive _ h.2,
    (grammaticalRaccordOf p hE hL).history_step,
    reconstructedHistory_eq_primalHistory _⟩

/-! ## 4. Ce que l'énergie lit de l'événement : le pas de chaque membre -/

/-- **Le pas d'un membre dans le transport cumulé** : `(Occ(z) / p_min(z))^{β_z − 1/2}`. La base est
le rapport des deux extrémités de l'écart sortant de l'événement de `z`. -/
noncomputable def memberStep (z : TrueZero) : ℝ :=
  ((occurrence z : ℝ) / (expectedMinimumPrime z : ℝ)) ^ (rZeroRadialPosition z.1 - 1 / 2)

theorem occurrence_div_expectedMinimum_mem (z : TrueZero) :
    0 < (occurrence z : ℝ) / (expectedMinimumPrime z : ℝ) ∧
      (occurrence z : ℝ) / (expectedMinimumPrime z : ℝ) < 1 := by
  have hO : (0 : ℝ) < occurrence z := by exact_mod_cast (occurrence_prime z).pos
  have hP : (0 : ℝ) < expectedMinimumPrime z := by exact_mod_cast expectedMinimumPrime_pos z
  have hlt : (occurrence z : ℝ) < expectedMinimumPrime z := by
    exact_mod_cast occurrence_lt_expectedMinimumPrime z
  exact ⟨div_pos hO hP, (div_lt_one hP).mpr hlt⟩

/-- **Le pas d'un membre est neutre si et seulement si le membre est en ligne.** La stricte
positivité de l'écart premier (`Occ < p_min`) est ce qui rend l'équivalence stricte. -/
theorem memberStep_eq_one_iff (z : TrueZero) :
    memberStep z = 1 ↔ rZeroRadialPosition z.1 = 1 / 2 := by
  obtain ⟨hpos, hlt⟩ := occurrence_div_expectedMinimum_mem z
  have hlog : Real.log ((occurrence z : ℝ) / (expectedMinimumPrime z : ℝ)) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hpos hlt.ne
  unfold memberStep
  rw [Real.rpow_def_of_pos hpos, Real.exp_eq_one_iff, mul_eq_zero]
  constructor
  · intro h
    have := h.resolve_left hlog
    linarith
  · intro h
    right; linarith

/-- Un membre à gauche de la ligne amplifie le transport cumulé. -/
theorem memberStep_gt_one_iff (z : TrueZero) :
    1 < memberStep z ↔ rZeroRadialPosition z.1 < 1 / 2 := by
  obtain ⟨hpos, hlt⟩ := occurrence_div_expectedMinimum_mem z
  unfold memberStep
  rw [Real.one_lt_rpow_iff_of_pos hpos]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · linarith
    · linarith
  · exact fun h => Or.inr ⟨hlt, by linarith⟩

/-- Un membre à droite de la ligne atténue le transport cumulé. -/
theorem memberStep_lt_one_iff (z : TrueZero) :
    memberStep z < 1 ↔ 1 / 2 < rZeroRadialPosition z.1 := by
  obtain ⟨hpos, hlt⟩ := occurrence_div_expectedMinimum_mem z
  unfold memberStep
  rw [Real.rpow_lt_one_iff_of_pos hpos]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · linarith
    · linarith
  · exact fun h => Or.inr ⟨hlt, by linarith⟩

/-- **Deux raccords successifs `e → m → l`** aux premiers `M₁`, `M₂` : le membre du milieu n'entre
que par `(M₁/M₂)^{β_m}`, soit le facteur en ligne `(M₁/M₂)^{1/2}` multiplié par
`(M₁/M₂)^{β_m − 1/2}`. -/
theorem two_raccord_transport (e m l : TrueZero) {M₁ M₂ : ℝ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    energyRatio e m M₁ * energyRatio m l M₂ =
      M₂ ^ rZeroRadialPosition l.1 / M₁ ^ rZeroRadialPosition e.1 *
        (‖zeroPoint e‖ / ‖zeroPoint l‖) * (M₁ / M₂) ^ (1 / 2 : ℝ) *
        (M₁ / M₂) ^ (rZeroRadialPosition m.1 - 1 / 2) := by
  rw [energyRatio_eq e m h₁, energyRatio_eq m l h₂]
  have hm := (zeroPoint_norm_pos m).ne'
  have hl := (zeroPoint_norm_pos l).ne'
  have hx : 0 < M₁ / M₂ := div_pos h₁ h₂
  have e0 : (M₁ / M₂) ^ (1 / 2 : ℝ) * (M₁ / M₂) ^ (rZeroRadialPosition m.1 - 1 / 2) =
      M₁ ^ rZeroRadialPosition m.1 / M₂ ^ rZeroRadialPosition m.1 := by
    rw [← Real.rpow_add hx, ← Real.div_rpow h₁.le h₂.le]
    congr 1; ring
  rw [mul_assoc _ ((M₁ / M₂) ^ (1 / 2 : ℝ)), e0, Real.rpow_sub h₁, Real.rpow_sub h₂]
  have a1 := (Real.rpow_pos_of_pos h₁ (rZeroRadialPosition e.1)).ne'
  have a2 := (Real.rpow_pos_of_pos h₂ (rZeroRadialPosition m.1)).ne'
  field_simp

/-- **Au raccord réel** : avec `M₁ = Occ(m)` et `M₂ = p_min(m)`, le facteur du membre du milieu est
son pas `memberStep m`. -/
theorem two_raccord_transport_memberStep (e m l : TrueZero) :
    energyRatio e m (occurrence m) * energyRatio m l (expectedMinimumPrime m) =
      (expectedMinimumPrime m : ℝ) ^ rZeroRadialPosition l.1 /
          (occurrence m : ℝ) ^ rZeroRadialPosition e.1 *
        (‖zeroPoint e‖ / ‖zeroPoint l‖) *
        ((occurrence m : ℝ) / (expectedMinimumPrime m : ℝ)) ^ (1 / 2 : ℝ) * memberStep m :=
  two_raccord_transport e m l (by exact_mod_cast (occurrence_prime m).pos)
    (by exact_mod_cast expectedMinimumPrime_pos m)

/-! ## 5. Le transport cumulé de toute une histoire -/

/-- **Produit des transports le long d'une histoire** de membres `0 … n+1` (positions radiales `β`,
normes `N`), aux premiers partagés `M 0 … M n` : les normes télescopent, et chaque membre intérieur
`k+1` n'entre que par `(M k / M (k+1))^{β (k+1)}`. -/
theorem history_transport_product (β M N : ℕ → ℝ) (hM : ∀ k, 0 < M k) (hN : ∀ k, 0 < N k)
    (n : ℕ) :
    ∏ k ∈ Finset.range (n + 1), (M k ^ (β (k + 1) - β k) * (N k / N (k + 1))) =
      N 0 / N (n + 1) * (M n ^ β (n + 1) / M 0 ^ β 0) *
        ∏ k ∈ Finset.range n, (M k / M (k + 1)) ^ β (k + 1) := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.prod_range_one, Finset.range_zero, Finset.prod_empty, mul_one]
    rw [Real.rpow_sub (hM 0)]
    ring
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Finset.prod_range_succ (fun k => (M k / M (k + 1)) ^ β (k + 1)),
      Real.rpow_sub (hM (n + 1)), Real.div_rpow (hM n).le (hM (n + 1)).le]
    have a0 := (Real.rpow_pos_of_pos (hM 0) (β 0)).ne'
    have a1 := (Real.rpow_pos_of_pos (hM (n + 1)) (β (n + 1))).ne'
    have n1 := (hN (n + 1)).ne'
    have n2 := (hN (n + 1 + 1)).ne'
    field_simp

/-- **La charge de l'histoire** : l'écart du transport cumulé à sa valeur en ligne. -/
noncomputable def historyCharge (β M : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (M k / M (k + 1)) ^ (β (k + 1) - 1 / 2)

/-- Le produit intérieur est sa valeur en ligne `(M 0 / M n)^{1/2}` multipliée par la charge. -/
theorem history_inner_eq_line_mul_charge (β M : ℕ → ℝ) (hM : ∀ k, 0 < M k) (n : ℕ) :
    ∏ k ∈ Finset.range n, (M k / M (k + 1)) ^ β (k + 1) =
      (M 0 / M n) ^ (1 / 2 : ℝ) * historyCharge β M n := by
  induction n with
  | zero => simp [historyCharge, div_self (hM 0).ne']
  | succ n ih =>
    have hx : 0 < M n / M (n + 1) := div_pos (hM n) (hM (n + 1))
    have hy : 0 < M 0 / M n := div_pos (hM 0) (hM n)
    have e1 : (M n / M (n + 1)) ^ β (n + 1) =
        (M n / M (n + 1)) ^ (1 / 2 : ℝ) * (M n / M (n + 1)) ^ (β (n + 1) - 1 / 2) := by
      rw [← Real.rpow_add hx]; congr 1; ring
    have e2 : (M 0 / M (n + 1)) ^ (1 / 2 : ℝ) =
        (M 0 / M n) ^ (1 / 2 : ℝ) * (M n / M (n + 1)) ^ (1 / 2 : ℝ) := by
      rw [← Real.mul_rpow hy.le hx.le, div_mul_div_cancel₀ (hM n).ne']
    unfold historyCharge at ih ⊢
    rw [Finset.prod_range_succ, ih, Finset.prod_range_succ, e1, e2]
    ring

/-- **Deux états cumulatifs successifs** : ajouter un membre multiplie la charge par le pas de ce
membre, l'écart de son événement porté à la puissance de son écart à la ligne. -/
theorem historyCharge_succ (β M : ℕ → ℝ) (n : ℕ) :
    historyCharge β M (n + 1) =
      historyCharge β M n * (M n / M (n + 1)) ^ (β (n + 1) - 1 / 2) := by
  unfold historyCharge
  rw [Finset.prod_range_succ]

/-- Le pas ajouté est neutre si et seulement si le membre ajouté est en ligne, dès que les premiers
partagés avancent strictement. -/
theorem historyStep_eq_one_iff {a b : ℝ} (ha : 0 < a) (hab : a < b) (x : ℝ) :
    (a / b) ^ (x - 1 / 2) = 1 ↔ x = 1 / 2 := by
  have hb : 0 < b := ha.trans hab
  have hpos : 0 < a / b := div_pos ha hb
  have hlog : Real.log (a / b) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hpos ((div_lt_one hb).mpr hab).ne
  rw [Real.rpow_def_of_pos hpos, Real.exp_eq_one_iff, mul_eq_zero]
  constructor
  · intro h
    have := h.resolve_left hlog
    linarith
  · intro h
    right; linarith

/-- **La charge est neutre à chaque état cumulatif si et seulement si tous les membres sont en
ligne** (premiers partagés strictement croissants). Caractérisation, jamais une prémisse. -/
theorem historyCharge_const_one_iff (β M : ℕ → ℝ) (hM : ∀ k, 0 < M k)
    (hlt : ∀ k, M k < M (k + 1)) :
    (∀ n, historyCharge β M n = 1) ↔ ∀ k, β (k + 1) = 1 / 2 := by
  constructor
  · intro h k
    have hs := historyCharge_succ β M k
    rw [h (k + 1), h k, one_mul] at hs
    exact (historyStep_eq_one_iff (hM k) (hlt k) _).mp hs.symm
  · intro h n
    induction n with
    | zero => simp [historyCharge]
    | succ n ih =>
      rw [historyCharge_succ, ih, one_mul]
      exact (historyStep_eq_one_iff (hM n) (hlt n) _).mpr (h n)

/-! ## 6. Test hors ligne : le certificat complet existe sur le passage horizontal -/

/-- **Le certificat grammatical complet n'exclut pas le hors-ligne.** Pour tout zéro hors ligne de
hauteur `≥ 2`, il existe un passage de même hauteur dont le raccord grammatical existe avec tout son
certificat (événement reconstruit depuis les zéros, écarts strictement positifs, histoire première
augmentée d'exactement cet événement), et dont le transport est renversé. -/
theorem off_grammaticalRaccord_complete_and_reversed {z : TrueZero}
    (hOff : PIsOffCriticalLine z.1) (hT2 : 2 ≤ rZeroHeight z.1) :
    ∃ p : TZeroPassage, ∃ hE : 0 < rZeroHeight p.zEarlierMember,
      ∃ hL : 0 < rZeroHeight p.zLaterMember,
        rZeroHeight p.zEarlierMember = rZeroHeight p.zLaterMember ∧
        (grammaticalRaccordOf p hE hL).event =
          reconstructedEventAt (nZeroSourceIndex p.zLaterMember) ∧
        0 < (grammaticalRaccordOf p hE hL).event.inGap ∧
        0 < (grammaticalRaccordOf p hE hL).event.outGap ∧
        primalHistory (nZeroSourceIndex p.zLaterMember) =
          primalHistory (nZeroSourceIndex p.zEarlierMember) ++
            [(grammaticalRaccordOf p hE hL).event] ∧
        ¬ (grammaticalRaccordOf p hE hL).toTowerRaccord.Oriented := by
  obtain ⟨p, hE, hL, hHz, hSame, _, _, _⟩ := off_event_increment_without_height hOff
  have hHMR := nullPassage_horizontal p ((thm_zeroPassage_null_iff_sameHeight p).mpr hSame)
  refine ⟨p, hE, hL, hSame, (grammaticalRaccordOf p hE hL).event_reconstructed,
    (grammaticalRaccordOf p hE hL).event_inGap_pos, (grammaticalRaccordOf p hE hL).event_outGap_pos,
    (grammaticalRaccordOf p hE hL).history_step, not_le.mpr ?_⟩
  exact towerRaccord_reverses_of_sameHeight (towerRaccordOf p hE hL) hSame (hHz ▸ hT2) hHMR.2.1

/-! ## 7. Les préfixes analytiques : les fenêtres de hauteur -/

/-- Le terme d'un membre dans la somme tronquée de la base est sa multiplicité fois `zeroTerm`. -/
theorem zeroContribution_eq_mul_zeroTerm (z : TrueZero) (x : ℝ) :
    cZeroContribution x (zeroPoint z) =
      (analyticOrderNatAt riemannZeta (zeroPoint z) : ℂ) * zeroTerm z x := rfl

/-- **Deux préfixes analytiques successifs** : la somme tronquée au cutoff `C₂` est celle au cutoff
`C₁ ≤ C₂` augmentée des seuls membres entrés entre les deux. -/
theorem symmetricZeroSum_increment (x : ℝ) {C₁ C₂ : ℝ} (h : C₁ ≤ C₂) :
    cSymmetricZeroSum x C₂ = cSymmetricZeroSum x C₁ +
      ∑ c ∈ finsetSymmetricZeroWindow C₂ \ finsetSymmetricZeroWindow C₁, cZeroContribution x c := by
  classical
  unfold cSymmetricZeroSum
  rw [add_comm]
  exact (Finset.sum_sdiff (thm_symmetricZeroWindow_mono h)).symm

/-- Un membre et son miroir entrent dans les mêmes fenêtres. -/
theorem window_mem_mirror_iff (z : TNonTrivialZetaZero) (C : ℝ) :
    cZeroSupport (zMirrorZero z) ∈ finsetSymmetricZeroWindow C ↔
      cZeroSupport z ∈ finsetSymmetricZeroWindow C := by
  rw [thm_mem_finsetSymmetricZeroWindow, thm_mem_finsetSymmetricZeroWindow]
  have h : (cZeroSupport (zMirrorZero z)).im = (cZeroSupport z).im := thm_mirror_sameHeight z
  rw [h]
  exact ⟨fun hh => ⟨z.2, hh.2⟩, fun hh => ⟨(zMirrorZero z).2, hh.2⟩⟩

/-- **Un préfixe analytique sépare les deux membres d'un passage si et seulement si la hauteur
avance.** Sur un passage horizontal, aucun état cumulatif de la formule explicite ne contient le
membre de sortie sans le membre d'entrée. -/
theorem passage_separated_by_window_iff (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember) :
    (∃ C : ℝ, cZeroSupport p.zEarlierMember ∈ finsetSymmetricZeroWindow C ∧
        cZeroSupport p.zLaterMember ∉ finsetSymmetricZeroWindow C) ↔
      rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember := by
  have hEa : |(cZeroSupport p.zEarlierMember).im| = rZeroHeight p.zEarlierMember := abs_of_pos hE
  have hLa : |(cZeroSupport p.zLaterMember).im| = rZeroHeight p.zLaterMember := abs_of_pos hL
  constructor
  · rintro ⟨C, hIn, hOut⟩
    rw [thm_mem_finsetSymmetricZeroWindow] at hIn hOut
    have h1 : rZeroHeight p.zEarlierMember ≤ C := hEa ▸ hIn.2
    have h2 : C < rZeroHeight p.zLaterMember := by
      by_contra hn
      exact hOut ⟨p.zLaterMember.2, hLa ▸ not_lt.mp hn⟩
    linarith
  · intro hT
    refine ⟨rZeroHeight p.zEarlierMember, ?_, ?_⟩
    · rw [thm_mem_finsetSymmetricZeroWindow]
      exact ⟨p.zEarlierMember.2, hEa.le⟩
    · rw [thm_mem_finsetSymmetricZeroWindow]
      rintro ⟨_, h⟩
      rw [hLa] at h
      linarith

/-- **Le raccord est orienté si et seulement si un préfixe analytique sépare ses deux membres**
(membre de sortie à hauteur `≥ 2`). -/
theorem towerRaccord_oriented_iff_window_separates (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hT2 : 2 ≤ rZeroHeight p.zEarlierMember) :
    (towerRaccordOf p hE hL).Oriented ↔
      ∃ C : ℝ, cZeroSupport p.zEarlierMember ∈ finsetSymmetricZeroWindow C ∧
        cZeroSupport p.zLaterMember ∉ finsetSymmetricZeroWindow C :=
  (towerRaccord_oriented_iff_height_lt p hE hL hT2).trans
    (passage_separated_by_window_iff p hE hL).symm

/-! ## 8. Le monde témoin devant la reconstruction complète -/

/-- Le canal de Chebyshev du monde témoin `ζ(s−d)ζ(s+d)` : la somme de ses coefficients
`Λ(n)(n^d + n^{−d})` (`shiftedWorld_negLogDeriv`). -/
noncomputable def shiftedPsi (d x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n * ((n : ℝ) ^ d + (n : ℝ) ^ (-d))

/-- Le poids reconstruit depuis le canal du monde témoin est `Λ(n)(n^d + n^{−d})`. -/
theorem shiftedPsi_weight (d : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    fnWeightFromPsi (shiftedPsi d) n = Λ n * ((n : ℝ) ^ d + (n : ℝ) ^ (-d)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold fnWeightFromPsi shiftedPsi
  have hFloorSucc : ⌊((m + 1 : ℕ) : ℝ)⌋₊ = m + 1 := Nat.floor_natCast _
  have hFloorPred : ⌊((m + 1 : ℕ) : ℝ) - 1⌋₊ = m := by
    push_cast
    rw [show (m : ℝ) + 1 - 1 = (m : ℝ) by ring]
    simp
  rw [hFloorSucc, hFloorPred, Finset.sum_Ioc_succ_top (Nat.zero_le m)]
  ring

/-- **Le foncteur de reconstruction ne reconnaît aucun premier dans le monde témoin**, pour tout
`d` (y compris `d = 0`, le monde `ζ²`) : le poids d'un premier `p` y vaut
`log p · (p^d + p^{−d}) ≥ 2 log p`, jamais `log p`. -/
theorem shiftedWorld_reconstructs_no_prime (d : ℝ) {p : ℕ} (hp : p.Prime) :
    ¬ PPrimeFromPsi (shiftedPsi d) p := by
  rintro ⟨_, hW⟩
  rw [shiftedPsi_weight d hp.one_le, vonMangoldt_apply_prime hp] at hW
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have ha : 0 < (p : ℝ) ^ d := Real.rpow_pos_of_pos hp0 d
  have hinv : (p : ℝ) ^ (-d) = ((p : ℝ) ^ d)⁻¹ := Real.rpow_neg hp0.le d
  have h2 : 2 ≤ (p : ℝ) ^ d + (p : ℝ) ^ (-d) := by
    rw [hinv]
    have hmul : (p : ℝ) ^ d * ((p : ℝ) ^ d)⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
    nlinarith [sq_nonneg ((p : ℝ) ^ d - 1), inv_pos.mpr ha, sq_nonneg (((p : ℝ) ^ d)⁻¹ - 1)]
  nlinarith

/-! ## 9. L'environnement complet du raccord sur un passage -/

/-- **Tout ce que le raccord porte, ensemble, sur un passage quelconque** : la géométrie (le premier
partagé dans la cellule de sortie et dans la cellule d'entrée), l'énergie (le transport exact),
l'événement premier complet (premier, prédécesseur, successeur, écarts non nuls), sa reconstruction
depuis les zéros, l'histoire augmentée d'exactement cet événement, et le détecteur sous ses deux
formes (la hauteur avance ; un préfixe analytique sépare les deux membres). -/
theorem grammaticalRaccord_environment (p : TZeroPassage)
    (hE : 0 < rZeroHeight p.zEarlierMember) (hL : 0 < rZeroHeight p.zLaterMember)
    (hT2 : 2 ≤ rZeroHeight p.zEarlierMember) :
    (contactMinusAt ⟨p.zEarlierMember, hE⟩ (grammaticalRaccordOf p hE hL).exitCell <
        (grammaticalRaccordOf p hE hL).M ∧
      ((grammaticalRaccordOf p hE hL).M : ℝ) ≤
        contactPlusAt ⟨p.zEarlierMember, hE⟩ (grammaticalRaccordOf p hE hL).exitCell) ∧
    (contactMinusAt ⟨p.zLaterMember, hL⟩ (grammaticalRaccordOf p hE hL).entryCell <
        (grammaticalRaccordOf p hE hL).M ∧
      ((grammaticalRaccordOf p hE hL).M : ℝ) ≤
        contactPlusAt ⟨p.zLaterMember, hL⟩ (grammaticalRaccordOf p hE hL).entryCell) ∧
    energyRatio ⟨p.zEarlierMember, hE⟩ ⟨p.zLaterMember, hL⟩ (grammaticalRaccordOf p hE hL).M =
      ((grammaticalRaccordOf p hE hL).M : ℝ) ^
          (rZeroRadialPosition p.zLaterMember - rZeroRadialPosition p.zEarlierMember) *
        (‖zeroPoint ⟨p.zEarlierMember, hE⟩‖ / ‖zeroPoint ⟨p.zLaterMember, hL⟩‖) ∧
    (grammaticalRaccordOf p hE hL).event.prime = (grammaticalRaccordOf p hE hL).M ∧
    (grammaticalRaccordOf p hE hL).event.predecessor = occurrence ⟨p.zEarlierMember, hE⟩ ∧
    (grammaticalRaccordOf p hE hL).event.successor = expectedMinimumPrime ⟨p.zLaterMember, hL⟩ ∧
    0 < (grammaticalRaccordOf p hE hL).event.inGap ∧
    0 < (grammaticalRaccordOf p hE hL).event.outGap ∧
    (grammaticalRaccordOf p hE hL).event =
      reconstructedEventAt (nZeroSourceIndex p.zLaterMember) ∧
    primalHistory (nZeroSourceIndex p.zLaterMember) =
      primalHistory (nZeroSourceIndex p.zEarlierMember) ++
        [(grammaticalRaccordOf p hE hL).event] ∧
    ((grammaticalRaccordOf p hE hL).toTowerRaccord.Oriented ↔
      rZeroHeight p.zEarlierMember < rZeroHeight p.zLaterMember) ∧
    ((grammaticalRaccordOf p hE hL).toTowerRaccord.Oriented ↔
      ∃ C : ℝ, cZeroSupport p.zEarlierMember ∈ finsetSymmetricZeroWindow C ∧
        cZeroSupport p.zLaterMember ∉ finsetSymmetricZeroWindow C) :=
  ⟨(grammaticalRaccordOf p hE hL).exitCell_contains,
    (grammaticalRaccordOf p hE hL).entryCell_contains,
    (grammaticalRaccordOf p hE hL).transport,
    (grammaticalRaccordOf p hE hL).event_prime,
    (grammaticalRaccordOf p hE hL).event_predecessor,
    (grammaticalRaccordOf p hE hL).event_successor,
    (grammaticalRaccordOf p hE hL).event_inGap_pos,
    (grammaticalRaccordOf p hE hL).event_outGap_pos,
    (grammaticalRaccordOf p hE hL).event_reconstructed,
    (grammaticalRaccordOf p hE hL).history_step,
    towerRaccord_oriented_iff_height_lt p hE hL hT2,
    towerRaccord_oriented_iff_window_separates p hE hL hT2⟩

/-! ## 10. L'organisme spectral (énoncé de l'auteur, 2026-09-30)

« L'ensemble complet des zéros non triviaux supérieurs, avec leur géométrie, leurs Tours, leurs
contacts, leur ordre de membres, leurs hauteurs, leurs coordonnées radiales et leurs transports
énergétiques, constitue le même organisme spectral que celui qui reconstruit exactement le reste
arithmétique de l'escalier des premiers ; cette reconstruction conserve simultanément la grammaire
première complète. » Les deux théorèmes ci-dessous en sont la forme compilée : le premier dit que le
membre qui porte la Tour EST le terme sommé par la formule explicite ; le second que la somme de
tous ces termes redonne `ψ` et toute l'histoire première. Ils sont inconditionnels : ils valent
que les zéros soient en ligne ou non. -/

/-- Tout descripteur de l'histoire (pattern, famille, méta-pattern, ordre des événements) calculé
sur l'histoire reconstruite depuis les zéros est celui de l'histoire première. -/
theorem reconstructedHistory_descriptor {α : Type*} (F : List PrimalEvent → α) (n : ℕ) :
    F (reconstructedHistory n) = F (primalHistory n) := by
  rw [reconstructedHistory_eq_primalHistory]

/-- **Un seul et même membre** : le zéro qui porte la Tour est le terme de la formule explicite.
Son terme dans la somme tronquée est sa multiplicité fois `zeroTerm` ; son terme dans le canal
compilé est `−m(ρ)·Perron.f` ; ce terme est réel exactement sur les rayons de la Tour (contacts) ;
son module est l'énergie `x^β/‖ρ‖` que transporte le raccord ; le zéro conjugué (branche
inférieure) apporte le terme conjugué. -/
theorem spectral_organism_member (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    cZeroContribution x (zeroPoint z) =
        (analyticOrderNatAt riemannZeta (zeroPoint z) : ℂ) * zeroTerm z x ∧
      nontrivialZeroResidueTerm x ⟨zeroPoint z, zeroPoint_isNontrivial z⟩ =
        -(zetaZeroMultiplicity (zeroPoint z) : ℂ) * Perron.f x (zeroPoint z) ∧
      ((zeroTerm z x).im = 0 ↔ ∃ k : ℤ, x = contactMinusAt z k) ∧
      ‖zeroTerm z x‖ = x ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖ ∧
      (x : ℂ) ^ (starRingEnd ℂ (zeroPoint z)) / starRingEnd ℂ (zeroPoint z) =
        starRingEnd ℂ (zeroTerm z x) :=
  ⟨rfl, rfl, zeroTerm_real_iff_ray hx, zeroTerm_norm hx, conjugate_term_eq_conj hx⟩

/-- **L'organisme entier reconstruit l'escalier et sa grammaire complète** : `ψ` est exactement
reconstruite depuis les zéros (`x ≥ 2`) ; chaque événement premier complet et toute l'histoire
première le sont aussi, ainsi que tout descripteur de cette histoire. -/
theorem spectral_organism_reconstructs {x : ℝ} (hx : 2 ≤ x) (n : ℕ) :
    psiRecoveredFromZeros x = (Chebyshev.psi x : ℂ) ∧
      reconstructedEventAt n = primalEventAt n ∧
      reconstructedHistory n = primalHistory n ∧
      ∀ {α : Type} (F : List PrimalEvent → α), F (reconstructedHistory n) = F (primalHistory n) :=
  ⟨liaison_analytic hx, reconstructedEvent_eq_primalEvent n,
    reconstructedHistory_eq_primalHistory n, fun F => reconstructedHistory_descriptor F n⟩

/-! ## 11. Le reste arithmétique, deux états successifs, et l'incrément d'un passage

Programme de l'auteur (2026-09-30) : retirer le fond lisse ; identifier le reste que les zéros
doivent produire ; comparer deux états successifs de ce reste ; faire apparaître la contribution
différentielle du passage spectral ; tester si un passage hors ligne produit le même incrément. -/

/-- Le fond lisse de la formule explicite : `x − log 2π − ½·log(1 − x⁻²)`. -/
noncomputable def smoothBackground (x : ℝ) : ℝ :=
  x - Real.log (2 * Real.pi) - 1 / 2 * Real.log (1 - x⁻¹ ^ 2)

/-- Le reste arithmétique : l'escalier `ψ` privé du fond lisse. -/
noncomputable def arithmeticRemainder (x : ℝ) : ℝ :=
  Chebyshev.psi x - smoothBackground x

/-- Le canal tronqué de la base est le fond lisse moins la somme des zéros de la fenêtre : ce que
les zéros doivent produire est exactement le reste. -/
theorem zeroChannelApprox_eq_background_sub_zeroSum (x C : ℝ) :
    rZeroChannelApprox x C = smoothBackground x - (cSymmetricZeroSum x C).re := by
  unfold rZeroChannelApprox smoothBackground
  ring

/-- **Deux états successifs du reste, à un événement premier** : de `p − 1` à `p`, le reste avance
du poids `log p` du premier, moins l'avance du fond lisse. -/
theorem remainder_increment_at_prime (n : ℕ) :
    arithmeticRemainder (fnPrimeAtRank n) - arithmeticRemainder ((fnPrimeAtRank n : ℝ) - 1) =
      Real.log (fnPrimeAtRank n) -
        (smoothBackground (fnPrimeAtRank n) - smoothBackground ((fnPrimeAtRank n : ℝ) - 1)) := by
  have h1 : 1 ≤ fnPrimeAtRank n := by have := thm_primeAtRank_ge_two n; omega
  have hw := thm_weightFromPsi_chebyshev h1
  rw [vonMangoldt_apply_prime (thm_primeAtRank_isPrime n)] at hw
  unfold fnWeightFromPsi at hw
  unfold arithmeticRemainder
  linarith

/-- **La contribution différentielle d'un membre** : la dérivée en `x` de son terme `x^ρ/ρ` est
`x^{ρ−1}`. -/
theorem zeroTerm_hasDerivAt (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => zeroTerm z y) ((x : ℂ) ^ (zeroPoint z - 1)) x := by
  have hne : zeroPoint z - 1 ≠ -1 := by
    intro h
    apply zeroPoint_ne_zero z
    linear_combination h
  have hd := hasDerivAt_ofReal_cpow_const' hx.ne' hne
  simpa only [zeroTerm, sub_add_cancel] using hd

/-- Le module de la contribution différentielle d'un membre est `x^{β−1}`. -/
theorem zeroTerm_density_norm (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (zeroPoint z - 1)‖ = x ^ (rZeroRadialPosition z.1 - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [zeroPoint_re]

/-- Pour `x > 1` et `d ≠ 0`, `x^d + x^{−d} > 2`. -/
theorem two_lt_rpow_add_rpow_neg {x d : ℝ} (hx : 1 < x) (hd : d ≠ 0) :
    2 < x ^ d + x ^ (-d) := by
  have hx0 : 0 < x := by linarith
  have ha : 0 < x ^ d := Real.rpow_pos_of_pos hx0 d
  have hne : x ^ d ≠ 1 := by
    rw [Real.rpow_def_of_pos hx0, Ne, Real.exp_eq_one_iff, mul_eq_zero]
    rintro (h | h)
    · exact (Real.log_pos hx).ne' h
    · exact hd h
  rw [Real.rpow_neg hx0.le]
  have hkey : x ^ d + (x ^ d)⁻¹ - 2 = (x ^ d - 1) ^ 2 / x ^ d := by
    field_simp
    ring
  have hpos : 0 < (x ^ d - 1) ^ 2 / x ^ d :=
    div_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hne)))) ha
  linarith

/-- **Le passage hors ligne ne produit pas l'incrément d'un passage en ligne.** Pour une paire à
même hauteur en `1/2 ∓ d`, la somme des modules des deux contributions différentielles vaut
`x^{−1/2}·(x^d + x^{−d})` : celle de deux membres en ligne, `2·x^{−1/2}`, multipliée par
`(x^d + x^{−d})/2`. -/
theorem off_pair_density_norm (e l : TrueZero) {x d : ℝ} (hx : 0 < x)
    (he : rZeroRadialPosition e.1 = 1 / 2 - d) (hl : rZeroRadialPosition l.1 = 1 / 2 + d) :
    ‖(x : ℂ) ^ (zeroPoint e - 1)‖ + ‖(x : ℂ) ^ (zeroPoint l - 1)‖ =
      x ^ (-(1 / 2) : ℝ) * (x ^ d + x ^ (-d)) := by
  rw [zeroTerm_density_norm e hx, zeroTerm_density_norm l hx, he, hl, mul_add,
    ← Real.rpow_add hx, ← Real.rpow_add hx]
  have h1 : (1 / 2 - d - 1 : ℝ) = -(1 / 2) + -d := by ring
  have h2 : (1 / 2 + d - 1 : ℝ) = -(1 / 2) + d := by ring
  rw [h1, h2]
  ring

/-- Hors ligne (`d ≠ 0`, `x > 1`), cette somme dépasse strictement celle de deux membres en ligne. -/
theorem off_pair_density_exceeds_line (e l : TrueZero) {x d : ℝ} (hx : 1 < x) (hd : d ≠ 0)
    (he : rZeroRadialPosition e.1 = 1 / 2 - d) (hl : rZeroRadialPosition l.1 = 1 / 2 + d) :
    2 * x ^ (-(1 / 2) : ℝ) <
      ‖(x : ℂ) ^ (zeroPoint e - 1)‖ + ‖(x : ℂ) ^ (zeroPoint l - 1)‖ := by
  have hx0 : 0 < x := by linarith
  rw [off_pair_density_norm e l hx0 he hl]
  have hp : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx0 _
  nlinarith [two_lt_rpow_add_rpow_neg hx hd]

/-! ## 12. Deux rigidités de plus lues par le raccord : l'injectivité et la charge par l'événement -/

/-- **Un événement premier appartient à un seul raccord** : deux raccords grammaticaux de même
premier partagé relient les mêmes Tours. -/
theorem grammaticalRaccord_M_injective {e₁ l₁ e₂ l₂ : TrueZero}
    (G₁ : GrammaticalRaccord e₁ l₁) (G₂ : GrammaticalRaccord e₂ l₂) (h : G₁.M = G₂.M) :
    e₁ = e₂ ∧ l₁ = l₂ := by
  constructor
  · apply expectedMinimumPrime_injective
    rw [← G₁.exit_eq, ← G₂.exit_eq, h]
  · have hO : occurrence l₁ = occurrence l₂ := by rw [← G₁.entry_eq, ← G₂.entry_eq, h]
    rw [occurrence_eq_primeAtRank, occurrence_eq_primeAtRank] at hO
    exact thm_zeroSourceIndex_injective (thm_primeAtRank_injective hO)

/-- **La charge d'une fibre se lit sur l'événement du raccord central** : avec `M₁`, `M₂`, `M₃` le
prédécesseur, le premier et le successeur de l'événement, `M₂² − M₁·M₃ = M₂·(g_in − g_out) +
g_in·g_out`. -/
theorem primalEvent_charge_by_gaps {n : ℕ} (hn : 0 < n) :
    ((primalEventAt n).prime : ℝ) ^ 2 -
        ((primalEventAt n).predecessor : ℝ) * ((primalEventAt n).successor : ℝ) =
      ((primalEventAt n).prime : ℝ) *
          (((primalEventAt n).inGap : ℝ) - ((primalEventAt n).outGap : ℝ)) +
        ((primalEventAt n).inGap : ℝ) * ((primalEventAt n).outGap : ℝ) := by
  have h1 := primalEvent_predecessor_add_inGap hn
  have h2 := primalEvent_prime_add_outGap n
  have h1' : ((primalEventAt n).predecessor : ℝ) + (primalEventAt n).inGap =
      (primalEventAt n).prime := by exact_mod_cast h1
  have h2' : ((primalEventAt n).prime : ℝ) + (primalEventAt n).outGap =
      (primalEventAt n).successor := by exact_mod_cast h2
  rw [← h2', ← sub_eq_iff_eq_add.mpr h1'.symm]
  ring

/-- Écart entrant `≥` écart sortant : la fibre centrée sur cet événement amplifie
(`M₁·M₃ < M₂²`). -/
theorem primalEvent_amplifies_of_inGap_ge {n : ℕ} (hn : 0 < n)
    (hg : (primalEventAt n).outGap ≤ (primalEventAt n).inGap) :
    ((primalEventAt n).predecessor : ℝ) * ((primalEventAt n).successor : ℝ) <
      ((primalEventAt n).prime : ℝ) ^ 2 := by
  have h := primalEvent_charge_by_gaps hn
  have hin : (0 : ℝ) < (primalEventAt n).inGap := by exact_mod_cast primalEvent_inGap_pos hn
  have hout : (0 : ℝ) < (primalEventAt n).outGap := by exact_mod_cast primalEvent_outGap_pos n
  have hp : (0 : ℝ) ≤ (primalEventAt n).prime := Nat.cast_nonneg _
  have hg' : ((primalEventAt n).outGap : ℝ) ≤ (primalEventAt n).inGap := by exact_mod_cast hg
  nlinarith [mul_pos hin hout, mul_nonneg hp (sub_nonneg.mpr hg')]

#print axioms reconstructedEvent_eq_primalEvent
#print axioms primalEvent_certificate
#print axioms reconstructedHistory_eq_primalHistory
#print axioms grammaticalRaccordOf
#print axioms grammaticalRaccord_eq
#print axioms passage_history_step
#print axioms memberStep_eq_one_iff
#print axioms two_raccord_transport_memberStep
#print axioms history_transport_product
#print axioms history_inner_eq_line_mul_charge
#print axioms historyCharge_const_one_iff
#print axioms off_grammaticalRaccord_complete_and_reversed
#print axioms passage_separated_by_window_iff
#print axioms towerRaccord_oriented_iff_window_separates
#print axioms shiftedWorld_reconstructs_no_prime
#print axioms grammaticalRaccord_environment
#print axioms spectral_organism_member
#print axioms spectral_organism_reconstructs
#print axioms remainder_increment_at_prime
#print axioms zeroTerm_hasDerivAt
#print axioms off_pair_density_norm
#print axioms off_pair_density_exceeds_line
#print axioms grammaticalRaccord_M_injective
#print axioms primalEvent_charge_by_gaps

end RHV6Fresh
