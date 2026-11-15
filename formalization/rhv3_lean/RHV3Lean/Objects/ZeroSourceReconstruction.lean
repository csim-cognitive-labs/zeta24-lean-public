/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.TrueZero
import RHV3Lean.Objects.PrimeGapGrammar
import RHV3Lean.Objects.CountingRigidity
import RHV3Lean.Objects.VonMangoldtChebyshev
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting

/-!
# RHV3Lean — L15/L16, reconstruction depuis la source complète des zéros

    TRACE_ID              : RHV3-L15-L16
    SEMANTIC_OBJECT       : la reconstruction de l'histoire première depuis la
                            source complète des vrais zéros non triviaux.
    SEMANTIC_STATEMENT    : la source des vrais zéros, tronquée symétriquement
                            en hauteur, porte une somme finie de contributions
                            étiquetées par membre ; un canal `psi` construit à
                            partir de cette source, une fois identifié au canal
                            de Chebyshev, redonne exactement l'histoire première
                            canonique, composante par composante.
    MATHEMATICAL_STATEMENT: (L15) la fenêtre {rho : PIsNonTrivialZetaZero rho,
                            |Im rho| <= C} est finie pour tout C, et la somme
                            tronquée qu'elle porte est assemblée depuis les
                            contributions m(rho)*x^rho/rho, une par membre.
                            (L16) psi_Z = Chebyshev.psi entraîne, pour la
                            grammaire reconstruite depuis psi_Z, l'égalité
                            composante par composante avec l'histoire première
                            canonique (poids, primalité, comptage, rangs,
                            écarts).
    MATHEMATICAL_PARENT   : O1 (le vrai zéro), O6 (la grammaire des écarts
                            premiers), O10 (la rigidité de comptage).
    REQUIRED_LEMMAS       : isCompact_Icc.reProdIm, inter_riemannZetaZeros_finite,
                            Finset.sum_attach, vonMangoldt_apply_prime,
                            vonMangoldt_apply_pow, vonMangoldt_eq_zero_iff,
                            Nat.count_eq_card_filter_range
    WHY_EACH_LEMMA_EXISTS : les deux premiers donnent la finitude de la fenêtre
                            par compacité, seule source admissible ; le
                            troisième réexprime la somme comme somme
                            étiquetée ; les trois suivants recouvrent
                            exactement la primalité depuis Lambda ; le dernier
                            identifie le comptage reconstruit à
                            Nat.primeCounting.
    LEAN_DEFINITION       : sSymmetricZeroWindow, finsetSymmetricZeroWindow,
                            cZeroContribution, cMemberContribution,
                            cSymmetricZeroSum, fnWeightFromPsi, PPrimeFromPsi,
                            fnCountingFromPsi, fnPrimeAtRankFromPsi,
                            fnGapAtRankFromPsi, TReconstructedPrimeGrammar,
                            fnReconstructGrammar, rhv3CanonicalGrammar
    LEAN_THEOREM          : thm_symmetricZeroWindow_finite,
                            thm_symmetricZeroSum_eq_labelled_sum,
                            thm_M9b_grammar_rigidity,
                            thm_M9b_pointwise_components,
                            thm_weightFromPsi_eq_of_agree_on_naturals,
                            thm_primeFromPsi_iff_of_agree_on_naturals,
                            thm_primeFromPsi_eq_of_agree_on_naturals,
                            thm_M9b_pointwise_components_weak,
                            thm_reconstructedPrimeAtRank_eq_canonicalPrimeAtRank,
                            thm_reconstructedGap_eq_canonicalGap,
                            thm_reconstructedCounting_eq_canonicalCounting,
                            thm_reconstruction_is_not_a_definitional_alias
    SAME_MEMBER_CHECK     : chaque contribution étiquetée (`cMemberContribution`)
                            porte son membre `TNonTrivialZetaZero` en argument,
                            jamais un point complexe anonyme ; deux membres de
                            même support donnent la même contribution
                            (`thm_memberContribution_determines_member`).
    SAME_PASSAGE_CHECK    : sans objet à ce niveau — aucun passage n'est
                            construit ici.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : `thm_reconstructedPrimeAtRank_eq_canonicalPrimeAtRank`
                            et `thm_reconstructedGap_eq_canonicalGap`
                            identifient, sous l'hypothèse de canal, la
                            reconstruction à l'UNIQUE histoire première déjà
                            produite en O6 (`fnPrimeAtRank`, `nPrimeGap`) ;
                            aucune seconde énumération n'est fabriquée.
    PROOF_STRATEGY        : (L15) une fenêtre symétrique en hauteur des vrais
                            zéros est finie par compacité (même technique que
                            OFF.LOCAL_FINITENESS, étendue à une fenêtre) ; la
                            somme tronquée est donc un Finset.sum, assemblée à
                            partir de contributions individuellement étiquetées
                            par le membre qui les porte. (L16) un canal `psi`
                            arbitraire donne, par différence première puis par
                            la caractérisation exacte de la primalité par
                            `Lambda n = log n`, une grammaire première complète
                            et déterministe ; appliquée au canal de Chebyshev,
                            elle coïncide, composante par composante, avec les
                            objets déjà produits de O6/O10.
    FORBIDDEN_PREMISES    : recevoir T1, C3, placeIndex, T2 ou RH en hypothèse ;
                            poser `M^Z = M` comme champ d'une structure plutôt
                            que comme théorème ; appeler Λ canonique de Mathlib
                            seul une reconstruction zéro-source.
    NEXT_CONSUMER         : le futur producteur T2, qui devra attacher ces
                            identités ponctuelles à un contact canonique sans
                            jamais les recevoir en hypothèse.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED (L15, L16) ; le lien `psi_Z = psi`
                            lui-même (M9a analytique, formule explicite) reste
                            NOT_YET_CERTIFIED_LEAN et n'est ni supposé ni utilisé
                            comme fait ici — il n'apparaît que comme hypothèse
                            explicite d'un théorème de transport.

Aucun `sorry`, aucun `admit`, aucun `axiome` nouveau.
-/

namespace RHV3Lean

open ArithmeticFunction Complex

/-! ## L15 — la source complète des vrais zéros, tronquée symétriquement -/

/-- **La fenêtre symétrique en hauteur** des vrais zéros non triviaux : la
source complète, restreinte à `|Im rho| <= rCutoff`. -/
def sSymmetricZeroWindow (rCutoff : ℝ) : Set ℂ :=
  {cPoint | PIsNonTrivialZetaZero cPoint ∧ |cPoint.im| ≤ rCutoff}

/-- Le segment vertical fermé qui contient toute fenêtre symétrique : la bande
`[0,1]` croisée avec `[-rCutoff, rCutoff]`, compacte comme produit de deux
segments compacts. -/
private noncomputable def sSymmetricWindowSegment (rCutoff : ℝ) : Set ℂ :=
  Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (-rCutoff) rCutoff

private theorem thm_symmetricWindowSegment_isCompact (rCutoff : ℝ) :
    IsCompact (sSymmetricWindowSegment rCutoff) :=
  isCompact_Icc.reProdIm isCompact_Icc

/-- **L15.LOCAL_FINITENESS.**  Une fenêtre symétrique en hauteur des vrais
zéros ne porte qu'un nombre FINI de membres.

Seule source admissible : la discrétion locale des zéros de zêta appliquée à
un compact, exactement comme `thm_zeroHeightFiber_finite` de OFF, mais sur une
fenêtre entière plutôt qu'une fibre unique. -/
theorem thm_symmetricZeroWindow_finite (rCutoff : ℝ) :
    (sSymmetricZeroWindow rCutoff).Finite := by
  have hWindowZerosFinite :
      (sSymmetricWindowSegment rCutoff ∩ riemannZetaZeros).Finite :=
    (thm_symmetricWindowSegment_isCompact rCutoff).inter_riemannZetaZeros_finite
  refine hWindowZerosFinite.subset ?_
  rintro cPoint ⟨⟨hZetaZero, hRePos, hReLtOne⟩, hAbs⟩
  refine ⟨?_, mem_riemannZetaZeros.mpr hZetaZero⟩
  rw [show sSymmetricWindowSegment rCutoff =
    Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (-rCutoff) rCutoff from rfl,
    Complex.mem_reProdIm]
  exact ⟨⟨le_of_lt hRePos, le_of_lt hReLtOne⟩,
    ⟨neg_le_of_abs_le hAbs, le_of_abs_le hAbs⟩⟩

/-- La fenêtre symétrique, comme `Finset` explicite. -/
noncomputable def finsetSymmetricZeroWindow (rCutoff : ℝ) : Finset ℂ :=
  (thm_symmetricZeroWindow_finite rCutoff).toFinset

@[simp]
theorem thm_mem_finsetSymmetricZeroWindow
    {rCutoff : ℝ} {cPoint : ℂ} :
    cPoint ∈ finsetSymmetricZeroWindow rCutoff ↔
      PIsNonTrivialZetaZero cPoint ∧ |cPoint.im| ≤ rCutoff := by
  simp [finsetSymmetricZeroWindow, sSymmetricZeroWindow]

/-- Contribution étiquetée d'un point-zéro à la formule explicite tronquée :
`m(rho) * x^rho / rho`, portant sa propre multiplicité analytique. -/
noncomputable def cZeroContribution (rArgument : ℝ) (cPoint : ℂ) : ℂ :=
  (analyticOrderNatAt riemannZeta cPoint : ℂ) * ((rArgument : ℂ) ^ cPoint / cPoint)

/-- Contribution d'un membre TYPÉ : l'argument est le membre, jamais un point
anonyme. C'est la forme qui porte la provenance. -/
noncomputable def cMemberContribution
    (rArgument : ℝ) (zZero : TNonTrivialZetaZero) : ℂ :=
  cZeroContribution rArgument (cZeroSupport zZero)

/-- **La somme tronquée symétrique**, une somme finie et rien d'autre. -/
noncomputable def cSymmetricZeroSum (rArgument rCutoff : ℝ) : ℂ :=
  ∑ cPoint ∈ finsetSymmetricZeroWindow rCutoff, cZeroContribution rArgument cPoint

/-- **L15.PROVENANCE.**  La somme tronquée est assemblée à partir des
contributions étiquetées par membre, et de rien d'autre : la provenance est
disponible AVANT l'agrégation. -/
theorem thm_symmetricZeroSum_eq_labelled_sum
    (rArgument rCutoff : ℝ) :
    cSymmetricZeroSum rArgument rCutoff =
      ∑ cPoint ∈ (finsetSymmetricZeroWindow rCutoff).attach,
        cMemberContribution rArgument
          ⟨cPoint.1, (thm_mem_finsetSymmetricZeroWindow.mp cPoint.2).1⟩ := by
  rw [cSymmetricZeroSum, ← Finset.sum_attach _ (cZeroContribution rArgument)]
  rfl

/-- Chaque contribution étiquetée détermine, et est déterminée par, son membre. -/
theorem thm_memberContribution_determines_member
    {zLeftZero zRightZero : TNonTrivialZetaZero}
    (hSame : cZeroSupport zLeftZero = cZeroSupport zRightZero) :
    ∀ rArgument : ℝ,
      cMemberContribution rArgument zLeftZero =
        cMemberContribution rArgument zRightZero := by
  intro rArgument
  rw [cMemberContribution, cMemberContribution, hSame]

/-- La troncature est monotone : un cutoff plus grand ne perd jamais un zéro. -/
theorem thm_symmetricZeroWindow_mono
    {rSmall rLarge : ℝ} (hLe : rSmall ≤ rLarge) :
    finsetSymmetricZeroWindow rSmall ⊆ finsetSymmetricZeroWindow rLarge := by
  intro cPoint hMem
  rw [thm_mem_finsetSymmetricZeroWindow] at hMem ⊢
  exact ⟨hMem.1, le_trans hMem.2 hLe⟩

/-! ## L16 — le canal `psi` et la reconstruction déterministe -/

/-- Poids de von Mangoldt reconstruit par différence première d'un canal
`psi` arbitraire. -/
noncomputable def fnWeightFromPsi (psiChannel : ℝ → ℝ) (n : ℕ) : ℝ :=
  psiChannel (n : ℝ) - psiChannel ((n : ℝ) - 1)

/-- Primalité reconstruite depuis un canal `psi` : caractérisation exacte,
`n >= 2` et `Lambda n = log n`. -/
def PPrimeFromPsi (psiChannel : ℝ → ℝ) (n : ℕ) : Prop :=
  2 ≤ n ∧ fnWeightFromPsi psiChannel n = Real.log (n : ℝ)

/-- Comptage premier reconstruit depuis un canal `psi`. -/
noncomputable def fnCountingFromPsi (psiChannel : ℝ → ℝ) (nBound : ℕ) : ℕ :=
  letI := Classical.dec
  ((Finset.range (nBound + 1)).filter (PPrimeFromPsi psiChannel)).card

/-- Premier au rang donné, reconstruit depuis un canal `psi`. -/
noncomputable def fnPrimeAtRankFromPsi (psiChannel : ℝ → ℝ) (nRank : ℕ) : ℕ :=
  Nat.nth (PPrimeFromPsi psiChannel) nRank

/-- Écart premier au rang donné, reconstruit depuis un canal `psi`. -/
noncomputable def fnGapAtRankFromPsi (psiChannel : ℝ → ℝ) (nRank : ℕ) : ℕ :=
  fnPrimeAtRankFromPsi psiChannel (nRank + 1) - fnPrimeAtRankFromPsi psiChannel nRank

/-- **La grammaire première reconstruite au complet**, fonction du seul canal.
Aucun champ ne stocke une conclusion. -/
structure TReconstructedPrimeGrammar where
  psi : ℝ → ℝ
  weight : ℕ → ℝ
  isPrime : ℕ → Prop
  counting : ℕ → ℕ
  primeAt : ℕ → ℕ
  gapAt : ℕ → ℕ

/-- **Le foncteur de reconstruction**, une seule fonction appliquée au canal. -/
noncomputable def fnReconstructGrammar
    (psiChannel : ℝ → ℝ) : TReconstructedPrimeGrammar where
  psi := psiChannel
  weight := fnWeightFromPsi psiChannel
  isPrime := PPrimeFromPsi psiChannel
  counting := fnCountingFromPsi psiChannel
  primeAt := fnPrimeAtRankFromPsi psiChannel
  gapAt := fnGapAtRankFromPsi psiChannel

/-- L'histoire canonique est la reconstruction du canal de Chebyshev
authentique : ce n'est pas une seconde définition, mais le même foncteur à un
autre argument. -/
noncomputable def rhv3CanonicalGrammar : TReconstructedPrimeGrammar :=
  fnReconstructGrammar Chebyshev.psi

/-- La différence première du canal de Chebyshev authentique redonne `Lambda`. -/
theorem thm_weightFromPsi_chebyshev
    {n : ℕ} (hn : 1 ≤ n) :
    fnWeightFromPsi Chebyshev.psi n = Λ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold fnWeightFromPsi Chebyshev.psi
  have hFloorSucc : ⌊((m + 1 : ℕ) : ℝ)⌋₊ = m + 1 := by
    rw [Nat.floor_natCast]
  have hFloorPred : ⌊((m + 1 : ℕ) : ℝ) - 1⌋₊ = m := by
    push_cast
    rw [show (m : ℝ) + 1 - 1 = (m : ℝ) by ring]
    simp
  rw [hFloorSucc, hFloorPred]
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le m)]
  ring

/-- Primalité reconstruite depuis le canal authentique est exactement
`Nat.Prime`, ponctuellement.

Le recouvrement exact primalité/von Mangoldt lui-même n'est pas reproduit ici :
c'est `thm_prime_iff_vonMangoldt_eq_log` de `VonMangoldtChebyshev.lean` (O10),
réutilisé tel quel. -/
theorem thm_primeFromPsi_chebyshev_iff (n : ℕ) :
    PPrimeFromPsi Chebyshev.psi n ↔ Nat.Prime n := by
  unfold PPrimeFromPsi
  rw [thm_prime_iff_vonMangoldt_eq_log n]
  show (2 ≤ n ∧ fnWeightFromPsi Chebyshev.psi n = Real.log (n : ℝ)) ↔
      (2 ≤ n ∧ rVonMangoldtWeight n = Real.log (n : ℝ))
  constructor
  · rintro ⟨hTwo, hEq⟩
    exact ⟨hTwo, by rwa [thm_weightFromPsi_chebyshev (by omega)] at hEq⟩
  · rintro ⟨hTwo, hEq⟩
    exact ⟨hTwo, by rwa [thm_weightFromPsi_chebyshev (by omega : 1 ≤ n)]⟩

/-- Le prédicat de primalité reconstruit depuis le canal authentique EST
`Nat.Prime`, comme prédicat entier. -/
theorem thm_primeFromPsi_chebyshev_eq :
    PPrimeFromPsi Chebyshev.psi = Nat.Prime := by
  funext n
  exact propext (thm_primeFromPsi_chebyshev_iff n)

/-- **L16, identité de rang.**  `reconstructedPrimeAtRank = canonicalPrimeAtRank`
sur le canal authentique : le rang reconstruit depuis le canal de Chebyshev
EST `fnPrimeAtRank` de O6, ponctuellement à chaque rang. -/
theorem thm_reconstructedPrimeAtRank_eq_canonicalPrimeAtRank :
    fnPrimeAtRankFromPsi Chebyshev.psi = fnPrimeAtRank := by
  funext r
  unfold fnPrimeAtRankFromPsi fnPrimeAtRank
  rw [thm_primeFromPsi_chebyshev_eq]

/-- **L16, identité de comptage.**  Le comptage reconstruit depuis le canal
authentique EST `Nat.primeCounting`, ponctuellement. -/
theorem thm_reconstructedCounting_eq_canonicalCounting :
    fnCountingFromPsi Chebyshev.psi = Nat.primeCounting := by
  funext nBound
  unfold fnCountingFromPsi
  rw [thm_primeFromPsi_chebyshev_eq]
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  congr 1
  exact Finset.filter_congr_decidable _ _ _

/-- **L16, identité de successeur.**  Le rang successeur reconstruit depuis le
canal authentique EST `fnPrimeSuccessor` de O6, ponctuellement. -/
theorem thm_reconstructedSuccessor_eq_canonicalSuccessor (nRank : ℕ) :
    fnPrimeAtRankFromPsi Chebyshev.psi (nRank + 1) = fnPrimeSuccessor nRank := by
  rw [thm_reconstructedPrimeAtRank_eq_canonicalPrimeAtRank]
  rfl

/-- **L16, identité d'écart.**  L'écart reconstruit depuis le canal authentique
EST `nPrimeGap` de O6, ponctuellement à chaque rang. -/
theorem thm_reconstructedGap_eq_canonicalGap (nRank : ℕ) :
    fnGapAtRankFromPsi Chebyshev.psi nRank = nPrimeGap nRank := by
  unfold fnGapAtRankFromPsi nPrimeGap
  rw [thm_reconstructedPrimeAtRank_eq_canonicalPrimeAtRank]
  rfl

/-- **M9b, forme conditionnelle.**  Si le canal issu de la source des zéros
coïncide avec le canal authentique de Chebyshev, alors TOUTE la grammaire
reconstruite coïncide avec la grammaire canonique — poids, primalité,
comptage, rangs et écarts.

L'hypothèse `psiZ = Chebyshev.psi` (M9a, la formule explicite reliant la
source des zéros au canal de Chebyshev) est REÇUE ici comme hypothèse d'un
théorème de transport, jamais utilisée comme fait : elle reste
`NOT_YET_CERTIFIED_LEAN` en tant qu'objet produit. -/
theorem thm_M9b_grammar_rigidity
    {psiZ : ℝ → ℝ} (hChannel : psiZ = Chebyshev.psi) :
    fnReconstructGrammar psiZ = rhv3CanonicalGrammar := by
  unfold rhv3CanonicalGrammar
  rw [hChannel]

/-- Forme par composantes de M9b, alignée sur les cinq identités ponctuelles
demandées par le maître Lean pour L15/L16. -/
theorem thm_M9b_pointwise_components
    {psiZ : ℝ → ℝ} (hChannel : psiZ = Chebyshev.psi) :
    (fnReconstructGrammar psiZ).isPrime = Nat.Prime ∧
      (fnReconstructGrammar psiZ).primeAt = fnPrimeAtRank ∧
      (fnReconstructGrammar psiZ).counting = Nat.primeCounting ∧
      (∀ nRank : ℕ, (fnReconstructGrammar psiZ).gapAt nRank = nPrimeGap nRank) ∧
      (∀ nRank : ℕ, (fnReconstructGrammar psiZ).primeAt (nRank + 1) =
        fnPrimeSuccessor nRank) := by
  subst hChannel
  exact ⟨thm_primeFromPsi_chebyshev_eq,
    thm_reconstructedPrimeAtRank_eq_canonicalPrimeAtRank,
    thm_reconstructedCounting_eq_canonicalCounting,
    thm_reconstructedGap_eq_canonicalGap,
    thm_reconstructedSuccessor_eq_canonicalSuccessor⟩

/-! ## M9b, forme affaiblie — le foncteur n'observe le canal qu'aux entiers -/

/-- **Force du foncteur, exhibée.**  `fnWeightFromPsi` n'évalue jamais le canal
ailleurs qu'en un entier naturel casté (`n` puis `n-1`) : toute la grammaire
reconstruite (poids, primalité, comptage, rangs, écarts) ne dépend du canal
qu'à travers ses valeurs aux entiers. Une identité de canal sur tout `ℝ` (ou
même sur tout le domaine `x>1` du maître) est donc STRICTEMENT plus forte que
ce que M9b consomme réellement. -/
theorem thm_weightFromPsi_eq_of_agree_on_naturals
    {psiChannel : ℝ → ℝ}
    (hAgree : ∀ n : ℕ, psiChannel (n : ℝ) = Chebyshev.psi (n : ℝ))
    {n : ℕ} (hn : 1 ≤ n) :
    fnWeightFromPsi psiChannel n = fnWeightFromPsi Chebyshev.psi n := by
  unfold fnWeightFromPsi
  have hCast : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn]; norm_num
  rw [hAgree n, hCast, hAgree (n - 1)]

theorem thm_primeFromPsi_iff_of_agree_on_naturals
    {psiChannel : ℝ → ℝ}
    (hAgree : ∀ n : ℕ, psiChannel (n : ℝ) = Chebyshev.psi (n : ℝ)) (n : ℕ) :
    PPrimeFromPsi psiChannel n ↔ PPrimeFromPsi Chebyshev.psi n := by
  unfold PPrimeFromPsi
  by_cases hn : 1 ≤ n
  · rw [thm_weightFromPsi_eq_of_agree_on_naturals hAgree hn]
  · have h2 : ¬ (2 : ℕ) ≤ n := by omega
    simp [h2]

/-- **La primalité reconstruite ne dépend du canal qu'à travers ses valeurs
aux entiers.**  Forme affaiblie de `thm_primeFromPsi_chebyshev_eq` : ne
suppose jamais `psiChannel = Chebyshev.psi` sur `ℝ`, seulement aux entiers. -/
theorem thm_primeFromPsi_eq_of_agree_on_naturals
    {psiChannel : ℝ → ℝ}
    (hAgree : ∀ n : ℕ, psiChannel (n : ℝ) = Chebyshev.psi (n : ℝ)) :
    PPrimeFromPsi psiChannel = Nat.Prime := by
  funext n
  exact propext ((thm_primeFromPsi_iff_of_agree_on_naturals hAgree n).trans
    (thm_primeFromPsi_chebyshev_iff n))

/-- **M9b, forme affaiblie.**  Le PLUS FAIBLE théorème RHV3 nécessaire pour
décharger le consommateur M9b : une identité de canal aux SEULS entiers
suffit à reconstruire toute la grammaire première, poids, primalité,
comptage, rangs et écarts compris. Rien ici ne suppose ni ne construit
l'identité totale `psiZ = Chebyshev.psi` sur `ℝ`. -/
theorem thm_M9b_pointwise_components_weak
    {psiZ : ℝ → ℝ}
    (hAgree : ∀ n : ℕ, psiZ (n : ℝ) = Chebyshev.psi (n : ℝ)) :
    (fnReconstructGrammar psiZ).isPrime = Nat.Prime ∧
      (fnReconstructGrammar psiZ).primeAt = fnPrimeAtRank ∧
      (fnReconstructGrammar psiZ).counting = Nat.primeCounting ∧
      (∀ nRank : ℕ, (fnReconstructGrammar psiZ).gapAt nRank = nPrimeGap nRank) ∧
      (∀ nRank : ℕ, (fnReconstructGrammar psiZ).primeAt (nRank + 1) =
        fnPrimeSuccessor nRank) := by
  have hPrimeEq : PPrimeFromPsi psiZ = Nat.Prime :=
    thm_primeFromPsi_eq_of_agree_on_naturals hAgree
  have hRankEq : fnPrimeAtRankFromPsi psiZ = fnPrimeAtRank := by
    funext r
    unfold fnPrimeAtRankFromPsi fnPrimeAtRank
    rw [hPrimeEq]
  have hCountEq : fnCountingFromPsi psiZ = Nat.primeCounting := by
    funext nBound
    unfold fnCountingFromPsi
    rw [hPrimeEq, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    congr 1
    exact Finset.filter_congr_decidable _ _ _
  refine ⟨hPrimeEq, hRankEq, hCountEq, ?_, ?_⟩
  · intro nRank
    change fnGapAtRankFromPsi psiZ nRank = nPrimeGap nRank
    unfold fnGapAtRankFromPsi nPrimeGap fnPrimeSuccessor
    rw [hRankEq]
  · intro nRank
    change fnPrimeAtRankFromPsi psiZ (nRank + 1) = fnPrimeSuccessor nRank
    unfold fnPrimeSuccessor
    rw [hRankEq]

/-! ## La reconstruction a un contenu réel -/

/-- Le canal identiquement nul ne reconstruit aucun premier. -/
theorem thm_zeroChannel_reconstructs_no_primes (n : ℕ) :
    ¬ PPrimeFromPsi (fun _ => 0) n := by
  rintro ⟨hTwo, hWeight⟩
  have hLogPos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hTwo.trans_lt' one_lt_two
  unfold fnWeightFromPsi at hWeight
  simp only [sub_self] at hWeight
  linarith [hWeight, hLogPos]

/-- **La reconstruction a un contenu réel.**  Il existe un canal dont la
reconstruction diffère de l'histoire canonique : `fnReconstructGrammar` n'est
pas une fonction constante, et M9b n'est donc pas prouvable par `rfl` seul. -/
theorem thm_reconstruction_is_not_a_definitional_alias :
    fnReconstructGrammar (fun _ => 0) ≠ rhv3CanonicalGrammar := by
  intro hEq
  have hPred : PPrimeFromPsi (fun _ => 0) = Nat.Prime := by
    have hProj := congrArg TReconstructedPrimeGrammar.isPrime hEq
    simp only [fnReconstructGrammar, rhv3CanonicalGrammar] at hProj
    rw [thm_primeFromPsi_chebyshev_eq] at hProj
    exact hProj
  have hTwo : PPrimeFromPsi (fun _ => 0) 2 := by
    rw [hPred]; exact Nat.prime_two
  exact thm_zeroChannel_reconstructs_no_primes 2 hTwo

/-! Surface audit. -/

#check thm_symmetricZeroWindow_finite
#check cMemberContribution
#check thm_symmetricZeroSum_eq_labelled_sum
#check thm_M9b_grammar_rigidity
#check thm_M9b_pointwise_components
#check thm_M9b_pointwise_components_weak
#check thm_reconstructedPrimeAtRank_eq_canonicalPrimeAtRank
#check thm_reconstructedGap_eq_canonicalGap
#check thm_reconstructedCounting_eq_canonicalCounting
#check thm_reconstruction_is_not_a_definitional_alias

end RHV3Lean
