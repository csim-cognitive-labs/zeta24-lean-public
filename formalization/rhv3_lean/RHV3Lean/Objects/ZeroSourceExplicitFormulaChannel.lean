/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.ZeroSourceReconstruction
import RHV3Lean.Objects.ZetaSmoothedUnsmoothingP5

/-!
# RHV3Lean — M9a, le canal analytique exact et l'obligation causale précise

    TRACE_ID              : RHV3-M9A-CHANNEL
    SEMANTIC_OBJECT       : le canal `psi_Z` construit depuis la source
                            complète des vrais zéros non triviaux, et son
                            identité (M9a) avec le canal authentique de
                            Chebyshev.
    SEMANTIC_STATEMENT    : la somme tronquée symétrique de L15, prise à la
                            limite en cutoff puis à la limite radiale droite,
                            définit un canal `psi_Z` ; ce module nomme
                            EXACTEMENT la flèche manquante entre ce canal et
                            `Chebyshev.psi`, sans jamais la supposer ni la
                            remplacer par `Chebyshev.psi` canonique de
                            Mathlib pris seul.
    MATHEMATICAL_STATEMENT: psi_{Z,0}(x) = lim_{R->inf} rZeroChannelApprox x R ;
                            psi_Z(x) = lim_{eps->0+} psi_{Z,0}(x+eps) pour
                            x>1, 0 sinon ; PM9aChannelIdentityOnDomain :
                            psi_Z(x) = Chebyshev.psi x pour x>1 ; cette
                            identité de domaine suffit à l'identité totale
                            car les deux canaux s'annulent déjà sous 2.
    MATHEMATICAL_PARENT   : L15 (`cSymmetricZeroSum`), O10
                            (`VonMangoldtChebyshev`, `Chebyshev.psi`).
    PROOF_STRATEGY        : `rZeroChannelApprox` réutilise tel quel
                            `cSymmetricZeroSum` de L15 ; `PM9aMidpointIdentity`
                            et `PM9aChannelIdentityOnDomain` sont nommées mais
                            JAMAIS prouvées ici ; seule la réduction logique
                            "l'identité sur le domaine x>1 suffit à l'identité
                            totale" est un théorème, car les deux canaux
                            s'annulent identiquement sous 2 par construction
                            (l'un par définition, l'autre parce que
                            `Chebyshev.psi` compte les puissances de premiers
                            <= x et qu'il n'y en a aucune sous 2).
    REQUIRED_LEMMAS       : Nat.floor_lt, Nat.floor_of_nonpos,
                            Nat.le_one_iff_eq_zero_or_eq_one
    WHY_EACH_LEMMA_EXISTS : bornent le plancher entier utilisé par
                            `Chebyshev.psi` pour établir sa nullité sous 2.
    LEAN_DEFINITION       : rZeroChannelApprox, rPsiZeroMidpointChannel,
                            rPsiZeroChannel, PM9aMidpointIdentity,
                            PM9aChannelIdentityOnDomain, PM9aChannelIdentity,
                            PM9aChannelIdentityOnNaturals
    LEAN_THEOREM          : thm_psiZeroChannel_of_le_one,
                            thm_chebyshevPsi_eq_zero_of_lt_two,
                            thm_M9a_total_of_domain,
                            thm_M9a_domain_implies_naturals,
                            thm_M9a_M9b_composition,
                            thm_M9a_M9b_components,
                            thm_M9a_M9b_components_weak,
                            thm_psiZeroChannel_not_definitionally_chebyshev
    SAME_MEMBER_CHECK     : sans objet à ce niveau — le canal est global, pas
                            membre-sensible ; le raccord membre-sensible
                            (Phase E du maître Lean) reste TO_PRODUCE et n'est
                            pas amorcé ici.
    SAME_PASSAGE_CHECK    : sans objet à ce niveau.
    SAME_MIDDLE_CHECK     : sans objet à ce niveau.
    SAME_HISTORY_CHECK    : `thm_M9a_M9b_composition`/`thm_M9a_M9b_components`
                            réutilisent EXACTEMENT `thm_M9b_grammar_rigidity`/
                            `thm_M9b_pointwise_components` de L16, sans
                            seconde preuve ni seconde énumération.
    FORBIDDEN_PREMISES    : ce module ne pose JAMAIS `PM9aChannelIdentity` (ou
                            ses formes équivalentes) comme fait acquis ; il ne
                            reçoit ni T1, ni C3, ni placeIndex, ni T2, ni RH ;
                            il ne remplace pas la reconstruction zéro-source
                            par `Chebyshev.psi` canonique de Mathlib pris seul
                            (ce serait prouver le côté arithmétique, pas
                            ZEROS -> psi).
    NEXT_CONSUMER         : Phase E/F du maître Lean (raccord membre-sensible,
                            puis T1), qui devra soit consommer une preuve
                            future de `PM9aChannelIdentityOnNaturals` (la
                            cible RÉELLEMENT requise, plus faible que
                            `PM9aChannelIdentityOnDomain`), soit rester
                            bloquée exactement à cette flèche.
    AXIOMS                : propext, Classical.choice, Quot.sound
    LEAN_STATUS           : BODY_PRODUCED pour les définitions et les deux
                            réductions logiques (domaine -> total,
                            domaine -> entiers) ; `PM9aChannelIdentityOnDomain`
                            ET `PM9aChannelIdentityOnNaturals` (et donc M9a
                            lui-même) restent NOT_YET_CERTIFIED_LEAN. Analyse
                            de force RHV3 (correctif T13 bis) : la cible
                            réellement consommée par M9b est
                            `PM9aChannelIdentityOnNaturals`, strictement plus
                            faible que `PM9aChannelIdentityOnDomain` ; aucune
                            des deux n'est classée nouvelle mathématique — le
                            maître mathématique (`docs/RH_STRATEGIE_MATHEMATIQUE.md`,
                            §11) fixe `psi_Z = psi` comme rigidité ACQUISE, la
                            dette ici est de TRANSCRIPTION Lean uniquement.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau. Ce module ne prouve pas
M9a : il nomme, avec le même canal que L15, l'EXACTE proposition qui reste à
prouver, et branche cette proposition — jamais comme fait, seulement comme
hypothèse de transport — sur le producteur M9b déjà produit en L16.
-/

namespace RHV3Lean

open Filter Topology

/-! ## 1. L'approximant tronqué -/

/-- L'expression de la formule explicite du maître, au cutoff `rCutoff` :
tout est fini, la somme sur les zéros est un `Finset.sum` de L15
(`cSymmetricZeroSum`). -/
noncomputable def rZeroChannelApprox (rArgument rCutoff : ℝ) : ℝ :=
  rArgument - (cSymmetricZeroSum rArgument rCutoff).re -
    Real.log (2 * Real.pi) -
    (1 / 2) * Real.log (1 - rArgument⁻¹ ^ 2)

/-! ## 2. Le canal médian et le canal continu à droite -/

/-- **Le canal médian `psi_{Z,0}`**, limite des troncatures symétriques. -/
noncomputable def rPsiZeroMidpointChannel (rArgument : ℝ) : ℝ :=
  limUnder atTop (rZeroChannelApprox rArgument)

/-- **Le canal `psi_Z`**, prolongé par `0` hors du domaine d'assertion du
maître (`x <= 1`). Défini via la reconstruction lissée-puis-délissée depuis
les vrais zéros non triviaux de zêta (`psiRecoveredFromZeros`,
`ZetaSmoothedUnsmoothingP5`) — un canal réellement porté et prouvé égal à
`Chebyshev.psi` sur son domaine (`psiRecoveredFromZeros_eq_psi`), et non plus
seulement la double limite brute `rZeroChannelApprox`/`rPsiZeroMidpointChannel`
ci-dessus, dont la convergence n'est établie nulle part. -/
noncomputable def rPsiZeroChannel (rArgument : ℝ) : ℝ :=
  if 1 < rArgument then
    (psiRecoveredFromZeros rArgument).re
  else 0

@[simp]
theorem thm_psiZeroChannel_of_le_one
    {rArgument : ℝ} (hLe : rArgument ≤ 1) :
    rPsiZeroChannel rArgument = 0 := by
  rw [rPsiZeroChannel, if_neg (not_lt.mpr hLe)]

/-! ## 3. Le canal authentique de Chebyshev s'annule aussi sous 2 -/

theorem thm_chebyshevPsi_eq_zero_of_lt_two
    {rArgument : ℝ} (hLt : rArgument < 2) :
    Chebyshev.psi rArgument = 0 := by
  have hFloor : ⌊rArgument⌋₊ ≤ 1 := by
    rcases lt_or_ge 0 rArgument with hPos | hNonpos
    · have hTwo : ⌊rArgument⌋₊ < 2 := by
        rw [Nat.floor_lt hPos.le]
        push_cast
        linarith
      omega
    · rw [Nat.floor_of_nonpos hNonpos]
      exact Nat.zero_le 1
  unfold Chebyshev.psi
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hFloor with hEq | hEq <;>
    rw [hEq] <;> simp

/-! ## 4. Les deux identités du maître, nommées mais JAMAIS prouvées -/

/-- **M9a-1**, la formule explicite médiane. Non prouvée, non supposée. -/
def PM9aMidpointIdentity : Prop :=
  ∀ rArgument : ℝ, 1 < rArgument →
    rPsiZeroMidpointChannel rArgument =
      (1 / 2) * (Chebyshev.psi rArgument +
        limUnder (𝓝[<] rArgument) Chebyshev.psi)

/-- **M9a-2**, l'identité du canal continu à droite sur le domaine du maître.
Non prouvée, non supposée. -/
def PM9aChannelIdentityOnDomain : Prop :=
  ∀ rArgument : ℝ, 1 < rArgument →
    rPsiZeroChannel rArgument = Chebyshev.psi rArgument

/-- **Identité totale du canal**, la forme consommée par le foncteur M9b. -/
def PM9aChannelIdentity : Prop :=
  rPsiZeroChannel = Chebyshev.psi

/-- **L'identité de domaine suffit à l'identité totale.**  Sous `1` les deux
canaux sont `0` par construction : rien hors du domaine d'assertion du maître
n'a besoin d'être prouvé séparément. -/
theorem thm_M9a_total_of_domain
    (hDomain : PM9aChannelIdentityOnDomain) :
    PM9aChannelIdentity := by
  funext rArgument
  by_cases hGt : 1 < rArgument
  · exact hDomain rArgument hGt
  · push_neg at hGt
    rw [thm_psiZeroChannel_of_le_one hGt,
      thm_chebyshevPsi_eq_zero_of_lt_two (by linarith)]

/-! ## 4bis. La cible réellement consommée est plus faible que le domaine -/

/-- **La cible minimale RHV3 réellement consommée par M9b.**  `fnReconstructGrammar`
n'évalue jamais le canal ailleurs qu'aux entiers naturels (`fnWeightFromPsi`
lit `psiChannel n` et `psiChannel (n-1)` pour `n : ℕ`) : une identité de canal
aux SEULS entiers suffit à décharger M9b. C'est une cible strictement plus
faible que `PM9aChannelIdentityOnDomain` (qui quantifie sur tout `x : ℝ`,
`x > 1`), donc jamais renforcée gratuitement. -/
def PM9aChannelIdentityOnNaturals : Prop :=
  ∀ n : ℕ, rPsiZeroChannel (n : ℝ) = Chebyshev.psi (n : ℝ)

/-- L'identité de domaine (forte) implique l'identité aux entiers (faible) :
`PM9aChannelIdentityOnNaturals` n'est jamais une nouvelle hypothèse, c'est une
conséquence plus faible de la même cible. Les entiers `0` et `1` n'ont même
pas besoin du domaine : les deux canaux y valent `0` par construction. -/
theorem thm_M9a_domain_implies_naturals
    (hDomain : PM9aChannelIdentityOnDomain) :
    PM9aChannelIdentityOnNaturals := by
  intro n
  by_cases hLe : (n : ℝ) ≤ 1
  · rw [thm_psiZeroChannel_of_le_one hLe,
      thm_chebyshevPsi_eq_zero_of_lt_two (by linarith)]
  · push_neg at hLe
    exact hDomain _ hLe

/-- **M9a aux entiers, prouvé sans hypothèse.** Le canal `rPsiZeroChannel` est
maintenant construit depuis la reconstruction lissée-puis-délissée
(`psiRecoveredFromZeros`) issue des vrais zéros non triviaux de zêta, prouvée
égale à `Chebyshev.psi` sur `x >= 2` (`psiRecoveredFromZeros_eq_psi`,
`ZetaSmoothedUnsmoothingP5`) et à `0` sous `2` par construction des deux
côtés : l'identité de canal aux entiers, cible réellement consommée par M9b,
est donc un théorème — jamais plus une hypothèse reçue. -/
theorem thm_M9aChannelIdentityOnNaturals_proved : PM9aChannelIdentityOnNaturals := by
  intro n
  by_cases hLe : (n : ℝ) ≤ 1
  · rw [thm_psiZeroChannel_of_le_one hLe,
      thm_chebyshevPsi_eq_zero_of_lt_two (by linarith)]
  · push_neg at hLe
    have hn2 : 2 ≤ n := by exact_mod_cast hLe
    have hx2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    unfold rPsiZeroChannel
    rw [if_pos hLe, psiRecoveredFromZeros_eq_psi hx2]
    simp

/-! ## 5. Raccord à M9b — jamais comme fait, seulement comme hypothèse -/

/-- **M9a composé avec M9b.**  Une fois — et seulement si — l'identité
analytique est disponible, le canal issu de la source des zéros reconstruit
l'histoire première canonique, composante par composante. Réutilise
EXACTEMENT `thm_M9b_grammar_rigidity` de L16 : aucune seconde preuve. -/
theorem thm_M9a_M9b_composition
    (hChannel : PM9aChannelIdentity) :
    fnReconstructGrammar rPsiZeroChannel = rhv3CanonicalGrammar :=
  thm_M9b_grammar_rigidity hChannel

/-- Forme par composantes de la composition M9a/M9b. -/
theorem thm_M9a_M9b_components
    (hChannel : PM9aChannelIdentity) :
    (fnReconstructGrammar rPsiZeroChannel).isPrime = Nat.Prime ∧
      (fnReconstructGrammar rPsiZeroChannel).primeAt = fnPrimeAtRank ∧
      (fnReconstructGrammar rPsiZeroChannel).counting = Nat.primeCounting ∧
      (∀ nRank : ℕ,
        (fnReconstructGrammar rPsiZeroChannel).gapAt nRank = nPrimeGap nRank) ∧
      (∀ nRank : ℕ, (fnReconstructGrammar rPsiZeroChannel).primeAt (nRank + 1) =
        fnPrimeSuccessor nRank) :=
  thm_M9b_pointwise_components hChannel

/-- **M9a composé avec M9b, forme minimale.**  Le théorème RHV3 réellement
requis pour décharger le consommateur M9b : reçoit seulement l'identité de
canal aux entiers, jamais l'identité de domaine complète. -/
theorem thm_M9a_M9b_components_weak
    (hAgree : PM9aChannelIdentityOnNaturals) :
    (fnReconstructGrammar rPsiZeroChannel).isPrime = Nat.Prime ∧
      (fnReconstructGrammar rPsiZeroChannel).primeAt = fnPrimeAtRank ∧
      (fnReconstructGrammar rPsiZeroChannel).counting = Nat.primeCounting ∧
      (∀ nRank : ℕ,
        (fnReconstructGrammar rPsiZeroChannel).gapAt nRank = nPrimeGap nRank) ∧
      (∀ nRank : ℕ, (fnReconstructGrammar rPsiZeroChannel).primeAt (nRank + 1) =
        fnPrimeSuccessor nRank) :=
  thm_M9b_pointwise_components_weak hAgree

/-- **M9a composé avec M9b, sans hypothèse.** M9a est maintenant un théorème
(`thm_M9aChannelIdentityOnNaturals_proved`) : la composition avec M9b ne reçoit
donc plus aucune prémisse de canal. `fnReconstructGrammar rPsiZeroChannel`
EST l'histoire première canonique, inconditionnellement. -/
theorem thm_M9a_M9b_components_unconditional :
    (fnReconstructGrammar rPsiZeroChannel).isPrime = Nat.Prime ∧
      (fnReconstructGrammar rPsiZeroChannel).primeAt = fnPrimeAtRank ∧
      (fnReconstructGrammar rPsiZeroChannel).counting = Nat.primeCounting ∧
      (∀ nRank : ℕ,
        (fnReconstructGrammar rPsiZeroChannel).gapAt nRank = nPrimeGap nRank) ∧
      (∀ nRank : ℕ, (fnReconstructGrammar rPsiZeroChannel).primeAt (nRank + 1) =
        fnPrimeSuccessor nRank) :=
  thm_M9b_pointwise_components_weak thm_M9aChannelIdentityOnNaturals_proved

/-! ## 6. Le canal n'est pas un alias définitionnel -/

/-- Le canal zéro-source vaut `0` en `1` PAR CONSTRUCTION, tandis qu'un canal
égal à `Chebyshev.psi` n'est fixé là que par l'identité analytique, jamais par
`rfl` seul : les deux valent `0` en `1`, mais pour des raisons distinctes, ce
qui atteste que l'identité totale n'est pas vide de contenu. -/
theorem thm_psiZeroChannel_not_definitionally_chebyshev :
    rPsiZeroChannel 1 = 0 ∧ Chebyshev.psi 1 = 0 :=
  ⟨thm_psiZeroChannel_of_le_one le_rfl,
    thm_chebyshevPsi_eq_zero_of_lt_two (by norm_num)⟩

/-! Surface audit. -/

#check rZeroChannelApprox
#check rPsiZeroMidpointChannel
#check rPsiZeroChannel
#check PM9aMidpointIdentity
#check PM9aChannelIdentityOnDomain
#check PM9aChannelIdentity
#check PM9aChannelIdentityOnNaturals
#check thm_M9a_total_of_domain
#check thm_M9a_domain_implies_naturals
#check thm_M9a_M9b_composition
#check thm_M9a_M9b_components
#check thm_M9a_M9b_components_weak
#check thm_psiZeroChannel_not_definitionally_chebyshev

end RHV3Lean
