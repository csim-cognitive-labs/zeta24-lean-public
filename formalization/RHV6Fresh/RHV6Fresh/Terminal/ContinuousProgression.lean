/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TranslationVsProgression
import Mathlib.NumberTheory.Bertrand

/-!
# RHV6Fresh — la progression continue `ΔΘ_n = T·log(p_{n+1}/p_n)` (2026-09-28)

Plan TDD (auteur, 2026-09-28) : `experiments/PLAN_TDD_PROGRESSION_CONTINUE_20260928.md`, suite de
`Terminal/TranslationVsProgression.lean` (commit `237c075c`).

Audit de l'auteur qui gouverne ce fichier : ce que `237c075c` réfute est « EV+1 ⟹ franchissement
d'au moins un anneau », PAS « EV+1 possède une progression arithmético-analytique strictement
positive ».  On abandonne `k`, les frontières d'anneau et `progression = différence de
coordonnées` ; on suit la progression CONTINUE `ΔΘ_n = T·log(p_{n+1}/p_n)`, l'accroissement de phase
exact du terme explicite entre deux premiers consécutifs (`phase_increment_eq_pi_span`).

Résultat numérique préalable (E112, `e112_phase_quantum_per_event_published.py`, commité) :
`ΔΘ_j` est strictement positif sur les 300 zéros ON réels (300/300), mais son minimum décroît sans
plancher observé (1,238 → 0,551 rad par blocs de 50 sur 300 zéros ; 0,454 → 0,224 rad par blocs de
500 sur 5000 zéros) : **il n'existe pas de quantum de phase structurel** — la chaîne « raréfaction
logarithmique + quantum ⟹ T croît » n'a pas son second maillon.  Ce fichier compile ce qui est VRAI
dans la chaîne continue (positivité, β-aveuglement, borne de Bertrand, forme EXACTE de « un quantum
force T » sous hypothèse locale explicite, satisfiabilité du quantum par la paire à même hauteur, et
la signature continue du passage OFF consécutif) — sans jamais poser le quantum comme prémisse
globale.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune hypothèse non déchargée. Aucun `Prop` de
prémisse n'est défini ici.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## C1 — la progression continue d'un événement est strictement positive, pour tout membre,
tout rang -/

/-- **La progression continue `ΔΘ_n` d'un événement est TOUJOURS strictement positive**, pour tout
membre `z` et tout rang `n` : conséquence directe de `phase_increment_eq_pi_span` (la progression
continue EST `π · TowerPrimeGapSpan`) et de la positivité de la hauteur et du ratio logarithmique de
place. Vrai sur la ligne comme hors ligne, sans aucune hypothèse sur `β`. -/
theorem phase_increment_pos (z : TrueZero) (n : ℕ) :
    0 < Real.pi * towerPosition z (fnPrimeSuccessor n : ℝ) -
        Real.pi * towerPosition z (fnPrimeAtRank n : ℝ) := by
  rw [phase_increment_eq_pi_span]
  unfold TowerPrimeGapSpan rTowerHeight
  exact mul_pos Real.pi_pos
    (mul_pos (div_pos (thm_upperZeroHeight_positive z) Real.pi_pos) (thm_primeGapLogRatio_pos n))

/-! ## C2 — la progression continue est aveugle à `β` -/

/-- **Même hauteur ⟹ même `ΔΘ_n`** : la progression continue ne dépend que de la hauteur `T` et du
rang `n`, jamais de `β`. Plus général que le miroir (`mirror_phase_increment_eq` ne compare `z` qu'à
son propre miroir) : ceci vaut pour deux membres QUELCONQUES de même hauteur. -/
theorem phase_increment_eq_of_sameHeight (z w : TrueZero) (h : rZeroHeight z.1 = rZeroHeight w.1)
    (n : ℕ) :
    Real.pi * towerPosition z (fnPrimeSuccessor n : ℝ) -
        Real.pi * towerPosition z (fnPrimeAtRank n : ℝ) =
      Real.pi * towerPosition w (fnPrimeSuccessor n : ℝ) -
        Real.pi * towerPosition w (fnPrimeAtRank n : ℝ) := by
  rw [phase_increment_eq_pi_span, phase_increment_eq_pi_span]
  unfold TowerPrimeGapSpan rTowerHeight
  rw [h]

/-! ## C3 — Bertrand : `p_{n+1} ≤ 2·p_n`, donc `ΔΘ_n ≤ T·log 2` -/

/-- **Bertrand sur l'histoire première fixe** : le premier successeur du rang `n` est au plus le
double du premier de ce rang. Preuve : Bertrand donne un premier `q` strictement entre `p_n` et
`2·p_n` ; s'il existait un premier successeur au-delà de `2·p_n`, `q` serait un premier strictement
entre `p_n` et `p_{n+1}` — absurde (`Nat.le_nth_of_lt_nth_succ`, corridor vide de l'histoire
première). -/
theorem primeSuccessor_le_two_mul (n : ℕ) : fnPrimeSuccessor n ≤ 2 * fnPrimeAtRank n := by
  obtain ⟨q, hq, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (fnPrimeAtRank n) (thm_primeAtRank_pos n).ne'
  by_contra hcon
  push_neg at hcon
  have hqlt : q < fnPrimeSuccessor n := lt_of_le_of_lt hle hcon
  have hnth : q ≤ fnPrimeAtRank n := Nat.le_nth_of_lt_nth_succ hqlt hq
  omega

/-- **La progression continue est bornée par `T · log 2`** : conséquence directe de la borne de
Bertrand sur l'histoire première fixe, portée dans la formule exacte de la progression continue.
Aucune asymptotique, aucun PNT — une seule inégalité arithmétique (Bertrand) transportée par
l'algèbre du terme explicite. -/
theorem phase_increment_le_height_mul_log_two (z : TrueZero) (n : ℕ) :
    Real.pi * towerPosition z (fnPrimeSuccessor n : ℝ) -
        Real.pi * towerPosition z (fnPrimeAtRank n : ℝ) ≤
      rZeroHeight z.1 * Real.log 2 := by
  have hp1 : (0 : ℝ) < (fnPrimeAtRank n : ℝ) := by exact_mod_cast thm_primeAtRank_pos n
  have hp2 : (0 : ℝ) < (fnPrimeSuccessor n : ℝ) := by
    unfold fnPrimeSuccessor; exact_mod_cast thm_primeAtRank_pos (n + 1)
  have hT : (0 : ℝ) ≤ rZeroHeight z.1 := (thm_upperZeroHeight_positive z).le
  have hle : (fnPrimeSuccessor n : ℝ) ≤ 2 * (fnPrimeAtRank n : ℝ) := by
    exact_mod_cast primeSuccessor_le_two_mul n
  have hlog : Real.log (fnPrimeSuccessor n : ℝ) - Real.log (fnPrimeAtRank n : ℝ) ≤ Real.log 2 := by
    rw [← Real.log_div hp2.ne' hp1.ne']
    exact Real.log_le_log (div_pos hp2 hp1) (by rw [div_le_iff₀ hp1]; linarith)
  rw [pi_mul_towerPosition, pi_mul_towerPosition]
  nlinarith [mul_le_mul_of_nonneg_left hlog hT]

/-! ## C3b — le plancher mobile : `g_n ≥ 1` (déjà compilé), `g_n ≥ 2` après `2` (nouveau), et la
borne événementielle `ΔΘ_n ≥ T · log(1 + g/p_n)` qui en découle (auteur, 2026-09-28, « ce plancher
mobile, imposé par la discrétisation des premiers, est ce qui manquait entre raréfaction, progression
continue et recul OFF ») -/

/-- **`g_n ≥ 1` est DÉJÀ un théorème compilé** (`thm_primeGap_positive`, RHV3Lean, base) : aucune
nouvelle brique n'est nécessaire pour cette forme. Restatement local, pour qu'elle apparaisse
littéralement dans ce fichier. -/
theorem primeGap_ge_one (n : ℕ) : 1 ≤ nPrimeGap n := thm_primeGap_positive n

/-- **`g_n ≥ 2` pour tout rang au-delà du premier `2`** : deux premiers `p_n, p_{n+1} > 2` sont
impairs (`Nat.Prime.eq_two_or_odd'`), leur écart est donc PAIR (`Nat.Odd.sub_odd`) et strictement
positif (`thm_primeGap_positive`) — un entier pair et non nul est `≥ 2`. Nouvelle brique, jamais
compilée avant ce jour, exactement la forme demandée par l'auteur. -/
theorem primeGap_ge_two_of_two_lt {n : ℕ} (h2 : 2 < fnPrimeAtRank n) : 2 ≤ nPrimeGap n := by
  have heq : fnPrimeSuccessor n = fnPrimeAtRank (n + 1) := rfl
  have hSucc : fnPrimeAtRank n < fnPrimeAtRank (n + 1) := by
    rw [← heq]; exact thm_primeAtRank_lt_successor n
  have hOddAt : Odd (fnPrimeAtRank n) :=
    (thm_primeAtRank_isPrime n).eq_two_or_odd'.resolve_left (by omega)
  have hOddSucc : Odd (fnPrimeAtRank (n + 1)) :=
    (thm_primeAtRank_isPrime (n + 1)).eq_two_or_odd'.resolve_left (by omega)
  have hEven : Even (nPrimeGap n) := by
    unfold nPrimeGap
    rw [heq]
    exact Nat.Odd.sub_odd hOddSucc hOddAt
  have hPos := thm_primeGap_positive n
  obtain ⟨j, hj⟩ := hEven
  omega

/-- **Borne événementielle universelle, plancher mobile** : `ΔΘ_n ≥ T · log(1 + 1/p_n) > 0`. C'est
EXACTEMENT la forme que E112 ne réfute pas — E112 réfute un quantum CONSTANT `c > 0` indépendant de
`n` ; ce plancher se contracte avec `p_n`, il n'est jamais constant. -/
theorem phase_increment_ge_height_mul_log_one_add_inv (z : TrueZero) (n : ℕ) :
    rZeroHeight z.1 * Real.log (1 + 1 / (fnPrimeAtRank n : ℝ)) ≤
      Real.pi * towerPosition z (fnPrimeSuccessor n : ℝ) -
        Real.pi * towerPosition z (fnPrimeAtRank n : ℝ) := by
  have hp1 : (0 : ℝ) < (fnPrimeAtRank n : ℝ) := by exact_mod_cast thm_primeAtRank_pos n
  have hT : (0 : ℝ) ≤ rZeroHeight z.1 := (thm_upperZeroHeight_positive z).le
  have hgap : (1 : ℝ) ≤ (nPrimeGap n : ℝ) := by exact_mod_cast primeGap_ge_one n
  have hratio : (1 : ℝ) + 1 / (fnPrimeAtRank n : ℝ) ≤
      1 + (nPrimeGap n : ℝ) / (fnPrimeAtRank n : ℝ) := by
    linarith [div_le_div_of_nonneg_right hgap hp1.le]
  have hlog : Real.log (1 + 1 / (fnPrimeAtRank n : ℝ)) ≤ rPrimeGapLogRatio n := by
    rw [thm_primeGapLogRatio_eq_log_one_add]
    exact Real.log_le_log (by positivity) hratio
  rw [phase_increment_eq_pi_span]
  unfold TowerPrimeGapSpan rTowerHeight
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmul := mul_le_mul_of_nonneg_left hlog hT
  calc rZeroHeight z.1 * Real.log (1 + 1 / (fnPrimeAtRank n : ℝ))
      ≤ rZeroHeight z.1 * rPrimeGapLogRatio n := hmul
    _ = Real.pi * (rZeroHeight z.1 / Real.pi * rPrimeGapLogRatio n) := by field_simp

/-- **Borne événementielle forte, après le premier `2`** : `ΔΘ_n ≥ T · log(1 + 2/p_n) > 0`, exactement
compatible avec l'observation E112 (les minima sont portés par les arêtes jumelles `g = 2`). -/
theorem phase_increment_ge_height_mul_log_one_add_two_div (z : TrueZero) {n : ℕ}
    (h2 : 2 < fnPrimeAtRank n) :
    rZeroHeight z.1 * Real.log (1 + 2 / (fnPrimeAtRank n : ℝ)) ≤
      Real.pi * towerPosition z (fnPrimeSuccessor n : ℝ) -
        Real.pi * towerPosition z (fnPrimeAtRank n : ℝ) := by
  have hp1 : (0 : ℝ) < (fnPrimeAtRank n : ℝ) := by exact_mod_cast thm_primeAtRank_pos n
  have hT : (0 : ℝ) ≤ rZeroHeight z.1 := (thm_upperZeroHeight_positive z).le
  have hgap : (2 : ℝ) ≤ (nPrimeGap n : ℝ) := by exact_mod_cast primeGap_ge_two_of_two_lt h2
  have hratio : (1 : ℝ) + 2 / (fnPrimeAtRank n : ℝ) ≤
      1 + (nPrimeGap n : ℝ) / (fnPrimeAtRank n : ℝ) := by
    linarith [div_le_div_of_nonneg_right hgap hp1.le]
  have hlog : Real.log (1 + 2 / (fnPrimeAtRank n : ℝ)) ≤ rPrimeGapLogRatio n := by
    rw [thm_primeGapLogRatio_eq_log_one_add]
    exact Real.log_le_log (by positivity) hratio
  rw [phase_increment_eq_pi_span]
  unfold TowerPrimeGapSpan rTowerHeight
  have hmul := mul_le_mul_of_nonneg_left hlog hT
  calc rZeroHeight z.1 * Real.log (1 + 2 / (fnPrimeAtRank n : ℝ))
      ≤ rZeroHeight z.1 * rPrimeGapLogRatio n := hmul
    _ = Real.pi * (rZeroHeight z.1 / Real.pi * rPrimeGapLogRatio n) := by field_simp

/-! ## C4 — forme EXACTE de « un quantum force `T` » (conditionnel local, jamais une prémisse
globale) -/

/-- **Ce qu'un quantum de phase, s'il existait, donnerait EXACTEMENT** : une borne inférieure locale
sur `T`, par rang, `T ≥ c / log(p_{n+1}/p_n)`. `c` n'est ici qu'une hypothèse LOCALE d'un théorème
conditionnel — jamais une prémisse globale posée sur tous les événements (E112 la réfute sur la
ligne : aucun `c > 0` uniforme n'est compatible avec les zéros ON). Ce que cette borne établit n'est
jamais `T_E < T_L` sur un passage, seulement une croissance moyenne. -/
theorem height_lower_bound_of_phase_quantum (z : TrueZero) (n : ℕ) {c : ℝ}
    (h : c ≤ Real.pi * towerPosition z (fnPrimeSuccessor n : ℝ) -
        Real.pi * towerPosition z (fnPrimeAtRank n : ℝ)) :
    c / rPrimeGapLogRatio n ≤ rZeroHeight z.1 := by
  rw [phase_increment_eq_pi_span] at h
  unfold TowerPrimeGapSpan rTowerHeight at h
  have heq : Real.pi * (rZeroHeight z.1 / Real.pi * rPrimeGapLogRatio n) =
      rZeroHeight z.1 * rPrimeGapLogRatio n := by
    field_simp
  rw [heq] at h
  rw [div_le_iff₀ (thm_primeGapLogRatio_pos n)]
  exact h

/-! ## C5 — le quantum, même admis, est satisfiable par les deux arêtes consécutives à la même
hauteur -/

/-- **Un quantum ne distingue pas « un `T` pour deux événements » de « deux `T` »** : quel que soit
`c`, il existe un seuil `T₀` au-delà duquel une seule hauteur `T` satisfait le quantum sur les DEUX
arêtes consécutives `n` et `n+1` simultanément. Pure inégalité réelle sur les ratios logarithmiques
de place, aucune hypothèse sur un zéro. -/
theorem quantum_pair_satisfiable_at_same_height (c : ℝ) (n : ℕ) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      c ≤ T * rPrimeGapLogRatio n ∧ c ≤ T * rPrimeGapLogRatio (n + 1) := by
  refine ⟨max (c / rPrimeGapLogRatio n) (c / rPrimeGapLogRatio (n + 1)), fun T hT => ?_⟩
  have h1 : c / rPrimeGapLogRatio n ≤ T := le_trans (le_max_left _ _) hT
  have h2 : c / rPrimeGapLogRatio (n + 1) ≤ T := le_trans (le_max_right _ _) hT
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ (thm_primeGapLogRatio_pos n)] at h1
    exact h1
  · rw [div_le_iff₀ (thm_primeGapLogRatio_pos (n + 1))] at h2
    exact h2

/-! ## C6 — la progression continue du passage OFF consécutif est strictement positive et vaut la
portée -/

/-- **La progression continue du second événement (membre miroir) est strictement positive** :
instance de `phase_increment_pos` sur le membre miroir et son propre rang `n(z*)`, écrite en termes
d'`occurrence`/`expectedMinimumPrime` (`occurrence_eq_primeAtRank`,
`expectedMinimum_eq_succ_occurrence`). **Prémisse retirée (auteur, 2026-09-28) :** le linter signalait
`hab` comme non référencé ; vraie que `z` et son miroir soient consécutifs ou non, elle ne le
requiert donc pas — retirée, contrôlé par le compilateur. Elle est réintroduite localement dans
`off_consecutive_continuous_progression_eq_span` (C6b) et `consecutive_continuous_signature` (C7),
qui en ont réellement besoin pour `mirror_sourceIndex_of_consecutive`. -/
theorem mirror_continuous_progression_pos (z : TrueZero) :
    0 < Real.pi * towerPosition (mirrorMember z) (expectedMinimumPrime (mirrorMember z) : ℝ) -
        Real.pi * towerPosition (mirrorMember z) (occurrence (mirrorMember z) : ℝ) := by
  rw [expectedMinimum_eq_succ_occurrence, occurrence_eq_primeAtRank]
  exact phase_increment_pos (mirrorMember z) (nZeroSourceIndex (mirrorMember z).1)

/-- **La progression continue du second événement vaut EXACTEMENT la portée `S_{n(z)+1}` de `z`**,
SOUS consécutivité stricte : `n(z*) = n(z) + 1` (`mirror_sourceIndex_of_consecutive`) et
`TowerPrimeGapSpan (z*) = TowerPrimeGapSpan z` sur tout rang (`mirror_span_eq`, la portée est
aveugle à `β`) transportent la valeur de `n(z*)` à `z` et `n(z) + 1`. C'est la formalisation EXACTE
du « NON RÉFUTÉ » de l'audit de l'auteur : chaque EV+1 possède une progression
arithmético-analytique strictement positive, et elle vaut `T · log(p_{n+2}/p_{n+1})` — jamais un
compteur d'anneaux. -/
theorem off_consecutive_continuous_progression_eq_span {z : TrueZero}
    (hab : PZeroMembersConsecutive z.1 (mirrorMember z).1) :
    Real.pi * towerPosition (mirrorMember z) (expectedMinimumPrime (mirrorMember z) : ℝ) -
        Real.pi * towerPosition (mirrorMember z) (occurrence (mirrorMember z) : ℝ) =
      Real.pi * TowerPrimeGapSpan z (nZeroSourceIndex z.1 + 1) := by
  rw [expectedMinimum_eq_succ_occurrence, occurrence_eq_primeAtRank, phase_increment_eq_pi_span,
    mirror_sourceIndex_of_consecutive hab, mirror_span_eq]

/-! ## C7 — signature continue du passage OFF consécutif (synthèse, sans anneau) -/

/-- **Signature continue du passage OFF consécutif** : l'horloge des membres avance d'exactement un
cran, la hauteur est identique, la progression continue du second événement est strictement
positive, elle vaut exactement `T · log(p_{n+2}/p_{n+1})` (une fonction de `(T, n)` seuls — le même
nombre que si le second événement était un zéro ON de hauteur `T` de rang `n + 1`, C2), et elle est
bornée par `T · log 2` (Bertrand, C3). **Prémisse retirée (auteur, 2026-09-28, « isole encore plus la
prémisse ») :** l'énoncé initial du plan portait une hypothèse `hOff : PIsOffCriticalLine z.1` ;
aucun des cinq conjoints ne l'utilise, `hab` (consécutivité) suffit à chacun — le compilateur accepte
le théorème sans elle. Retirée : l'énoncé tient donc aussi pour `z` SUR la ligne (`β = 1/2`), où
`mirrorMember z = z` (`mirrorMember_eq_self_of_onLine`) le rend trivial. C'est la preuve directe,
par le compilateur, que la signature continue du passage consécutif ne distingue pas OFF de ON ; ce
qui distinguerait est `T_E < T_L` (`PHeightProgression` ⟺ RH, `ReverseEngineeredClosure.lean`), non
compilable sans prémisse. -/
theorem consecutive_continuous_signature {z : TrueZero}
    (hab : PZeroMembersConsecutive z.1 (mirrorMember z).1) :
    nZeroSourceIndex (mirrorMember z).1 = nZeroSourceIndex z.1 + 1 ∧
    rZeroHeight (mirrorMember z).1 = rZeroHeight z.1 ∧
    0 < Real.pi * towerPosition (mirrorMember z) (expectedMinimumPrime (mirrorMember z) : ℝ) -
        Real.pi * towerPosition (mirrorMember z) (occurrence (mirrorMember z) : ℝ) ∧
    Real.pi * towerPosition (mirrorMember z) (expectedMinimumPrime (mirrorMember z) : ℝ) -
        Real.pi * towerPosition (mirrorMember z) (occurrence (mirrorMember z) : ℝ) =
      rZeroHeight z.1 * rPrimeGapLogRatio (nZeroSourceIndex z.1 + 1) ∧
    Real.pi * towerPosition (mirrorMember z) (expectedMinimumPrime (mirrorMember z) : ℝ) -
        Real.pi * towerPosition (mirrorMember z) (occurrence (mirrorMember z) : ℝ) ≤
      rZeroHeight z.1 * Real.log 2 := by
  have hspan : Real.pi * TowerPrimeGapSpan z (nZeroSourceIndex z.1 + 1) =
      rZeroHeight z.1 * rPrimeGapLogRatio (nZeroSourceIndex z.1 + 1) := by
    unfold TowerPrimeGapSpan rTowerHeight
    field_simp
  refine ⟨mirror_sourceIndex_of_consecutive hab, mirrorMember_ordinate z,
    mirror_continuous_progression_pos z, ?_, ?_⟩
  · rw [off_consecutive_continuous_progression_eq_span hab, hspan]
  · rw [off_consecutive_continuous_progression_eq_span hab, ← phase_increment_eq_pi_span]
    exact phase_increment_le_height_mul_log_two z (nZeroSourceIndex z.1 + 1)

/-! ## C8 — la translation miroir contre la progression continue SUIVANTE (E113) -/

/-- **Le rapport `R` de l'auteur (2026-09-28)** : la translation miroir `π·(θ(z*,q) − θ(z,q))`,
composée avec `mirror_translation_lt`, contre la progression continue du prochain événement
`ΔΘ_{n+1}(z*) = T·log(p_{n+2}/p_{n+1})` (`off_consecutive_continuous_progression_eq_span`).
Composition triviale des deux théorèmes déjà compilés (`mirror_translation_lt`,
`phase_increment_eq_pi_span`), aucune nouvelle prémisse au-delà de `hβ`/`hab` déjà requises par
chacun d'eux séparément. E113 (`e113_translation_vs_next_progression_published.py`) mesure ce
rapport sur les 299 arêtes réelles disponibles : `< 10⁻²` partout, DÉCROISSANT avec le rang (jamais
de rapprochement vers `1`), y compris sur les arêtes jumelles (`g_{n+1}=2`, minima de `ΔΘ`). -/
theorem mirror_translation_over_next_progression_lt {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (hab : PZeroMembersConsecutive z.1 (mirrorMember z).1) (q : ℝ) :
    (Real.pi * towerPosition (mirrorMember z) q - Real.pi * towerPosition z q) /
        (Real.pi * TowerPrimeGapSpan z (nZeroSourceIndex z.1 + 1)) <
      (1 - 2 * rZeroRadialPosition z.1) /
        (rZeroHeight z.1 ^ 2 * rPrimeGapLogRatio (nZeroSourceIndex z.1 + 1)) := by
  have hT : (0 : ℝ) < rZeroHeight z.1 := z.2
  have hr : (0 : ℝ) < rPrimeGapLogRatio (nZeroSourceIndex z.1 + 1) := thm_primeGapLogRatio_pos _
  have hspan : Real.pi * TowerPrimeGapSpan z (nZeroSourceIndex z.1 + 1) =
      rZeroHeight z.1 * rPrimeGapLogRatio (nZeroSourceIndex z.1 + 1) := by
    unfold TowerPrimeGapSpan rTowerHeight; field_simp
  have hTr : (0 : ℝ) < rZeroHeight z.1 * rPrimeGapLogRatio (nZeroSourceIndex z.1 + 1) := by positivity
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have htrans := (mirror_translation_lt hβ q).2
  have hnum : Real.pi * towerPosition (mirrorMember z) q - Real.pi * towerPosition z q <
      (1 - 2 * rZeroRadialPosition z.1) / rZeroHeight z.1 := by
    have hmul := mul_lt_mul_of_pos_left htrans hπ
    have hrw : Real.pi * ((1 - 2 * rZeroRadialPosition z.1) / (Real.pi * rZeroHeight z.1)) =
        (1 - 2 * rZeroRadialPosition z.1) / rZeroHeight z.1 := by
      field_simp
    calc Real.pi * towerPosition (mirrorMember z) q - Real.pi * towerPosition z q
        = Real.pi * (towerPosition (mirrorMember z) q - towerPosition z q) := by ring
      _ < Real.pi * ((1 - 2 * rZeroRadialPosition z.1) / (Real.pi * rZeroHeight z.1)) := hmul
      _ = (1 - 2 * rZeroRadialPosition z.1) / rZeroHeight z.1 := hrw
  rw [hspan]
  calc (Real.pi * towerPosition (mirrorMember z) q - Real.pi * towerPosition z q) /
        (rZeroHeight z.1 * rPrimeGapLogRatio (nZeroSourceIndex z.1 + 1))
      < ((1 - 2 * rZeroRadialPosition z.1) / rZeroHeight z.1) /
          (rZeroHeight z.1 * rPrimeGapLogRatio (nZeroSourceIndex z.1 + 1)) :=
        div_lt_div_of_pos_right hnum hTr
    _ = (1 - 2 * rZeroRadialPosition z.1) /
          (rZeroHeight z.1 ^ 2 * rPrimeGapLogRatio (nZeroSourceIndex z.1 + 1)) := by
        rw [div_div, sq, mul_assoc]

/-!
## Verdict

`phase_increment_pos` établit sans condition que chaque arête première force une progression
continue strictement positive de phase — la reformulation exacte, continue, de ce que l'audit de
l'auteur dit ne PAS être réfuté par `237c075c`. `phase_increment_le_height_mul_log_two` la borne par
Bertrand, sans PNT ni asymptotique. `height_lower_bound_of_phase_quantum` donne la forme EXACTE, et
SEULEMENT locale, de ce qu'un quantum apporterait ; `quantum_pair_satisfiable_at_same_height` montre
qu'aucun quantum, même admis, ne peut distinguer « une hauteur, deux événements » de « deux
hauteurs » — le second maillon de la chaîne (« quantum ⟹ `T` croît strictement d'un passage à
l'autre ») n'existe dans aucun théorème ici, et E112 montre numériquement qu'il ne peut exister
(aucun `c > 0` uniforme n'est compatible avec les 300 zéros ON).
`consecutive_continuous_signature` formalise la signature continue du passage consécutif, SANS
hypothèse `PIsOffCriticalLine` (retirée, contrôlée par le compilateur) : elle est, terme à terme, la
même que celle d'un passage ON de même hauteur (C2), et tient trivialement sur la ligne elle-même —
la progression continue seule ne sépare pas OFF de ON.
`primeGap_ge_two_of_two_lt` compile le plancher mobile demandé par l'auteur (2026-09-28) : brique
NOUVELLE (jamais compilée avant ce jour, ni dans RHV3Lean ni ailleurs), `g_n ≥ 2` après le premier `2`
par parité (deux impairs distincts diffèrent d'un pair non nul). `g_n ≥ 1` était déjà compilé
(`thm_primeGap_positive`, restaté ici `primeGap_ge_one`). Les deux donnent
`phase_increment_ge_height_mul_log_one_add_inv`/`..._two_div` : `ΔΘ_n ≥ T·log(1+1/p_n)` (universel) et
`ΔΘ_n ≥ T·log(1+2/p_n)` (après `2`) — un plancher qui se CONTRACTE avec `p_n` au lieu d'être constant,
donc jamais réfuté par E112 (qui réfute seulement un `c` constant indépendant de `n`).
`mirror_translation_over_next_progression_lt` compile le rapport `R` proposé par l'auteur
(2026-09-28) : la translation miroir, RAPPORTÉE à la progression continue du prochain événement, est
bornée par `(1−2β)/(T²·r_{n+1})` — composition triviale, aucune prémisse nouvelle. E113 mesure ce
rapport `< 10⁻²` et DÉCROISSANT avec le rang sur les 299 arêtes réelles disponibles, y compris sur
les arêtes jumelles : aucun rapprochement observé vers `1`, aucune contradiction. Aucun `Prop` de
prémisse n'est défini ici ; `RH_FOUND=FALSE`.
-/

end RHV6Fresh
