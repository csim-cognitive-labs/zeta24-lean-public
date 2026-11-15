/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Tower.InvertedTower
import RHV6Fresh.Foundation.ZetaReflect
import RHV6Fresh.Direct.MirrorCount

/-!
# RHV6Fresh — le mouvement réfléchi : l'orientation opposée est un théorème

Niveau GÉOMÉTRIE.  La seconde Tour de la paire est la Tour du zéro que l'équation fonctionnelle
produit, `1 − ρ = (1 − β, −T)` (`zetaFunctionalReflect`, `Foundation/ZetaReflect.lean`), conjugué
du miroir supérieur `(1 − β, T)`.  Les mêmes formules tangentielles appliquées à `(1 − β, −T)`
donnent une phase `−φ*` et un pas logarithmique `−π/T` : la spirale tourne dans l'autre sens.  Ses
rayons sont ceux du miroir supérieur parcourus à l'envers, `C'_j = C*_{−j}`
(`reflectedIncidence_eq`).  Son anneau à sa propre coordonnée `j = −(k+1)` a pour entrée `C*_{k+1}`
et pour dernier rayon `C*_k` (`reflected_entry_eq_contactPlus`, `reflected_lastRay_eq_contactMinus`) :
l'inversion des contacts de la seconde Tour est un THÉORÈME de l'équation fonctionnelle et de la
conjugaison, jamais une définition ni un énoncé.  `β ↦ 1 − β` seul ne l'apporte pas (le miroir
supérieur tourne dans le même sens : `mirror_step_positive`).

Aucun premier, aucun rang, aucun comptage n'entre ici.  Aucun `sorry`, aucun `admit`, aucun axiome
nouveau.
-/

namespace RHV6Fresh

open RHV3Lean
open scoped ComplexConjugate

/-! ## 1. Les formules tangentielles du zéro réfléchi `(β*, −T)` -/

/-- Phase du zéro réfléchi : `arctan(−T/β*) = −φ*`. -/
noncomputable def reflectedPhase (w : TrueZero) : ℝ :=
  Real.arctan (-(rZeroHeight w.1) / rZeroRadialPosition w.1)

theorem reflectedPhase_eq_neg (w : TrueZero) :
    reflectedPhase w = -(towerMotionOf w).phase := by
  rw [towerMotion_phase]
  unfold reflectedPhase
  rw [neg_div, Real.arctan_neg]

/-- Log-rayon du zéro réfléchi à sa coordonnée `j` : `(−φ* + jπ)/(−T)`. -/
noncomputable def reflectedLogIncidence (w : TrueZero) (j : ℤ) : ℝ :=
  (reflectedPhase w + (j : ℝ) * Real.pi) / (-(rZeroHeight w.1))

/-- Rayon du zéro réfléchi à sa coordonnée `j`. -/
noncomputable def reflectedIncidence (w : TrueZero) (j : ℤ) : ℝ :=
  Real.exp (reflectedLogIncidence w j)

/-- **Identité de conjugaison** : `log C'_j = log C*_{−j}`. -/
theorem reflectedLogIncidence_eq (w : TrueZero) (j : ℤ) :
    reflectedLogIncidence w j = (towerMotionOf w).logIncidence (-j) := by
  have hT : rZeroHeight w.1 ≠ 0 := ne_of_gt w.2
  rw [(towerMotionOf w).logIncidence_eq]
  unfold reflectedLogIncidence
  rw [reflectedPhase_eq_neg]
  push_cast
  field_simp
  ring

/-- **Identité de conjugaison** : `C'_j = C*_{−j}`, les rayons du miroir parcourus à l'envers. -/
theorem reflectedIncidence_eq (w : TrueZero) (j : ℤ) :
    reflectedIncidence w j = (towerMotionOf w).incidence (-j) := by
  rw [reflectedIncidence, reflectedLogIncidence_eq, (towerMotionOf w).incidence_eq]

/-! ## 2. Le renversement du sens de parcours -/

/-- Le pas logarithmique du zéro réfléchi est `−π/T` : la spirale tourne dans l'autre sens. -/
theorem reflected_step (w : TrueZero) (j : ℤ) :
    reflectedLogIncidence w (j + 1) - reflectedLogIncidence w j = -(Real.pi / rZeroHeight w.1) := by
  have hT : rZeroHeight w.1 ≠ 0 := ne_of_gt w.2
  unfold reflectedLogIncidence
  push_cast
  field_simp
  ring

/-- Le pas logarithmique du miroir supérieur `(1 − β, T)` est `+π/T` : `β ↦ 1 − β` seul ne renverse
rien. -/
theorem mirror_step_positive (w : TrueZero) (k : ℤ) :
    (towerMotionOf w).logIncidence (k + 1) - (towerMotionOf w).logIncidence k =
      Real.pi / rZeroHeight w.1 := by
  have hT : rZeroHeight w.1 ≠ 0 := ne_of_gt w.2
  rw [(towerMotionOf w).logIncidence_eq, (towerMotionOf w).logIncidence_eq]
  push_cast
  field_simp
  ring

/-- Les rayons du zéro réfléchi décroissent avec sa coordonnée : orientation opposée (théorème). -/
theorem reflectedIncidence_antitone (w : TrueZero) (j : ℤ) :
    reflectedIncidence w (j + 1) < reflectedIncidence w j := by
  unfold reflectedIncidence
  apply Real.exp_lt_exp.mpr
  have h := reflected_step w j
  have hpos : 0 < Real.pi / rZeroHeight w.1 := div_pos Real.pi_pos w.2
  linarith

/-! ### Le mouvement réfléchi depuis sa propre origine n'atteint aucun premier

Tous les derniers rayons `C'_{j+1}`, `j ≥ 0`, du mouvement réfléchi parcouru depuis son origine
`C'_0 = C*_0` sont strictement sous `1` (`φ* < π/2`, pas `−π/T`) : la règle du pivot (« le mouvement
depuis l'origine canonique s'arrête au premier anneau dont le dernier rayon atteint le pivot ») n'y a
aucun événement d'arrêt. -/

theorem reflected_lastRay_lt_one (w : TrueZero) (j : ℕ) :
    reflectedIncidence w ((j : ℤ) + 1) < 1 := by
  have hneg : reflectedLogIncidence w ((j : ℤ) + 1) < 0 := by
    rw [reflectedLogIncidence_eq, (towerMotionOf w).logIncidence_eq, towerMotion_phase]
    have hT : 0 < rZeroHeight w.1 := w.2
    have hφ := Real.arctan_lt_pi_div_two (rZeroHeight w.1 / rZeroRadialPosition w.1)
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    apply div_neg_of_neg_of_pos _ hT
    push_cast
    nlinarith [Real.pi_pos]
  unfold reflectedIncidence
  calc Real.exp (reflectedLogIncidence w ((j : ℤ) + 1)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr hneg
    _ = 1 := Real.exp_zero

/-- Aucun anneau du mouvement réfléchi parcouru depuis son origine n'atteint un premier à son dernier
rayon : la règle du pivot n'y a pas d'événement d'arrêt. -/
theorem reflected_no_stop_event (w : TrueZero) (j : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    ¬ ((p : ℝ) ≤ reflectedIncidence w ((j : ℤ) + 1)) := by
  intro h
  have h1 := reflected_lastRay_lt_one w j
  have hp' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  linarith

/-! ## 3. L'anneau du zéro réfléchi : entrée en haut, dernier rayon en bas (théorème) -/

/-- À sa coordonnée `j = −(k+1)`, l'entrée du zéro réfléchi est le rayon du haut `C*_{k+1}`. -/
theorem reflected_entry_eq_contactPlus (w : TrueZero) (k : ℤ) :
    reflectedIncidence w (-(k + 1)) = contactPlusAt w k := by
  rw [reflectedIncidence_eq, neg_neg]
  rfl

/-- À sa coordonnée `j = −(k+1)`, le dernier rayon du zéro réfléchi (coordonnée `j + 1`) est le rayon
du bas `C*_k`. -/
theorem reflected_lastRay_eq_contactMinus (w : TrueZero) (k : ℤ) :
    reflectedIncidence w (-(k + 1) + 1) = contactMinusAt w k := by
  rw [reflectedIncidence_eq]
  unfold contactMinusAt
  congr 1
  ring

/-- **L'inversion des contacts est un théorème** : la paire inversée à la coordonnée `k` est
exactement l'anneau du zéro réfléchi à sa coordonnée `−(k+1)`, entrée puis dernier rayon dans SON
sens de parcours. -/
theorem invertedPairAt_eq_reflected (w : TrueZero) (k : ℤ) :
    (invertedPairAt w k).entryContact = reflectedIncidence w (-(k + 1)) ∧
      (invertedPairAt w k).lastRayContact = reflectedIncidence w (-(k + 1) + 1) := by
  rw [invertedPairAt_entryContact, invertedPairAt_lastRayContact,
    reflected_entry_eq_contactPlus, reflected_lastRay_eq_contactMinus]
  exact ⟨rfl, rfl⟩

/-- **La seconde Tour place ses deux contacts hors du domaine où le mouvement réfléchi honnête
(depuis sa propre origine, `j ≥ 1`) ne rencontre jamais aucun premier** (`reflected_no_stop_event`) :
si la règle avant (non réfléchie) donne une coordonnée `k ≥ 0` — ce qui est TOUJOURS le cas en
pratique, `k` allant de 2 à plus de 1300 sur les 300 hauteurs publiées d'Odlyzko (E085) —, alors les
deux coordonnées réfléchies utilisées par `invertedPairAt w k` (entrée `−(k+1)`, dernier rayon
`−k`) sont TOUTES DEUX `≤ 0`, donc n'appartiennent jamais à `{(j : ℕ) + 1 | j : ℕ}` : la seconde Tour
n'est JAMAIS obtenue en suivant le mouvement réfléchi depuis SA PROPRE origine vers l'avant ; elle
place directement ses contacts à la coordonnée que donne la règle AVANT (non réfléchie) sur `w`, puis
les relit avec les rôles échangés. L'identité `invertedPairAt_eq_reflected` reste un théorème vrai
(la valeur numérique coïncide), mais ce n'est pas une trajectoire honnête du mouvement réfléchi : ce
dernier, suivi depuis son origine, ne s'arrête jamais (`reflected_no_stop_event`). -/
theorem invertedPairAt_coordinate_le_zero (w : TrueZero) {k : ℤ} (hk : 0 ≤ k) :
    -(k + 1) ≤ 0 ∧ -(k + 1) + 1 ≤ 0 := by omega

/-- **Le mouvement réfléchi authentique du membre miroir, suivi depuis SA PROPRE origine, ne rencontre
jamais `p_min(z*)`** — instanciation directe de `reflected_no_stop_event` avec `p := p_min(z*)` : c'est
l'énoncé exact demandé par l'auteur (« la seconde Tour authentique ne peut pas atteindre le prochain
premier »), maintenant sur l'objet lui-même, pas seulement sur une borne générale (`invertedPairAt_coordinate_le_zero`
montrait seulement que `secondTowerOf` n'utilise pas ce domaine ; ceci montre ce qui s'y passerait). -/
theorem reflectedFromOrigin_never_reaches_expectedMinimum (z : TrueZero) (j : ℕ) :
    ¬ ((expectedMinimumPrime (mirrorMember z) : ℝ) ≤
        reflectedIncidence (mirrorMember z) ((j : ℤ) + 1)) :=
  reflected_no_stop_event (mirrorMember z) j (expectedMinimumPrime_prime (mirrorMember z)).pos

/-- **Ce fait est aveugle à `β`** : il tient identiquement pour un zéro SUR la droite critique
(`β = 1/2`), où aucune contradiction n'est cherchée ni possible (`RiemannHypothesis` n'exclut aucun
zéro sur la droite). La même instance de `reflected_no_stop_event`, sans utiliser `hβ`, le prouve : le
mouvement réfléchi ne s'arrête jamais que le zéro soit sur la droite ou hors ligne. Un fait qui tient
identiquement des deux côtés ne peut distinguer `β = 1/2` de `β ≠ 1/2` : il ne peut donc, seul, fournir
la contradiction cherchée (qui doit être spécifique au côté hors ligne). -/
theorem reflectedFromOrigin_never_reaches_expectedMinimum_beta_blind (z : TrueZero)
    (hβ : rZeroRadialPosition z.1 = 1 / 2) (j : ℕ) :
    ¬ ((expectedMinimumPrime (mirrorMember z) : ℝ) ≤
        reflectedIncidence (mirrorMember z) ((j : ℤ) + 1)) :=
  reflectedFromOrigin_never_reaches_expectedMinimum z j

/-! ### Rigidité en amont appliquée à l'objet réfléchi authentique (auteur, réarchitecture demandée,
2026-09-26)

Exigence de l'auteur : posséder d'abord la rigidité de la règle du pivot ON (`pivotCoordinate_isLeast`,
`Direct/PivotCell.lean` : la coordonnée d'arrêt est le PLUS PETIT `k` tel que `q ≤ C_{k+1}` — c'est
`IsLeast`, jamais un choix, jamais un `∃` libre), puis l'appliquer sur l'objet OFF authentique : le
mouvement réfléchi `reflectedIncidence (mirrorMember z)`, suivi depuis SA PROPRE origine, visant SON
obligation propre `p_min(z*)`. Résultat, par la MÊME rigidité (`IsLeast`), appliquée ici : l'ensemble
que `pivotCoordinate_isLeast` rend non vide et pourvu d'un plus petit élément côté ON est VIDE côté
mouvement réfléchi authentique — aucune coordonnée d'arrêt n'existe, par le théorème lui-même, pas par
absence de recherche. -/

/-- **L'ensemble d'arrêt de la règle du pivot, transposé au mouvement réfléchi authentique visant son
obligation propre, est VIDE** : contrairement à `pivotCoordinate_isLeast` (côté ON/avant, cet ensemble
a toujours un plus petit élément), ici aucun `j` ne satisfait le critère d'arrêt — théorème, pas
absence de recherche. -/
theorem reflectedStopSet_own_expectedMinimum_eq_empty (z : TrueZero) :
    {j : ℕ | (expectedMinimumPrime (mirrorMember z) : ℝ) ≤
        reflectedIncidence (mirrorMember z) ((j : ℤ) + 1)} = ∅ := by
  ext j
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact reflectedFromOrigin_never_reaches_expectedMinimum z j

/-- **Corollaire direct : aucune coordonnée d'arrêt (`IsLeast`) n'existe** pour le mouvement réfléchi
authentique visant `p_min(z*)` — la rigidité `IsLeast` qui gouverne toute Tour ON/avant
(`pivotCoordinate_isLeast`) échoue structurellement, par théorème, quand on l'applique à l'objet
réfléchi authentique poursuivant sa propre obligation. C'est l'énoncé rigide, sans `∃j` libre et sans
emprunt à la règle avant du membre miroir, que l'auteur demande : la rigidité amont (ON), transposée
telle quelle à l'objet OFF authentique, ne produit aucun contact — ni conforme, ni contradictoire :
absente. -/
theorem no_reflectedStopCoordinate_own_expectedMinimum (z : TrueZero) :
    ¬ ∃ j : ℕ, IsLeast
      {j' : ℕ | (expectedMinimumPrime (mirrorMember z) : ℝ) ≤
          reflectedIncidence (mirrorMember z) ((j' : ℤ) + 1)} j := by
  rintro ⟨j, hj, -⟩
  rw [reflectedStopSet_own_expectedMinimum_eq_empty] at hj
  exact hj

/-! ## 4. Le mouvement réfléchi comme objet -/

/-- Le mouvement du zéro réfléchi `(β*, −T)` : phase `−φ*`, vitesse `−T`. -/
structure ReflectedMotion (w : TrueZero) where
  phase : ℝ
  logIncidence : ℤ → ℝ
  incidence : ℤ → ℝ
  phase_eq : phase = Real.arctan (-(rZeroHeight w.1) / rZeroRadialPosition w.1)
  logIncidence_eq : ∀ j : ℤ,
    logIncidence j = (phase + (j : ℝ) * Real.pi) / (-(rZeroHeight w.1))
  incidence_eq : ∀ j : ℤ, incidence j = Real.exp (logIncidence j)

/-- Le mouvement réfléchi produit par les seules coordonnées du miroir. -/
noncomputable def reflectedMotionOf (w : TrueZero) : ReflectedMotion w where
  phase := reflectedPhase w
  logIncidence := reflectedLogIncidence w
  incidence := reflectedIncidence w
  phase_eq := rfl
  logIncidence_eq := fun _ => rfl
  incidence_eq := fun _ => rfl

theorem reflectedMotion_incidence (w : TrueZero) (j : ℤ) :
    (reflectedMotionOf w).incidence j = (towerMotionOf w).incidence (-j) :=
  reflectedIncidence_eq w j

/-! ## 5. Le zéro réfléchi est un vrai zéro de zêta, aux coordonnées `(1 − β, −T)` -/

/-- Le support du zéro réfléchi de `z` est le conjugué du support de son miroir supérieur. -/
theorem reflectedZero_support (z : TrueZero) :
    zetaFunctionalReflect (cZeroSupport z.1) = conj (cZeroSupport (mirrorMember z).1) :=
  functionalReflect_support_eq_conj_mirror z

/-- Le zéro réfléchi de `z` est un zéro non trivial de zêta. -/
theorem reflectedZero_isZero (z : TrueZero) :
    PIsNonTrivialZetaZero (zetaFunctionalReflect (cZeroSupport z.1)) :=
  zeta_functionalReflect_zero _ z.1.2

/-- Sa partie réelle est `1 − β`, celle du miroir supérieur. -/
theorem reflectedZero_re (z : TrueZero) :
    (zetaFunctionalReflect (cZeroSupport z.1)).re = rZeroRadialPosition (mirrorMember z).1 :=
  functionalReflect_re_eq_mirror z

/-- Sa partie imaginaire est `−T` : la vitesse angulaire du mouvement réfléchi. -/
theorem reflectedZero_im (z : TrueZero) :
    (zetaFunctionalReflect (cZeroSupport z.1)).im = -(rZeroHeight (mirrorMember z).1) :=
  functionalReflect_im_eq_neg_mirror z

end RHV6Fresh
