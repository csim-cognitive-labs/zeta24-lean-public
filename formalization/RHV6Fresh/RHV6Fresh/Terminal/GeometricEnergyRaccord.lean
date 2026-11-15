/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Direct.PivotCell
import RHV6Fresh.Terminal.ExplicitFormulaLink

/-!
# RHV6Fresh — le raccord géométrie–énergie–grammaire (correction de P6/E116, auteur 2026-09-28)

Objection de l'auteur sur `energy_balance_two_primes_false` telle qu'appliquée dans le plan
E116/P6 : la prémisse `PEnergyBalanceAtRaccords` compare `‖zeroTerm e q‖` et `‖zeroTerm l q‖`
directement AU PREMIER `q = occurrence(l)` ou `q = expectedMinimumPrime(l)`. Mais rien n'affirme
que ce premier soit un RAYON de l'une ou l'autre Tour (`zeroTerm_real_iff_ray` : seuls les rayons
`contactMinusAt` annulent la partie imaginaire). Le premier est en général STRICTEMENT À
L'INTÉRIEUR de la cellule qui l'encadre `(C⁻, C⁺]`, jamais un contact. Comparer les amplitudes
AU premier confond donc « le premier lu par la cellule » et « le contact qui délimite la
cellule » — c'est une prémisse mal posée, pas une conséquence géométrique correcte.

Ce fichier transporte le premier dans sa cellule authentique (rien de nouveau : `Direct/
PivotCell.lean` le fait déjà pour `pivotPair`/`pivotCoordinate`), puis établit, SANS aucune
hypothèse énergétique postulée, l'encadrement correct de l'amplitude à ce premier par les
amplitudes de la Tour à SES DEUX CONTACTS PROPRES (où le terme `zeroTerm` est authentiquement
réel, `ray_zeroTerm_real`). C'est l'objet demandé par l'auteur : « premier → cellule unique →
contacts propres → zeroTerm aux contacts → amplitude de l'étage », substitué à « premier →
égalité arbitraire de deux amplitudes au premier ».

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune hypothèse de type RH. Ce fichier NE
referme PAS `PEnergyBalanceAtRaccords` (`Terminal/HorizontalExclusion.lean`, `↔ RiemannHypothesis`,
inchangé) : l'encadrement obtenu ici est vrai pour TOUT zéro (β quelconque), il ne force donc
aucune égalité — c'est précisément ce qu'un énoncé honnête doit produire : le bon objet
géométrique à comparer, pas une fermeture.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Le premier transporté dans sa cellule unique (transport, pas une donnée nouvelle) -/

/-- **Le premier `q` est encadré par les deux contacts de sa cellule unique** : reformulation de
`entry_lt_pivot`/`pivot_le_lastRay` (déjà compilés, `Direct/PivotCell.lean`) directement en termes
de `contactMinusAt`/`contactPlusAt`, sans passer par `pivotPair`. -/
theorem prime_raccord_has_unique_tower_cell (z : TrueZero) {q : ℝ} (hq : 0 < q) :
    contactMinusAt z (pivotCoordinate z q) < q ∧
      q ≤ contactPlusAt z (pivotCoordinate z q) := by
  have h1 := entry_lt_pivot z hq
  have h2 := pivot_le_lastRay z hq
  unfold pivotPair at h1 h2
  rw [analyticPairAt_entryContact] at h1
  rw [analyticPairAt_lastRayContact] at h2
  exact ⟨h1, h2⟩

/-! ## 2. Les contacts propres de la cellule sont des points réels du terme (déjà compilé) -/

/-- Le contact d'entrée de la cellule du premier `q` est un rayon authentique de la Tour : le
terme y est réel (transport direct de `ray_zeroTerm_real`, aucune preuve nouvelle). -/
theorem pivotCell_entry_zeroTerm_real (z : TrueZero) (q : ℝ) :
    (zeroTerm z (contactMinusAt z (pivotCoordinate z q))).im = 0 :=
  ray_zeroTerm_real z (pivotCoordinate z q)

/-- Le dernier rayon de la cellule du premier `q` est également un rayon authentique. -/
theorem pivotCell_lastRay_zeroTerm_real (z : TrueZero) (q : ℝ) :
    (zeroTerm z (contactPlusAt z (pivotCoordinate z q))).im = 0 :=
  ray_zeroTerm_real z (pivotCoordinate z q + 1)

/-! ## 3. L'amplitude au premier est encadrée par les amplitudes de ses deux contacts propres -/

/-- **Le théorème correct, substitué à l'égalité mal posée de P6/E116** : l'amplitude
`‖zeroTerm z q‖` au premier `q` (qui n'est en général PAS un rayon) est strictement encadrée par
les amplitudes de la Tour à ses deux contacts propres — les seuls points où `zeroTerm` est
authentiquement réel. Preuve : `prime_raccord_has_unique_tower_cell` place `q` dans `(C⁻, C⁺]`,
puis `zeroTerm_norm` réduit l'amplitude à `x ↦ x^β/‖ρ‖`, strictement croissante en `x` (`β > 0`,
`Real.rpow_lt_rpow`/`Real.rpow_le_rpow`). -/
theorem pivotCell_amplitude_brackets (z : TrueZero) {q : ℝ} (hq : 0 < q) :
    ‖zeroTerm z (contactMinusAt z (pivotCoordinate z q))‖ < ‖zeroTerm z q‖ ∧
      ‖zeroTerm z q‖ ≤ ‖zeroTerm z (contactPlusAt z (pivotCoordinate z q))‖ := by
  obtain ⟨h1, h2⟩ := prime_raccord_has_unique_tower_cell z hq
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hCm : 0 < contactMinusAt z (pivotCoordinate z q) := contactMinusAt_positive z _
  have hCp : 0 < contactPlusAt z (pivotCoordinate z q) := contactPlusAt_positive z _
  have hN : 0 < ‖zeroPoint z‖ := norm_pos_iff.mpr (zeroPoint_ne_zero z)
  rw [zeroTerm_norm hCm, zeroTerm_norm hq, zeroTerm_norm hCp]
  constructor
  · exact div_lt_div_of_pos_right (Real.rpow_lt_rpow hCm.le h1 hβ) hN
  · exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hq.le h2 hβ.le) hN.le

/-! ## 4. Application au couple horizontal `(e, l)` aux deux raccords de la grammaire

Le premier `occurrence(l)` et le premier `expectedMinimumPrime(l)` sont exactement ceux de
`PEnergyBalanceAtRaccords` (`Terminal/HorizontalExclusion.lean`) — mais désormais comparés à
leurs contacts propres dans CHAQUE Tour, jamais à eux-mêmes directement. Ceci donne quatre
inégalités authentiques (jamais des égalités postulées), pour tout couple `(e, l)` de même
hauteur ou non, sans aucune hypothèse de type RH. -/

/-- **Encadrement correct aux deux raccords de la grammaire, pour les deux Tours du couple** :
substitut direct de la prémisse mal posée de P6. Ne force, et ne peut forcer, aucune égalité —
c'est un fait vrai pour tout `e`, tout `l`, toute hauteur, tout `β` : l'objet géométrique correct,
pas une fermeture de `PEnergyBalanceAtRaccords`. -/
theorem horizontalRaccords_amplitude_brackets (e l : TrueZero) :
    (‖zeroTerm e (contactMinusAt e (pivotCoordinate e (occurrence l : ℝ)))‖ <
        ‖zeroTerm e (occurrence l : ℝ)‖ ∧
      ‖zeroTerm e (occurrence l : ℝ)‖ ≤
        ‖zeroTerm e (contactPlusAt e (pivotCoordinate e (occurrence l : ℝ)))‖) ∧
    (‖zeroTerm l (contactMinusAt l (pivotCoordinate l (occurrence l : ℝ)))‖ <
        ‖zeroTerm l (occurrence l : ℝ)‖ ∧
      ‖zeroTerm l (occurrence l : ℝ)‖ ≤
        ‖zeroTerm l (contactPlusAt l (pivotCoordinate l (occurrence l : ℝ)))‖) ∧
    (‖zeroTerm e (contactMinusAt e (pivotCoordinate e (expectedMinimumPrime l : ℝ)))‖ <
        ‖zeroTerm e (expectedMinimumPrime l : ℝ)‖ ∧
      ‖zeroTerm e (expectedMinimumPrime l : ℝ)‖ ≤
        ‖zeroTerm e (contactPlusAt e (pivotCoordinate e (expectedMinimumPrime l : ℝ)))‖) ∧
    (‖zeroTerm l (contactMinusAt l (pivotCoordinate l (expectedMinimumPrime l : ℝ)))‖ <
        ‖zeroTerm l (expectedMinimumPrime l : ℝ)‖ ∧
      ‖zeroTerm l (expectedMinimumPrime l : ℝ)‖ ≤
        ‖zeroTerm l (contactPlusAt l (pivotCoordinate l (expectedMinimumPrime l : ℝ)))‖) :=
  ⟨pivotCell_amplitude_brackets e (by exact_mod_cast occurrence_pos l),
    pivotCell_amplitude_brackets l (by exact_mod_cast occurrence_pos l),
    pivotCell_amplitude_brackets e (by exact_mod_cast expectedMinimumPrime_pos l),
    pivotCell_amplitude_brackets l (by exact_mod_cast expectedMinimumPrime_pos l)⟩

/-! ## 5. La dichotomie cellule/comptage (auteur, 2026-09-28, seconde correction) : à même hauteur,
la translation β ne peut décaler la coordonnée du pivot que de `0` ou `±1` cran, jamais plus
(`pivotCoordinate_sameHeight_shift_le_one`, `Direct/PivotCell.lean`, déjà compilé). Ceci force
l'alternative suivante, sans hypothèse nouvelle : soit `e` et `l` lisent le MÊME anneau au premier
`q` (aucun changement de cellule ⟹ comparaison directe des amplitudes aux quatre contacts propres
correspondants, `sameCell_four_contacts_bracket`), soit ils diffèrent d'exactement un cran (le
changement de cellule lui-même, observable par construction dans la coordonnée lue). Cette
dichotomie est vraie pour tout couple de même hauteur, tout `β` : elle ne referme RIEN par
elle-même (aucune des deux branches n'est exclue par un théorème) — c'est la jonction correcte
entre géométrie (translation β) et grammaire (lecture des premiers), substituée à l'égalité
ponctuelle mal posée de P6, sans jamais postuler laquelle des deux branches est réalisée. -/

/-- **Trichotomie de la coordonnée du pivot à même hauteur** : transport direct de
`pivotCoordinate_sameHeight_shift_le_one` (déjà compilé) en une disjonction explicite. -/
theorem sameHeight_pivotCoordinate_dichotomy (e l : TrueZero)
    (hT : rZeroHeight e.1 = rZeroHeight l.1) (q : ℝ) :
    pivotCoordinate l q = pivotCoordinate e q ∨
      pivotCoordinate l q = pivotCoordinate e q + 1 ∨
      pivotCoordinate l q = pivotCoordinate e q - 1 := by
  have h := pivotCoordinate_sameHeight_shift_le_one e l hT q
  rw [abs_le] at h
  omega

/-- **Branche « pas de changement de cellule »** : si les deux Tours lisent la même coordonnée au
premier `q`, l'amplitude de chacune à `q` est encadrée par SES DEUX contacts propres, tous deux
indexés par le MÊME entier — les « quatre contacts correspondants » demandés, jamais quatre
indices indépendants. -/
theorem sameCell_four_contacts_bracket (e l : TrueZero) {q : ℝ} (hq : 0 < q)
    (hSame : pivotCoordinate l q = pivotCoordinate e q) :
    (‖zeroTerm e (contactMinusAt e (pivotCoordinate e q))‖ < ‖zeroTerm e q‖ ∧
        ‖zeroTerm e q‖ ≤ ‖zeroTerm e (contactPlusAt e (pivotCoordinate e q))‖) ∧
      (‖zeroTerm l (contactMinusAt l (pivotCoordinate e q))‖ < ‖zeroTerm l q‖ ∧
        ‖zeroTerm l q‖ ≤ ‖zeroTerm l (contactPlusAt l (pivotCoordinate e q))‖) := by
  refine ⟨pivotCell_amplitude_brackets e hq, ?_⟩
  have h := pivotCell_amplitude_brackets l hq
  rwa [hSame] at h

/-- **La dichotomie appliquée aux deux raccords exacts de la grammaire** (`occurrence l`,
`expectedMinimumPrime l`) pour le couple horizontal `(e, l)` de même hauteur : à chacun des deux
raccords, soit la cellule est partagée (branche énergétique, `sameCell_four_contacts_bracket`),
soit elle diffère d'un cran (branche comptage). Aucune des deux branches n'est postulée ni
exclue ici — c'est la question ouverte, formalisée sans fermeture. -/
theorem horizontal_cell_dichotomy_at_raccords (e l : TrueZero)
    (hT : rZeroHeight e.1 = rZeroHeight l.1) :
    (pivotCoordinate l (occurrence l : ℝ) = pivotCoordinate e (occurrence l : ℝ) ∨
        pivotCoordinate l (occurrence l : ℝ) = pivotCoordinate e (occurrence l : ℝ) + 1 ∨
        pivotCoordinate l (occurrence l : ℝ) = pivotCoordinate e (occurrence l : ℝ) - 1) ∧
      (pivotCoordinate l (expectedMinimumPrime l : ℝ) =
          pivotCoordinate e (expectedMinimumPrime l : ℝ) ∨
        pivotCoordinate l (expectedMinimumPrime l : ℝ) =
          pivotCoordinate e (expectedMinimumPrime l : ℝ) + 1 ∨
        pivotCoordinate l (expectedMinimumPrime l : ℝ) =
          pivotCoordinate e (expectedMinimumPrime l : ℝ) - 1) :=
  ⟨sameHeight_pivotCoordinate_dichotomy e l hT _, sameHeight_pivotCoordinate_dichotomy e l hT _⟩

/-! ## 6. Audit -/

#print axioms prime_raccord_has_unique_tower_cell
#print axioms pivotCell_amplitude_brackets
#print axioms horizontalRaccords_amplitude_brackets
#print axioms sameHeight_pivotCoordinate_dichotomy
#print axioms sameCell_four_contacts_bracket
#print axioms horizontal_cell_dichotomy_at_raccords

end RHV6Fresh
