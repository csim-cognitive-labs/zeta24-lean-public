# Journal de compilation — `Terminal/RawSpectralChannel.lean` (E406–E411, 2026-11-02)

Commande : `lake env lean RHV6Fresh/Terminal/RawSpectralChannel.lean` puis `lake build RHV6Fresh.Terminal.RawSpectralChannel`.
Lean v4.33.0-rc2, Mathlib du dépôt. Toutes les erreurs sont copiées telles quelles.

## Passage 1 (module complet, 37 déclarations) — 6 erreurs
1. `66:27 Tactic rewrite failed: Did not find x ^ ?y * x ^ ?z … ⊢ x ^ 1 * (x ^ 1) ^ (-(2 * (↑n + 1))) ≤ 1` :
   `rw [← Real.rpow_one x]` a réécrit toutes les occurrences de `x`. Corrigé par une égalité intermédiaire
   `x * x ^ (−a) = x ^ (1 + −a)` (`Real.rpow_add`, `Real.rpow_one`).
2. `168:18 RHV6Fresh.lowCount has already been declared` (clash avec `CountingDeficit.lean`, objet ℕ) : renommé
   `lowMultiplicityCount`. Conséquence : l'erreur `350:2 Type mismatch … ↑(lowCount H)` disparaît avec le renommage.
3. `202:2 No goals to be solved` : `field_simp` fermait déjà le but de `cellTerm_eq_mul` ; `ring` final retiré
   (diagnostiqué au passage 2 : le `ring` superflu était celui de `cellTerm_eq_mul`, pas celui de `hasDerivAt_cellTerm`).
4. `237:12 Unknown identifier norm_image_sub_le_of_norm_hasDerivWithin_le` (deux occurrences, lignes 237 et 257) :
   le lemme vit dans le namespace `Convex` → `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`.

## Passage 2 — 2 erreurs (mauvaise attribution du `ring` superflu)
`204:2 No goals to be solved` (le `ring` après `field_simp` de `cellTerm_eq_mul`) et `207:49 unsolved goals ⊢ -↑m / ↑ρ * ↑y ^ ↑ρ
= -↑m * (↑y ^ ↑ρ / ↑ρ)` (le `ring` retiré à tort dans `hasDerivAt_cellTerm`). Corrigé en échangeant.

## Passage 3 — 0 erreur
`lake env lean` : aucune erreur ; sept `#print axioms` : `[propext, Classical.choice, Quot.sound]`.
`lake build RHV6Fresh.Terminal.RawSpectralChannel` : `Built … (9.1s)`, `Build completed successfully (9039 jobs)`.
Deux avertissements de style corrigés ensuite (une ligne de 102 caractères coupée, un `show` remplacé par `change`) ;
reconstruction verte (voir le commit).

## Tentative E411-1 (ajoutée, compilée, retirée) — le but affiché par le compilateur
Scaffold : `refine riemannHypothesis_of_psiRemainder_at_events ?_ ; intro ε hε ; obtain ⟨H, C₁, C₂, …⟩ : ∃ … := by skip`
puis `abs_psiRemainder_le_of_packets`. Sortie (copiée) :
```
RHV6Fresh/Terminal/RawSpectralChannel.lean:423:80: error: unsolved goals
ε : ℝ
hε : 0 < ε
⊢ ∃ H C₁ C₂,
    0 ≤ C₁ ∧
      0 ≤ C₂ ∧
        (∀ (N : ℕ), 2 ≤ N → ‖localPacket (↑(lowFrequencies H)) N‖ ≤ C₁ * ↑N ^ (1 / 2 + ε)) ∧
          ∀ (N : ℕ), 2 ≤ N → ‖localPacket (↑(lowFrequencies H))ᶜ N‖ ≤ C₂ * ↑N ^ (1 / 2 + ε)
```
(plus deux buts secondaires élémentaires : positivité de la constante, et le cas `E − 1` pour `E = 2`, non poursuivis.)
Verdict par le critère déclaré : MORTE. Le premier conjoint (paquet bas) exige, pour tout `H`, que chaque indice de
hauteur au plus `H` ait sa part de cellule de niveau `N^{1/2+ε}` au plus, c'est-à-dire `β ≤ 1/2 + ε` pour les zéros bas :
circulaire. Le second conjoint est la borne de queue elle-même. La réduction `abs_psiRemainder_le_of_packets` reste
compilée (implication vraie), le théorème `attempt_E411_1` est retiré du module.

## Tentative E411-2 — morte par inspection, sans compilation
Critère déclaré : « si la seconde différence ne contrôle pas le niveau ». E408 borne le paquet bas PAR AU-DESSUS et le
complément PAR AU-DESSOUS (`break_realized_by_high_frequencies` est une minoration). Aucune majoration du niveau du
complément n'en découle, et le télescopage des incrémens ne fournirait qu'un exposant un. Aucun énoncé posé.
