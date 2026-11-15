# Journal de compilation — GapContactRegimes.lean (2026-11-01)

Module isolé `RHV6Fresh/Terminal/GapContactRegimes.lean` (non ajouté à `RHV6Fresh.lean`, chaîne intacte). Consigne de
l'auteur : contacts et formules tangentielles à la base de toute démarche ; raisonner sur la foule des zéros, jamais sur
deux ou trois.

| Tentative | Durée | Résultat | Erreurs exactes |
|---|---|---|---|
| 1 | 18 s | échec | neuf `rw` échouent parce que `z.2` est élaboré en `0 < (↑↑z).im` et non `0 < rZeroHeight z.1` (motif absent) ; `div_div_eq_mul_div` appliqué avant `unfold towerPitch` ; `abs_of_pos` mal appliqué dans `unit_contribution_le_length`. |
| 2 | 16 s | échec | `ring` après un `field_simp` qui fermait déjà (`unit_contribution_vanishes_at_full_periods`) ; `outgoingMember_height` absent (il vit dans `OccurrenceHeightComposition`, non importé). |
| 3 | 16 s | **succès** | aucune. |

Corrections : `have hT : 0 < rZeroHeight z.1 := z.2` partout ; ordre `unfold` puis `rw` ; `rw [one_mul, abs_of_pos]` ;
`ring` supprimé ; `C.outgoing_same_height` à la place. 18 théorèmes, tous `[propext, Classical.choice, Quot.sound]`,
0 `sorry`. Journaux bruts `attempt1..3.log` ici (ignorés par git).
