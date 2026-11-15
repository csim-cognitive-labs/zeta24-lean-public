# Journal de compilation — `Terminal/RawMeetingRemainder.lean` (2026-11-02)

Trois passages du compilateur, tous consignés avec les erreurs exactes. Module isolé (non importé par
`RHV6Fresh.lean`), aucun `sorry`, aucun axiome hors `propext`, `Classical.choice`, `Quot.sound`.

## Tentative 1 — échec (erreurs du compilateur)
- `RHV6Fresh.rawRemainder has already been declared` : le nom existe déjà dans le corpus
  (`FirstGainPremise.lean`, objet réel `chebyshevMidpoint − rawBackground`). Renommé `psiRemainder`
  (entier, `ψ(N) − N`, sans fond). Les erreurs suivantes (`massA (?N + 1)` non trouvé, `psiRemainder 0`
  non trouvé, « type mismatch » sur `↑(Nat.find hex − 1)`) étaient toutes des conséquences de ce clash.
- `natMul_smoothedVonMangoldtSum_eq` : `norm_cast` a produit `NNRat.divNat` et `Int.subNatNat`
  (but non fermé : `↑M * Λ n - ↑M * Λ n * ↑(NNRat.divNat n M) = Λ n * ↑(Int.subNatNat M n)`).
  Remplacé par `rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]; congr 1` puis `field_simp`.
- `Unknown identifier le_or_lt` (deux fois) : remplacé par `le_or_gt`.
- `No goals to be solved` après `norm_num` dans `hhalf2` : `norm_num` fermait déjà le but.
- `push_neg` déprécié : remplacé par `push Not at hcon`.

## Tentative 2 — une seule erreur
- `linarith failed` (ligne 352) dans `mem_remainderExponents_of_psiRemainder` : les hypothèses `e1`, `e2`
  portaient la constante développée `C + 1/2 + backgroundConstant` alors que le but portait le nom `C'`
  introduit par `set` ; `linarith` les lisait comme des atomes distincts. Corrigé par `rw [hC'def]`.
  Tout le reste compilait ; les `#print axioms` des énoncés en aval affichaient `sorryAx` uniquement
  par propagation de cette erreur.

## Tentative 3 — le manque unique, tranché par le compilateur
Énoncé ajouté temporairement en fin de module, puis retiré (aucun `sorry` dans le module engagé) :
```lean
theorem riemannHypothesis_from_raw_meetings : RiemannHypothesis := by
  refine riemannHypothesis_of_psiRemainder_at_events ?_
```
Sortie exacte du compilateur :
```
RawMeetingRemainder.lean:474:67: error: unsolved goals
⊢ ∀ (ε : ℝ),
    0 < ε →
      ∃ C,
        0 ≤ C ∧
          ∀ (E : ℕ),
            IsRawEvent E → |psiRemainder E| ≤ C * ↑E ^ (1 / 2 + ε) ∧ |psiRemainder (E - 1)| ≤ C * ↑E ^ (1 / 2 + ε)
```
C'est le seul but ouvert : la borne du reste brut `ψ(E) − E`, des deux côtés de chaque rencontre brute
`E` (premier ou puissance de premier), d'exposant `1/2 + ε`, depuis les seuls premiers. Tout le reste
de la chaîne (rencontres → entiers → reste lissé → position radiale → RH) est compilé.

## Passage final
`lake build RHV6Fresh.Terminal.RawMeetingRemainder` : `Build completed successfully`, 22 déclarations,
axiomes standard sur les six énoncés imprimés.
