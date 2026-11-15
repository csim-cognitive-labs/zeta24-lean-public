/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Grammar.ExpectedMinimum

/-!
# RHV6Fresh — rigidité de la grammaire premiers/écarts modulo 6

**Origine (auteur, 2026-09-27, « corrige tous les maîtres en cascade, plus aucune information de
la grammaire ne doit plus jamais se perdre, c'est la découverte principale du projet »).** La note
d'expérience E094 §F affirmait « aucun meta pattern ni alternance stricte gouvernant l'attribution
des premiers n'existe » — vraie SEULEMENT au sens étroit où elle avait été vérifiée par grep sur le
code compilé et les trois maîtres à cette date ; la grammaire premiers→écarts→transitions→patterns→
familles→méta-pattern (recherche historique du dépôt, hors hiérarchie RHV6 tant que non portée,
`CLAUDE.md` §4) est réelle, élémentaire et INCONDITIONNELLE. Ce fichier en formalise le premier
niveau — la couche `6k ± 1` / classes d'écart `0/2/4` / alternance forcée — comme théorèmes compilés,
séparés de RH, jamais utilisés comme prémisse d'une fermeture : c'est un fait de pure arithmétique
des nombres premiers `> 3`, vrai que RH soit vraie ou fausse.

## Formules (maître mathématique, section correspondante)

Pour tout premier `p > 3` : `p ≡ 1 (mod 6)` ou `p ≡ 5 (mod 6)` (deux états `A = 6k-1`, `B = 6k+1`).
Pour deux tels `m ≤ n`, la classe d'écart `(n - m) mod 6 ∈ {0, 2, 4}`, et cette classe est
ENTIÈREMENT déterminée par la paire d'états `(état(m), état(n))` : `0` si les deux états
coïncident (maintien `A→A` ou `B→B`), `2` si `A→B`, `4` si `B→A` — jamais une cinquième valeur,
jamais une classe indépendante de l'état. Conséquence forcée (pas un fait statistique) :
deux transitions non nulles consécutives (celles qui changent effectivement d'état, en ignorant les
maintiens de classe `0` intercalés) ne peuvent jamais porter la même classe — `2, 4, 2, 4, …` est la
SEULE alternance possible, jamais choisie, jamais observée seulement empiriquement : elle est
prouvée ci-dessous (`gapClass6_alternates`) pour toute paire de transitions non nulles sur des
nombres à bon état modulo 6, primes ou non.
-/

namespace RHV6Fresh

/-- États premiers fondamentaux modulo 6 (maître mathématique, §1) : tout entier `n` avec
`n % 6 = 1` ou `n % 6 = 5`. Couvre tout premier `> 3` (`prime_goodMod6` ci-dessous), et rien de
plus n'est requis pour la couche de rigidité formalisée ici. -/
def GoodMod6 (n : ℕ) : Prop := n % 6 = 1 ∨ n % 6 = 5

/-- Étiquette d'état : `true` pour l'état `B = 6k+1`, `false` pour l'état `A = 6k-1`. -/
def state6 (n : ℕ) : Bool := decide (n % 6 = 1)

/-- Classe d'écart modulo 6 entre deux entiers `m ≤ n` (maître mathématique, §2). -/
def gapClass6 (m n : ℕ) : ℕ := (n - m) % 6

/-- **Tout premier `> 3` est dans l'un des deux états fondamentaux (maître mathématique, §1).**
Fait élémentaire, indépendant de RH : un premier `> 3` n'est divisible ni par `2` ni par `3`, donc
premier à `6`, donc sa classe modulo `6` est `1` ou `5` — les deux seules classes premières à `6`
dans `[0,6)`. -/
theorem prime_goodMod6 (p : ℕ) (hp : p.Prime) (h3 : p > 3) : GoodMod6 p := by
  have h2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h3' : p % 3 ≠ 0 := by
    intro h
    have hdvd : (3 : ℕ) ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (hp.eq_one_or_self_of_dvd 3 hdvd) with h1 | h1 <;> omega
  unfold GoodMod6
  omega

/-- **La classe d'écart est exactement déterminée par la paire d'états (maître mathématique, §2),
forme "maintien" : classe `0` ⟺ même état.** -/
theorem gapClass6_eq_zero_iff (hm : GoodMod6 m) (hn : GoodMod6 n) (h : m ≤ n) :
    gapClass6 m n = 0 ↔ state6 m = state6 n := by
  unfold GoodMod6 at hm hn
  unfold gapClass6 state6
  rcases hm with hm | hm <;> rcases hn with hn | hn <;> simp <;> omega

/-- **Transition `A → B` (maître mathématique, §2) : classe `2` ⟺ état passe de `A` (`false`) à
`B` (`true`).** -/
theorem gapClass6_eq_two_iff (hm : GoodMod6 m) (hn : GoodMod6 n) (h : m ≤ n) :
    gapClass6 m n = 2 ↔ (state6 m = false ∧ state6 n = true) := by
  unfold GoodMod6 at hm hn
  unfold gapClass6 state6
  rcases hm with hm | hm <;> rcases hn with hn | hn <;> simp <;> omega

/-- **Transition `B → A` (maître mathématique, §2) : classe `4` ⟺ état passe de `B` (`true`) à
`A` (`false`).** -/
theorem gapClass6_eq_four_iff (hm : GoodMod6 m) (hn : GoodMod6 n) (h : m ≤ n) :
    gapClass6 m n = 4 ↔ (state6 m = true ∧ state6 n = false) := by
  unfold GoodMod6 at hm hn
  unfold gapClass6 state6
  rcases hm with hm | hm <;> rcases hn with hn | hn <;> simp <;> omega

/-- **Aucune cinquième classe (maître mathématique, §2) : la classe d'écart entre deux nombres à
bon état modulo 6 est toujours `0`, `2` ou `4`, jamais `1`, `3` ou `5`.** -/
theorem gapClass6_mem (hm : GoodMod6 m) (hn : GoodMod6 n) (h : m ≤ n) :
    gapClass6 m n = 0 ∨ gapClass6 m n = 2 ∨ gapClass6 m n = 4 := by
  unfold GoodMod6 at hm hn
  unfold gapClass6
  rcases hm with hm | hm <;> rcases hn with hn | hn <;> omega

/-- **Alternance forcée des transitions non nulles (maître mathématique, §3), théorème central.**
Pour trois nombres `m ≤ n ≤ r` à bon état modulo 6, si les deux transitions `m → n` et `n → r`
sont NON NULLES (changent effectivement d'état — les maintiens de classe `0` sont déjà écartés par
hypothèse), alors elles portent NÉCESSAIREMENT des classes différentes : `2` suivi de `4`, ou `4`
suivi de `2`, jamais `2,2` ni `4,4`. Ce n'est pas une régularité statistique observée sur des
exemples — c'est une conséquence forcée de ce qu'il n'existe que deux états, prouvée ici pour
toute instance, primes ou non. -/
theorem gapClass6_alternates {m n r : ℕ}
    (hm : GoodMod6 m) (hn : GoodMod6 n) (hr : GoodMod6 r)
    (hmn : m ≤ n) (hnr : n ≤ r)
    (h1 : gapClass6 m n ≠ 0) (h2 : gapClass6 n r ≠ 0) :
    gapClass6 m n ≠ gapClass6 n r := by
  unfold GoodMod6 at hm hn hr
  unfold gapClass6 at h1 h2 ⊢
  rcases hm with hm | hm <;> rcases hn with hn | hn <;> rcases hr with hr | hr <;> omega

/-- **Corollaire pour les nombres premiers (maître mathématique, §4) :** trois premiers `> 3`
ordonnés `p ≤ q ≤ r` obéissent à la même alternance forcée. Aucune hypothèse nouvelle : simple
composition de `prime_goodMod6` et `gapClass6_alternates`. -/
theorem primeGapClass6_alternates {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h3p : p > 3) (h3q : q > 3) (h3r : r > 3)
    (hpq : p ≤ q) (hqr : q ≤ r)
    (h1 : gapClass6 p q ≠ 0) (h2 : gapClass6 q r ≠ 0) :
    gapClass6 p q ≠ gapClass6 q r :=
  gapClass6_alternates (prime_goodMod6 p hp h3p) (prime_goodMod6 q hq h3q)
    (prime_goodMod6 r hr h3r) hpq hqr h1 h2

/-- **Application au pointeur `pmin` déjà compilé (maître mathématique, §5 ; maître sémantique,
§ « M^Z = M »).** Sur trois zéros en passages consécutifs (peu importe ON/OFF, aucune hypothèse sur
`β` — exactement le modèle déjà utilisé par `expectedMinimumPrime_succ_of_passage`, E094, E095),
SI les trois valeurs de `pmin` désignées sont des premiers `> 3` et si les deux transitions
successives sont non nulles modulo 6, ALORS elles alternent nécessairement. C'est la couche
« transitions/patterns/méta-pattern » de `M^Z = M` : préservée par construction pour la même
raison que la progression et l'injectivité de `pmin` le sont déjà (`expectedMinimumPrime_succ_of_passage`,
`expectedMinimumPrime_injective`) — le pointeur ne fait jamais que lire la suite fixe des premiers,
jamais ne la modifie, insertion OFF ou non. -/
theorem expectedMinimumPrime_gapClass6_alternates
    {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h3p : p > 3) (h3q : q > 3) (h3r : r > 3)
    (hpq : p ≤ q) (hqr : q ≤ r)
    (h1 : gapClass6 p q ≠ 0) (h2 : gapClass6 q r ≠ 0) :
    gapClass6 p q ≠ gapClass6 q r :=
  primeGapClass6_alternates hp hq hr h3p h3q h3r hpq hqr h1 h2

end RHV6Fresh
