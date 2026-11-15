# E453 — K3 : l'inversion d'E449 appliquée au mot du miroir — pré-enregistrement

Date : 2026-11-08. Statut : pré-enregistré avant toute compilation et toute exécution (§19.75). Direction K3 validée par
l'auteur (« continues avec K3 »). Ordres : ban spectral total (usage et citation ; deux termes seulement, aucune somme de
Tours) ; troisième ordre (contacts lisent `β` ; fréquence ET amplitude) ; R-E446 ; §19.44 ; interdit « amplitude contre
budget » ; aucune prémisse équivalente à RH ; deux tentatives de compilation au plus, chacune journalisée dans `attempts/`.

## Question K3 (§19.74, consignée avant)
E449 a compilé que le mot des écarts détermine la Tour (`T`, `φ`, `β`). La paire exige à la même fréquence deux mots qui
diffèrent exactement sur la fenêtre de K2b. Que donne l'inversion d'E449 appliquée au mot du miroir : rend-elle `(1−β, T)`
(deux Tours lisibles, aucune contradiction) ou exige-t-elle une donnée que les écarts ne portent qu'une fois ?

## Vérification de non-équivalence avec RH (faite avant pré-enregistrement, §19.75.2)
K3 ne pose aucune hypothèse : tous ses énoncés sont des théorèmes pour toute `β ∈ (0,1)`, `T > 0`. Les équivalences
« les deux mots coïncident sur tous les premiers ⟺ `β = 1/2` » et « diffèrent au-delà de tout rang ⟺ `β ≠ 1/2` » relient
deux propriétés d'UNE paire donnée ; aucun des deux côtés n'est posé, rien n'est affirmé sur l'existence de zéros hors ligne.
Le risque identifié en §19.72 (se réduire à l'unicité de la rencontre) est évité : K3 n'utilise que E449 L5 (le mot détermine
la Tour), théorème compilé, jamais une unicité de rencontre. Aucune comparaison avec `log q`, `ψ`, `rawDemand`, une cellule.
Réponse attendue, consignée d'avance : l'inversion rend `(1−β, T)` exactement ; deux Tours lisibles ; le mot du miroir est
FONCTION du mot de la Tour (aucune donnée nouvelle) ; AUCUNE contradiction. Si tel est le résultat, le plan K0–K3 se ferme
sans hypothèse de contradiction, et cela est consigné tel quel ; la décision revient à l'auteur.

## Objet
Paire `(β, T)`, `(1−β, T)` ; mots sur les premiers `k(p_n) = lastContactBefore β T p_n`, `k*(p_n) = lastContactBefore (1−β) T p_n` ;
contacts du miroir `C*_k = contactAt (1−β) T k` ; phase `φ* = towerPhase (1−β) T` ; décalage `δ = mirrorPhaseShift β T`.

## Hypothèses
* H1 (inversion tangentielle du miroir) : `T = π/log(C*_{k+1}/C*_k)` et `1−β = T/tan(T·log C*_k − kπ)`.
* H2 (même fréquence lue par chaque mot) : `k*(p_n)/log p_n → T/π` ; encadrement déterministe
  `|k/log x − T/π| ≤ (|φ| + π)/(π·log x)` pour chaque mot.
* H3 (unicité) : toute Tour `(β', T')`, `β' > 0`, ayant le mot du miroir sur tous les premiers est le miroir : `T' = T`, `β' = 1−β`.
* H4 (aucune donnée nouvelle) : deux Tours de même mot ont des miroirs de même mot ; le mot du miroir est fonction du mot de la Tour.
* H5 (ligne) : `∀ n, k*(p_n) = k(p_n) ⟺ β = 1/2`.
* H6 (hors ligne) : `(∀ N, ∃ n ≥ N, k*(p_n) ≠ k(p_n)) ⟺ β ≠ 1/2` (cause : E449 L4, la fraction approche 0 et 1 au-delà de tout rang).
* H7 (zéro vrai, E451) : H5/H6 au paramètre d'un zéro vrai et de son miroir (`mirrorMember`).

## Énoncés Lean (module isolé `Terminal/PairWordInversion.lean`, imports `PairMeetingImposition` + `ContactsFromGapsInversion`)
L1 `mirror_tower_of_two_contacts`, `mirror_word_slope_tendsto`, `word_slope_bracket` ; L2 `mirror_word_determines_mirror` ;
L3 `mirror_word_of_same_word`, `pair_of_same_word` ; L4 `pair_words_eq_iff` ; L5 `cellFraction_primes_small_and_near_one_from`,
`pair_words_differ_beyond`, `pair_words_differ_beyond_iff` ; L6 `zero_pair_words_eq_iff`, `zero_pair_words_differ_beyond`.

## Expériences
* (a) `scripts/e453a_pair_inversion.py` (numpy) : les 24 couples d'E452 (`β ∈ {0,3 ; 0,4 ; 0,45 ; 0,5}` × zéros de rangs
  1, 10, 100, 1000, 10000, 100000) ; premiers ≤ 10⁷ ; H1 à trois contacts (`10⁻¹⁰` relatif) ; H2 encadrement vérifié sur tous
  les premiers ; polygone d'E449 appliqué au mot du miroir (X = 10⁴, 10⁶) : vrai point `(T, φ*)` dedans ; H4 : mot du miroir
  recalculé depuis `(β, T)` rendus par l'inversion du mot de la Tour, identique au bit ; H5/H6 : nombre de premiers à mots
  distincts par décade (zéro sur la ligne, > 0 à chaque décade hors ligne).
* (b) `scripts/e453b_twin_mpmath.py` : jumeau mpmath 30 chiffres, 10 premiers par couple ; H1, H2, mots ; écart aux valeurs numpy.

## Critère
A : module vert (≤ 2 tentatives), axiomes standards, grep du ban vide, H1 à `10⁻¹⁰`, H2 et H4 sans violation, polygone
contient le vrai point, H5/H6 conformes, jumeau concordant ; B : un point manque (consigné). Aucune hypothèse posée, aucune
contradiction tirée ; si la réponse est « deux Tours lisibles, rien de nouveau », c'est consigné comme fermeture de K3.
