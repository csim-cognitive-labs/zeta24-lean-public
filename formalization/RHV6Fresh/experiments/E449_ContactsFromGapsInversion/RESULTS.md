# E449 — Résultats : le chemin inverse, des écarts premiers aux contacts puis au zéro (§19.71, 2026-11-08)

Pré-enregistrement : `README.md` (commit `d3802a56`, avant toute compilation). Priorité de l'auteur du 2026-11-08.
Ordres maintenus : ban spectral, troisième ordre, aucune contradiction cherchée, une Tour à la fois.

## Partie compilée : `Terminal/ContactsFromGapsInversion.lean` (module isolé, importe `BreakAmplitudeSequence`)
Sondes en brouillon (`E449_SCRATCH.lean`, supprimé) : `attempts/probe1.txt` (7 erreurs : un `push_cast` manquant avant
`ring` ; `tendsto_const_nhds` sans type explicite ; deux `ring` après un `field_simp` qui fermait déjà le but ;
`push_neg` déprécié remplacé par `push Not`), `attempts/probe2.txt` (vert). Module définitif :
`attempts/build_attempt1.txt` **vert à la première tentative** (9092 jobs), 21 déclarations sur
`[propext, Classical.choice, Quot.sound]`. Grep du ban spectral : vide. `lake build RHV6Fresh` complet : vert (9064 jobs).

| bloc | énoncés | ce qui est compilé |
|---|---|---|
| L1 | `phase_of_contact`, `log_contact_ratio`, `frequency_of_two_contacts`, `beta_of_phase`, `tower_of_two_contacts` | **formule tangentielle** : `T = π/log(C_{k+1}/C_k)`, `φ = T·log C_k − kπ`, `β = T/tan φ` ; deux contacts consécutifs rendent `(β, T)` exactement |
| L2 | `stagePosition_mul_pi`, `phase_eq_word_sub_fraction`, `phase_bracket` | en tout point `φ = T·log x − π(k(x) + f(x))` ; le mot seul encadre la phase dans une fenêtre de largeur `π` |
| L3 | `lastContactBefore_div_log_tendsto`, `primes_tendsto_atTop`, `word_slope_tendsto` | **fréquence d'abord** : `k(x)/log x → T/π`, en particulier le long des premiers |
| L4 | `fract_small_and_near_one_of_steps`, `stagePosition_primes_tendsto_atTop`, `stagePosition_primes_step_tendsto_zero`, `cellFraction_primes_small_and_near_one` | **cause** : pas de l'orbite `→ 0` (`logGapsVanish_holds`, PNT porté) et position non bornée ⇒ pour tout `ε`, il existe un premier de fraction `< ε` suivi d'un premier de fraction `> 1 − ε` |
| L5 | `frequency_eq_of_same_word`, `le_of_forall_lt_add_pi_mul`, `phase_le_of_same_word_same_frequency`, `phase_eq_of_same_word`, `beta_eq_of_phase_eq`, `tower_eq_of_same_word` | **le mot détermine la Tour** : deux Tours (`β, β' > 0`) de même mot sur tous les premiers ont même `T`, même `φ`, même `β` |

Hypothèses du pré-enregistrement : H1–H5 compilées (H1 = L1, H2 = L2, H3 = L3, H4 = L4, H5 = L5) ; H6 consignée
(tout vaut pour toute Tour, zéro ou non ; vérifié par les contrôles ci-dessous).

## Expérience chiffrée (`scripts/e449a_inversion.py`, journal `logs/e449a_log.txt`, `data/e449a_results.json`)
Zéros d'Odlyzko (SHA-256 vérifié), `β = 1/2`, premiers ≤ 10⁷ ; le mot `k(p_n)` est calculé puis seuls les entiers sont
gardés ; polygone des `(T, φ)` compatibles avec `phase_bracket` sur les premiers ≤ X (bissection sur la fonction concave
`g`, grille de 2 001 valeurs de `T`) ; `β` par la formule tangentielle sur le polygone.

(a) **Reconstruction depuis le mot, six zéros de la ligne.** Le vrai `(T, φ)` est dans le polygone et `β = 1/2` dans la
plage de `β` pour les 30 couples (hauteur, X). Largeurs à X = 10⁷ (664 579 premiers) :

| rang | T | largeur de T | largeur de φ | plage de β |
|---|---|---|---|---|
| 1 | 14,1347 | 3,0·10⁻⁵ | 4,5·10⁻⁴ | [0,4970 ; 0,5033] |
| 10 | 49,7738 | 2,6·10⁻⁵ | 3,9·10⁻⁴ | [0,4950 ; 0,5146] |
| 10² | 236,5242 | 6,3·10⁻⁶ | 8,8·10⁻⁵ | [0,4863 ; 0,5071] |
| 10³ | 1 419,4225 | 6,1·10⁻⁶ | 8,8·10⁻⁵ | [0,4152 ; 0,5401] |
| 10⁴ | 9 877,7827 | 2,5·10⁻⁵ | 3,9·10⁻⁴ | [−0,92 ; 2,93] |
| 10⁵ | 74 920,8275 | 4,4·10⁻⁵ | 6,8·10⁻⁴ | [−33 ; 17,6] |

Décroissance avec X (rang 1) : largeur de T 5,5·10⁻² (X = 10³), 1,2·10⁻², 1,4·10⁻³, 1,7·10⁻⁴, 3,0·10⁻⁵ (X = 10⁷) ;
largeur de φ 0,35 → 4,5·10⁻⁴ ; plage de β [−0,90 ; 4,07] → [0,4970 ; 0,5033]. Même décroissance à tous les rangs.
**Lecture.** La fréquence est rendue par le mot avec une précision qui ne dépend presque pas de la hauteur ; la phase est
rendue dans une fenêtre qui se referme avec X ; `β = T/tan φ` amplifie la largeur de phase par `T` environ (la phase est
voisine de `π/2`) : au rang 1, `β` est retrouvé à ±0,003 ; au rang 10⁴ la plage de `β` reste large de 3,8 avec 664 579
premiers. C'est la lecture par la position seule (quelle cellule) ; elle rend `T` d'abord, `φ` ensuite, et `β` seulement
quand `T` est petit ou le nombre de premiers immense : conforme au troisième ordre (la lecture exacte de `β` passe par
l'amplitude, non par la seule position).

(b) **Contrôles (H6).** Trois hauteurs qui ne sont PAS des zéros (milieux entre zéros consécutifs aux rangs 1, 100, 10⁴) :
reconstruction identique (vrai point dedans, largeurs à X = 10⁷ : T 4,1·10⁻⁵ / 3,0·10⁻⁵ / 1,4·10⁻⁵, β au rang 1
[0,4950 ; 0,5062]). **Le mot rend la Tour dont il est le mot, zéro ou non** : rien, à cette étape, ne distingue le mot d'un
zéro ; consigné d'avance (H6), confirmé.

(c) **Cause.** Fenêtre de phase à `T` exact = `π·(min f + 1 − max f)` : rang 1, 2,5·10⁻² (X = 10³) → 2,3·10⁻⁵ (X = 10⁷) ;
`min f` 2,7·10⁻⁴ → 2,0·10⁻⁷, `1 − max f` 7,6·10⁻³ → 7,0·10⁻⁶ ; pas maximal de l'orbite dans la dernière décade 0,53 →
4,4·10⁻⁴ (rang 1), 2,8·10³ → 2,3 (rang 10⁵) : les pas s'annulent (écarts logarithmiques, PNT porté) et la fenêtre se
referme, comme compilé en L4. La largeur de φ du polygone (4,5·10⁻⁴ au rang 1) dépasse cette fenêtre (2,3·10⁻⁵) parce que
`T` n'est lui-même connu qu'à 3·10⁻⁵ près et que `T·log p` porte cette incertitude.

(d) **Formule tangentielle depuis deux contacts** (flottant double) : `T` retrouvé à 10⁻¹⁵–10⁻¹³ près aux rangs ≤ 10²,
`φ` à 10⁻¹⁵–10⁻¹², `β` à 4·10⁻¹⁴ (rang 1, k = 2) ; l'erreur sur `β` croît comme `T·(erreur sur φ)` : 1,3·10⁻⁷ (rang 10²),
9·10⁻³ (rang 10⁴), 3,7 (rang 10⁵, k ≈ 3,8·10⁵) — perte de précision du flottant sur `T·log C_k`, pas de la formule : le
jumeau à 30 chiffres la rend exacte (ci-dessous).

## Jumeau (`scripts/e449b_twin_mpmath.py`, 30 chiffres, sympy, journal `logs/e449b_log.txt`, `data/e449b_twin.json`)
Rangs 1 et 100, premiers ≤ 10⁶, polygone recalculé indépendamment (bissection 60 pas, grille 41 points) :
* rang 1 : `T ∈ [14,134629079233 ; 14,134796829721]`, `φ ∈ [1,5342316617 ; 1,5363640115]`, `β ∈ [0,48689 ; 0,51706]` ;
  écarts avec e449a (X = 10⁶) : 1,8·10⁻¹⁴ et 1,6·10⁻¹⁴ sur les bornes de `T`, 2,1·10⁻¹³ et 1,9·10⁻¹³ sur celles de `φ` ;
  formule tangentielle : erreur sur `β` 2,4·10⁻²⁷ ; `ok = True`.
* rang 100 : `T ∈ [236,524178937654 ; 236,524237393244]`, `φ ∈ [1,5680331273 ; 1,5687823742]`, `β ∈ [0,47635 ; 0,65357]` ;
  écarts avec e449a : 0 et 0 sur `T`, 4,3·10⁻¹⁴ et 3,4·10⁻¹⁴ sur `φ` ; formule tangentielle : erreur sur `β` 1,5·10⁻²³,
  vrai point dedans ; **`ok = False`** parce que le seuil pré-écrit dans le script pour l'erreur tangentielle était
  10⁻²⁴ : à 30 chiffres, `T·log C_k ≈ 3 800` consomme quatre chiffres et `β = T/tan φ` en consomme encore (phase voisine de
  `π/2`) ; 1,5·10⁻²³ est la précision attendue de l'arithmétique, pas un défaut de la formule. Le script n'a pas été relancé
  avec un seuil élargi : le drapeau `all_ok = False` du jumeau est conservé tel quel et expliqué ici.

## Verdict
**A** sur les critères pré-enregistrés : vrai point toujours dans le polygone (30 couples zéros + 15 couples contrôles),
largeurs décroissantes avec le nombre de premiers à toutes les hauteurs, formule tangentielle exacte à la précision de
l'arithmétique (flottant puis 30 chiffres), polygone identique entre les deux calculs indépendants à 10⁻¹³ près. Réserve
consignée : drapeau du jumeau au rang 100 faux par seuil trop strict (voir ci-dessus).

## Ce que cela établit (cause, pas constat) — et ce que cela ne dit pas
1. **Le mot des écarts détermine la Tour** (`tower_eq_of_same_word`) : savoir dans quelle cellule tombe chaque premier
   (combien de contacts chaque écart contient) fixe `T` (pente du mot, `word_slope_tendsto`), puis `φ` (la fenêtre de
   phase se referme parce que les pas de l'orbite s'annulent — `logGapsVanish_holds`, PNT porté — et que la position
   d'étage est non bornée : `cellFraction_primes_small_and_near_one`), puis `β` par la formule tangentielle
   (`beta_of_phase`). La cause est arithmétique et compilée : l'annulation des écarts logarithmiques.
2. **Deux contacts exacts rendent `(β, T)` exactement** (`tower_of_two_contacts`) : c'est la formule tangentielle de
   l'auteur, compilée ; le chiffre la confirme à 10⁻²⁷ en 30 chiffres.
3. **Ce que la position seule ne fait pas** : `β = T/tan φ` amplifie la fenêtre de phase par `T` ; avec 664 579 premiers,
   `β` est rendu à ±0,003 au rang 1 et pas du tout au rang 10⁴. La lecture exacte de `β` depuis les cassures demande
   l'amplitude aux contacts (troisième ordre), non la seule cellule.
4. **H6, confirmée** : le chemin inverse rend la Tour dont on a le mot, zéro ou non (contrôles identiques). Rien, à cette
   étape, ne dit pourquoi le mot observé est celui d'un zéro ; aucune conclusion n'est tirée sur les OFF (ordre), aucune
   obligation n'est proposée.
