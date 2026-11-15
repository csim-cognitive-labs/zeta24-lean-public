> Version française conservée à titre de référence. Main language: English, see README.md.

# E449 — Le chemin inverse : des écarts premiers aux contacts, puis au zéro par la formule tangentielle (pré-enregistrement, §19.71, 2026-11-08)

Nouvelle priorité de l'auteur (2026-11-08) : « Reconstitue les contacts depuis les écarts premiers exactement avec toutes
les règles établies. Retrouve les zéros sur la ligne critique pour l'instant si nécessaire… la formule tangentielle te
retrouve β et T du zéro si tu as établi le contact correctement. Chemin inverse : écarts / cassures / zéros. Toutes les
expériences nécessaires et le Lean correspondant si tu trouves quelque chose (root cause et pas constat). »
Ordres maintenus : ban spectral total ; troisième ordre (les contacts lisent β, fréquence ET amplitude) ; aucune
recherche de contradiction OFF ; une Tour à la fois.

## Ce que les règles établies disent des contacts dans les écarts (compilé, E436–E448)
Un premier `p` tombe dans la cellule `k(p) = ⌊(T·log p − φ)/π⌋` (`lastContactBefore`), `φ = arctan(T/β)` la phase
tangentielle (`towerPhase`) ; la cassure `log p` est payée par le dernier contact `C_{k(p)} = p·e^{−π f(p)/T}` (E447) ;
d'un premier au suivant la cellule avance du déplacement exact R1 (E442) et la fraction suit l'orbite d'E448. Le **mot**
d'une Tour sur les premiers est la suite `k(p_n)` (de façon équivalente : les déplacements, c'est-à-dire combien de
contacts chaque écart contient). Question inverse : le mot détermine-t-il la Tour, et par quelle cause ?

## Hypothèses (à décider par le compilateur, puis par le nombre)
* H1 (formule tangentielle, inversion exacte depuis deux contacts) : `T = π / log(C_{k+1}/C_k)` et
  `φ = T·log C_k − kπ`, puis `β = T / tan φ` : deux contacts consécutifs rendent `(β, T)` exactement.
* H2 (encadrement par le mot) : pour tout `x`, `T·log x − π(k(x)+1) < φ ≤ T·log x − π·k(x)` ; chaque premier encadre la
  phase dans une fenêtre de largeur `π` ; le mot sur les premiers encadre `(T, φ)` dans un polygone convexe.
* H3 (fréquence d'abord) : `k(x)/log x → T/π` : la pente du mot rend la fréquence, sans amplitude.
* H4 (cause : les écarts logarithmiques s'annulent, PNT porté) : la fraction de cellule aux premiers approche `0` et `1`
  d'aussi près qu'on veut (`∀ ε, ∃ n, f(p_n) < ε` et `∃ n, f(p_n) > 1 − ε`), parce que les pas de l'orbite
  `T·log(p_{n+1}/p_n)/π` tendent vers `0` (`logGapsVanish_holds`) tandis que la position d'étage est non bornée : à
  chaque franchissement d'un entier par un pas petit, la fraction est petite juste après et proche de `1` juste avant.
* H5 (le mot détermine la phase, puis β) : le polygone de H2 se réduit à un point : `φ = inf_n (T·log p_n − π·k(p_n))` ;
  deux Tours de même mot sur tous les premiers ont même `T`, même `φ`, donc même `β` (formule tangentielle, `β > 0`).
* H6 (ce que le mot ne fait pas, à consigner honnêtement) : H1–H5 valent pour TOUTE Tour `(β, T)`, zéro ou non ; le
  chemin inverse rend la Tour dont on a le mot, il ne dit pas à cette étape pourquoi ce mot est celui d'un zéro.

## Énoncés prévus (module isolé `Terminal/ContactsFromGapsInversion.lean`, import `BreakAmplitudeSequence`, `LogGapsTheorem`)
L1 `frequency_of_two_contacts`, `phase_of_contact`, `beta_of_phase` (`β = T / tan φ`), `tower_of_two_contacts` (H1) ;
L2 `phase_bracket` (H2), `phase_bracket_prime` ; L3 `lastContactBefore_div_log_tendsto` (H3) ;
L4 `cellFraction_small_eventually`, `cellFraction_near_one_eventually` (H4, par `logGapsVanish_holds`) ;
L5 `phase_eq_of_same_word` (H5), `tower_eq_of_same_word` (`T = T' ∧ β = β'`).
Deux tentatives de compilation au plus sur le module définitif, sondes en `*_SCRATCH.lean`, sorties dans `attempts/`.

## Expériences (après compilation ; zéros d'Odlyzko, premiers ≤ 10⁷)
(a) **reconstruction depuis le mot** : pour 6 hauteurs sur la ligne (rangs 1, 10, 10², 10³, 10⁴, 10⁵), le mot `k(p_n)`
est calculé puis OUBLIÉ sauf les entiers ; programme linéaire (2 × 664 578 demi-plans) donnant `[T_lo, T_hi]` et
`[φ_lo, φ_hi]`, puis `[β_lo, β_hi]` par la formule tangentielle ; largeurs en fonction du nombre de premiers utilisés
(10³, 10⁴, 10⁵, 10⁶, 10⁷) ; le vrai `(1/2, T)` doit être dans le polygone ; (b) **contrôle** : trois hauteurs qui ne sont
pas des zéros (milieux entre zéros consécutifs) traitées à l'identique : la reconstruction doit réussir pareil (H6) ;
(c) **cause** : `min f`, `1 − max f` et le pas maximal `T·log(p_{n+1}/p_n)/π` par décade ; (d) **formule tangentielle
exacte** : depuis deux contacts consécutifs calculés, `(β, T)` retrouvés au flottant près. Jumeau mpmath 30 chiffres :
(d) et la largeur de phase sur les premiers ≤ 10⁶ pour deux hauteurs.
Critère : A si le vrai point est toujours dans le polygone, si les largeurs décroissent avec le nombre de premiers et si
(d) est exact ; B si une identité compile mais le nombre contredit ; C sinon. H6 est consignée quelle que soit l'issue.
