# Audit interne de conclusion — RHV6Fresh (2026-10-03)

Sur ordre de l'auteur : relire CLAUDE.md, les trois maîtres et l'historique du maître sémantique ; dresser la liste
des pistes épuisées et des pistes ouvertes ; analyser les figures et l'ensemble des expériences ; conclure.
Le lemme de variation quadratique locale proposé par l'auteur le même jour est traité au §4 et compilé
(`Terminal/QuadraticVariation.lean`).

L'audit a été fait par trois lectures parallèles, puis contrôlé contre le code :
- l'historique (83 commits du maître sémantique, 137 de CLAUDE.md, 283 commits RHV6 depuis le 2026-09-20) ;
- les expériences (E075–E163 dans `experiments/`, E001–E074 dans `docs/experiments/` et `research/`) ;
- les figures (38 PNG).

## 1. Ce que le programme a produit

- **Code.** 96 fichiers Lean, 1237 théorèmes, 196 objets. Aucun `sorry`, aucun axiome ajouté. Build PASS.
- **Caractérisation finale compilée.** RH ⟺ aucun zéro de côté inférieur, et RH ⟺ la prémisse unique « aucun
  changement de régime ».
- **Réductions compilées vers des formes classiques.** RH ⟺ reste lissé `≤ C√x` ⟺ `θ* = 1/2`. Ce sont des équivalents
  du critère de von Koch, obtenus à partir des seuls premiers.
- **Géométrie complète d'un membre.** Une Tour est le terme `x^ρ/ρ` de la formule explicite. À l'échelle `√x`, c'est un
  cercle en ligne ; hors ligne, une paire est un couple de spirales miroir de même rotation et de dérives opposées.
  Chaque Tour lit le signe de sa profondeur.
- **Obstructions compilées.** Ce sont des énoncés vrais dans des mondes qui ont des zéros hors ligne : `W_δ`,
  `regimeWitness`, `engagedBreakWorld`, et le monde de signes cohérents.

## 2. Historique : comment chaque direction s'est fermée

Le détail chronologique (phases A à H, du 2026-09-22 au 2026-10-03, avec les commits) a été vérifié sur `git log`. Les
pistes se ferment toujours selon l'un de cinq motifs.

| Motif de clôture | Nombre | Exemples |
|---|---|---|
| (a) Reformulation ⟺ RH | ≈ 15 | `PNoRegimeChange`, absence d'entrée horizontale, fibres singletons, représentation en ligne, borne `√x`, `θ* = 1/2`, flèche d'entrée + amorce, conservation, exclusion horizontale, poussée verticale |
| (b) Vraie dans un monde témoin, donc non séparante | ≈ 16 | réponse radiale au premier ordre, phase, positivité/Landau, diagonale, `Tr`, grammaire mod 6, mots, interaction, boucle miroir, système rigide global |
| (c) Certificat ou lecture d'un membre donné, pas une contrainte | ≈ 15 | fibre multiple, écart à la ligne, bit de changement, pente, symétrie à quatre secteurs, étalon de boucle, signe de courbure, compensation |
| (d) Réfutation numérique | ≈ 7 | E089/E090, E111, E146-H2, E147, E151, E112, E156 |
| (e) Verdict de l'auteur | ≥ 10 | course `lineValue`, Perron/RvM, `ΔT_min`, route `Li`, paquet nu, Mellin hors build |

Trois renversements de méthode ont eu lieu :
- 2026-09-25 : le code compilé devient l'autorité ;
- 2026-09-29 : ménage de treize fichiers et de dix prémisses ;
- 2026-10-02 : maîtres purgés en quatorze sections.

Aucun de ces renversements n'a changé la frontière, qui est restée la même depuis le 2026-09-30 : la borne en `√x`
du reste arithmétique.

## 3. Expériences et figures

**Expériences.** Environ 100 identifiants sous RHV6 (E075–E163), plus E001–E074 de l'époque RHV5. Classement :

| Classe | Nombre approximatif |
|---|---|
| Réfute une hypothèse | ≈ 25 |
| Ne sépare pas | ≈ 30 |
| Sépare par le poids exact Λ | ≈ 9 |
| Sépare par l'amplitude | ≈ 6 |
| Sépare par le comptage | ≈ 2 |
| Contrôle ou figure | ≈ 25 |

- **Seules couches séparatrices :** la taille exacte du poids et le comptage. Les autres « séparations » portent sur
  l'amplitude d'un β choisi à la main : elles valident l'algèbre, pas un fait sur ζ.
- **Aucun monde à poids exacts signés avec des membres hors ligne n'existe comme contrôle.** Ce serait ζ elle-même,
  c'est-à-dire un contre-exemple.
- **Faiblesses de méthode :**
  - la plupart des scripts antérieurs à E163 n'ont pas d'assertions internes ;
  - les numéros E117–E121 ont chacun deux versions ;
  - quelques durées citées dans CLAUDE.md diffèrent d'une seconde des sorties.

  Aucune contradiction numérique entre expériences n'a été trouvée : les écarts apparents tiennent à des lectures
  différentes (V lu en avant ou à rebours, M contre C⁺, invariance de `Tr` limitée à `W_δ`).

**Figures.**
- Toutes sont cohérentes avec la théorie : cercle de rayon `1/|ρ|` à l'échelle `√x`, dérive `e^{±dπ/T}` par demi-tour,
  contacts tous les `π/T` en `log x`.
- **Aucune figure ne montre de différence ON/OFF autre que la dérive radiale.** Le décalage de phase est inférieur à
  `1/(πT)` cellule. E151 et E115-C lisent la hauteur et le comptage.
- E163 et E088d sont les seules figures de référence. E088c (sans axes) est remplacée par E088d.
- Défauts de présentation sans effet sur les conclusions :
  - titre tronqué (E117-1) ;
  - titres superposés (E120) ;
  - ordonnée tronquée (E121) ;
  - décalage invisible (E119) ;
  - axes non commensurables (E115-C).

## 4. Le lemme de variation quadratique locale (proposition de l'auteur, 2026-10-03) : calculé, compilé, tranché

**Énoncé à trancher.** On compare une paire séparée à sa référence fusionnée sur la ligne (le double de même
hauteur), sur une même fenêtre. La variation d'énergie est-elle « excès propre + terme croisé », avec un terme croisé
nul ou de signe forcé par la structure multiplicative et le miroir ?

**Résultat compilé** (`Terminal/QuadraticVariation.lean`, 15 théorèmes, axiomes standard) :

1. **Décomposition exacte.** Variation = (énergie de la paire − énergie du double) + 2⟨atome, complément⟩
   (`windowVariation_split`).
2. **Excès propre.** En chaque point il vaut `q(4κ + κ²)`. Il est `≥ 0`, et nul ⟺ `d log q = 0`
   (`pair_self_excess_eq`, `pair_self_excess_eq_zero_iff`, `window_self_excess_nonneg`). L'intuition de l'auteur est
   juste : l'excès symétrique de second ordre est strict.
3. **Le complément s'élimine exactement, mais le terme croisé ne disparaît pas.** Le reste total `R` est fixé par les
   premiers, donc le complément vaut `R − paire`, et la variation vaut `2⟨atome, R⟩ − E(atome)`
   (`windowVariation_via_remainder`, `complement_cross_eq_remainder_cross`). Le terme croisé devient
   `Σ μ(q) κ_q(d) Re(q^{1/2+iT} R̄(q))` (`remainder_cross_curvature`) : une lecture du reste arithmétique à la
   fréquence de la paire, pondérée par la courbure.
4. **Ni le miroir ni l'algèbre ne le fixent.** Il est pair en `d`, donc dans le canal symétrique dont dispose le côté
   arithmétique (`remainder_cross_even`). Pour tout atome non nul, toute valeur réelle est atteinte par un complément
   (`cross_term_unconstrained`).

**Verdict sur l'embranchement binaire posé par l'auteur : le terme croisé reste libre.**
- Le déterminer, c'est savoir si le reste contient la paire. C'est la lecture du pôle, déjà compilée
  (`cpow_series_growth_fibre_zero`, `radial_le_of_remainder_growth`).
- Le borner pour toutes les hauteurs et toutes les profondeurs, c'est la croissance critique du reste [⟺RH].

**Deux points de plus ferment la voie :**
- **La référence fusionnée, avec le même complément, n'est pas un monde arithmétique.** Par l'unicité spectrale
  compilée (`no_intruder`, `recovers_member`), aucune représentation à poids `Λ` n'a d'autres membres. Une « variation
  à poids premiers fixés » n'existe donc pas : la comparaison oppose ζ à une fonction sans produit d'Euler.
- **L'hypothèse « les poids exacts sont d'énergie minimale parmi les représentations miroir de la même histoire »**
  est vide aux poids exacts, où la représentation est unique. Elle est fausse au niveau diagonal : le monde de signes
  cohérents de E155 a même support et même `|w| = Λ`, donc la même énergie diagonale terme à terme, et il porte des
  membres hors ligne (`diagonal_sign_blind`, `signedWorld_diagonal_linear`). Le surplus de `W_δ` vient de la taille de
  ses poids (`shiftedWorld_weight_sq_eq_iff`), pas de la séparation de ses membres.

Selon le critère même de l'auteur (« s'il reste libre, la voie locale B est bloquée »), **la voie locale B est close**.

## 5. Pistes épuisées

Toutes les pistes du §13 des trois maîtres sont épuisées, plus celle-ci :

- **Géométrie et Tours.** Seconde Tour, pivot, collisions ; orientation du demi-tour ; numéro et place de cellule ;
  premier partagé ; enroulement, fréquence, résolution ; symétries (paire recentrée, quatre secteurs, Tour entière) ;
  boucle miroir et jauge ; canal antisymétrique.
- **Grammaire.** Mod 6, états, transitions, mots, canaux, alternance, premiers pointés, dette miroir d'un mot.
- **Énergie.** Poussée verticale, équilibres aux raccords, énergie du quartet, carré « qui élimine les compensations »,
  diagonale, loi de partage diagonale/croisés, survie globale, rigidité de compensation sur l'histoire, et variation
  quadratique locale (§4).
- **Reste et exposant.** Positivité et Landau, `Li` comme contenu de cellule, platitude du transport entre hauteurs,
  accumulation radiale sur les écarts.
- **Fenêtre.** Fenêtre minimale sur les premiers partagés, ordre 1 côté premier, horizon fixé, comptage, signes de `Z`
  et rang contre le double, interaction des continuations, stabilité sous raffinement.
- **Global.** Système rigide global, compensation par le complément, budget zeta23 (même porté à 1, il est aveugle à
  une paire isolée).
- **Prémisses.** Les treize prémisses retirées et leurs caractérisations ⟺ RH.

## 6. Pistes ouvertes

À l'intérieur du programme, **aucune piste locale n'est ouverte**. Tout ce qui reste ouvert est global et classique :

1. **La croissance critique du reste**, sous l'une de ses formes équivalentes compilées : `θ* = 1/2`, reste lissé
   `≤ C√x`, prémisse unique. C'est RH sous la forme de von Koch.
2. **La voie de la somme des Tours par Mellin**, parquée hors build. Elle opère à l'échelle de la somme, donc sur le
   même énoncé global.
3. **Hors build, zeta23.** La proportion de zéros simples en ligne est `> 2/3`. Elle ne peut pas exclure une paire.

Toute nouvelle piste doit passer un double filtre :
- être **fausse dans le monde décalé et dans le monde de signes cohérents** ;
- **ne pas se réduire** à une lecture du reste à une fréquence donnée.

Aucune piste candidate connue ne passe ce filtre.

## 7. Conclusion

1. Le programme RHV6 a réduit RH, par des théorèmes compilés, à un seul énoncé : la croissance critique du reste
   arithmétique exact. C'est un énoncé global sur la taille exacte et l'organisation signée des poids de von Mangoldt.
2. Le programme a établi, par des mondes témoins compilés, que **toute loi locale formée des couches qu'il manipule**
   (géométrie, grammaire, comptage, positivité, diagonale, symétries, compensation, variation d'énergie) **est soit
   vraie dans un monde à zéros hors ligne, soit équivalente à cette croissance, soit un certificat d'un membre donné**.
3. **Le lemme de variation quadratique locale, dernier candidat, est tranché.** Son terme croisé est la lecture du
   reste à la fréquence de la paire. Il n'est fixé par aucune identité.
4. **RH_FOUND = FALSE.** Les outils du programme ne contiennent pas l'ingrédient qui manque. Continuer à ouvrir des
   pistes locales (E164, E165, …) n'a pas d'objet : chacune retomberait dans l'une des trois classes ci-dessus.
5. **Recommandation : clore le chantier.**
   - Livrer le corpus pour ce qu'il est : une bibliothèque compilée de réductions et d'obstructions. Son résultat
     principal est un énoncé d'obstruction : toute loi vraie dans `W_δ`, `regimeWitness` ou le monde de signes
     cohérents ne peut pas impliquer RH.
   - Ne reprendre que si un ingrédient analytique nouveau sur les poids exacts (une majoration du reste à toutes les
     fréquences) est apporté de l'extérieur. Un tel ingrédient serait une démonstration de RH, non une piste locale.
