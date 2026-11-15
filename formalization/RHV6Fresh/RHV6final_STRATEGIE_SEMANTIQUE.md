# RHV6 — MAÎTRE SÉMANTIQUE

Version purgée du 2026-10-02. Ce document est écrit en mots seuls : aucune formule, aucun nom du code. Les
formules sont dans le maître mathématique, les noms et l'inventaire dans le maître Lean. Chaque énoncé est
dit avec sa portée exacte : « compilé » signifie qu'un théorème du code l'établit, avec les hypothèses que son énoncé déclare le cas échéant ;
« équivaut à la cible » signifie qu'une équivalence compilée le relie à l'hypothèse de Riemann sans le
démontrer ; « non compilé » et « non dérivé » disent ce qui manque. L'historique des versions est dans le
journal git ; il n'est pas recopié ici.

## 1. Autorité, périmètre et méthode

**Objectif unique.** Un terme compilé, inconditionnel, dont le type est exactement l'hypothèse de Riemann,
dans le projet RHV6Fresh. Ce terme ne dépend que des trois axiomes standard ; il ne contient aucun trou de
preuve, aucun axiome ajouté, aucune hypothèse non déchargée. Aucun tel terme ne compile à ce jour.

**Hiérarchie.** Premièrement, le code compilé du projet RHV6Fresh : un théorème compilé est vrai et ne se
conteste pas. Deuxièmement, le port dans ce projet de la réflexion de zêta validée par Lean et par des
mathématiciens : il est incontestable. Troisièmement, les trois maîtres, alignés sur le code après coup :
en cas de conflit avec un théorème compilé, c'est le maître qui est corrigé. Aucune interdiction d'un maître
ne prévaut contre un énoncé compilé.

**Périmètre du code.** Le projet RHV6Fresh n'a qu'une dépendance de preuve : sa base compilée, le projet
RHV3, qui fournit les zéros, la formule explicite, la fonction de Tchebychev et les objets premiers, et qui
fait partie de l'autorité de premier rang ; au-dessous, la bibliothèque mathématique standard. Aucun autre
projet du dépôt n'est une dépendance : ni RHV5, ni RHV2, ni RHV4, ni le critère d'écart. Leurs théorèmes
peuvent être cités comme précédents historiques ; ils n'ont aucune autorité ici et ne sont jamais importés.
Les répertoires de compilation ne sont jamais versionnés.

**Vocabulaire de portée.** Un théorème qui classe un objet déjà donné le caractérise : il ne le décide pas
et ne le génère pas. Une équivalence avec la présence d'un zéro hors ligne est un certificat : ce n'est ni
un déclencheur ni une cause. Une fonction qui garantit par changement de signe l'existence d'un zéro est un
détecteur par existence, pas un générateur. La ligne critique est le lieu fixe de la réflexion. Ne jamais
écrire « la cible, c'est l'hypothèse de Riemann » d'une loi locale : seule la forme globale de la prémisse
lui est équivalente (section 11).

**Méthode.** Ne jamais tester une contrainte isolément ni couper un énoncé de l'auteur : chaque livraison
reprend le paquet entier — liaison au suivant, tout en ligne, lissage et écarts, grammaire première,
pointage sur un zéro — sur les mêmes objets. Ne pas accorder un zéro hors ligne pour en mesurer les effets :
partir de l'état engagé sur la ligne et n'appliquer que les lois de progression disponibles ; formuler les
énoncés sur le régime, jamais sur le hors-ligne. Zêta produit les zéros : la production d'un zéro n'est pas
induite par le zéro précédent, elle est liée ; on reprend à chaque fois les liaisons compilées (ordre,
miroir, grammaire première, somme, côté arithmétique, fonction réelle sur la ligne). Toute loi candidate
doit être fausse dans les mondes témoins (section 10). Quand l'auteur demande une réponse sémantique, elle
est donnée sans nom du code et sans formule.

**Règles de travail en vigueur.** Tout se fait dans le build principal du projet, où tous les théorèmes sont dans le
champ ; aucune sonde, aucun essai à part, aucun fichier hors du projet. Après chaque compilation, le travail est
consigné sur la branche principale même si le build ne compile pas : la branche peut être rouge, et l'erreur du build
principal est l'erreur de référence. Aucun trou de preuve, aucun axiome ajouté ; la seule prémisse nommée du code est
la prémisse unique (section 11). Le verrou est la traduction en mots du but unique que le compilateur affiche ; il
n'est ni choisi ni reformulé, et aucun verrou n'est ajouté. L'enroulement compilé des Tours à l'infini est un sujet
fermé : il n'est ni rouvert ni contesté. Vocabulaire : on écrit « caractérise » et « certificat » ; jamais
« anti-compensation » comme flèche manquante ; jamais « moitié » pour la symétrie miroir ; jamais « sans hypothèse »
ou « sans prémisse » pour un théorème qui a des hypothèses ; jamais « toutes les contraintes sont utilisées » parce
qu'elles sont importées ; jamais une difficulté affirmée sans vérification. Pistes réfutées, à ne pas reproposer : la
croissance des écarts de premiers contre la plage de phase ; les écarts de hauteur croissants (section 13).

## 2. Domaine

On travaille exclusivement avec les vrais zéros non triviaux de zêta : partie réelle strictement entre zéro
et un, existence garantie par la théorie analytique, jamais par une construction. La moitié supérieure de
ces zéros, ceux de partie imaginaire strictement positive, est ordonnée par la hauteur croissante puis par
la partie réelle croissante ; ses éléments sont les membres. Cet ordre est celui de l'énumération ; il
n'est jamais à lui seul un argument de la preuve.

**Le plan des zéros.** Dans le plan des zéros, chaque zéro possède une hauteur, sa partie imaginaire, et une partie réelle. La
ligne critique est la droite des parties réelles égales à un demi ; elle est le lieu fixe de la réflexion miroir
(section 8). Un zéro de partie réelle un demi est en ligne, tout autre est hors ligne. Ce plan est distinct du plan des
Tours (section 4) : un point du plan des zéros est un zéro, il n'est pas une courbe.

Un point du plan choisi pour ses coordonnées n'a ni Tour, ni contacts, ni lien avec les premiers, même s'il
a les coordonnées d'un vrai zéro : il faut passer par zêta, car c'est elle qui impose ses contraintes.
Aucun raisonnement ne porte sur des points synthétiques.

Les contrôles numériques utilisent les zéros publiés par Odlyzko. Un contrôle numérique n'est jamais une
preuve : il peut réfuter une implémentation, jamais un énoncé de ce maître. Personne ne sait calculer un
zéro hors ligne : il n'est jamais calculé ni approché ; ce que le projet en sait vient du port de la
réflexion (équation fonctionnelle, conjugaison, conservation de la multiplicité). Quand une expérience place
une partie réelle autre qu'un demi à une hauteur publiée, c'est un monde de contrôle, jamais un zéro.

## 3. Les trois objets

La démonstration porte sur trois objets et trois seulement : l'ensemble ordonné des vrais zéros non
triviaux ; la Tour propre de chaque zéro ; l'unique histoire ordonnée des nombres premiers, telle que la
reconstruit, depuis les zéros, le canal de Tchebychev et de Von Mangoldt, avec sa grammaire complète (rangs,
occurrences, primalité, écarts, états, transitions, progression). Aucun objet ne crée une seconde histoire
première, une seconde famille de Tours ou une seconde notion de progression. Les cellules, positions,
états, registres, raccords et comptages définis plus bas sont des porteurs de ces trois objets.

## 4. La Tour propre

**Ce qu'elle est.** Chaque zéro apporte à la formule explicite de Riemann un terme : un nombre positif élevé
à la puissance du zéro, divisé par le zéro. La Tour propre d'un zéro est la trace de ce terme dans le plan
complexe, quand le nombre parcourt tout l'axe des réels positifs. C'est une spirale unique et continue,
entièrement déterminée par la partie réelle et la hauteur du zéro : son argument avance avec le logarithme
du nombre, à une vitesse angulaire par unité de logarithme du nombre égale à la hauteur, décalé d'une phase que fixent ensemble la partie réelle et la
hauteur ; son éloignement de l'origine, l'amplitude du terme, croît comme le nombre élevé à la partie
réelle, divisé par la norme du zéro. Une Tour par zéro ; une Tour ne porte jamais deux zéros. C'est compilé.

**Le plan des Tours, la Tour brute, la Tour normalisée, le pôle de rotation.** Le plan des Tours est le plan complexe où l'on
trace les termes des zéros ; il est distinct du plan des zéros. La Tour brute d'un zéro est la trace de son terme quand
l'abscisse parcourt les réels positifs. Le zéro détermine cette trace ; il n'en est ni le centre ni le point de départ : la
Tour ne part pas de son zéro et n'est pas centrée sur lui. En un, la Tour vaut l'inverse du zéro ; au premier nombre
premier, deux, elle vaut deux élevé à la puissance du zéro, divisé par le zéro. L'origine du plan des Tours est le pôle de
rotation de toutes les Tours, sans exception ; ce n'est pas le milieu d'une paire de zéros, objet du plan des zéros
(section 8). La hauteur fixe la vitesse angulaire en coordonnée logarithmique, c'est-à-dire l'angle parcouru par unité de
logarithme de l'abscisse. La Tour normalisée est la Tour brute ramenée à l'échelle de la ligne, c'est-à-dire divisée par la
racine carrée de l'abscisse ; l'écart radial du zéro à la ligne fixe alors le taux de croissance (au-dessus de la ligne) ou
de décroissance (au-dessous) de l'amplitude, par unité de logarithme de l'abscisse. Un zéro en ligne donne une Tour
normalisée qui est un cercle centré à l'origine ; un zéro hors ligne donne une spirale, qui n'a pas cette symétrie
centrale.

**La conjugaison et la symétrie centrale.** La conjugaison transforme la Tour d'un zéro en la Tour du zéro conjugué. Cela ne
signifie pas que chaque Tour soit elle-même invariante par réflexion. La symétrie centrale d'une Tour normalisée (l'opposé
de tout point de la Tour est un point de la Tour) caractérise l'appartenance du zéro à la ligne. C'est un théorème compilé,
non une affirmation : toutes les Tours des zéros en ligne sont symétriques. Deux lectures équivalentes, compilées : la tangente
de la Tour normalisée est perpendiculaire au rayon exactement quand le zéro est en ligne (sa composante le long du rayon est
l'écart radial à la ligne multiplié par le carré du rayon) ; un demi-tour plus loin, la Tour est à l'opposé, multipliée par un
facteur radial qui vaut un exactement sur la ligne. Pour le zéro suivant, c'est cette opposition exacte, ou cette
perpendicularité, qui reste à établir (la Tour brute d'un zéro en ligne est une spirale : un demi-tour plus loin elle est à
l'opposé avec une dilatation ; c'est sa forme normalisée qui est un cercle, à l'opposition exacte) : l'enroulement autour de la même origine et la périodicité du demi-tour ne suppriment
pas à eux seuls ce facteur radial.

**Ses contacts.** Les contacts, ou rayons, sont les points où la Tour coupe l'axe réel du plan : ce sont
exactement les nombres où le terme du zéro est réel. Il y en a un à chaque demi-tour, sans fin dans les
deux sens ; le côté de l'axe alterne strictement d'un contact au suivant. Il faut distinguer l'abscisse de lecture d'un contact, le
nombre positif où la Tour coupe l'axe réel, et le point atteint, point complexe de l'axe réel dont la distance à l'origine
est l'amplitude en ce contact. Le rapport de deux contacts consécutifs ne dépend que de la hauteur : son logarithme est
l'écart logarithmique entre deux contacts successifs, fixé par la hauteur, et il diminue quand la hauteur augmente. C'est
le pas de la Tour, qui n'est pas un écart entre premiers.
Au contact, le terme vaut, au signe alterné près, l'amplitude en ce contact ; cette amplitude croît le long
des contacts au rythme que fixe la hauteur. Compilé.

**Ses cellules.** Deux contacts consécutifs délimitent une cellule, ou anneau. Les cellules d'une Tour sont
en nombre infini et recouvrent tout l'axe : tout nombre positif, donc tout premier, a une cellule et une
seule dans la Tour de tout zéro. Une cellule peut contenir zéro, un ou plusieurs premiers ; jusqu'à
plusieurs milliers aux hauteurs basses et pour de grands premiers. Compilé ; le dénombrement est numérique.

**Un numéro de cellule ne désigne aucun premier.** Le numéro d'une cellule est relatif à l'origine de sa Tour, et
l'échelle de la grille est fixée par la hauteur. Prendre pour numéro le rang du zéro donne des anneaux qui montent
comme la racine de la hauteur, à la place que fixe le comptage des zéros : ils ne logent un premier que lorsque
cette racine franchit deux, trois ou cinq (neuf rangs sur trois cents), jamais le premier du rang. Numérique (E151).

**L'enroulement à numéro fixé.** Une Tour est une spirale dont le pas se resserre quand la hauteur monte : un même
nombre de demi-tours est atteint de plus en plus près de un. À numéro fixé, au moins un, l'anneau d'un zéro plus
haut est donc strictement plus bas que celui du zéro précédent, et les premiers anneaux d'un zéro contiennent ceux
de tous les zéros situés au-dessus : chaque zéro s'enroule à l'intérieur du précédent. À même hauteur il n'y a pas
d'enroulement, seulement une translation rigide de toute la grille (on entend par là que toutes les abscisses de contact
sont multipliées par un même facteur, c'est-à-dire un décalage uniforme en coordonnée logarithmique ; ce n'est pas un
déplacement de la courbe) ; l'enroulement est la contraction du pas
propre au régime vertical, lue à numéro fixé. Conséquences, toutes compilées et vraies pour toute partie réelle :
un anneau de numéro fixé ne peut loger un premier donné que dans une fenêtre bornée de hauteurs, et il est vide
de tout premier au-delà d'une hauteur finie ; pour le quatrième anneau, seuls les deux premiers zéros de toute la
suite y logent un premier (trois puis deux), ce qui n'est pas un échantillon mais un énoncé sur tous les zéros ;
inversement chaque premier franchit tout numéro fixé et s'enfonce sans retour dans la grille des zéros
successifs. Numériquement (E151) : un premier avance en moyenne d'une part de cellule par passage égale à la part
de hauteur du registre ; les petits premiers avancent de moins d'une cellule par passage, les grands de plus,
et la frontière est la racine de la hauteur rapportée à deux pi, la longueur de la somme principale de
Riemann–Siegel ; la grille d'un zéro sépare dans des cellules distinctes tous les premiers jusqu'à une borne qui
croît avec la hauteur (dix-sept au premier zéro, six cent quarante et un au trois-centième). L'enroulement est
le même dans le monde témoin aux mêmes hauteurs : il lit la hauteur et le comptage, il ne lit pas la partie
réelle et ne porte pas la flèche.

**L'enroulement à l'infini.** L'enroulement compilé à l'infini encadre les contacts d'une Tour entre ceux des Tours précédentes
et suivantes, au-delà de seuils propres à chaque comparaison. Cet encadrement est acquis, pour toutes les Tours et toutes
les positions radiales ; il n'affirme pas à lui seul la conservation radiale. C'est un sujet fermé (section 1).

**L'origine canonique.** Le premier contact au-dessus de un est l'origine canonique : un point de départ
unique, obtenu sans nombre premier, sans rang et sans comptage. Les contacts se numérotent à partir d'elle
par demi-tours. Le début du mouvement est ainsi fixé une fois pour toutes. Compilé.

**La position d'un nombre dans une Tour.** La position d'un nombre est le nombre réel de demi-tours qui le
séparent de l'origine de la numérotation : la hauteur fois le logarithme du nombre, moins la phase, rapporté
à un demi-tour. Sa partie entière donne la cellule ; sa partie fractionnaire, la place dans la cellule. Dans
une même Tour, la différence entre les positions de lecture de deux nombres ne dépend que de la hauteur : cette
différence efface le décalage commun sans démontrer qu'il est nul. Ce n'est pas un énoncé général selon lequel les écarts
de premiers seraient lus par la hauteur seule dans toute Tour. Compilé.

**La Tour de ligne et la forme normale.** La Tour de ligne à une hauteur est la Tour qu'aurait un zéro de
partie réelle un demi à cette hauteur ; elle ne dépend que de la hauteur. Toute Tour est la Tour de ligne à
sa hauteur, translatée d'un bloc (translation rigide au sens ci-dessus) : la grille d'une Tour est l'ensemble de ses
abscisses de contact ; à hauteur fixée, la partie réelle multiplie toutes les abscisses de contact par un même facteur
relativement à la grille de ligne, le facteur radial, et tous ses contacts sont ceux de la Tour de ligne multipliés par lui ; et la position de tout nombre est sa position de ligne plus un même décalage,
toujours plus petit qu'une fraction de cellule inversement proportionnelle à la hauteur. Le facteur radial
vaut un exactement sur la ligne ; il est plus grand sous la ligne, plus petit au-dessus. Le décalage, appelé
résidu de changement, est nul exactement sur la ligne. Compilé : c'est la forme normale de toute Tour.

**Les deux signatures de la partie réelle.** Une variation de la partie réelle a deux visages, et deux
seulement. Dans la géométrie, elle translate d'un bloc toute la grille, du même petit décalage en tout
point. Dans l'amplitude, elle multiplie le terme par une puissance du nombre lu, différente en chaque point.
Le premier visage existe pareillement dans les mondes témoins, qui ont le même support premier avec des poids
modifiés ; seul le second lit les poids des premiers. Compilé.

**L'inversion.** Deux contacts consécutifs quelconques d'une Tour redonnent exactement son zéro : leur
rapport donne la hauteur, puis la loi tangentielle donne la partie réelle. Deux zéros distincts ne partagent
jamais deux contacts consécutifs. L'inversion certifie l'appartenance de contacts à une Tour ; elle ne
choisit aucune cellule. Compilé.

## 5. L'état propre et la règle du pivot

**L'occurrence est une étiquette de rang.** Le rang d'un membre est le nombre de membres situés au-dessous
de lui. La grammaire première lui assigne son occurrence : le premier de ce rang. L'occurrence est donc une
étiquette ; elle est injective ; la Tour la loge dans une de ses cellules, elle ne la choisit pas. « Un zéro,
un premier » est cette étiquette, pas une géométrie. Compilé.

**Le minimum attendu.** Le minimum attendu d'un membre est le premier qui suit immédiatement son occurrence.
Il est défini par la progression première seule, avant toute Tour et sans le miroir. Deux membres distincts
ont deux minimums attendus distincts. Compilé.

**Le pivot et l'état propre.** Le pivot d'une Tour est le minimum attendu de son membre, dans le sens de
parcours de cette Tour (section 8 pour l'orientation opposée). La règle du pivot fixe la cellule de l'état
propre : c'est l'unique cellule de la Tour qui contient le pivot, la plus petite qui l'atteint. L'état propre
est la paire de contacts consécutifs qui l'encadrent : l'incidence d'entrée, strictement au-dessous du pivot,
et le dernier rayon, au-dessus ou sur lui. Aucune cellule n'est choisie parmi d'autres, aucune formule de
coordonnée n'est cherchée : la cellule se calcule depuis le pivot, et son numéro est une lecture, jamais un
paramètre. L'unicité de la cellule vaut pour tout nombre positif ; que la cellule contienne le minimum
attendu est vrai par construction. Compilé.

**Référence et cible constatée.** La référence est le pivot, fixée avant la Tour. La cible constatée est le
dernier premier que le comptage atteint au dernier rayon, lu ensuite. Elle ne descend jamais sous la
référence ; elle peut la dépasser, à cause des sauts de l'histoire première (un peu moins d'un tiers des
trois cents premiers membres publiés). Il n'y a pas de circularité. Sur ces trois cents membres, la cellule
contient le minimum attendu dans tous les cas et les quinze contacts historiques sont exactement retrouvés.
Compilé ; proportions numériques.

## 6. Le comptage et la grammaire première reconstruite

Le comptage de Von Mangoldt et de Tchebychev s'applique à l'unique histoire des premiers. Le canal
analytique reconstruit, depuis les zéros, exactement cette histoire : poids, primalité, comptage, rangs,
écarts, événement par événement. Le comptage va du début de l'histoire jusqu'à un contact ; il lit, il ne
sélectionne jamais, et il n'entre jamais dans la construction de l'état propre ; les contacts ne sont pas
des premiers. L'auteur note cette identité de la grammaire reconstruite et de la grammaire première « M^Z = M ».
Compilé.

**Le noyau rigide.** Trois blocs sont des théorèmes sans hypothèse. L'unicité de la cellule et de la paire
de contacts de l'état propre, pour toute partie réelle. La chaîne arithmétique entre deux membres
consécutifs : la place avance d'un, l'occurrence du suivant est le minimum attendu du précédent, les
minimums attendus avancent strictement. Le lien de comptage : le rang et le premier lus à tout contact d'une
Tour, dans les deux orientations, sont exactement la fonction de comptage de Tchebychev et de Von Mangoldt
évaluée en ce contact. C'est ce lien qui fait de la position sur l'axe une identité arithmétique.

**Ce que le noyau ne couvre pas.** Il ne dit rien de la position radiale ; il est vrai dans tout monde qui a
le même support premier.

## 7. La progression et la grammaire première

**Le passage et la succession.** La succession est l'ordre des membres : par hauteur croissante, puis, à hauteur égale, par
partie réelle croissante. Un passage est la relation entre deux membres consécutifs de l'énumération ; leur rang avance de
un, leurs occurrences premières sont successives et distinctes, et la hauteur ne recule pas. Sur tout
passage : la place avance d'exactement un ; la hauteur ne recule jamais ; l'occurrence avance strictement ;
le membre suivant pointe le minimum attendu du précédent, qui est son occurrence ; les minimums attendus
avancent strictement. Ce sens de progression vient de l'ordre des membres, pas de la somme de la formule
explicite, qui porte tous les zéros, est fermée par conjugaison et ne dépend d'aucun ordre de sommation.
Compilé, sans hypothèse sur la partie réelle.

**Le premier partagé.** Sur tout passage, le premier qui est à la fois le minimum attendu du membre de
départ et l'occurrence du membre d'arrivée est le premier partagé. Il est unique et déterminé par le rang.

**Deux grammaires.** La grammaire par rang (un membre, un événement premier) est inconditionnelle et aveugle
à la partie réelle et à la hauteur. La grammaire par hauteurs (une hauteur, un événement) donne le même
premier à un zéro hors ligne et à son miroir. Les deux coïncident exactement quand chaque hauteur ne porte
qu'un membre, et « toute hauteur ne porte qu'un membre » équivaut à la cible (compilé, section 10) ; de même,
« la place avance donc la hauteur avance », pris sur tout passage, équivaut à la cible, puisque c'est dire
que tout passage est vertical. Hors ligne, il existe un passage où la place et l'occurrence avancent sans
que la hauteur avance (compilé).

**La rigidité modulo six.** Tout premier plus grand que trois est dans l'un de deux états : un de moins
qu'un multiple de six, ou un de plus. L'écart entre deux tels premiers, rapporté à six, ne prend que trois
classes : nulle quand l'état se maintient, deux quand il passe du premier état au second, quatre dans
l'autre sens. Deux changements d'état effectifs consécutifs, en ignorant les maintiens, portent toujours
des classes différentes : l'alternance deux, quatre est forcée. Conséquence quantitative : deux transitions
consécutives entre premiers plus grands que trois avancent d'au moins six. Compilé, vrai que l'hypothèse
de Riemann soit vraie ou fausse : c'est la découverte arithmétique de base du projet, à ne jamais perdre.
L'alternance donne plus qu'un plancher. Deux changements d'état consécutifs avancent exactement de six fois la somme de
leurs deux magnitudes plus un ; on revient à l'état de départ exactement quand l'avance est un multiple de six ; sur
toute fenêtre, le nombre de passages du premier état au second et le nombre de passages inverses diffèrent d'au plus
une unité, fixée par les états des deux extrémités. Compilé.

**Magnitude, classe, transition, mot, sollicitation, canal.** La magnitude d'un écart est le nombre de fois que six y
entre ; la classe est ce qui reste, zéro, deux ou quatre. La transition d'un événement est le couple des états de
départ et d'arrivée : maintien dans le premier état, passage du premier au second, passage du second au premier,
maintien dans le second ; elle fixe la classe, et les deux maintiens sont deux transitions distinctes de même classe.
Un mot grammatical est une suite d'événements consécutifs lue avec, pour chacun, sa magnitude et sa transition. La
sollicitation d'un événement est ce qu'il impose à chaque Tour : une avance de phase par la hauteur, une variation
d'amplitude par la partie réelle, une variation d'énergie par son double, toutes trois proportionnelles au même écart
logarithmique. Un canal de transition réunit les événements d'une même transition ; le poids d'un canal dans une
cellule est la part de l'histoire qu'il y apporte. Ce sont des fonctions des positions des premiers seules.

**La hiérarchie descriptive.** Au-delà, la recherche historique a décrit des motifs, des familles de motifs,
leurs relations d'ordre et une structure supérieure, en visant que la reconstruction depuis les zéros
conserve la même suite de transitions, de motifs, de familles et d'ordre que l'histoire réelle. Cette
hiérarchie reste descriptive au-delà des mots courts : sont compilés les états, les classes, l'alternance, l'avance
exacte de deux changements, le retour d'état et le verrou des passages d'un état à l'autre. La
reconstruction compilée conserve toute description tirée de l'histoire première, puisqu'elle redonne
l'histoire elle-même.

**Portée.** Le pas grammatical est aveugle au régime : sur tout passage, l'événement imposé est le premier
suivant. Grammaire, occurrence, minimum attendu, états et classes sont des fonctions du rang seul. Ils sont
identiques dans les mondes témoins. Ils ne portent pas la position radiale. Aveugle au régime ne veut pas dire sans
contrainte : la grammaire ne fixe pas la partie réelle, mais elle fixe la succession structurée des sollicitations
auxquelles la partie réelle répond. Sur tout mot, l'écart entre les réponses énergétiques des deux membres d'une
paire miroir est fixé par les seules extrémités du mot et proportionnel à la profondeur de la paire (compilé) : la
structure interne du mot n'y entre pas.

## 8. Le miroir, les quatre zéros et la seconde Tour

**Le miroir, le miroir annulé, le milieu de la paire, le carré de quatre zéros.** Le miroir est la réflexion par la ligne
critique : il conserve la hauteur et réfléchit la partie réelle, qui devient son complément à un. La ligne critique est le
lieu fixe de cette réflexion. Un miroir annulé signifie que le zéro coïncide avec son miroir : cela caractérise un zéro en
ligne. Le milieu d'une paire miroir est le point de la ligne critique situé à la hauteur commune de ses deux membres ; des
hauteurs différentes donnent des milieux différents, et deux membres miroirs de même hauteur partagent le même milieu. Un
zéro en ligne coïncide avec le milieu de sa propre paire. Un zéro hors ligne de hauteur positive appartient à un carré de
quatre membres distincts, obtenus par miroir et conjugaison : la symétrie miroir n'est pas une moitié, un zéro hors ligne
vient toujours en carré. Le milieu de la paire est un objet du plan des zéros ; le pôle de rotation d'une Tour est l'origine
du plan des Tours : ce sont deux objets distincts, jamais désignés par le même mot « centre ». Entre les deux plans, la
symétrie centrale de la Tour normalisée, le miroir annulé et le zéro au milieu de sa paire sont équivalents ; cette
équivalence relie des propriétés, elle n'identifie pas l'origine de la courbe et le milieu de la paire.

**Les quatre zéros.** D'un zéro hors ligne naissent quatre zéros de même multiplicité : lui-même, son
conjugué, son miroir (un moins le conjugué) et son réfléchi par l'équation fonctionnelle (un moins le zéro,
conjugué du miroir). Compilé. Dans la moitié supérieure, deux sont membres : le zéro et son miroir, à la
même hauteur, de parties réelles complémentaires à un. Le miroir vient strictement après le zéro de partie
réelle inférieure ; ils portent deux événements distincts. Sous consécutivité stricte, l'occurrence du
miroir est exactement le minimum attendu du premier, et les deux minimums attendus sont strictement ordonnés.
Sur la ligne, le miroir est le membre lui-même.

**Contraintes compilées du miroir.** La progression de hauteur entre les deux membres de la paire est nulle ;
ce n'est pas la hauteur qui est nulle. La translation des contacts du miroir par rapport à ceux du zéro est
uniforme ; hors ligne, aucun contact du miroir ne coïncide avec un contact du zéro : les contacts du miroir
s'entrelacent strictement dans les cellules du zéro, avec un défaut de superposition qui décroît comme
l'inverse de la hauteur sans jamais s'annuler. Un seul contact commun, ou une phase commune, force la ligne.
L'amplitude du miroir domine celle du zéro hors ligne ; elles sont égales sur la ligne. Les deux forces
horizontales du zéro et de son miroir ont une résultante nulle pour tout zéro, et la tension propre de la
paire ne s'annule que sur la ligne.

**La Tour du miroir et la seconde Tour.** Le miroir a sa Tour propre par la même construction que tout
zéro, jamais déduite de la première. La seconde Tour de la paire est la Tour du zéro réfléchi, de hauteur
opposée : les mêmes formules lui donnent la phase opposée et le pas opposé, si bien qu'elle parcourt les
contacts du miroir en sens inverse. Son dernier rayon est le croisement au-dessous de son pivot, son
incidence d'entrée le croisement au-dessus. Cette inversion des rôles est un théorème de l'équation
fonctionnelle et de la conjugaison ; le seul passage de la partie réelle à son complément ne renverse rien.
Le pivot de la seconde Tour est le sien, le minimum attendu du miroir : deux événements, deux pivots. Le
mouvement réfléchi, depuis sa propre origine, n'atteint aucun premier ; ce zéro n'est jamais membre.

**Lecture de la seconde Tour.** Que la seconde Tour lise l'histoire jusqu'à l'occurrence du miroir équivaut
à une position de cette occurrence dans les anneaux du miroir ; elle est acquise dès que l'écart logarithmique
entre l'occurrence et le minimum attendu du miroir dépasse un demi-tour. Les anneaux du miroir sont ceux du
membre décalés de moins d'un demi-anneau. Compilé. Sur les substituts publiés, cette lecture tient dans un
peu plus de deux tiers des cas : elle dépend des données.

**Ce qui n'est plus une direction.** La collision entre la lecture de la seconde Tour et la non-atteinte du
minimum attendu du zéro original, ainsi que les deux lois de l'inversion qui la portaient, sont retirées du
code : la vérification comparait le dernier rayon de la seconde Tour à la référence d'un autre zéro, à
travers l'inversion d'une cellule fixe, ce qui ne mesurait pas la bonne quantité. Sur une même grille,
« même cellule » et « cellule inférieure » partagent les nombres en deux ; une contradiction écrite avec ces
deux mots est de la forme « A et non A » et ne lit rien de propre aux premiers. Voir section 13.

## 9. La formule explicite, le reste et l'identité de chaque membre

**La Tour est le terme du zéro.** La Tour n'est pas une géométrie posée à côté de zêta : c'est la géométrie
du terme que ce zéro porte dans la formule explicite compilée. La position dans la Tour est l'argument de ce
terme ; les contacts sont les points où il est réel ; l'inversion des contacts de la seconde Tour est la
conjugaison du terme ; la partie réelle entre dans l'amplitude. Compilé.

**L'organisme spectral.** L'ensemble des membres, avec leurs Tours, leurs contacts, leur ordre, leurs
hauteurs, leurs parties réelles et leurs transports, est l'organisme qui, après retrait du fond lisse,
reconstruit exactement le reste arithmétique de l'escalier des premiers ; cette reconstruction redonne chaque
événement premier complet, toute l'histoire première et toute description tirée d'elle. Compilé, sans
condition sur la position des zéros.

**Le reste arithmétique.** On additionne, pour chaque entier au-dessous d'une abscisse, le poids que la
grammaire première lui donne (le logarithme du premier pour une puissance de ce premier, rien sinon), adouci
par un facteur qui décroît jusqu'à l'abscisse, puis on retire un fond lisse explicite. Aucun zéro non
trivial n'entre dans cette définition ; le poids d'un premier y est le poids de son événement. Le résidu
arithmétique est égal au résidu spectral, contribution collective des zéros. Compilé.

**L'identité de chaque membre.** Aucun membre n'est retirable : son terme ne s'annule en aucune abscisse. Les
profils d'exposants distincts sont indépendants, et la décomposition en profils est unique, somme infinie
comprise. Dans toute représentation du reste par des points et des poids, chaque zéro figure avec exactement
sa multiplicité, aucun point qui n'est pas un zéro ne porte de poids, et la partie réelle, la hauteur et la
multiplicité de chaque membre sont retrouvées. Le reste, comme fonction, détermine donc individuellement
chaque terme ; une fenêtre finie du reste n'est qu'un nombre. L'identité d'un zéro hors ligne n'est effacée
par aucune compensation. Compilé. L'isolement d'un terme est donc acquis ; ce que cette identité ne donne pas est la valeur de sa
partie réelle.

**Le paquet de hauteur et la compensation.** Le paquet de hauteur réunit tous les indices de la formule
explicite qui ont la même hauteur absolue. Le canal se découpe exactement, sans troncature, en paquet plus
complément ; la compensation, reste exact moins paquet, est fournie exactement par le complément, à chaque
marche, à chaque événement premier et pour toute abscisse. Compilé. La compensation est la même identité lue
après soustraction : elle ne contraint pas le complément.

**La lecture inverse.** La différence du reste entre deux événements arithmétiques se lit des deux côtés :
côté premiers, somme des poids des événements de l'intervalle moins l'avance du fond ; côté zéros,
différence de leur contribution ; elle se découpe en paquet et complément. Compilé.

**La marche et sa demande exacte.** Une marche est le passage de l'histoire première d'un événement premier au
suivant. Elle est pure quand aucune puissance de premier ne s'intercale entre les deux premiers consécutifs. L'écart
exact de la marche est la distance entre ces deux premiers ; il s'écrit d'une seule façon comme six fois une
magnitude, nombre entier qui fluctue et croît sans borne connue, plus une classe, qui ne prend que trois valeurs et
alterne (section 7) ; magnitude et classe sont des fonctions du rang seul. La demande arithmétique exacte de la marche
est ce que le reste doit gagner entre les deux événements : sur une marche pure, le poids du premier atteint moins
l'avance du fond lisse, et l'écart y entre par sa magnitude et sa classe. Compilé. L'avance du fond est la longueur
de l'écart à moins de cinq centièmes près (E137, numérique) : la demande est positive pour les petits écarts,
négative pour les grands, et c'est la magnitude de l'écart qui la commande.

**La réponse collective.** La contribution d'une Tour à une marche est la variation, entre les deux bords de la
marche, de la projection réelle du terme de son membre et de son conjugué : elle dépend ensemble du rayon (la partie
réelle), de la phase (la hauteur), du cosinus aux deux bords et des deux premiers exacts. La réponse collective est la
somme des contributions de toutes les Tours ; elle égale exactement la demande, sur toute marche, et la part que
fournit le complément de toute partie des Tours est forcée (compilé). Une Tour seule ne reproduit pas la demande, ni
quelques Tours ; un long préfixe de vraies Tours la reproduit à la troncature près (E137). La relation entre premiers
et zéros est collective : un événement adresse sa demande à l'ensemble spectral, il ne choisit aucune Tour.

**Diagonale, croisés, renforcement, compensation.** La diagonale d'une marche est la somme des énergies
individuelles, les carrés des contributions : les ressources individuelles du système. Les croisés sont le carré de
la réponse moins la diagonale, c'est-à-dire la somme, sur les couples de Tours distinctes, des produits de leurs
contributions. Deux Tours qui contribuent dans le même sens se renforcent ; dans des sens opposés, elles se
compensent. Le carré de la réponse est la diagonale plus les croisés ; une fois la réponse fixée par la demande, les
croisés valent le carré de la demande moins la diagonale ; il y a compensation nette exactement quand la diagonale
dépasse le carré de la demande ; des contributions de même signe ne se compensent pas ; changer les signes des
contributions ne change pas la diagonale, qui ne voit donc pas les compensations. Compilé. Le taux de survie d'une
famille de marches est la somme des carrés de leurs réponses rapportée à la somme de leurs diagonales : la part de
l'énergie individuelle qui survit aux compensations ; il vaut un en moyenne quand les signes des contributions sont
tirés au hasard.

**Résolution et bandes de hauteurs.** La résolution d'une Tour est la largeur de ses cellules sur l'échelle
logarithmique, un demi-tour, fixée par la hauteur seule : plus la hauteur est grande, plus la Tour découpe finement
la même histoire. Une bande de hauteurs réunit les Tours de résolution voisine ; les croisés se partagent en croisés
internes à une bande et croisés entre bandes. Une résolution grossière est celle des Tours basses.

**Dérive radiale, dette et rigidité de compensation.** Une dérive radiale est un déplacement de la partie réelle d'un
membre hors de la ligne ; sur sa Tour, c'est une translation de la grille et une pente d'amplitude (section 4). Une
paire déplacée hors de la ligne à une hauteur fournit à chaque marche la contribution de la paire en ligne multipliée
par un facteur plus grand que un, fixé par le déplacement et par l'abscisse (E137, à la précision machine ; la forme
nue du facteur est compilée). La dette de compensation est la différence, marche par marche, entre ce que fournit la
paire déplacée et ce que fournirait la paire en ligne : pour reproduire la même demande, les autres Tours devraient
la fournir par leurs croisés. La rigidité de compensation est l'impossibilité de cacher la dette sur toute
l'histoire : dans toute représentation spectrale du même reste exact, le membre déplacé figure avec son poids, et il
porte l'exposant de croissance du reste au-dessus d'un demi. Compilé : c'est l'unicité de la représentation
spectrale et la lecture du pôle. Sur une fenêtre finie, si l'on traite les contributions des autres Tours comme des
paramètres libres, une réorganisation compense la dette dès qu'elle a plus de paramètres que de marches, et cesse de la
compenser hors de la fenêtre (E137bis) : les équations de demande d'une fenêtre, prises seules, sont sous-déterminées.
Cela ne dit rien d'une fenêtre de zêta, dont les Tours ne sont pas libres : ce sont de vrais membres, dans leur ordre,
avec leurs hauteurs, leur miroir et leurs amplitudes, devant le même mot premier et sous la même formule explicite.

**Poids signés et structure multiplicative.** Les poids de l'histoire première sont positifs. Les signes dont parle
la démarche sont ceux des contributions, après projection des poids par les phases des Tours, ou ceux que les mondes
de contrôle imposent artificiellement aux poids. L'organisation des poids signés est la manière dont les poids exacts,
rencontrés dans leur ordre exact, sont transformés par les phases en contributions qui se renforcent ou se compensent.
La structure multiplicative est le fait que ces poids viennent de la factorisation des entiers et du produit d'Euler :
ce n'est pas une suite arbitraire de nombres de même distribution, et l'ordre ne se déplace pas sans changer l'objet.

**Le budget global (zeta23).** Le dépôt zeta23, compilé et validé hors de ce build, transforme le côté premier en
contrainte sur le nombre et la nature des zéros, sans associer un premier à un zéro. Côté premier, des fonctions test
fabriquent une trace et un second moment ; les termes hors diagonale, interactions entre deux événements premiers
distincts, y sont bornés par la somme des carrés des poids (inégalité de Montgomery et Vaughan). Côté zéros, chaque
zéro en ligne est un atome individuel avec sa multiplicité ; une paire hors ligne et son reflet forment un bloc à deux
membres. La trace mesure le poids total porté par le système ; l'énergie quadratique, sa concentration. L'inégalité
rang–trace transforme trace et énergie en un nombre minimal d'atomes simples en ligne : asymptotiquement, plus des deux
tiers des zéros sont simples et en ligne, plus des cinq sixièmes sont distincts. Cette inégalité est tendue : un zéro
double en ligne et une paire hors ligne très proche de la ligne y coûtent exactement le même prix, et aucune
inégalité ne consommant que ces quantités ne peut l'améliorer. Un résultat de densité est une proportion sur une
fenêtre de hauteurs : il ne voit aucun ensemble de zéros de proportion nulle, en particulier aucune paire isolée.

**Le tout en ligne et l'écart.** Le tout en ligne est l'ensemble des membres en ligne ; il est en
correspondance exacte avec les hauteurs où la fonction réelle sur la ligne s'annule. Le reste est le tout en
ligne plus un écart ; l'écart est fixé par le côté arithmétique et par la fonction réelle de la hauteur ;
aucune repondération des membres en ligne ne l'imite ; un membre hors ligne le rend non nul. Compilé.

**La lecture par la taille.** Si le reste est borné par une puissance de l'abscisse, aucun zéro n'a une
partie réelle au-delà de cet exposant. L'hypothèse de Riemann équivaut à : le reste est borné par une
constante fois la racine carrée de l'abscisse. Les deux sens sont compilés ; la borne n'est pas dérivée.
L'égalité du reste avec la somme des zéros ne donne pas sa taille.

**Hauteur et pente : les deux coordonnées d'un membre.** Le terme d'un membre a deux coordonnées qui ne se
mélangent pas. Quand on avance dans les premiers, sa position dans la Tour avance du seul fait de la hauteur : c'est
la fréquence, l'enroulement et la résolution ; son amplitude croît du seul fait de la partie réelle : c'est la pente
du raffinement. Ramenée à l'échelle de la racine carrée, l'amplitude est constante exactement pour un membre en
ligne. Un membre déplacé, comme ceux du monde témoin, garde sa hauteur, donc son horloge, son enroulement et sa
résolution, et change seulement sa pente. Un membre de hauteur donnée et de décalage donné n'émerge d'un reste de
taille racine carrée qu'au-delà d'une abscisse qui croît comme une puissance de sa hauteur, d'exposant l'inverse du
décalage. Compilé. Numériquement (E150, premiers jusqu'à cent millions) : le fond fixe l'échelle et non les
événements, puisque le reste, négligeable en proportion, déplace la position des premiers de plusieurs centaines
d'écarts ; la reconstruction par les premiers membres sépare les événements premiers à la largeur de cellule de la
dernière Tour, comme le tamis de l'enroulement ; lue sur les premiers seuls, sans aucun zéro, la pente de chaque
membre isolé est nulle à quelques dix-millièmes près, et celle du monde témoin aux mêmes hauteurs est celle que son
décalage prédit. La pente se lit donc sur l'arithmétique, membre par membre, tant que la plage des premiers résout ce
membre ; c'est la lecture déjà compilée par la taille et par l'unicité, appliquée à une plage finie. Elle ne fixe la
pente d'aucun membre au-delà de cette plage : la pente un demi pour tous les membres à la fois est la borne en racine
carrée, toujours non dérivée.

**Caractérisations.** Aucun zéro de partie réelle inférieure à un demi équivaut à la cible. « Le canal admet
une représentation dont tous les exposants sont sur la ligne », « l'écart est nul pour toute abscisse »,
« le reste est la somme sur les seules hauteurs où la fonction réelle s'annule » équivalent chacun à la
cible. Ce sont des caractérisations, pas des théorèmes.

## 10. Régimes, raccords et mondes témoins

**Les régimes d'un passage.** Un passage est vertical quand la hauteur avance, horizontal quand elle ne
change pas. Le mot « vertical » est le nom que le code donne à un passage dont la hauteur augmente ; cette désignation ne
contient pas la conservation de la partie réelle et ne dit rien de celle des deux membres. Le régime d'un passage est son
type, vertical ou horizontal ; un changement de régime est une jonction de deux passages consécutifs de types différents.
Les deux types sont exclusifs et exhaustifs. Un passage vertical est pur si ses deux membres sont en
ligne, diagonal sinon : sur un passage vertical, le départ est sur la ligne ou à sa droite, l'arrivée sur la
ligne ou à sa gauche, de sorte que la partie réelle ne peut que reculer. Un passage horizontal a une
extrémité hors ligne et sa partie réelle avance strictement. Compilé.

**Le régime lu sur la Tour.** Le pas de la Tour ne dépend que de la hauteur. Vertical équivaut à « le pas se
contracte strictement » ; horizontal équivaut à « le pas est conservé » et à « la grille d'arrivée est une
translatée rigide de la grille de départ » (toutes les abscisses de contact multipliées par un même facteur). Tout passage se décompose en une contraction de pas, due à la
hauteur, et une translation, due à la partie réelle : vertical pur, contraction sans translation ; diagonal parti de la ligne, contraction et translation d'une fraction de cellule (les contacts de l'arrivée
sont ceux de la Tour de ligne multipliés par un facteur plus grand que un, ceux de son miroir par un facteur
plus petit ; la phase de l'arrivée dépasse la phase de ligne et son poids est plus faible que le poids de
ligne) ; horizontal, pas
conservé et translation non nulle. Le régime est visible dans les contacts, pas dans le reste total.
Vocabulaire : « contraction de grille », « translation rigide de grille » ; « poussée » reste l'intuition
(la poussée verticale est la succession par la hauteur, la poussée horizontale la succession à hauteur fixe
par deux parties réelles distinctes ; aucune force physique n'est supposée).

**Les jonctions.** Sur un membre placé entre deux passages consécutifs : vertical puis vertical, il est sur
la ligne ; vertical puis horizontal, il est strictement à gauche ; horizontal puis vertical, strictement à
droite. Aucun changement de régime n'a lieu sur un membre en ligne : un membre en ligne atteint
verticalement est quitté verticalement, et la sortie horizontale d'un membre en ligne n'existe que s'il a été
atteint horizontalement, au milieu d'une fibre d'au moins trois membres. Toute entrée en régime horizontal est précédée d'un passage
diagonal ; après une chaîne verticale, ce passage diagonal part de la ligne. Un zéro hors ligne exige une
entrée en régime horizontal. Une hauteur porte plusieurs membres si et seulement si elle porte un membre hors
ligne ; la fibre multiple est le certificat d'un hors-ligne, lu par la hauteur, pas sa cause. Compilé.
« Aucune entrée en régime horizontal », « aucun passage diagonal et un bas de chaîne vertical », « toute
fibre réduite à un membre » équivalent chacun à la cible.

**La fonction réelle sur la ligne.** La réflexion échange deux points et conjugue la valeur de zêta
complétée ; sur la ligne les deux points coïncident, la valeur est réelle. Un zéro en ligne est une seule
équation réelle en la hauteur ; un changement de signe de cette fonction entre deux hauteurs garantit un
membre en ligne entre elles. Strictement entre les deux hauteurs d'un passage, elle ne s'annule pas et garde
son signe. C'est un détecteur par existence : il ne donne ni la hauteur suivante, ni l'exhaustivité, ni
l'exclusion d'une fibre hors ligne là où il ne s'annule pas. Compilé.

**La cellule de changement de régime.** Quatre membres consécutifs et trois passages : entrée verticale, passage
central horizontal, sortie verticale. Chaque passage a son premier partagé ; ces trois premiers sont consécutifs et
séparés par deux écarts ; avec le premier du membre de départ, la cellule touche quatre premiers consécutifs et trois
écarts. Elle consomme un rang sans hauteur nouvelle : quatre membres pour trois hauteurs, et l'étiquette de rang de
tous les membres au-dessus est décalée d'une unité. Compilé. Les deux membres centraux sont exactement miroirs, l'entrée strictement à
gauche ; le pas se contracte, est conservé, se contracte ; la translation rigide n'existe qu'au centre ; les
trois raccords sont en trois premiers consécutifs. Au centre, le terme du membre de sortie est celui du
membre d'entrée multiplié par le transport et tourné d'un angle constant, qui est la translation des contacts
lue comme phase. Le produit des trois transports est le produit en ligne fois une charge, jamais neutre dans
une cellule, dont l'exposant est l'écart à la ligne et dont la base ne contient que les trois premiers : un
grand écart puis un petit amplifie, un petit puis un grand atténue. Compilé. L'existence d'une cellule à
partir d'un hors-ligne n'est pas compilée.

**Les deux horloges.** L'horloge des membres compte les zéros franchis, celle des hauteurs les hauteurs
nouvelles. Elles coïncident sur la ligne ; un zéro hors ligne les sépare : un événement sans avancée de
hauteur. Compilé.

**L'énergie et le transport.** L'énergie d'une Tour en un nombre est l'amplitude de son terme en ce nombre.
Le transport d'un passage en un nombre est le rapport des énergies de la Tour d'arrivée et de la Tour de
départ ; il vaut le nombre élevé à la différence des parties réelles, multiplié par le rapport inverse des
normes. Le logarithme de ce rapport est la part horizontale moins la part verticale. À même partie réelle, la
Tour la plus haute porte strictement moins d'énergie en tout point ; dès que la partie réelle avance, il
existe un seuil au-delà duquel la Tour d'arrivée porte strictement plus. Le transport est le même en tout
point si et seulement si les deux parties réelles sont égales. Deux égalités d'énergie en deux premiers
distincts forcent l'égalité des parties réelles ; une seule ne suffit jamais. Compilé.

**Le raccord.** Sur tout passage, le raccord réunit le premier partagé, la cellule de sortie de la Tour de
départ et la cellule d'entrée de la Tour d'arrivée qui le contiennent, l'encadrement de son énergie par les
contacts de chacune, et le transport en ce premier. Il existe sur tout passage et il est unique ; aucun champ
n'est choisi. Il est orienté quand le transport ne dépasse pas un. Tout passage qui fait avancer la hauteur
a un raccord orienté, cas diagonal compris ; un passage horizontal à hauteur au moins deux existe avec tous
ses champs et a un transport strictement plus grand que un. Le détecteur est donc complet : à hauteur de
sortie au moins deux, orienté si et seulement si la hauteur avance. Compilé. Tout ce que contient le raccord
existe aussi sur le passage horizontal : son contenu ne fournit pas l'orientation. À hauteur égale, les
numéros de cellule d'un même nombre dans deux Tours diffèrent d'un cran au plus ; les cellules de deux Tours
consécutives de la ligne se recouvrent.

**Le raccord grammatical.** Il étend le raccord par l'événement premier complet du premier partagé :
prédécesseur (l'occurrence de départ), successeur (le minimum attendu d'arrivée), deux écarts strictement
positifs, état, classes et transitions, place dans l'alternance, poids. Une adresse n'est pas un événement :
un premier appartient à une histoire. Cet événement est celui que les zéros reconstruisent ; sur tout passage
l'histoire première gagne exactement cet événement. Le pas énergétique d'un membre est le rapport de son
occurrence à son minimum attendu élevé à son écart à la ligne : neutre si et seulement si le membre est en
ligne ; à gauche il amplifie, à droite il atténue ; une histoire est neutre à chaque état si et seulement si
tous ses membres sont en ligne. Une paire hors ligne pèse strictement plus que deux membres en ligne dans
l'incrément du reste, à toute échelle ; mais l'incrément exigé ne fixe que la somme sur tous les zéros.
Compilé. Le certificat complet existe aussi sur le passage horizontal hors ligne : il n'exclut pas le
hors-ligne. Un préfixe analytique sépare les deux membres d'un passage si et seulement si la hauteur avance.
Numériquement, un passage hors ligne placé entre deux membres en ligne satisfait le quartet, l'ordre, le rang
et l'événement complet ; inséré, il viole le comptage ; substitué à deux voisins, il garde le comptage mais
s'écarte de l'incrément exigé, nettement aux rangs bas, au niveau de l'erreur de troncature aux rangs hauts.

**Le système rigide global.** Un seul objet réunit, chacune remplie par un théorème, les couches : ordre,
miroir, deux horloges, contacts, énergie, branche supérieure, raccord grammatical, détecteur, pas, grammaire
reconstruite, formule explicite, fond lisse et reste. La rigidité globale n'est pas une prémisse : c'est un
théorème. Un hors-ligne y conserve les trois égalités (reste arithmétique égal au reste spectral, grammaire
reconstruite égale à la grammaire première, géométrie et énergie du même ensemble de zéros), parce qu'elles
sont vraies quel que soit l'ensemble des zéros. Le système seul ne ferme pas.

**La capture des contacts.** La superposition des contacts du miroir sur ceux du zéro et leur entrelacement
strict sont exclusifs, contact par contact, et uniformes sur la Tour ; la superposition vaut sur la ligne ;
hors ligne, l'entrelacement est strict et la superposition est presque atteinte, sans l'être. Compilé comme
faits ; la capture, exigée de tout zéro, est la cible et n'est plus une direction.

**Les mondes témoins.** Trois fonctions de contrôle sont compilées. Le monde décalé, produit de deux copies
de zêta déplacées horizontalement en sens opposés : même support premier, même grammaire, tous ses zéros hors
ligne, poids de chaque premier modifié, comptage des zéros doublé ; il n'a aucun état engagé. Le monde de
rupture, au même support premier avec des poids multipliés par une puissance de l'entier : il garde chaque membre
en ligne de zêta et porte deux jumeaux hors ligne à une hauteur supérieure ; la consécutivité de ces membres
n'est pas compilée. La fonction fixe sans premiers, de même réflexion, même conjugaison, réelle sur la
ligne : un membre en ligne, seul à sa hauteur, puis deux jumeaux à la hauteur suivante ; son régime change
sans qu'aucun paramètre ne change. Toute loi candidate doit être fausse dans ces mondes ; une loi qui ne lit
que positions, grammaire, hauteurs, contacts ou réflexion y est vraie et ne peut pas clore. Ce qui les sépare
de zêta : le poids exact de chaque premier et le nombre de membres par unité de hauteur. La reconstruction
de l'histoire première ne reconnaît aucun premier dans le monde décalé, car chaque poids y est au moins
doublé, même pour un décalage nul. Un seul quartet inséré entre deux membres en ligne satisfait toutes les
rigidités d'indice et les identités globales de comptage ; il ne se heurte qu'à la taille de l'écart entre
les premiers et leur loi moyenne, que rien d'inconditionnel ne borne assez.

## 11. L'état engagé et la prémisse unique

**L'état engagé.** Un état engagé est un membre en ligne atteint par un passage vertical. Le code nomme aussi « état engagé »
l'ensemble des propriétés que porte tout membre en ligne, et cet ensemble équivaut à être en ligne (compilé). Un membre en
ligne porte ensemble : son
miroir est lui-même, la poussée horizontale est nulle, ses contacts sont ceux que sa hauteur détermine, son
facteur radial vaut un, la fonction réelle sur la ligne s'annule à sa hauteur. Un passage vertical existe
par théorème : zêta porte au moins deux hauteurs distinctes, sinon la somme des Tours serait une fonction
lisse nulle avant le premier événement premier, donc nulle partout, alors que la somme des premiers ne l'est
pas. Compilé. Cette existence ne localise pas les extrémités du passage sur la ligne : elle n'engage aucun membre.

**Engagé par quoi, par qui, pourquoi.** Un membre est engagé par l'annulation de son miroir. Zêta porte deux symétries :
la réflexion, qui échange une partie réelle et son complément, et la conjugaison, qui change le signe de la partie
imaginaire. Composées, elles envoient tout membre sur son miroir. Sur la ligne, et seulement sur la ligne, ce miroir est
le membre lui-même : les quatre zéros se réduisent à deux, il n'existe aucune seconde position radiale à la même hauteur,
et la seule coordonnée libre qui reste est la hauteur. C'est pourquoi, dans l'état engagé, la grille de la Tour est
placée par la hauteur seule, sans translation, et le passage qui en part est vertical. L'engagement est fait par zêta
elle-même, par ses deux symétries ; il n'est choisi par personne. Qu'un premier membre soit en ligne est un fait annoncé comme connu dans la littérature ; aucune preuve n'en est présente dans le dépôt, aucun théorème
compilé n'a pour conclusion que le membre le plus bas est en ligne : cette amorce n'est pas acquise ici. Un passage vertical
existe par théorème, sans qu'aucun de ses membres soit engagé de ce fait. Ce qui reste à établir est la transmission
de l'engagement (section 12). Les équivalences « passage par passage » disent la forme de la cible, pas l'échelle de son mécanisme :
un changement de régime n'est pas un objet d'un seul passage (il exige une entrée diagonale, un passage horizontal, une
sortie, donc au moins quatre membres et trois passages, un premier partagé par passage, ces trois premiers
consécutifs et séparés par deux écarts, et il décale d'un rang l'étiquette de tous les membres au-dessus), et la grammaire raisonne sur des fenêtres de plusieurs événements. La démonstration de l'auteur et son statut sont énoncés en section 12 ; le seul verrou en vigueur est celui de la
section 14 ; la cellule minimale de changement de régime est un fait compilé de structure, elle n'est pas un verrou.
Le monde de rupture et la fonction fixe sans premiers ont la même réflexion, la même conjugaison, la même réalité sur
la ligne, un membre engagé, et pourtant un changement de régime à l'arrivée : les deux symétries engagent, elles ne
transmettent pas seules ; la transmission passe par les premiers.

**La progression depuis l'état engagé.** Le membre suivant est unique ; depuis la ligne, il est fonction de
la hauteur de départ seule. Les lois compilées donnent, depuis un membre engagé atteint verticalement : un
passage vertical, le rang avancé d'un cran, le pas contracté, les contacts d'arrivée égaux à ceux de la Tour
de ligne à la nouvelle hauteur fois un facteur radial unique, la fonction réelle sans zéro strictement entre
les deux hauteurs, l'événement premier reproduit au raccord, le raccord orienté. Sur la position radiale de
l'arrivée, une seule inégalité : elle ne dépasse pas la ligne (fait d'inventaire, sans rôle dans la démonstration de l'auteur). Si la fibre suivante est réduite à un membre,
ce membre est engagé et tout passage qui en part est vertical. Compilé.

**Les liaisons tiennent sur l'arrivée.** Ordre, miroir, grammaire première, somme, côté arithmétique,
fonction réelle tiennent ensemble sur le membre d'arrivée. Sa partie réelle n'est pas un degré de liberté :
elle est écrite dans le côté arithmétique, dans toute représentation du reste. C'est une équivalence : elle
dit où le régime de l'arrivée est écrit, pas ce qui y est écrit. Les liaisons tiennent aussi pour deux
jumeaux de même hauteur : « une Tour par zéro » est compilé, « une Tour par hauteur » équivaut à la cible.

**Les paramètres de zêta.** Zêta est un produit, sur les premiers, d'un même facteur : ses seuls paramètres
sont les premiers, et aucun ne dépend de la hauteur. « Aucun paramètre ne change, donc le régime ne change
pas » ne suffit pas, la fonction fixe sans premiers le montre ; c'est par les premiers, et par eux seuls, que
le régime peut être transmis. Compilé.

**La persistance du régime engagé.** Seule la partie réelle change le régime. Si, sur un passage vertical
parti de la ligne, seule la hauteur évolue, le régime est transmis ; sous cette loi, tout membre au-dessus
d'un membre engagé est engagé, atteint et quitté verticalement, sans fin, par récurrence sur le rang. La loi
est nécessaire (vraie sous l'hypothèse de Riemann), elle n'est pas dérivée ; elle est conséquence de la borne
en racine carrée du reste. Compilé. Plus généralement, si une loi donne la partie réelle de l'arrivée depuis
la hauteur, la partie réelle et l'événement du départ, et si elle préserve la ligne, la ligne est invariante.

**La prémisse unique.** La seule prémisse définie comme proposition nommée dans le code est : aucun changement de régime n'est possible ;
(la prémisse en vigueur de la démarche, en hypothèse explicite, est depuis le 2026-10-06 le premier gain collectif maximal, section 12) ; à aucune
jonction entre deux passages consécutifs le régime ne change, dans aucun sens. Elle ne porte ni sur la
hauteur, ni sur une taille, ni sur un fait annexe. Elle équivaut à la cible, sans aucune condition annexe ;
le bas de la chaîne est réglé par le théorème d'engagement. Lue sur un pas vertical parti de la ligne :
l'arrivée ne peut pas passer à droite de la ligne (compilé) ; qu'elle ne passe pas à gauche équivaut à
l'absence de changement de régime à l'arrivée (compilé) ; sous la prémisse, de la ligne à une hauteur on
arrive sur la ligne à la hauteur suivante (compilé). Cette lecture caractérise la prémisse sur un pas ; elle n'est pas le verrou en vigueur (sections 12 et 14), et la partie réelle de
l'arrivée ne dépassant pas un demi n'est pas une étape de la démonstration de l'auteur.

**Portée de la cible locale.** La loi locale de conservation dit : sur tout passage parti de la ligne,
l'arrivée est en ligne. Avec l'amorce — les membres sans prédécesseur en ligne sont en ligne — elle donne
l'hypothèse de Riemann ; seule, elle n'est pas l'hypothèse de Riemann. Sur un pas vertical, arrivée en ligne
équivaut à aucun changement de régime à l'arrivée. Le monde décalé n'a aucun état engagé et ne teste pas
cette cible ; le monde de rupture et la fonction fixe sans premiers la violent, alors qu'ils ont miroir,
conjugaison et réalité sur la ligne : la loi n'est pas structurelle, elle doit lire les premiers et leurs
poids exacts. Compilé.

## 12. Ce que la démarche a établi sur la flèche, et ce qui manque

**Composer la grammaire et la cinématique.** La position de l'occurrence d'un membre dans sa Tour se
découpe en une part que la hauteur détermine et une part radiale, nulle si et seulement si le membre est en
ligne. Sur tout passage, le déplacement de cette position est exactement le déplacement au raccord (hauteur
et phase) plus la progression continue de l'événement (la hauteur fois le logarithme du rapport de deux
premiers consécutifs). Sur une chaîne de passages, la somme des raccords et des progressions est le
déplacement total ; une sommation d'Abel télescope la progression première et le déplacement de hauteur en
termes d'extrémités ; à l'intérieur de la chaîne, les parts radiales disparaissent. Avec l'alternance, deux
progressions consécutives valent au moins trois fois le plancher d'un pas. Compilé. C'est une identité,
vraie pour toute partie réelle : elle ne donne aucune borne inférieure sur l'avancée de hauteur (le passage
de même hauteur la satisfait), et elle ne fixe la partie réelle de l'arrivée qu'à travers la position de son
occurrence, que rien ne fixe. Elle tient mot pour mot dans les mondes témoins.

**L'excès d'une transition.** L'excès d'une transition est ce que la position de l'occurrence avance
au-delà de la progression grammaticale. En ligne vers en ligne, il vaut la part de hauteur ; sur une
diagonale partie de la ligne, il est strictement inférieur ; à même hauteur, la part de hauteur est nulle et
l'excès strictement positif. Dans la première configuration hors ligne permise par l'ordre (ligne, diagonale,
même hauteur), le déficit de la première transition est remboursé exactement par la seconde ; sur toute
chaîne partie de la ligne, la somme des excès moins la somme des parts de hauteur est la seule part radiale
de l'arrivée, quelle que soit la longueur. Compilé. À aucun nombre de transitions la liberté radiale n'est
confrontée : seul un énoncé sur la position elle-même confronterait.

**L'inventaire au point engagé.** Tout ce que porte le départ (miroir, poussée, facteur radial, contacts,
phase, pas, fonction réelle) a une composante radiale nulle sur la ligne. La grammaire est fonction du rang
seul. Ce qui traverse le passage (contacts, registre, pas, transport) lit la partie réelle de l'arrivée et
est neutre si et seulement si l'arrivée est en ligne. Le générateur — la fonction qui, depuis la ligne,
donne la hauteur et la partie réelle de l'arrivée depuis la hauteur de départ — existe, puisque zêta
l'écrit ; « le générateur fixe la ligne » équivaut à « seule la hauteur évolue ». Compilé. Aucun mécanisme de
l'inventaire ne calcule le générateur.

**La réponse radiale aux poids.** Dans la famille qui déplace zêta d'une quantité fixée, chaque poids
premier est multiplié par une puissance de l'entier qui le porte, chaque membre se déplace de la même
quantité, et la réponse radiale est nulle exactement quand le module de chaque poids est conservé. Pour toute
fonction réelle sur la ligne, tout membre simple en ligne et toute direction de déformation réelle, la
réponse radiale au premier ordre est nulle. Compilé. Cette annulation vient de la réflexion et de la
simplicité ; elle ne lit aucun poids et tient pour la fonction fixe sans premiers : elle ne transmet pas le
régime. Non compilé : l'existence de la courbe suivie ; le théorème classique selon lequel aucune déformation
des coefficients ne conserve exactement l'équation fonctionnelle.

**Le résidu de changement et ses prédicteurs.** Le résidu de changement de l'arrivée est sa position réelle
dans sa Tour moins sa position dans la Tour de ligne à la même hauteur ; le premier y disparaît, il ne reste
que la phase. Toutes les lectures du changement disent la même chose : le résidu est nul exactement quand
rien n'a changé ; il tient dans une fenêtre qui se resserre comme l'inverse de la hauteur. Un prédicteur ne
reçoit que la hauteur de départ et le rang ; une fonction de ces données égale au résidu existe, puisque zêta
produit le suivant, et l'existence d'un prédicteur exact et nul dans l'état engagé équivaut à « seule la
hauteur évolue ». La croissance du reste encadre le résidu sans lire aucun zéro ; « résidu nul partout »
équivaut à la borne en racine carrée du reste. Compilé. Une formule arithmétique du résidu
par passage, ou la borne, ne sont pas dérivées ; ce n'est pas le verrou en vigueur (section 14).

**Rétro-ingénierie des trois cents premiers membres (contrôle numérique).** Quatre formules ressortent des
données. Le rang seul donne la hauteur à une fraction d'espacement près. Relation tangentielle : un membre en
ligne est à la hauteur où une somme pondérée des positions des entiers jusqu'à la racine de la hauteur, lues
dans la Tour de ligne, s'équilibre ; elle localise les trois cents membres et le successeur sur chacun des
passages, mais c'est une seule équation réelle, qui ne localise que des membres en ligne. Le poids exact se lit
collectivement : en moyenne sur les membres, la position d'un entier est décalée exactement quand c'est une
puissance de premier, proportionnellement à son poids. Un prédicteur du résidu sans lire la partie réelle :
sur un intervalle de hauteurs choisi sans les zéros, le nombre de membres moins le nombre de changements de
signe de la fonction réelle ; il est nul sur les trois cents intervalles et se déclenche dans la fonction fixe
sans premiers. Aucune liaison propre à un passage entre la grammaire, la position de l'occurrence et le pas de
hauteur. Ce que les données ne montrent pas : pourquoi ce prédicteur reste nul à toute hauteur.

**Le bit de changement.** Sur un passage vertical, pas de changement équivaut à : aucun membre hors ligne
n'est atteint avant que la fonction réelle ne s'annule au-dessus du départ ; un changement de signe fixe
l'échéance de l'arrivée. Compilé. Verdict de l'auteur : cette piste (course, fonction réelle, comptage de
fenêtre) n'est pas la bonne démarche, elle détourne vers une comparaison de zéros en hauteur ; elle n'est pas
poursuivie.

**La flèche entre deux événements canoniques.** La flèche réunit le départ engagé, l'avancée du rang d'un
cran et le premier partagé ; elle existe sur tout passage parti de la ligne. Avant l'arrivée, la position du
premier partagé dans la Tour de départ est sa position de ligne. Dans la Tour d'arrivée, la différence entre deux positions de
lecture ne lit que la hauteur et efface le décalage commun sans démontrer qu'il est nul, et la cellule d'entrée est celle de la Tour de ligne hors d'une marge qui
se referme avec la hauteur. La composante radiale est portée par une seule quantité : la position du premier
partagé dans sa cellule d'entrée, position de ligne plus le résidu ; la conservation équivaut à « le premier
partagé entre à sa position de ligne ». Le premier partagé se déplace d'une Tour à l'autre de sa part de
hauteur plus le résidu, sans terme de grammaire. Compilé. Ce n'est pas un point privilégié : la translation
étant rigide, la même équivalence vaut pour tout nombre (section 4).

**La flèche d'entrée écrite sur le terme d'Euler (caractérisation, non verrou en vigueur).** La flèche équivaut à la loi locale de conservation sur la moitié
supérieure ; avec l'amorce, elle équivaut à la cible. Sous forme d'événement : le module du terme d'Euler
d'un entier plus grand que un, pris au membre d'arrivée, vaut l'inverse de la racine de cet entier si et
seulement si l'arrivée est en ligne, quel que soit l'entier ; le facteur d'Euler d'un premier ne s'annule en
aucun membre : il lit l'arrivée, il ne la fixe pas. Compilé. Numériquement : flèche et amorce vérifiées sur
les mille premiers membres par le comptage de Turing, sans le poids ; la position du premier partagé dans sa
cellule est équirépartie ; le produit d'Euler tronqué au premier partagé marque la hauteur d'arrivée mais
aussi les zéros hors ligne du monde décalé ; le poids exact sépare le monde décalé à chaque événement.

**Premiers pointés, trois cents membres contre cent cinquante paires.** Occurrence, minimum attendu, états
et classes sont des fonctions du rang ; même Tour, la différence de position ne lit que la hauteur ; même hauteur,
translation rigide ; même premier, hauteur plus phase. Numériquement, aux mêmes hauteurs : mêmes premiers
pointés, même alternance, position d'entrée du premier partagé décalée de moins d'une fraction de cellule égale à l'inverse de pi fois
la hauteur, avec la même médiane ; ce qui sépare est l'amplitude et le comptage (un membre de plus sur chaque
intervalle de paire). La grammaire, les premiers pointés et les classes sont aveugles au régime.

**Tour = grille infinie : les deux réponses.** Le régime des zéros en ligne est caractérisé, sans prémisse :
une grille par hauteur, contraction sans translation d'un membre en ligne au suivant. Un régime concurrent
est détectable comme lecture, pas comme déclencheur : il se lit en n'importe quel point de la grille et dans
le transport, qui cesse d'être le même en tout point ; ces deux lectures demandent la partie réelle. Sans
elle, seuls le comptage (nombre de membres contre changements de signe) ou le poids le détectent. Sur les
premiers seuls, il ne laisse qu'une trace statistique : une fraction de premiers proportionnelle au résidu
change de cellule, le premier partagé jamais. Compilé ; trace numérique vérifiée sur trois cents hauteurs.

**La démonstration de l'auteur, son statut, l'erreur de référence et le verrou unique.** Énoncé de l'auteur, mot pour mot, à
employer partout où la démonstration est énoncée (le régime ON est le régime des membres en ligne) :

> Une fois le régime ON engagé, du fait de l'enroulement des Tours, la partie réelle du zéro suivant est forcément la même
> que celle du zéro qui a engagé le régime.

Écarts de premiers dans la démonstration (auteur) : c'est uniquement dans le régime ON que les écarts de premiers sont
atteints par la hauteur seule ; la partie réelle étant fixée, la hauteur doit progresser suffisamment. La phrase générale
selon laquelle, dans une Tour, l'écart entre deux premiers serait lu par la hauteur seule n'est pas un énoncé de la
démonstration et n'y figure pas ; l'identité compilée sur la différence de deux positions de lecture dans une même Tour
reste dans l'inventaire avec sa portée : elle efface le décalage commun sans démontrer qu'il est nul. La phrase selon
laquelle la partie réelle du zéro atteint ne dépasse pas un demi n'est pas non plus la démonstration de l'auteur : elle ne
figure dans aucun énoncé de la démonstration ; le théorème compilé qui la porte reste dans l'inventaire, sans rôle dans la
démonstration.

Statut, « prouvé ou pas, nous verrons » (auteur) :

| Étape | Portée exacte |
|---|---|
| Existence d'un passage vertical | Établie ; ne localise pas ses extrémités sur la ligne. |
| Propriétés d'un membre ON | Établies sous l'hypothèse qu'il est ON ; ne produisent pas ce membre. |
| Sortie d'un état engagé | Établie : le passage suivant avance en hauteur. |
| Propriétés de l'arrivée | Établies : pas réduit, encadrement des contacts à l'infini. |
| Écarts de premiers dans le régime ON | Énoncé de l'auteur : la partie réelle étant fixée, les écarts ne sont atteints que par la hauteur, qui doit progresser suffisamment. Compilé : seulement l'identité des différences de lecture dans une même Tour, qui efface le décalage commun sans démontrer qu'il est nul. |
| Énoncé de l'auteur (régime ON engagé et enroulement, donc même partie réelle au zéro suivant) | Écrit dans le build principal ; compile ; conditionnel à la domination individuelle de toute amplitude par celle d'un même zéro sur tout l'horizon, qui est la conclusion du raccord ouvert de l'unique prémisse minimale (premier gain collectif maximal à tout rang) ; ni la prémisse ni ce raccord ne sont dérivés (2026-10-06). |
| Budget collectif de la somme de tous les zéros suivants (la somme à l'infini, signée, de toutes les contributions au-dessus d'une hauteur reste sous un multiple de l'échelle de la ligne) : propriété à démontrer, jamais un fait acquis | Compilé sans condition : un seul zéro suivant hors ligne réfute ce budget, parce que ce zéro et son miroir, de même hauteur, sont lus chacun dans la somme signée, sans compensation durable par les autres ; le budget caractérise « tous les zéros plus hauts sont en ligne », conjugués et multiplicités compris ; le reste exact des premiers est égal à une part basse, somme finie dont aucun membre n'est supposé en ligne, plus la somme de tous les suivants : identité, qui ne donne aucune borne. Compilé sous hypothèse : sous ce budget à la hauteur du zéro engagé, la partie réelle du zéro suivant est celle du zéro qui a engagé le régime. Non dérivé : le budget lui-même ; aucune expérience sur grille finie ne le certifie. |
| Réduction au cas bas : pour le successeur immédiat du zéro engagé, le côté au-dessus de la ligne est exclu ; il reste le côté strictement sous la ligne | Compilé sans condition, pour toute paire miroir hors ligne : le retard de phase du membre sous la ligne dépasse strictement l'avance de phase de son miroir ; les contacts de la paire, pris ensemble, sont au-delà de ceux de la Tour de ligne de même hauteur ; les dilatations de demi-tour des deux membres se compensent exactement ; la dérive radiale est tournée vers l'intérieur sous la ligne, vers l'extérieur au-dessus ; la hauteur est gardée au passage qui quitte le membre bas ; le budget collectif est réfuté. Ces lectures ne dépendent que de la partie réelle et de la hauteur : elles valent dans tout monde. Non dérivé : la contradiction du cas bas. |
| Les deux zéros suivants : le premier zéro sous la ligne et le zéro qui le suit à hauteur gardée | Compilé, et présent dans le but avec un second zéro effectivement produit : le premier zéro sous la ligne est captif au raccord qui l'atteint ; le passage qui le quitte garde la hauteur ; le second zéro est strictement plus à droite et au plus à la position réfléchie du premier (il n'est démontré ni qu'il est le miroir, ni qu'il est au-dessus de la ligne) ; sa Tour est une Tour distincte de même intervalle logarithmique, contacts translatés en deçà ; elle dépasse celle du premier en des premiers arbitrairement grands ; la captivité au raccord qui quitte le premier est fausse par calcul. Mesure : raccord du premier au second renversé dans tous les cas calculés, vrai aussi dans le monde témoin. Non dérivé : une contrainte acquise que cette fenêtre contredirait. |
| Audit des figures du surplus hors ligne : amplitude, signe, paire, somme collective | Trois objets à ne pas confondre : le terme brut d'une Tour, le terme lissé du reste, la somme de tous les termes. Compilé : au contact propre d'une Tour, la partie réelle du terme brut vaut l'amplitude avec un signe qui alterne d'un contact au suivant (le surplus signé alterne, seul le surplus d'amplitude est positif) ; pour une paire miroir prise avec ses dénominateurs exacts, le carré de l'amplitude de la somme est la somme des deux carrés plus un terme croisé strictement positif, donc la paire dépasse chacun de ses deux membres en tout point : aucune compensation à l'intérieur de la paire. La forme en cosinus hyperbolique n'est exacte que sans les dénominateurs. Mesuré : le dépassement individuel du miroir haut a lieu au-delà d'une abscisse d'égalité calculée, vérifiée des deux côtés ; il n'est interdit par aucun énoncé démontré. La somme signée de tous les suivants, sur une plage finie, reste dans une plage où une paire proche de la ligne ou haute ne se distingue pas ; la queue n'est pas certifiée. Le reste lissé exact des premiers est reconstruit par les zéros publiés, vérification de zéros connus sur une plage finie. Non dérivé : toute borne de la somme collective ; toute contradiction du cas bas. |
| Comptage certifié, Zeta 23 et reste exact : ce qui interdit, ce qui détecte, ce qui reste indéterminé | L'exclusion du côté haut est locale : elle porte sur le membre atteint par un passage où la hauteur avance strictement ; le miroir d'un membre bas est atteint à hauteur égale, aucun énoncé démontré ne lui interdit d'être au-dessus de la ligne sans hypothèse équivalente à la conclusion. Sous une hauteur de coupure, le nombre total de zéros de la bande, compté avec multiplicité par une méthode qui ne suppose rien sur leur position, est égal au nombre de changements de signe de la fonction réelle sur la ligne : la liste des trois cents, et des cinq mille, premiers zéros est exhaustive, tous simples et en ligne ; ajout d'une paire, remplacement d'un zéro en ligne par une paire, fusion de deux zéros en ligne en une paire, zéro rendu double y sont interdits ; c'est un calcul certifié hors du code compilé, et il ne dit rien au-dessus de la coupure. Le reste exact des premiers ne détecte avec garantie qu'une perturbation basse, déjà exclue par le comptage, et la lit par le nombre et la position des termes, pas par la partie réelle ; au-dessus de la coupure, la queue inconnue absorbe toute paire. Zeta 23 démontre des proportions asymptotiques (simples en ligne, distincts en ligne, distincts) : aucune ne désigne un préfixe de zéros ordonnés, aucune ne certifie le premier zéro ni une fenêtre ; sa méthode est démontrée incapable de séparer une paire hors ligne d'un zéro double en ligne. Compilé : la paire miroir prise en termes lissés dépasse aussi chacun de ses membres en tout point. Non dérivé : le budget collectif au-dessus du zéro engagé, l'unicité du membre à la hauteur du successeur, la captivité au raccord sortant. |
| Fenêtres de douze, vingt-quatre et trente-six transitions : progression des premiers, de la phase et de la hauteur | Une fenêtre de m transitions réunit m plus un membres et m plus une occurrences premières. Démontré : au-delà de trois, deux écarts consécutifs entre premiers font au moins six, sans que les écarts alternent strictement entre deux et quatre ; un nombre pair de transitions fait avancer la suite des premiers d'au moins trois fois ce nombre ; la classe d'un écart modulo six est la transition entre les deux résidus. La progression de phase d'un membre est strictement positive même quand la hauteur ne bouge pas : c'est une progression de phase, pas de hauteur. L'identité qui compose progression première et déplacement de hauteur est vraie pour toute suite de hauteurs, la suite constante comprise : les premiers n'exigent aucune progression de hauteur. Le comptage avec multiplicité (résultat publié, non compilé ici) limite le nombre de membres à une même hauteur, donc la fréquence des passages de même hauteur dans une fenêtre ; il permet toujours une paire isolée. Les insertions hypothétiques de paires ne changent pas la progression première de la fenêtre, seulement sa hauteur ; aucune quantité du registre ne borne ce déficit. Non dérivé : une progression de hauteur minimale imposée par les événements premiers, l'exclusion d'une paire isolée. |
| Inversion tangentielle autour de deux et trois, et amorce certifiée des trois premiers zéros | Démontré, pour tout zéro et tout indice : deux contacts successifs rendent la hauteur et la partie réelle du membre, et deux membres qui ont la même paire de contacts indexée sont confondus ; l'inversion d'un membre ne lit que ses propres contacts. Pour toute partie réelle et toute hauteur, tout réel positif est dans une cellule et une seule : l'encadrement d'un premier ne sélectionne rien. Un premier égal à un contact fixe la partie réelle en fonction de la hauteur ; la partie réelle est dans la bande si et seulement si la phase dépasse l'arc de la hauteur ; deux premiers tous deux contacts d'une même Tour quantifient la hauteur. L'invariance de la cotangente par un demi-tour ne suffit pas : seul le contact indexé fixe l'indice. Mesuré et certifié hors Lean : autour de deux et trois, la contrainte est satisfaite par une région de dimension deux et par les cinquante et un premiers zéros, pas seulement le premier ; deux et trois ne sont pas des contacts du premier zéro ; supposer trois comme pivot suppose le rang nul, donc le comptage. Les trois premiers zéros sont certifiés séparément, indépendamment de l'hypothèse de Riemann, par comptage total dans la bande avec multiplicité à quatre coupures (zéro, un, deux, trois, par deux méthodes) et un changement de signe sur la ligne dans chaque tranche : chacun est simple et sur la ligne, aucun zéro hors ligne ne les précède ni ne s'intercale, aucun ne partage leur hauteur. Certificat externe, pas preuve formelle. Non dérivé : une propriété acquise au premier zéro et conservée par la succession ; la transmission au-delà de la troisième racine. |
| Décroissance des intervalles, prédicteur sans fuite, fenêtre hors ligne conjointe, raréfaction première | Démontré : la largeur logarithmique d'une cellule ne lit que la hauteur ; la contraction d'une Tour à la suivante est exactement le rapport des hauteurs ; le logarithme d'un contact se sépare en une part de rétrécissement, fixée par la hauteur, et une part de translation, fixée par la phase ; la phase de tout membre de la bande est fixée par la hauteur à moins de l'inverse de la hauteur, la partie réelle ne l'est pas ; deux Tours de la bande dont les hauteurs diffèrent d'environ un cinquième ou plus sont emboîtées à tout indice, quelles que soient leurs parties réelles ; la fenêtre formée d'un prédécesseur en ligne, d'un membre bas, de son miroir à la même hauteur et d'un suivant satisfait contacts, largeurs, phases et emboîtements pour tout écart à la ligne, si petit soit-il ; il existe des suites d'entiers sans premier de toute longueur. Mesuré, avec un théorème de comptage cité : la hauteur d'un rang donné est encadrée à quelques espacements près ; le comptage garantit une contraction sur une fenêtre de quelques transitions, jamais sur un passage ; un passage de même hauteur dans une fenêtre de douze, vingt-quatre ou trente-six transitions est compensé par les autres ; la raréfaction première n'entre dans les Tours que par la phase et n'interdit ni ne limite un passage de même hauteur. Seul le comptage exact certifié, hors Lean et sous la coupure, vide la région hors ligne. Non dérivé : une contraction à chaque passage. |
| Régime en ligne seulement : l'anneau radial entre deux Tours successives | Chaque Tour étant ramenée à l'échelle de la ligne par la même normalisation, démontré : la Tour d'un zéro en ligne est un cercle dont le rayon ne dépend que de sa hauteur et décroît strictement quand la hauteur monte ; entre deux Tours en ligne de hauteurs distinctes, l'anneau a pour limite haute le rayon de la Tour actuelle et pour limite basse le rayon de la Tour suivante, son épaisseur est strictement positive, et une Tour en ligne est dans l'anneau si et seulement si sa hauteur est entre les deux ; si la hauteur de la Tour suivante est encadrée par deux bornes, son rayon et l'épaisseur de l'anneau sont encadrés par les rayons de ces bornes ; les rayons des Tours en ligne passent sous tout seuil positif au-delà d'une hauteur explicite sans jamais être nuls : zéro est la limite basse de l'ensemble, pas la frontière basse d'un anneau. Portée : la limite basse précise d'un anneau exige la hauteur de la Tour suivante ; la borne de hauteur tirée du comptage est une hypothèse, son calcul et sa validation anneau par anneau ne sont pas faits ; tout suppose les zéros concernés en ligne et rien ne démontre que le zéro suivant l'est ; cette frontière radiale n'est pas l'ordre des contacts de l'enroulement. Précisions (auteur, 2026-10-06) : la caractérisation exacte de l'anneau, pour deux membres en ligne de hauteurs croissantes et un troisième membre en ligne, est : son rayon est entre les deux limites si et seulement si sa hauteur est entre les deux hauteurs ; elle concerne des membres en ligne et ne choisit pas à elle seule le prochain zéro. Limite basse : entre deux hauteurs en ligne finies, toute Tour en ligne a un rayon au moins égal à la limite basse, strictement positive ; l'absence d'un plancher uniforme quand les hauteurs deviennent arbitrairement grandes ne supprime pas cette borne locale ; mais la limite basse de l'anneau pour le membre atteint est une fonction qui attend « ce membre est en ligne » : conditionnelle, elle ne peut pas servir à le prouver. Limite haute : le rayon du zéro engagé est acquis ; la domination de la Tour atteinte par ce rayon sur les abscisses au moins un est démontrée équivalente à une condition explicite d'écart de hauteur, non dérivée pour un membre bas ; sur tout l'axe positif, la domination équivaut à « même partie réelle et supports ordonnés », donc jamais pour un membre bas. |
| Régime en ligne seulement : croisement des lectures sur les mêmes membres, et ce que l'événement supplémentaire impose | L'anneau est défini entre deux Tours en ligne données, sans consécutivité ; entre deux membres consécutifs, aucune Tour en ligne n'a son rayon strictement entre les deux. Sans supposer le zéro suivant en ligne, les données précédentes imposent : une hauteur strictement nouvelle, un intervalle entre contacts strictement réduit, une phase dans une fenêtre étroite au-dessus de la phase de ligne, tous les contacts égaux aux contacts de ligne multipliés par un seul facteur enfermé dans une fenêtre étroite, et un rayon borné par le haut seulement. Aucune limite basse uniforme jusqu'à l'infini n'est imposée à un membre bas ; sur tout domaine fini il garde un plancher strictement positif. Au contact propre d'un zéro en ligne, son terme brut est réel, de signe alterné, de taille fixée par la hauteur ; son terme dans le reste lissé est ce terme brut divisé par un facteur propre au zéro : transfert membre par membre, rien sur la somme. La position du suivant aux contacts du zéro engagé est fixée par les hauteurs et les phases. Dans le cas bas, la paire sort de tout anneau : conséquence, pas contradiction. La limite basse globale des rayons équivaut à des hauteurs en ligne non bornées, non démontrées ici. Identités déterministes et bornes démontrées ; le facteur unique n'est pas fixé à un : description géométrique et encadrement prédictif haut, pas une obligation de conservation. |
| Persistance | Théorème conditionnel à une loi de transmission universelle. |
| RH | Fermeture conditionnelle à la transmission et à une amorce couvrant le début de l'énumération. |

Formulation correcte de l'état : plusieurs propriétés et compositions conditionnelles sont compilées ; la transmission
reste ouverte ; l'amorce annoncée comme connue (littérature) est distinguée d'une preuve présente dans le dépôt, dont il
n'existe aucune.

Erreur de référence du build principal (une seule erreur, un seul but non résolu ; sortie du script de statut). L'énoncé du
théorème demande toujours que la partie réelle du zéro atteint soit celle du zéro qui a engagé le régime. La preuve a déjà exclu,
pour ce zéro atteint par un passage où la hauteur avance, le côté au-dessus de la ligne ; il reste le cas où sa partie réelle est
strictement sous un demi, et dans ce cas une contradiction doit être produite. Le contexte contient les faits du zéro engagé (en
ligne, Tour symétrique, miroir annulé, demi-tour exact), des faits vrais pour toute partie réelle (place et enroulement à
l'infini, lectures d'écarts dans une même Tour, milieu de la paire, premier partagé, rang, progression première des fenêtres),
des équivalences dont aucun côté n'est acquis (budget collectif), et les conséquences du cas bas (miroir au-dessus de la ligne à
la même hauteur, passage suivant de même hauteur, captivité de ce passage fausse, second zéro à la même hauteur, paire qui dépasse
chacun de ses membres). L'ancienne forme du but, l'égalité des parties réelles affichée telle quelle, précède cette réduction : elle
est périmée.

Verrou sémantique unique, fixé par l'auteur (2026-10-09) et traduction du but affiché par le compilateur au dernier build : Depuis un zéro ON engagé, prouver que les obligations du passage authentique et de la reconstruction arithmétique exacte maintiennent l'annulation du miroir : le prochain membre conserve la même partie réelle et la progression se poursuit par la hauteur.

Les formes équivalentes compilées : grille d'arrivée non translatée, transport le même en tout point, partie réelle de
l'arrivée égale à un demi, miroir de l'arrivée annulé ; elles caractérisent la cible locale, elles ne la dérivent pas. Aucune
loi qui ne lit que la géométrie ne la donne à elle seule dans les mondes témoins, où la translation existe ; le canal qui
sépare ces mondes est l'amplitude, c'est-à-dire le poids exact des premiers. La forme globale est inchangée : la prémisse
unique équivaut à la cible, qui équivaut à la borne en racine carrée du reste arithmétique ; ces équivalences globales
caractérisent la cible, elles ne sont pas le maillon. Les énoncés compilés rencontrés plus bas (plancher radial, prison à
l'infini, loi de fenêtre, passage de même hauteur, captivité, grille non translatée) décrivent des faits avec leur portée
exacte ; aucun n'est le verrou.

**Les routes de fermeture, réunies en une seule.** Entre deux membres, deux transports sont orthogonaux : le transport
vertical, avancée de la position d'un même réel d'une Tour à l'autre, ne lit que les hauteurs et les phases ; le
transport radial, pente du rapport d'amplitude, ne lit que les parties réelles. L'enroulement, la fréquence et la
résolution appartiennent au premier ; le changement de régime appartient au second. Toutes les routes ouvertes s'y
ramènent, par des énoncés compilés. La route arithmétique compilée part des premiers et de leur poids exact, passe par
le reste lissé de la somme pondérée des premiers, puis par son exposant de croissance, la bande des parties réelles et
le transport radial ; le logarithme intégral n'y figure pas, il est une lecture macroscopique séparée (E153).
Premièrement, la route du transport : tous les transports radiaux plats équivaut
à la cible, sans amorce, parce que le transport d'un membre vers son miroir, à la même hauteur, vaut un moins deux
fois sa partie réelle ; le miroir fournit l'ancre que l'amorce fournissait. Deuxièmement, la route du reste : une
borne de croissance du reste arithmétique, défini par les seuls premiers, place tous les membres dans une bande
symétrique autour de la ligne, force son exposant à valoir au moins un demi, et borne tout transport radial par
deux fois l'exposant moins un ; à l'exposant un demi tous les transports sont plats. La forme sans facteur
logarithmique et la forme « un demi plus tout epsilon » équivalent chacune à la cible ; l'absence de facteur
logarithmique tient au lissage, qui donne à chaque membre un coefficient absolument sommable ; pour la somme non
lissée les logarithmes reviennent. Troisièmement, le lien entre les deux : aucun membre ne peut être compensé par un
autre dans le reste, parce que la lecture du pôle, par la transformée de Mellin et le prolongement analytique, lit
chaque exposant séparément ; sous une borne d'exposant donnée, le plus haut des deux exposants d'un membre et de son
miroir ne la dépasse pas. L'inégalité selon laquelle le paquet nu d'un membre et de son miroir ne descend pas sous la
loi critique, avec égalité exactement en ligne, est vraie, mais elle ne porte ni les coefficients de la formule
explicite ni les phases ; elle n'est pas l'argument d'anti-compensation. Numériquement (E152), le transport radial entre hauteurs consécutives, lu sur les premiers seuls, est plat
dans zêta et aussi dans le monde témoin ; seule la pente rapportée à la racine carrée sépare le témoin. La platitude
entre hauteurs ne fournit donc pas l'ancre ; l'ancre est l'exposant critique du reste. Les routes de la prémisse
unique, de la flèche d'entrée, du résidu de changement et du transport aboutissent ainsi à une seule quantité :
l'exposant de croissance du reste arithmétique lissé, dont la valeur un demi caractérise la cible ; sa dérivation depuis le poids exact des premiers n'est pas acquise, et ce n'est pas le verrou en vigueur (section 14).
Cet exposant est désormais un seul nombre, la borne inférieure des exposants admissibles. Il est encadré sans
condition entre un demi et un : la borne basse vient de l'existence des membres, la borne haute des premiers seuls,
par la positivité des poids et la majoration de Chebyshev ; la cible équivaut à ce que ce nombre vaille un demi
(compilé, E153). La borne haute ne redonne que la bande fermée, plus faible que la bande ouverte connue. Tout exposant
strictement inférieur à un donnerait déjà une bande fixe sans zéro ; aucun n'est dérivé, et la difficulté est déjà
là, pas seulement dans le dernier pas vers un demi. Audit de la positivité (E153) : la positivité des poids ne donne
que l'exposant un ; après soustraction du fond le reste change de signe ; les mondes témoins ont le même support premier,
des poids positifs (au moins le double du poids exact), un axe réel sans zéro, et des exposants qui parcourent tout
l'intervalle de un demi à un. Aucune propriété de signe, théorème de Landau compris, ne peut donc porter l'exposant
un demi ; ce qui sépare est la taille exacte du poids, qui égale celle du monde de référence exactement quand le
décalage est nul (compilé). Le canal est écrit en réel : chaque couple conjugué contribue un cosinus de la fréquence
de sa hauteur, d'amplitude la puissance de sa partie réelle, et cette somme réelle reconstruit le reste calculé sur
les premiers seuls (E153).
Énergie quadratique et résolution de la Tour (E154). Mettre le reste au carré change l'amplitude en énergie positive
et double l'exposant radial : l'énergie cumulée sur l'échelle logarithmique croît avec l'exposant un dans zêta et un
plus deux fois le décalage dans le monde témoin. Les compensations ne disparaissent pas, elles deviennent des termes
croisés ; ceux de hauteurs distinctes s'éteignent en moyenne, celui du paquet miroir, de même hauteur, ne s'éteint
pas ; l'excès du témoin est porté par le seul membre au-dessus de la ligne. Chaque cellule de la Tour d'un membre est
un demi-tour de son propre terme : elle le lit à pleine amplitude, et l'énergie propre par unité de largeur est la
même d'une cellule à la suivante exactement quand le membre est en ligne (compilé, caractérisation vraie dans tout
monde). À la résolution de la Tour, l'énergie de cellule rapportée au fond se découpe en deux facteurs : un transfert
(énergie rapportée à la somme des carrés des poids) et la taille des poids rapportée au fond. Le premier est le même
dans zêta et dans le témoin, par construction, car dans une cellule le poids du témoin n'est que celui de zêta
multiplié par un facteur presque constant ; il ne teste aucune loi, mais il est nettement plus petit que pour un
ensemble aléatoire : les premiers sont plus réguliers que le hasard à cette résolution. Le second sépare : il reste
borné dans zêta, car le poids d'une puissance de premier ne dépasse pas son logarithme, et la somme des carrés des
poids a l'exposant critique depuis les premiers seuls (compilé) ; il croît dans le témoin, dont le poids au carré
dépasse quatre fois celui de zêta sauf au décalage nul (compilé). La borne quadratique critique suivrait de ces
deux facteurs si le transfert était borné à toutes les résolutions ; ce transfert n'est pas dérivé, il porte toute
la difficulté, et le témoin ne peut ni le confirmer ni le réfuter.
Lecture exacte de l'axe algébrique et aveuglement de la diagonale (E155). Le logarithme intégral est un fond
macroscopique de comptage, une moyenne ; il ne dit le contenu d'aucune cellule. Les objets locaux sont exacts : les
contacts, où la projection réelle du terme propre vaut son rayon au signe près et où l'oscillation ne cache pas
l'amplitude (compilé) ; les cellules d'un demi-tour ; le rayon ; les premiers, leurs poids et leurs écarts. L'écart
entre deux premiers consécutifs est la différence de leurs poids (compilé) ; la Tour d'un membre le lit trois fois :
en demi-tours par la hauteur, en amplitude par la position radiale, en énergie par le double de la position radiale
(compilé). Quand la hauteur monte, le même écart est traversé par de plus en plus de contacts : la Tour sur-résout
l'axe discret, elle ne le moyenne pas. Le long d'une chaîne d'événements, toute lecture cumulée se télescope : elle
ne garde que les extrémités, ni les écarts intermédiaires ni leur ordre (compilé) ; l'écart radial d'une paire
miroir, cumulé sur les écarts exacts, est le facteur d'amplitude des extrémités, c'est-à-dire la translation rigide
déjà connue, et non une contrainte nouvelle. Trois niveaux de taille exacte des poids sont à distinguer : même valeur
absolue, même carré, même valeur signée ; le troisième est zêta elle-même et ne fournit aucun témoin. Aux deux
premiers niveaux, un monde de même support premier, de même valeur absolue des poids et de même somme des carrés,
terme à terme, a la même borne critique de diagonale (compilé) ; E155 en construit un dont les signes sont organisés
de façon cohérente : il porte des membres hors ligne, son énergie prend l'exposant double de leur partie réelle, et
son transfert croît sans borne. La diagonale ne contrôle donc pas le transfert. Les mondes séparent ainsi : ordre
détruit localement, par signes aléatoires ou ensemble aléatoire de même densité, transfert au niveau du hasard,
borné et critique ; zêta, transfert nettement plus petit que le hasard à toutes les résolutions mesurées, sans
croissance ; écarts permutés sur de longues plages, même distribution d'écarts, transfert énorme aux résolutions
grossières et presque normal aux résolutions fines ; signes cohérents, transfert croissant. Une borne quadratique n'est
pas la pièce manquante, et une loi de corrélation des poids signés sur toute l'histoire ne l'est pas davantage : ce
serait encore une propriété globale, équivalente à la cible. Le verrou en vigueur est celui de la section 14.
Réponse collective à chaque marche, diagonale et croisés (E137bis). La flèche consolidée réunit quatre expériences :
la magnitude exacte des écarts (E103), la demande exacte de chaque marche et la réponse collective des Tours (E137),
l'énergie quadratique (E154) et l'aveuglement de la diagonale (E155). E137 est la version linéaire du verrou : la
demande fixe la somme des contributions, pas la part de chacune. E154 et E155 en sont la version quadratique : la
diagonale ne voit pas les compensations. Le carré de la réponse se découpe exactement en diagonale et croisés, et les
croisés sont forcés par la demande (compilé). Numériquement, sur les marches jusqu'à cinq mille avec cinq mille Tours :
la diagonale d'une marche croît avec la longueur de l'écart ; la compensation est maximale là où la demande s'annule,
quand l'écart est voisin du logarithme du premier, avec une survie de un à deux dixièmes à la magnitude un ; il y a
renforcement aux petits écarts et aux grands, où la survie dépasse quatre. Sur toutes les marches réunies, la survie
de zêta vaut un, comme le hasard : la survie globale ne distingue rien. Ce qui distingue zêta du hasard est que ses
compensations sont placées là où la demande exacte les exige : avec des signes ou des phases tirés au hasard, ou avec
l'ordre des écarts permuté, la survie reste voisine de un et la réponse ne reproduit plus la demande ; la réponse
collective lit l'ordre exact. Les compensations vivent à toutes les résolutions, à l'intérieur des bandes de hauteurs
et entre bandes ; aucune bande seule ne reproduit la demande. Le monde témoin décalé reproduit sa propre demande
exacte par ses propres Tours, avec une diagonale qui croît avec l'exposant double du décalage et, classe de magnitude
par classe de magnitude, la même loi de partage que zêta (à trois pour cent près pour un décalage d'un quart, dans un
facteur un virgule quatre pour un décalage d'un dixième). La loi de partage entre diagonale et croisés, renormalisée,
ne sépare donc pas zêta du témoin ; seule la taille absolue, l'exposant de croissance, sépare. La dette d'une paire
déplacée hors de la ligne est exacte et déterministe ; une réorganisation libre des autres Tours, en amplitude et en
phase, traitée comme libre, la compense exactement sur une fenêtre finie dès qu'elle a plus de paramètres que de
marches, et échoue au-delà de la fenêtre ; cela dit que les équations de demande d'une fenêtre sont sous-déterminées,
non qu'aucune fenêtre de zêta ne décide. L'hypothèse de fermeture — aucune compensation collective ne cache durablement la dette d'une dérive
radiale tout en reproduisant exactement la même histoire première — se découpe donc en deux moitiés. La première est
un théorème : sur toute l'histoire, la dette ne se cache pas, par l'unicité de la représentation spectrale, et elle
porte l'exposant de croissance du reste au-dessus d'un demi (compilé). La seconde — l'histoire exacte de zêta ne porte
aucune dette — est l'exposant critique du reste, équivalent à la cible, non dérivé. La rigidité de compensation est
donc acquise. La taille critique de l'histoire exacte est la caractérisation globale de la cible. L'exclusion de
la cellule minimale de changement de régime par le mot premier exact lu par les Tours de la fenêtre est une formulation
locale équivalente de cette caractérisation ; elle n'est pas le verrou en vigueur (section 14).

La grammaire comme suite de sollicitations, jointe au budget global (E157, zeta23). Les deux poids sont fixés
d'avance : l'histoire première, avec ses positions, ses poids exacts et ses écarts, d'un côté ; le spectre des zéros de
l'autre ; aucun des deux ne s'ajuste à l'autre après coup. La grammaire est exacte et ses attentes se calculent : sur les
premiers jusqu'à dix millions, aucune violation de l'alternance ; les maintiens sont moins fréquents que les changements
et de magnitude plus grande, puisqu'un maintien exige un écart multiple de six ; l'avance de deux changements
consécutifs est exacte partout. Sur tout mot, la dette miroir est fixée par les extrémités, à la précision machine.
Contrôles à profondeur grammaticale croissante, à échelle de permutation fixée : garder toute la grammaire modulo six,
même suite d'états, mêmes transitions, alternance exacte, ne rend pas à l'histoire la régularité de zêta aux
résolutions des Tours ; le transfert reste celui des écarts permutés sans grammaire, jusqu'à seize fois le niveau
critique à la résolution la plus grossière. Garder en plus le voisinage immédiat des magnitudes n'y change rien. Garder
les magnitudes à leur rang en détruisant la grammaire rend zêta à toutes les résolutions. La régularité est portée par
l'ordre à longue portée des magnitudes, c'est-à-dire par la position exacte des premiers ; la classe ne déplace un
événement que de quatre unités au plus. Par canal de transition, zêta est déjà plus régulière que le hasard, les canaux
de changement le plus, parce que l'alternance verrouille leurs effectifs ; mais la somme est bien plus régulière que
chaque canal : les canaux se compensent entre eux, et seule leur somme suit le fond. Dans un monde de même grammaire à
membres hors ligne, les canaux se renforcent entre eux. Séparer par canal montre où passe la compensation ; cela ne
crée pas de contrainte nouvelle, et la grammaire, identique dans tous ces mondes, ne sépare pas. Quand la profondeur
d'une paire hors ligne tend vers zéro, le budget global ne la voit pas (elle coûte comme un zéro double en ligne), la
dette locale de la Tour et l'excès d'exposant la voient, mais en proportion de la profondeur ; aucun des trois, ni leur
réunion, n'interdit une paire isolée. Les trois niveaux restent distincts : plus des deux tiers en ligne, acquis dans
zeta23 ; une proportion un, ouverte ; aucun zéro hors ligne, la cible. Ces trois niveaux comptent des zéros et
parlent du hors-ligne : ils sont hors de la flèche, qui part de l'état engagé et parle du régime.

La fenêtre minimale de changement de régime, lue d'un seul tenant (E158). L'unité minimale d'un changement de régime
est la cellule : un membre engagé ou non, l'entrée hors de la ligne, son miroir à la même hauteur, la sortie. Avec un
passage engagé de chaque côté, la fenêtre « avant engagé, entrée, passage à une seule hauteur, sortie, après engagé » a
six membres et cinq passages ; aucune contrainte établie ne porte à six passages. Sur cette fenêtre, chaque ordre en la
profondeur a sa place. Au premier ordre, les lectures individuelles des Tours : les deux membres centraux avancent leur
phase du même angle sur chaque marche, leurs amplitudes s'écartent d'un facteur fixé par la profondeur, et la charge de
la cellule lit la structure interne du mot, puisque son logarithme est la profondeur fois la comparaison des deux pas
relatifs ; c'est la vraie jonction de la grammaire et de l'amplitude. Sur les mots premiers réels, la charge serait
amplifiante dans un peu plus de la moitié des cellules, exactement quand le second pas relatif est plus court que le
premier, et sa taille est la profondeur fois l'écart relatif, très petite. Au second ordre seulement, le côté premier :
la contribution d'une paire miroir à la formule explicite ne change pas quand la profondeur change de signe, donc le
côté premier, qui ne voit que la somme sur tous les membres, ne lit la profondeur qu'à l'ordre deux, comme l'écart à
un zéro double en ligne. Orienter par le mot avant de mettre au carré n'y change rien : la parité est dans la paire,
pas dans l'ordre des opérations. Numériquement, pour une cellule synthétique substituée à deux membres réels, le défaut
côté premier croît exactement comme le carré de la profondeur ; sur les premiers du mot il reste à un centième du reste
des autres Tours, et il ne dépasse ce reste qu'au-delà d'un horizon très au-delà du mot (pour une profondeur de quatre
dixièmes à la hauteur quatre-vingts, les premiers du mot sont entre soixante-dix et quatre-vingt-dix et l'horizon vers
trois cent soixante ; pour un dixième, au-delà de dix millions). Ce que le côté premier voit d'abord est la fusion de
deux hauteurs en une, c'est-à-dire le comptage. Conséquence : la fenêtre est locale dans les membres, pas dans les
premiers ; ses Tours lisent toute l'histoire première, et toute lecture de la profondeur se fait au second ordre
contre un zéro double en ligne, à l'échelle où l'amplitude émerge, non sur les seuls premiers partagés de la cellule.

La paire hors ligne contre le double en ligne : courbure, signe et horizon (E159). La référence d'une paire hors ligne
n'est pas l'absence de membre, mais le double membre en ligne de même hauteur : c'est la configuration que le budget
global de zeta23 ne sépare pas d'une paire serrée. Contre cette référence, la lecture de la paire en tout réel est le
terme en ligne multiplié par une courbure radiale réelle, nulle au premier ordre, minorée par le carré du produit de la
profondeur et du logarithme du réel, et croissante avec ce réel. La profondeur n'est pas perdue par la réflexion : elle
est convertie en courbure logarithmique. Le terme de la formule explicite suit cette courbure, aux corrections près
qu'apporte le dénominateur, d'autant plus petites que la hauteur est grande. Trois conséquences sont établies.
Premièrement, toute lecture linéaire des premiers jusqu'à un horizon donné sépare la paire du double au plus de cette
courbure prise à l'horizon : à horizon fixé, une paire assez proche de la ligne ne se distingue plus du double ; pour
séparer une paire de profondeur donnée, l'horizon doit croître comme l'exponentielle de l'inverse de la profondeur, et
la mesure contre le reste exact le confirme (l'horizon d'émergence suit la courbure, à un facteur deux près, et croît
avec la hauteur). Deuxièmement, le comptage ne sépare pas la paire du double : les deux ajoutent deux unités au
comptage avec multiplicité et aucun changement de signe de la fonction réelle de la ligne ; l'écart de comptage connu
sépare la paire du membre simple, pas du double, et la consommation d'un rang sans hauteur nouvelle n'est qu'une
étiquette par membre distinct. Troisièmement, le double en ligne est une configuration dégénérée de référence, un point de comparaison dans
l'espace des configurations et non un événement de l'histoire des zéros : rien n'établit que la succession réelle des
membres passe par un double avant une paire. Ses deux continuations sont portées par un seul paramètre réel, le carré
signé de l'écart : positif, la paire est séparée radialement à une seule hauteur
(régime horizontal) ; négatif, la paire est séparée en hauteur sur la ligne (deux membres en ligne serrés, régime
vertical). Contre le double, la paire hors ligne lit une courbure positive et la paire en ligne serrée une courbure
négative, de même taille, et la courbure dépend du paramètre au premier ordre : la profondeur ne s'y voit qu'au carré,
mais le signe du paramètre s'y voit à l'ordre un. Ce signe est un certificat d'une continuation donnée : il classe deux
configurations qu'on se donne, il n'est sélectionné par aucune lecture des premiers. Les plus proches membres en ligne
de zêta lisent bien une courbure négative. Extraire un premier ordre en
la profondeur n'est donc pas la voie ; que le côté premier exact de zêta n'admette que la continuation verticale lorsqu'une
fenêtre est comparée à sa configuration dégénérée de référence sur la ligne est une forme locale de la croissance
critique du reste, non dérivée et non verrou en vigueur (section 14).

Les trois étages et l'ordre des membres. Le régime engagé est massivement réalisé : hors de ce build, zeta23 en
certifie plus des deux tiers, et l'existence de membres en ligne arbitrairement hauts suffit pour ce qui suit. Un
changement de régime a la structure de la cellule. Si la fenêtre exclut cette cellule dans les deux sens de la
progression, un seul membre engagé fixe tous les autres : c'est déjà compilé sous la forme de la prémisse unique,
équivalente à la cible. Comme des membres en ligne existent au-dessus de toute hauteur, un membre hors ligne
appartiendrait, dans l'ordre des membres par hauteur, à une portion hors ligne finie, avec une entrée depuis le régime
engagé et une sortie vers lui. Ce sont des membres différents : chaque Tour est une trajectoire le long de l'axe arithmétique, mais la succession
d'un membre au suivant n'en est pas une ; aucune paire
ne quitte la ligne puis n'y revient, et la cellule de sortie n'est pas l'inverse dynamique de la cellule d'entrée ; une
exclusion de la cellule minimale devrait porter sur l'une et l'autre, chacune pour elle-même. Le budget de zeta23 sert de méthode pour la forme
quadratique côté premier, pas de source de la persistance ; découper sa forme par mots après coup peut détruire la
structure en différence de logarithmes qui la rend bornable ; il faut construire la fonction test à partir de la
fenêtre.

Les deux continuations et leur interaction avec les Tours engagées (E160). La contribution propre d'une paire perd son
premier ordre par symétrie ; on pouvait espérer que son interaction avec les Tours déjà engagées, de hauteurs
différentes, garde une orientation. Ce n'est pas le cas, et c'est établi sans aucune donnée arithmétique.
L'interaction de deux termes est leur terme croisé dans l'énergie de leur somme. Le changement d'interaction d'une
continuation avec n'importe quelle Tour, ou n'importe quelle famille finie de Tours, est la courbure de la continuation
multipliée par l'interaction du double avec ces Tours : le facteur qui dépend de la continuation est la courbure
propre, rien d'autre ; l'autre facteur ne dépend pas de la continuation. La paire, prise comme
ensemble symétrique, ne donne aucune orientation de profondeur à lire : toute lecture de la paire, propre ou croisée,
est paire en la profondeur ; une Tour seule, elle, lit le signe de sa profondeur au premier ordre, par le sens de
variation de son rayon le long de l'ordre des premiers. Les deux
continuations changent l'interaction avec une même Tour en sens opposés, mais le sens commun est fixé par la phase
relative du double et de la Tour : avec une Tour de hauteur différente, l'interaction est une amplitude fois le cosinus
de la différence des hauteurs fois le logarithme, et elle change de signe au-delà de tout horizon. Le seul terme de
signe fixe est le terme propre : la continuation radiale a plus d'énergie que le double, la continuation verticale
moins ; c'est le paquet de hauteur déjà connu. Mesures : la factorisation tient à trois millièmes près avec les vrais
dénominateurs ; la moitié des Tours engagées interagit positivement avec le double ; contre tout le côté premier, le
signe de l'interaction au premier ordre est fixe dans zêta, mais il l'est aussi, et dans le même sens, dans le monde
décalé, qui porte une paire hors ligne à chaque hauteur, et il devient libre dès qu'on retire le terme propre du membre
de référence, comme dans les mondes à écarts permutés et à signes aléatoires. Ce qui produit le signe fixe est la
présence d'un membre à la hauteur de référence, quelle que soit sa position radiale : ni l'ordre des premiers ni la
structure multiplicative. L'interaction ne sélectionne donc aucune continuation. Sous raffinement, l'asymétrie est
réelle : la courbure verticale reste bornée à tout horizon, la courbure radiale ne l'est par aucun ; mais en faire une
loi, c'est dire que rien dans le reste ne compense indéfiniment une courbure qui croît, c'est-à-dire la croissance
critique du reste, équivalente à la cible. Lu sur le pôle de rotation commun : toute Tour, en ligne ou non, tourne autour de
l'origine, et la progression en hauteur change l'enroulement sans déplacer ce pôle ; le fait d'avoir l'origine pour pôle n'est donc pas
propre au régime engagé, il vaut dans tout monde. Ce qui est propre au régime engagé est que, ramenées à l'échelle de la
racine carrée, ses Tours sont des cercles concentriques de rayon constant ; un membre hors ligne est une spirale autour
du même pôle de rotation. Les deux continuations du double déplacent son point le long de son propre rayon, sans rotation : la
radiale vers l'extérieur, la verticale vers l'intérieur ; c'est la même courbure lue depuis le pôle de rotation.

Les quatre secteurs autour du milieu de la paire et du pôle de la Tour. Deux niveaux sont à distinguer : la paire de membres et la
Tour entière. Dans le plan des zéros, le milieu de la paire est le point de l'axe critique à la hauteur considérée ; l'axe critique y
est un axe de symétrie exacte de zêta, lieu fixe de la réflexion qui conserve la hauteur ; l'horizontale à cette hauteur
ne l'est pas, la conjugaison envoyant la hauteur sur son opposée. Au niveau de la paire : toute paire invariante par la
réflexion de l'axe critique, recentrée en son milieu, a un écart porté par l'un des deux axes, l'horizontal pour une
paire miroir, le vertical pour deux membres sur l'axe critique. C'est le classement d'un seul déplacement ; il vaut pour
toute paire, en ligne ou non, et ne dit rien de la Tour. Au niveau de la Tour entière, avec tous ses contacts, ses
rayons, son ordre de lecture et son sens d'enroulement : les deux axes passent par le pôle de rotation de la Tour, l'origine, l'axe
arithmétique porte les contacts, l'axe critique lui est perpendiculaire, et les trois transformations naturelles se
calculent exactement. L'opposition centrale est l'avance d'un demi-tour : elle envoie chaque contact sur le suivant. La
réflexion par l'axe arithmétique est la lecture de la Tour à rebours : elle envoie chaque contact sur son opposé
d'indice. La réflexion par l'axe critique est aussi une lecture à rebours, décalée d'un demi-tour. Ramenée à l'échelle de
la racine carrée, la Tour est invariante par les trois, chacune exactement si le membre est en ligne : la Tour en ligne
est un cercle, et ses contacts tombent sur deux points opposés de l'axe arithmétique. Hors ligne, aucune des trois n'est
une symétrie ; la Tour est une spirale, l'opposition centrale n'est vraie qu'à une dilatation près, et la réflexion
arithmétique échange la Tour avec une Tour de profondeur opposée, lue à rebours. Dans le plan brut, sans l'échelle de
la racine carrée, aucune Tour n'a ces symétries. La symétrie est géométrique, la lecture arithmétique est orientée :
seule l'opposition centrale conserve l'ordre de lecture et le sens d'enroulement ; les deux réflexions renversent l'ordre
des premiers, et une réflexion lue dans le sens arithmétique donne la Tour du membre conjugué, de hauteur opposée.
Modulo un tour, les positions des premiers sont denses : aucune des trois images n'est retenue ni exclue par les
premiers, seul l'ordre les distingue (numérique, E161). Portée : la symétrie à quatre secteurs de la Tour entière est un
certificat de la position radiale du membre donné, du même ordre que l'amplitude plate à l'échelle de la racine carrée ;
vraie pour les membres de zêta, fausse pour ceux du monde décalé ; elle caractérise la Tour d'un membre, elle ne fixe
pas la Tour suivante.

La Tour comme trajectoire, et la boucle miroir remise dans l'ordre arithmétique (E162). Une Tour est une trajectoire : le
long de l'axe arithmétique, lu dans l'ordre croissant des premiers, son point a une phase, un rayon, une vitesse et un
sens de rotation. Sa vitesse est sa position multipliée par un facteur constant, dont une part est la vitesse angulaire,
égale à la hauteur par unité de logarithme de l'abscisse, et l'autre le taux radial, égal à la profondeur par unité de logarithme de l'abscisse. Ramené à l'échelle de la racine carrée, le rayon lu
dans l'ordre des premiers croît exactement si le membre est au-dessus de la ligne, décroît exactement s'il est en
dessous, et reste constant exactement s'il est en ligne : une Tour seule lit donc le signe de sa profondeur au premier
ordre, dans une orientation qui est celle de l'arithmétique. Ce qui est aveugle au signe de la profondeur est la somme
d'une paire miroir, pas une Tour ; ce qui n'est pas une trajectoire est la succession d'un membre au suivant, pas la
Tour. La boucle miroir est la réflexion par l'axe arithmétique suivie de la remise dans le sens de rotation d'origine,
c'est-à-dire d'une lecture à rebours. Elle se calcule exactement : elle rend la Tour du membre miroir, multipliée par un
étalon constant. En ligne, le membre miroir est le membre lui-même et l'étalon est une rotation pure : la boucle rend la
même Tour, tournée d'un angle constant, sans dilatation. Hors ligne, elle rend la Tour d'un autre membre véritable, de
profondeur opposée, et l'étalon dilate ou contracte. L'étalon conservé caractérise donc la position en ligne du membre
donné. Au niveau collectif, sur toute famille de membres stable par la réflexion, en ligne ou non, la somme après boucle
est la somme sur la même famille : les mêmes membres, permutés dans chaque paire miroir, avec des coefficients miroirs.
Côté premier, cet objet est la somme des poids divisés par l'entier, la normalisation miroir, et non la somme des poids :
ce n'est pas le même objet arithmétique, en ligne compris ; les coefficients d'un même membre y diffèrent toujours, et
n'ont le même module qu'en ligne. L'unicité de la représentation, appliquée à cet objet, redonne la stabilité de
l'ensemble des membres par la réflexion, c'est-à-dire les quatre zéros ; elle ne donne pas l'invariance de chaque
membre. Tout cela vaut mot pour mot dans le monde décalé, qui a le miroir et le produit, dont la fermeture collective
est exacte et dont tous les membres sont hors ligne (numérique, E162). Portée : l'étalon de boucle est un certificat ;
la fermeture collective est la symétrie du miroir, déjà acquise ; aucune des deux ne fixe la position radiale.

Le canal antisymétrique d'une paire miroir (E163). Une paire miroir hors ligne n'est pas une spirale : ce sont deux
trajectoires distinctes, de même hauteur, donc de même rotation, dont les dérives radiales sont exactement opposées ;
la ligne est le cas où elles se confondent en un seul cercle. Leur somme est paire en la profondeur ; leur différence,
le canal antisymétrique, est nulle en ligne, change de signe quand on échange les deux membres et n'est pas nulle hors
ligne : elle sait quel membre croît et lequel décroît. Le côté arithmétique de zêta n'a pas de tel canal. Toute
expression arithmétique est la somme, sur toute la famille des membres, d'un même poids évalué en chaque membre ; sur
une famille stable par le miroir, l'expression originale et l'expression miroir sont donc égales, pour tout poids, et
leur différence est nulle identiquement. Un poids qui changerait de signe par le miroir s'annule sur la ligne, et s'il
est régulier sur tout le plan il est nul. La différence de deux expressions arithmétiques distinctes, par exemple
l'originale et celle que rend la boucle, est un nouveau poids, qui lit aussi les membres en ligne : ce n'est pas le
canal antisymétrique. Mais l'absence d'observable n'est pas l'annulation : toute paire hors ligne forme une famille
stable dont le canal collectif est nul pour tout poids, alors que son canal de Tour ne l'est pas. Le monde décalé
ajoute un contrôle : il porte le canal antisymétrique côté premier, parce qu'il se factorise en deux produits d'Euler
dont chacun nourrit une des deux spirales, et tous ses membres sont hors ligne ; disposer du canal ne force donc pas la
fusion, et ne pas en disposer ne la force pas non plus (compilé et numérique, E163). Exiger un objet collectif que la
boucle fixe membre par membre revient à exiger la conclusion, puisque la boucle déplace tout membre hors ligne vers son
miroir. Portée : la géométrie qui sépare la ligne de la paire est entièrement connue et lue sur chaque Tour ; ce qui
reste est la raison pour laquelle l'unique histoire première exacte de zêta, qui ne voit une paire que par sa somme,
autoriserait le cercle et interdirait le couple de spirales miroir.

La variation quadratique locale (auteur, 2026-10-03). On compare, sur une même fenêtre, l'énergie d'une configuration
où une paire miroir est séparée à celle de sa référence fusionnée sur la ligne, le double en ligne de même hauteur,
tout le reste étant identique. La variation se décompose exactement en deux parts. La première est l'excès propre de la
paire sur le double : en chaque point il vaut le point multiplié par la courbure radiale et par quatre plus cette
courbure ; il est positif et nul exactement si la courbure l'est. La seconde est deux fois l'interaction de l'atome,
paire moins double, avec le complément. Ce terme croisé ne disparaît pas. Si l'on fixe le reste total, qui est donné
par le côté arithmétique, le complément s'élimine exactement : la variation devient deux fois la lecture du reste par
l'atome, moins l'énergie de l'atome. Cette lecture est, en chaque point, la courbure multipliée par l'interaction du
terme en ligne de la hauteur de la paire avec le reste : une lecture du reste arithmétique à la fréquence de la paire,
pondérée par la courbure. Elle est paire en la profondeur, donc portée par le seul canal symétrique, celui dont dispose
le côté arithmétique ; et l'algèbre ne la fixe pas : pour tout atome non nul, toute valeur est réalisée par un
complément (compilé). Le terme croisé ne s'annule donc pas et n'a pas de signe forcé par le miroir ni par la courbure ;
sa valeur dit si le reste contient la paire, ce qui est la lecture du pôle déjà compilée, et le borner sur toutes les
hauteurs et toutes les profondeurs est la croissance critique du reste. De plus, la référence fusionnée, avec le même
complément, n'est pas un monde arithmétique : par l'unicité de la représentation, aucune représentation à poids exacts
n'a d'autres membres ; une « variation à poids premiers fixés » n'existe pas, et comparer les deux énergies revient à
comparer zêta à une fonction sans produit d'Euler. L'hypothèse « les poids exacts réalisent l'énergie minimale parmi
les représentations miroir de la même histoire » est vide au niveau des poids exacts, où la représentation est unique,
et fausse au niveau diagonal : un monde de même support et de même valeur absolue des poids, donc de même énergie
diagonale terme à terme, porte des membres hors ligne (E155) ; le surplus du monde décalé vient de la taille de ses
poids, pas de la séparation. Portée : la voie locale par variation d'énergie est circulaire ; son unique terme libre
est la lecture du reste exact à la fréquence de la paire.

**Les cent trente-six rigidités qui étayent la flèche.** Chaque rigidité ci-dessous est un énoncé établi :
compilé sans hypothèse, sauf mention « numérique » ou « équivaut à la cible ». Aucune ne contredit la flèche ; chacune
en tient un maillon. Aucune ne la ferme seule, et toutes ensemble ne la ferment pas : elles tiennent toutes dans un
monde qui porterait une dette, sauf la taille critique de l'histoire, qui équivaut à la cible.

Les zéros et la ligne (maillon : état engagé, Tour suivante).
1. Les zéros non triviaux sont dans la bande ouverte ; leur existence vient de la théorie analytique.
2. Un zéro hors ligne en donne quatre, de même multiplicité.
3. Le miroir d'un zéro hors ligne est distinct de lui, à la même hauteur, de partie réelle complémentaire.
4. La ligne est le lieu fixe de la réflexion ; la fonction complétée y est réelle.
5. Un changement de signe de la fonction réelle garantit un membre en ligne (détecteur par existence).
6. Entre les deux hauteurs d'un passage, la fonction réelle ne s'annule pas et garde son signe.
7. Sur tout passage la place avance d'un, la hauteur ne recule pas, l'occurrence avance strictement.
8. Le membre suivant est unique et, depuis la ligne, fonction de la hauteur de départ seule.

La Tour (maillon : nouvelle grille exacte).
9. Une Tour par zéro, trace de son terme ; une Tour ne porte jamais deux zéros.
10. Un contact à chaque demi-tour, sans fin dans les deux sens, de côté alterné.
11. Le rapport de deux contacts consécutifs ne dépend que de la hauteur.
12. Tout nombre positif a une cellule et une seule dans la Tour de tout zéro.
13. L'origine canonique est obtenue sans premier, sans rang et sans comptage.
14. Dans une même Tour, l'écart de position entre deux nombres ne dépend que de la hauteur.
15. Toute Tour est la Tour de ligne translatée d'un bloc ; le facteur radial vaut un exactement sur la ligne.
16. Le résidu de changement tient dans une fenêtre qui se referme comme l'inverse de la hauteur ; nul exactement sur la ligne.
17. La partie réelle a deux signatures et deux seulement : translation de la grille, puissance de l'amplitude.
18. Deux contacts consécutifs redonnent le zéro ; deux zéros distincts n'en partagent jamais deux.
19. À numéro fixé, le contact descend strictement quand la hauteur monte ; les anneaux s'emboîtent.
20. Un anneau de numéro fixé est vide de tout premier au-delà d'une hauteur finie.
21. Au contact, la projection réelle du terme a exactement la taille de son rayon.
22. Une cellule est un demi-tour du terme propre ; son incrément vaut au moins deux fois le rayon au contact bas rapporté à la norme du zéro.
23. L'énergie propre par unité de largeur est la même d'une cellule à la suivante exactement sur la ligne.
24. Position dans la Tour et amplitude sont deux coordonnées séparées : la première lue par la hauteur seule, la seconde par la partie réelle seule.
25. L'amplitude ramenée à l'échelle de la racine carrée est constante exactement sur la ligne.

La grammaire première (maillon : même histoire ordonnée des premiers, écarts exacts).
26. L'occurrence est une étiquette de rang, injective.
27. Le minimum attendu est le premier qui suit l'occurrence ; deux membres distincts ont deux minimums distincts.
28. La cellule de l'état propre est unique et contient le pivot.
29. L'occurrence du membre suivant est le minimum attendu du précédent.
30. Le comptage lu à tout contact est la fonction de Tchebychev en ce contact.
31. La grammaire reconstruite depuis les zéros est la grammaire première.
32. Le premier partagé d'un passage est unique et déterminé par le rang.
33. Tout premier plus grand que trois est dans l'un de deux états modulo six.
34. L'écart entre deux tels premiers n'a que trois classes.
35. Les changements d'état effectifs alternent : deux, quatre, deux, quatre.
36. Deux transitions consécutives avancent d'au moins six.
37. L'écart s'écrit d'une seule façon comme six fois sa magnitude plus sa classe (vérifié jusqu'à deux millions, numérique ; l'écriture est compilée).
38. Magnitude et classe sont des fonctions du rang seul, aveugles à la partie réelle.
39. L'écart logarithmique entre deux premiers est la différence de leurs poids exacts.
40. Une Tour lit le même écart trois fois : en demi-tours par la hauteur, en amplitude par la partie réelle, en énergie par son double.
41. Toute lecture cumulée le long d'une chaîne d'écarts se télescope : seules les extrémités restent.

Passages, régimes et raccords (maillon : Tour d'arrivée non translatée).
42. Deux régimes de passage, vertical et horizontal, exclusifs et exhaustifs.
43. Vertical équivaut à pas contracté ; horizontal équivaut à pas conservé et à translation rigide.
44. Deux passages verticaux de suite forcent la ligne au membre commun.
45. Aucun changement de régime sur la ligne.
46. Un membre hors ligne exige une entrée en régime horizontal, précédée d'un passage diagonal.
47. Sur la ligne, la poussée horizontale est nulle et tout passage entre deux membres en ligne est vertical.
48. Un membre en ligne atteint verticalement est quitté verticalement.
49. À l'arrivée d'un passage vertical, le facteur radial vaut au moins un ; au plus un équivaut au régime gardé.
50. Le raccord existe et est unique sur tout passage, avec son transport exact.
51. Le raccord est orienté sur tout passage à hauteur croissante ; à même hauteur, le transport dépasse un.
52. La charge radiale d'une fibre est neutre exactement sur la ligne, de signe fixé par deux écarts de premiers.
53. Le registre d'un passage est raccord plus progression ; sur une chaîne, il se télescope par sommation d'Abel.
54. L'excès d'une transition vaut la part de hauteur sur la ligne, moins sur une diagonale, plus à même hauteur ; le déficit est remboursé exactement.
55. Le miroir est annulé exactement sur la ligne ; un mouvement radial existe exactement s'il y a un membre hors ligne.
56. Un changement de régime crée un mouvement radial et une jonction hors ligne.
57. Dans une cellule verticale, horizontale, verticale, les membres centraux sont miroirs, leur phase est verrouillée, la charge n'est jamais neutre.
58. Les contacts de deux membres miroirs hors ligne ne coïncident jamais ; leur translation est uniforme.
59. La seconde Tour est la première Tour du membre miroir lue à rebours ; elle existe aussi sur la ligne.
60. Depuis la ligne, la composante radiale de l'arrivée est portée par la seule position d'entrée d'un nombre dans sa cellule, la même pour tout nombre.

La formule explicite et l'unicité (maillon : réponses de toutes les Tours).
61. La Tour est le terme du zéro dans la formule explicite.
62. La somme explicite ne dépend d'aucun ordre de sommation.
63. L'organisme spectral reconstruit le reste exact et toute l'histoire première.
64. Le reste arithmétique est défini par les seuls premiers ; le poids d'un premier y est celui de son événement.
65. Le résidu arithmétique égale le résidu spectral.
66. Aucun membre n'est retirable : son terme ne s'annule en aucune abscisse.
67. Les profils d'exposants distincts sont indépendants.
68. La décomposition en profils est unique, somme infinie comprise.
69. Toute représentation contient chaque zéro avec sa multiplicité ; aucun point étranger n'y porte de poids.
70. Partie réelle, hauteur et multiplicité de chaque membre sont retrouvées dans toute représentation.
71. L'identité d'un membre hors ligne n'est effacée par aucune compensation.
72. Le canal se découpe exactement en paquet de hauteur et complément ; la compensation est fournie exactement par le complément.
73. Entre deux événements, la différence du reste se lit côté premiers et côté zéros.
74. Le reste est le tout en ligne plus un écart, qu'aucune repondération des membres en ligne n'imite.

La marche et la réponse collective (maillon : demandes exactes, renforcements et compensations).
75. La demande d'une marche pure est le poids du premier atteint moins l'avance du fond.
76. L'écart entre dans la demande par sa magnitude et sa classe.
77. La réponse collective égale la demande sur toute marche.
78. Le carré de la réponse est la diagonale plus les croisés ; les croisés sont la somme hors diagonale.
79. Les croisés sont forcés par la demande ; compensation nette exactement quand la diagonale dépasse le carré de la demande.
80. Des contributions de même signe ne se compensent pas.
81. La diagonale ne voit pas les signes des contributions.
82. Un monde de poids de même valeur absolue a la même diagonale terme à terme et la même borne critique de diagonale.
83. Une paire hors ligne multiplie la contribution de la paire en ligne par un facteur plus grand que un (numérique à la précision machine ; forme nue compilée).
84. La survie se règle sur la magnitude : compensation maximale où la demande s'annule (numérique, E137bis).
85. Signes, phases ou ordre détruits : la réponse ne reproduit plus la demande (numérique, E137bis).

La taille et l'exposant (maillon : impossibilité d'une dérive radiale).
86. Une croissance bornée du reste interdit tout exposant au-delà, par la lecture du pôle.
87. Le reste est borné par une constante fois l'abscisse, depuis les premiers seuls ; bande fermée.
88. L'exposant de croissance du reste est entre un demi et un.
89. Le plus haut exposant d'un membre et de son miroir ne dépasse pas l'exposant du reste.
90. Une dérive radiale porte l'exposant du reste strictement au-dessus d'un demi : la dette se lit dans la taille.
91. Le transport radial est borné par deux fois l'exposant moins un.
92. La somme des carrés des poids a l'exposant critique, depuis les premiers seuls.
93. Le paquet nu d'un membre et de son miroir ne descend pas sous la loi critique, avec égalité exactement sur la ligne.
94. Un membre déplacé n'émerge d'un reste de taille critique qu'au-delà d'un horizon qui croît avec sa hauteur.

La grammaire comme suite de sollicitations et le budget global (maillons : écarts exacts, demandes, réponses).
95. Deux changements d'état consécutifs avancent exactement de six fois la somme de leurs magnitudes plus un.
96. Le retour à l'état de départ équivaut à une avance multiple de six.
97. Sur toute fenêtre, passages d'un état à l'autre et passages inverses diffèrent d'au plus une unité, fixée par les extrémités.
98. Sur tout mot, la dette énergétique d'une paire miroir est fixée par les extrémités et proportionnelle à la profondeur ; non nulle exactement hors de la ligne.
99. Les maintiens d'état sont moins fréquents et de magnitude plus grande que les changements (numérique, E157).
100. La régularité de zêta aux résolutions des Tours revient avec les magnitudes à leur rang, pas avec toute la grammaire modulo six (numérique, E157).
101. Par canal de transition, zêta est plus régulière que le hasard ; sa régularité d'ensemble est faite de compensations entre canaux (numérique, E157).
102. Plus des deux tiers des zéros sont asymptotiquement simples et en ligne ; plus des cinq sixièmes sont distincts (zeta23, hors de ce build).
103. Le côté premier borne ses termes hors diagonale par la somme des carrés des poids (zeta23, hors de ce build).
104. L'inégalité rang–trace est tendue : un zéro double en ligne et une paire hors ligne proche y coûtent le même prix (zeta23, hors de ce build).

La fenêtre minimale de changement de régime (maillons : écarts exacts, réponses, organisation).
105. Un changement de régime a pour unité minimale quatre membres et trois passages ; un premier partagé par passage, trois premiers consécutifs, deux écarts entre eux ; avec un passage engagé de chaque côté, six membres et cinq passages.
106. La cellule consomme un rang sans hauteur nouvelle : quatre membres pour trois hauteurs.
107. Sur toute marche, les deux membres centraux avancent leur phase du même angle et s'écartent en amplitude d'un facteur fixé par la profondeur ; sommé sur un mot, cet écart ne voit que les extrémités.
108. La charge de la cellule lit la structure interne du mot : la profondeur fois la comparaison des deux pas relatifs, de signe opposé quand la profondeur change de signe, bornée par la profondeur fois la somme des écarts relatifs.
109. Le côté premier ne lit la profondeur d'une paire miroir qu'à l'ordre deux : la contribution de la paire est paire en la profondeur, sans terme du premier ordre.
110. Sur les mots réels la charge serait amplifiante dans un peu plus de la moitié des cellules ; le défaut côté premier d'une cellule synthétique croît comme le carré de la profondeur et n'émerge du reste qu'au-delà d'un horizon très au-delà du mot (numérique, E158).
111. Contre le double en ligne de même hauteur, la paire hors ligne lit en tout réel le terme en ligne fois une courbure radiale réelle, minorée par le carré de la profondeur fois le logarithme du réel, et croissante avec le réel.
112. Toute lecture linéaire des premiers jusqu'à un horizon sépare la paire du double au plus de cette courbure prise à l'horizon : à horizon fixé, une paire assez proche de la ligne se confond avec le double.
113. Contre le double, la paire en ligne serrée lit une courbure négative de même taille : les deux continuations de la configuration dégénérée sont les deux signes d'un seul paramètre, dont la courbure dépend au premier ordre ; ce signe classe une continuation donnée, il n'est sélectionné par rien.
114. Le comptage avec multiplicité et les changements de signe sur la ligne sont les mêmes pour la paire et pour le double ; l'horizon d'émergence suit la courbure (numérique, E159).
115. Le changement d'interaction d'une continuation avec toute famille de Tours est la courbure propre de la continuation fois l'interaction du double avec cette famille ; toute lecture de la paire est paire en la profondeur.
116. Avec une Tour de hauteur différente, l'interaction du double change de signe au-delà de tout horizon : le sens commun des deux changements est fixé par une phase relative, pas par la continuation.
117. Le seul terme de signe fixe est le terme propre : la continuation radiale a plus d'énergie que le double, la verticale moins.
118. La courbure verticale est bornée à tout horizon, la radiale ne l'est par aucun ; contre tout le côté premier, le signe de l'interaction est fixé par la seule présence d'un membre à la hauteur de référence, dans zêta comme dans le monde décalé (numérique, E160).
119. Autour de son milieu sur l'axe critique, toute paire invariante par la réflexion de cet axe a, recentrée, un écart porté par l'un des deux axes : c'est le classement d'un seul déplacement, vrai en ligne ou non ; il ne choisit pas l'axe qui porte la paire et ne dit rien de la Tour.
120. Ramenée à l'échelle de la racine carrée, la Tour entière est invariante par l'opposition centrale (contact suivant), par la réflexion arithmétique (lecture à rebours) et par la réflexion critique, chacune exactement si le membre est en ligne ; seule l'opposition centrale conserve l'ordre des premiers et le sens d'enroulement ; hors ligne, la réflexion arithmétique échange la Tour avec une Tour de profondeur opposée ; dans le plan brut, aucune Tour n'a ces symétries (compilé et numérique, E161).
121. Une Tour est une trajectoire le long de l'axe arithmétique : vitesse angulaire égale à la hauteur et taux radial égal à la profondeur, par unité de logarithme de l'abscisse ; à l'échelle de la racine carrée, son rayon croît, décroît ou reste constant dans l'ordre des premiers selon que le membre est au-dessus, en dessous ou sur la ligne. Une Tour seule lit le signe de sa profondeur ; la somme d'une paire miroir ne le lit pas ; la succession des membres n'est pas une trajectoire.
122. La boucle miroir remise dans l'ordre arithmétique rend la Tour du membre miroir multipliée par un étalon constant, de module un exactement en ligne ; sur toute famille stable par la réflexion, elle rend la même famille avec les coefficients miroirs, dans zêta comme dans le monde décalé (compilé et numérique, E162).
123. Une paire miroir hors ligne est un couple de trajectoires de même rotation et de dérives radiales opposées, dont la différence est nulle exactement en ligne ; le côté arithmétique de zêta ne la voit que par sa somme : l'expression originale et l'expression miroir sont égales pour tout poids sur toute famille stable, et aucun poids régulier n'est impair par le miroir ; le monde décalé, à deux produits d'Euler, porte cette différence côté premier et a tous ses membres hors ligne (compilé et numérique, E163).
124. Contre sa référence fusionnée sur la ligne, une paire séparée ajoute à l'énergie d'une fenêtre un excès propre strictement positif dès que la courbure est non nulle, plus deux fois une interaction avec le complément ; le reste total fixé, le complément s'élimine et cette interaction devient la lecture du reste arithmétique à la fréquence de la paire, pondérée par la courbure, paire en la profondeur, non fixée par l'algèbre (compilé).

125. Le champ du premier membre en ligne est l'amplitude de sa Tour le long de l'axe des premiers ; tout membre en ligne au moins aussi haut reste dans ce champ ; un membre et son miroir qui restent dans le champ d'un membre en ligne sont en ligne ; pour le premier membre, en ligne, « aucun membre ne dépasse son champ » équivaut à la cible (compilé). L'enroulement à indice fixé le long des premiers vaut pour toutes positions radiales dès un écart de hauteur : il ne lit pas la profondeur (compilé).
126. Chaque Tour est prisonnière de la précédente quand elle ne dépasse jamais son amplitude le long de l'axe des premiers. La position radiale d'une Tour est fixée le long de toute la Tour : le rapport de deux Tours est une seule puissance de l'axe. Une Tour de même position radiale que le premier membre en ligne, plus haute, reste dans son champ ; une Tour de position radiale fixée plus grande en sort, sans aucun changement le long de la Tour ; une fonction fixe sans paramètre, avec miroir, conjugaison et réalité sur la ligne, a un premier membre en ligne et une Tour de position radiale fixée qui sort de son champ. Une Tour prisonnière ne monte pas en position radiale, donc la hauteur avance sur son passage ; la hauteur qui avance sur tout passage donne la cible ; « chaque Tour est prisonnière de la précédente » équivaut à la cible (compilé). La grammaire du passage ne force pas l'avance de hauteur : le passage de même hauteur la satisfait (compilé).
127. L'évasion d'une Tour se paie dans le reste exact : toute borne du reste est un mur pour chaque Tour, et une Tour au-dessus de la ligne oblige le reste à dépasser toute borne plus basse que sa position radiale. Depuis les poids exacts seuls, par leur positivité et le comptage de Tchebychev, le mur démontré est à la position radiale un : le disponible démontré couvre le besoin de toute Tour, la comparaison ne ferme pas à ce niveau. Règle minimale posée pour la suite : le reste exact, somme de toutes les Tours, est captif d'une seule Tour et de son miroir, avec une seule constante. Captif d'un seul côté, cette Tour est au sommet : aucune position radiale ne dépasse la sienne. Captif des deux côtés, cette Tour est en ligne, toutes les Tours sont prisonnières et la cible suit. La règle équivaut à la cible ; dans le monde décalé, la mesure numérique la montre violée (constante croissante), et c'est le côté du miroir qui y échoue. Cette règle confronte le reste entier à une seule Tour : ce n'est pas l'objet de la captivité, qui est le couple de deux Tours successives à leur raccord (rigidité suivante).
128. Hiérarchie de Tour à Tour, lue au raccord premier qui relie deux Tours successives. Entre deux Tours en ligne, la plus haute est plus faible en tout point de l'axe des premiers, d'un rapport constant ; ses contacts sont plus serrés ; sa phase tourne plus vite, la vitesse de rotation par unité de logarithme de l'abscisse augmente avec la hauteur, elle ne diminue pas ; son décalage de phase est plus grand. Sur tout passage où la hauteur avance, quelles que soient les positions radiales, la Tour d'arrivée ne lit pas plus d'énergie au premier partagé que la Tour de départ et son pas est plus petit : la hiérarchie est un théorème à chacun de ces raccords. Le seul raccord où elle tombe est le passage de même hauteur : pas conservé, vitesse conservée, énergie renversée au premier partagé. Depuis l'état engagé, la hiérarchie au raccord suivant met l'arrivée en ligne ; tenue à tous les raccords, elle donne la cible et l'enveloppe de la première Tour, et elle équivaut à la cible. Mesure sur les trois cents premiers zéros : énergie, pas et vitesse ordonnés à chaque raccord ; le premier zéro porte environ un cinquième de la somme des amplitudes et les deux tiers de la somme des énergies ; lue depuis les premiers seuls, l'amplitude du reste à la fréquence de chaque Tour décroît de Tour en Tour. Les écarts de hauteur se resserrent en moyenne, ils n'augmentent pas. Progression obligatoire depuis l'état engagé : un membre en ligne atteint verticalement est quitté par un passage où la hauteur avance, et la hiérarchie tient à ce raccord quelle que soit la position radiale de l'arrivée (compilé) ; la hiérarchie au raccord d'après, celui qui quitte l'arrivée, n'est pas dérivée ; ce n'est pas le verrou en vigueur (section 14).
129. Ce que les seuls paramètres d'une Tour fixent. Les paramètres sont la position radiale, la hauteur et le support. Comparer deux Tours en un point de l'axe des premiers revient à comparer ces paramètres, rien d'autre (compilé). Une Tour de position radiale non supérieure et de support non inférieur reste dans le champ pour toujours ; sur la ligne, l'ordre des énergies est l'ordre des hauteurs en tout point de l'axe (compilé). Horizon garanti : en remplaçant la vraie position radiale par le pire cas possible, aucune Tour ne dépasse le champ du premier membre en ligne avant un horizon qui ne dépend que de sa hauteur et croît comme le carré de celle-ci (compilé) ; c'est une borne uniforme volontairement pessimiste, pas l'horizon de la Tour. De tout membre et de son miroir, le membre du côté bas reste dans le champ pour toujours, par la géométrie seule (compilé). Le membre du côté haut a un horizon exact, fixé par sa profondeur et son support : il sort du champ exactement quand son gain de profondeur dépasse le rapport des supports, et un membre du côté haut interdit toute borne globale du reste d'exposant plus petit que le sien (compilé ; c'est une lecture asymptotique globale, elle ne compare pas un coût de sortie à ce qui est disponible à un raccord). Numérique : sur les trois cents premiers membres le premier du raccord est encore au-delà de l'horizon garanti ; à partir du rang six cents environ il tombe en deçà, et l'écart grandit sans fin ; la première Tour porte un peu plus du cinquième de toute l'énergie des Tours en ligne, les énergies décroissent strictement de Tour en Tour. Portée : ces énoncés comparent les seules amplitudes des Tours ; ils n'utilisent ni les poids exacts, ni les phases, ni les premiers du raccord, ni le reste. Ils établissent jusqu'où la géométrie seule va : le membre bas d'un miroir est emprisonné automatiquement, et une Tour plus haute dont la position radiale dépasse la ligne sort ; la comparaison laisse non borné le gain de profondeur du membre haut ; ce n'est pas le verrou en vigueur (section 14), et elle n'établit pas que la Tour suivante ne puisse garder la hauteur de la précédente. Cette comparaison de chaque Tour à la première, poursuivie jusqu'à l'infini, n'est pas l'objet local ; l'objet local est le couple de Tours successives au premier de leur raccord (rigidité 131).
130. La double rigidité, lue sur un passage. Première rigidité, la liaison entre les premiers et chaque Tour : le premier partagé est celui que la reconstruction de la grammaire depuis les zéros impose, il est premier, il suit strictement le précédent, son poids exact est celui que la somme arithmétique lui donne, sa position dans la Tour d'arrivée est donnée par la formule tangentielle, et le registre du passage tient (compilé, sur tout passage, sans hypothèse). Seconde rigidité, la lecture des écarts : dans une Tour, la différence entre deux positions de lecture ne dépend que de la hauteur ; deux Tours la lisent de la même façon exactement quand elles ont la même hauteur ; la hauteur se retrouve depuis un seul écart ainsi lu (compilé). Cette différence efface le décalage commun sans démontrer qu'il est nul : ce n'est pas un énoncé général selon lequel les écarts de premiers seraient atteints par la hauteur seule dans toute Tour. Selon l'auteur, c'est uniquement dans le régime ON que ces écarts sont atteints par la hauteur seule, la partie réelle étant fixée et la hauteur devant progresser suffisamment (énoncé de l'auteur, non démontré). Quand la hauteur avance, tous les paramètres concourent : pas contracté, phase plus grande, support plus grand, amplitude plus faible en tout point, chaque écart lu sur plus de cellules, contacts d'indice fixé rapprochés ; sur un passage où la hauteur avance, la hiérarchie tient au raccord et la position radiale ne monte pas (compilé). Portée : sur un passage de même hauteur les deux rigidités tiennent aussi, la Tour d'arrivée lit tous les écarts exactement comme la Tour de départ, le registre est équilibré par la seule chute de phase, et pourtant l'énergie au raccord est renversée et la Tour d'arrivée n'est pas prisonnière (compilé) ; un modèle de paramètres sans aucun zéro satisfait les mêmes formules et sort. La lecture de la différence de positions par la hauteur seule est précisément ce qui la rend aveugle à la position radiale : elle ne distingue pas un jumeau de même hauteur. « Aucun passage de même hauteur » équivaut à la cible (compilé) ; la tentative « la double rigidité empêche la Tour de sortir », sans hypothèse ajoutée, laisse au compilateur un seul but ouvert, la contradiction sur le passage de même hauteur.
131. La captivité locale, calculée au raccord exact et renouvelée de raccord en raccord. L'objet est le couple de deux Tours successives, lu au seul premier qui les raccorde, et non la comparaison de chaque Tour à la première jusqu'à l'infini, ni une borne du reste entier. La captivité locale est définie par l'énergie seule : au premier de l'événement, la Tour d'arrivée ne lit pas plus d'énergie que la Tour de départ ; elle ne fait aucune référence à l'orientation du raccord, et son identité avec cette orientation est un énoncé séparé (compilé). Le rapport des énergies de deux Tours successives en un point ne dépend que de l'écart de leurs positions radiales, du point et du rapport de leurs supports (compilé). La captivité locale est un budget : le coût de sortie, écart radial multiplié par le logarithme du premier du raccord, ne doit pas dépasser le disponible, écart des logarithmes des deux supports ; la Tour d'arrivée est sous la Tour de départ exactement quand le budget tient (compilé) ; ni phase ni reste n'y figurent. Calculé au raccord exact, par les deux supports seuls : quand la position radiale ne monte pas et que la hauteur ne recule pas, le disponible peut être négatif (le support d'arrivée peut être plus petit que le support de départ quand les hauteurs sont proches), mais il reste au-dessus du coût avec un excédent proportionnel à l'écart radial ; quand la hauteur avance, la captivité tient donc par le budget lui-même ; à même hauteur, le coût dépasse le disponible d'une quantité strictement positive proportionnelle à l'écart radial, en tout premier, et la captivité locale est fausse ; la captivité locale équivaut à l'avancée de la hauteur, et les deux sens sortent du budget (compilé). La même loi répétée le long d'une chaîne borne l'énergie de la dernière Tour à son raccord par celle de la première au sien, multipliée par les pas intérieurs ; ce produit vaut au moins un : la loi répétée n'est ni une décroissance cumulée de l'énergie ni une prison globale (compilé). La transition première exacte réunit sur un même objet tout ce qui est démontré de l'événement premier du raccord : l'événement complet avec son prédécesseur, son successeur, ses écarts et ses classes, le premier partagé, son poids exact, sa reconstruction depuis les zéros, le pas de l'histoire, l'incrément exact du reste à cet événement, la position de phase du premier dans la Tour d'arrivée, le registre du passage et le rapport d'énergie ; elle existe sur tout passage, chaque composante étant un théorème (compilé). Sur le passage de même hauteur elle existe entière, les deux termes au premier partagé ne diffèrent que par le rapport d'énergie et une rotation de phase constante, et l'énergie est strictement renversée (compilé). Portée : l'inégalité locale est calculée, elle est renversée au seul raccord de même hauteur ; le poids exact du premier partagé, pris seul, ne peut pas interdire ce passage, puisqu'il y est présent ; plus généralement, une transition faite uniquement de faits déjà démontrés n'apporte rien comme hypothèse : le lemme « même hauteur et transition exacte entraînent la captivité » équivaut à « aucun passage de même hauteur » (compilé). L'information qui porterait ce lemme n'est dans aucune composante actuelle de la transition ; elle doit être un fait nouveau sur l'événement, vrai quand la hauteur avance et faux sur deux jumeaux. Tenté sans hypothèse ajoutée, ce lemme laisse au compilateur un seul but, le budget, avec sa négation et toutes les composantes de la transition dans le contexte. Ordre des flèches et réalignement de l'auteur : un membre n'a que deux coordonnées, sa position radiale et sa hauteur ; il n'y a aucune diagonale dans zêta, et aucune arrivée hors ligne depuis l'état engagé n'est établie. Sur un pas parti de l'état engagé, la hauteur avance : c'est un enroulement, le pas de la Tour d'arrivée est contracté et ses contacts se referment. Une position radiale différente n'est pas un second mouvement : c'est une translation rigide de toute la grille d'arrivée par un facteur unique, le même pour tous les contacts. Les composantes sont donc l'enroulement imposé, la captivité énergétique au raccord exact et la succession des événements premiers ; leur composition équivaut à la non-translation de la grille d'arrivée, et un plancher radial isolé n'est pas ce qu'elles donnent ; ce n'est pas le verrou en vigueur (section 14) ; et grille non translatée, facteur de translation neutre, contacts égaux à ceux de la Tour de ligne et arrivée en ligne sont la même propriété (compilé). Sur ce pas tiennent ensemble, sur les mêmes objets (compilé) : le rang avance d'un cran, le premier de référence est strictement plus grand, la hauteur avance, l'arrivée n'est pas au-dessus de la ligne, le pas est contracté, la Tour d'arrivée est captive au raccord, la translation ne peut que pousser les contacts vers l'extérieur, chaque contact est le contact de ligne translaté, et les contacts sont exactement les annulations de la partie imaginaire du terme de la Tour. L'emboîtement des Tours (chaque contact de rang au moins un de la Tour d'arrivée strictement en deçà du contact de même rang de la Tour de départ) est établi entre deux Tours en ligne dès que la hauteur avance, et pour toutes positions radiales quand l'avance de hauteur fournit la profondeur requise (compilé). Depuis un départ en ligne, l'emboîtement n'est pas indépendant de la translation : il équivaut, rang par rang, à une borne supérieure sur elle ; un emboîtement perdu certifie une grille translatée (compilé). Enroulement et ordre enferment donc la translation dans une fenêtre, entre la valeur neutre et le rapport des contacts de ligne des deux hauteurs ; ils ne l'annulent pas. La loi locale de conservation équivaut à la réunion de deux énoncés : la Tour d'arrivée est emboîtée sur tout pas parti de l'état engagé, et succession, captivité et emboîtement entraînent la non-translation (compilé). Aucun des deux n'est dérivé sans condition : la tentative de non-translation, sans hypothèse ajoutée, laisse au compilateur un seul but, la neutralité du facteur de translation, avec la fenêtre et toute la composition dans le contexte. Paramètre de l'auteur : la Tour ne s'enroule pas seulement à l'intérieur de la précédente, elle doit laisser la place à la suivante, et l'obligation vaut pour toutes les Tours jusqu'à l'infini ; l'espace réservé à une Tour est donc limité des deux côtés. Tous les contacts de rang positif de toutes les Tours restent au-delà d'un plancher commun, vers lequel les Tours suivantes s'accumulent sans l'atteindre ; l'emboîtement se transmet de Tour en Tour ; entre trois Tours successives emboîtées, chaque contact de la Tour du milieu est strictement entre celui de la suivante et celui de la précédente, et la translation de la Tour du milieu est bornée des deux côtés (compilé). Dans ces énoncés, valables à tout indice, l'enroulement de la Tour suivante figure comme hypothèse ; l'enroulement à l'infini de toutes les Tours, lui, est compilé (plus bas). Sur un pas où la hauteur avance, la contraction du pas de la Tour suivante et la non-translation de la grille d'arrivée sont équivalentes, sans qu'aucune des deux soit démontrée ; deux contractions successives, la seconde supposée, donnent une grille non translatée (compilé). Portée : une Tour de même hauteur prend sa place sans s'enrouler, par translation, tous ses contacts strictement en deçà et son pas inchangé ; l'emboîtement des contacts seul ne porte donc pas l'obligation, c'est la contraction du pas qui la porte (compilé). L'obligation d'enroulement à tous les pas équivaut à l'hypothèse de Riemann (compilé)  ; la transmission de la contraction, de la contraction acquise à un pas à la contraction au pas suivant, se ferme quand la hauteur avance au pas suivant et laisse un but ouvert quand elle n'avance pas, le pas de la Tour suivante étant alors égal à celui de la Tour d'arrivée (non dérivé) ; ce n'est pas le verrou en vigueur (section 14). La Tour bloquée par le haut et par le bas par toutes les autres, jusqu'à l'infini, est un objet : nécessaire sous l'hypothèse de Riemann ; à tout indice positif il n'est pas dérivé, mais à l'infini il l'est, sans hypothèse sur la position radiale, pour toutes les Tours et toutes positions radiales : à partir d'un indice, toute Tour qui en suit une s'enroule en elle, la Tour de même hauteur par translation vers l'intérieur (compilé) ; ce fait vaut pour toute assignation radiale, il ne fixe donc aucune position radiale ; le miroir d'un membre bas le suit à la même hauteur et prend sa place en lui, pas inchangé ; dans le monde des seuls paramètres, une paire miroir laisse à chaque Tour sa place (compilé). La capture renouvelée au raccord suivant, celui qui relie la Tour d'arrivée à la Tour d'après, équivaut à la non-translation de la grille d'arrivée (compilé) ; la capture du premier raccord ne la donne pas ; depuis l'état engagé, la capture du raccord suivant n'est pas dérivée. Revue de l'auteur : chaque zéro contribue jusqu'à l'infini, et cette persistance est une identité déjà démontrée, pas une propriété à poser : la contribution d'un zéro en un premier est son terme propre, et la même Tour lue en deux premiers se transporte par le seul facteur radial (compilé). Le rapport d'énergie de deux Tours successives se transporte donc, d'un premier à un autre, par la puissance de l'écart de leurs positions radiales (compilé). Quand la Tour suivante garde la hauteur de l'arrivée, sa position radiale est strictement plus haute : le rapport transporté croît sans borne, et comme les premiers sont non bornés, il existe un premier futur où l'énergie de la Tour suivante dépasse strictement celle de l'arrivée (compilé). L'inégalité « l'énergie de la suivante reste sous celle de l'arrivée en tout premier à partir du raccord » n'est pas la loi de persistance : c'est une conséquence de type hypothèse de Riemann (nécessaire sous elle, et sur tous les passages elle l'entraîne, compilé) ; elle n'est pas à démontrer comme telle. L'évasion individuelle en un premier ne contredit pas, à elle seule, la reconstruction collective de l'histoire première, qui porte sur la somme de tous les zéros. Un membre en ligne atteint verticalement est quitté verticalement (compilé) ; ce fait porte sur un membre en ligne, et il n'établit pas pour tout membre que le pas qui le suit n'est pas de même hauteur ; la différence de positions lue sur un écart de premiers fixe la hauteur de la Tour qui la lit, et la hauteur qui avance fait concourir pas, phase, support et lecture des écarts (compilé, hors verrou), mais la Tour de même hauteur satisfait aussi ces lectures (compilé). La tentative selon laquelle le pas qui suit le pas engagé ne peut pas garder la hauteur laisse au compilateur un seul but, la contradiction, avec en contexte le pas engagé entier, l'évasion individuelle en un premier et la reconstruction collective en ce premier (non contredite). La place de toute Tour parmi toutes les autres ne porte aucune position radiale et n'entre pas dans la fermeture : à l'infini elle est un théorème vrai pour toute assignation radiale, et à tout indice positif elle n'est pas dérivée et n'est pas utilisée. Lecture antérieure, conservée comme équivalence : sur ce pas, arrivée en ligne et plancher radial de l'arrivée sont la même propriété ; le seul plancher compilé sur une arrivée lit le passage suivant ; une arrivée translatée porterait la transition première exacte entière, un coût de sortie strictement négatif et la captivité locale, l'énergie au premier partagé ne donne donc aucun plancher ; sous le plancher le régime engagé perdure (compilé).
Les mondes témoins et les caractérisations (garde-fous de la flèche).
132. Le monde décalé a le même support premier, la même grammaire, des poids positifs plus grands, tous ses zéros hors ligne.
133. Son poids vaut au moins le double du poids exact et son carré au moins quatre fois le carré du poids exact, avec égalité exactement au décalage nul.
134. Le monde de rupture engagée porte un membre en ligne puis deux jumeaux ; la fonction fixe sans premiers change de régime.
135. La prémisse unique, la conservation avec l'amorce, la représentation en ligne, la borne en racine carrée et l'exposant un demi équivalent chacune à la cible.
136. La cible équivaut à l'absence de toute dette dans l'histoire exacte : caractérisée, non dérivée.

Généralisation (auteur, 2026-10-15, §102) : le besoin de synchronisation d'un signal est son amplitude, à l'échelle de la ligne,
lue aux points de rencontre ; la contrainte généralisée dit que ce besoin est le même à toutes les rencontres, sans dire sa valeur.
Démontré : un besoin constant caractérise un signal de la ligne ; à deux rencontres consécutives, de même ; entre deux signaux à
besoin constant seule la fréquence change, le pas se raccourcit, l'amplitude attendue baisse d'un rapport fixé par les deux hauteurs ;
un signal d'amplitude décroissante n'a pas un besoin constant, et deux rencontres où le besoin n'a pas diminué l'excluent ; la
contrainte quantifiée sur tous les signaux a la force de l'hypothèse. Le but est réduit, sans perte et dans les mots de l'auteur, à
deux rencontres de la courbe des premiers, à la hauteur du zéro suivant, où le besoin n'a pas diminué ; il reste ouvert.

Verrou du couple (auteur, 2026-10-16, §103) : le signal d'un zéro, ramené à l'échelle de la ligne et projeté sur l'axe algébrique,
porte trois lectures sur le même objet : l'espacement de ses rencontres avec l'axe, qui dit sa fréquence et ne voit pas sa position
radiale ; la position d'une seule rencontre, qui dit sa position radiale à fréquence donnée ; le besoin de synchronisation à deux
rencontres consécutives, qui dit la même position radiale. Démontré : on ne peut pas changer l'amplitude sans déplacer les points de
passage obligés (un besoin constant équivaut à des rencontres non translatées ; une dérive du besoin déplace toutes les rencontres
hors des positions de la ligne) ; on ne peut pas réaligner les rencontres en changeant la fréquence (l'espacement se contracte, aucune
translation rigide) ; changer la position radiale à fréquence fixe translate rigidement toutes les rencontres et fait dériver le
besoin ; le couple fréquence–position radiale est verrouillé, aucune solution diagonale ne satisfait l'espacement et une rencontre,
ou l'espacement et le besoin, d'un autre signal. Le but est réduit, sans perte, à la demande de la courbe des premiers au signal placé
à la hauteur du zéro suivant, en forme de couple : deux rencontres consécutives où le besoin est le même ; il reste ouvert. Les
conclusions des expériences historiques à OFF fabriqués ne sont pas réutilisées ; seule la géométrie démontrée de la Tour l'est.

La fréquence est déjà occupée (auteur, 2026-10-16, §104) : les premiers et leurs signaux sont déjà définis, immuables ; à chaque
hauteur attendue d'un zéro, le signal des écarts a sa fréquence et son point de rencontre à une demi : cette fréquence est occupée
par un zéro sur la ligne. Il est impossible de définir un zéro hors de la ligne avec exactement cette fréquence, puisque lorsque
cette hauteur est rencontrée par les signaux des écarts des premiers, ils sont sur l'axe critique. Le côté au-dessus d'une demi est
exclu par son miroir ; le seul candidat hors de la ligne est en dessous d'une demi, à une fréquence que les signaux des écarts
n'atteignent pas sur l'axe critique. Écrit : une fréquence occupée est une hauteur où un signal sur la ligne existe, et ses
rencontres sont exactement les positions de la ligne ; un seul signal par fréquence signifie que deux signaux de même fréquence
partagent leur point de rencontre ; avec le verrou du couple, tout zéro d'une fréquence occupée est alors sur la ligne et la
fréquence d'un zéro hors de la ligne n'est pas occupée ; une fréquence prise est une fréquence occupée par un signal sur la ligne dont
le zéro partage le point de rencontre, ce qui équivaut à être sur la ligne. Le but est réduit, sans perte, à : la fréquence du zéro
suivant est prise par le signal sur la ligne que la courbe des premiers engendre à cette fréquence ; il reste ouvert. Les lois
quantifiées (un seul signal par fréquence ; toute fréquence prise) ont la force de l'hypothèse ; le module écrit le point de
l'auteur, il ne le dérive pas des écarts. Direction d'écriture de ce qui reste : écarts exacts ⟶ fréquences engendrées ⟶ point de
rencontre de chacune ⟶ aucune en dessous d'une demi.

Des écarts exacts vers les fréquences engendrées et leurs points de rencontre (auteur, 2026-10-16, §105, E321) : les rigidités connues sont écrites du zéro vers ses effets ; elles sont renversées, dans le sens premiers vers zéro, partout où l'effet est une fonction strictement monotone du paramètre. Une fréquence engendrée est une hauteur portée par un signal de la courbe des écarts exacts ; son point de rencontre est l'abscisse où sa Tour normalisée coupe l'axe algébrique. La position de la rencontre impose la position radiale, le rapport des besoins à deux rencontres consécutives aussi, et les deux lectures concordent. Rencontre à la position de la ligne : signal sur la ligne ; rencontre au-delà de cette position : signal en dessous d'une demi, c'est la forme, côté premiers, d'une fréquence à rencontre sous une demi. À une fréquence engendrée, un seul signal équivaut à la rencontre sur la ligne et à toute la fibre sur la ligne : le miroir d'un signal engendré est engendré à la même fréquence, une rencontre commune le confond avec le signal. Une mesure finie de la translation de la rencontre, à une précision donnée, détecte tout signal assez bas et ne voit aucun signal assez proche d'une demi : c'est la résolution de l'expérience, pas une démonstration. Mesuré sur les seuls premiers, à vingt fréquences : chaque fréquence engendrée est une hauteur de zêta, sa rencontre est à la position de la ligne, son besoin est constant, elle ne porte qu'un signal ; le monde témoin en porte deux ; le porteur dans les écarts est la suite des tailles exactes dans leur ordre, la suite des rangs seule n'engendre rien. La loi « aucune fréquence engendrée n'a de rencontre en dessous d'une demi » a la force de l'hypothèse. Le but de la chaîne est ramené sans perte à : le point de rencontre du signal engendré à la fréquence du zéro suivant est à la position de la ligne.

Réimplémentation après audit (texte collé par l'auteur, 2026-10-16, §109) : la première écriture désignait la fréquence engendrée et sa rencontre par un zéro déjà donné ; la propriété « rencontre sur la ligne » y était la propriété cherchée et non une conséquence, et le dernier pas de la chaîne demandait la position radiale du zéro lui-même. Les objets sont réécrits depuis le reste des premiers et rien d'autre : une représentation du reste des premiers est une famille de signaux dont la somme reproduit ce reste sur tout l'horizon ; une fréquence est engendrée par les premiers quand toute représentation porte un signal de poids non nul à cette fréquence ; le point de rencontre d'un signal est l'abscisse où il coupe l'axe algébrique, fonction du seul signal, la même pour un signal et son conjugué ; la rencontre arithmétique à une fréquence est la rencontre commune de tous les signaux de cette fréquence dans toute représentation. Un signal n'y est désigné que par sa fréquence, jamais par sa position radiale, qui est ce que l'on cherche. Démontré, par l'unicité de la décomposition du reste et sans fixer aucun exposant : une fréquence engendrée par les premiers est une hauteur de zéro et réciproquement ; la rencontre d'un zéro est la rencontre de son signal ; la position de la ligne est la rencontre du signal de la ligne à cette fréquence ; la rencontre arithmétique à la position de la ligne équivaut à la rencontre sur la ligne de tous les zéros de cette hauteur ; une rencontre arithmétique au-delà de la position de la ligne équivaut à un signal en dessous d'une demi ; la loi côté premiers, sur toutes les fréquences, a la force de l'hypothèse. Le but de la chaîne est maintenant : dans toute représentation du reste des premiers, tout signal de poids non nul à la fréquence du zéro suivant rencontre l'axe à la position de la ligne ; il porte sur tous les signaux de cette fréquence et non sur le seul zéro considéré, les deux formes étant réfutées par la zone sous un demi dans le contexte. Ce que la correction ne fait pas : fixer une position radiale ; l'unicité retrouve chaque signal tel qu'il est. La lecture de la rencontre dans l'expérience est calibrée sur un contrôle de ligne.
Trois objets distincts (texte de support collé par l'auteur, 2026-10-16, §110) : la rencontre propre d'un signal est l'abscisse où ce signal seul coupe l'axe ; la rencontre collective est l'abscisse où la somme de tous les signaux, c'est-à-dire la courbe des premiers débarrassée de son fond, s'annule ; l'événement premier est le point où la courbe des premiers change de pente, d'une quantité égale au poids du premier. Démontré : le but de la chaîne porte sur la rencontre propre de chaque signal de la fréquence considérée, par définition ; la rencontre collective est une relation sur tous les signaux à la fois, la même dans toute représentation, et à une telle rencontre chaque signal vaut l'opposé de la somme des autres, de sorte qu'elle ne fixe la rencontre propre d'aucun signal ; la courbe des premiers est affine par morceaux entre deux entiers consécutifs, de pente égale au poids cumulé, et son changement de pente en un entier est le poids de cet entier, non nul exactement aux puissances de premiers ; toute somme finie de signaux est dérivable, donc l'événement premier n'appartient à aucune sous-somme finie, il est porté par la somme infinie seule. Corrigé : les expériences qui lisaient « la rencontre à la position de la ligne » lisaient les zéros d'une contribution filtrée du signal collectif, calibrés sur un contrôle de ligne, c'est-à-dire une rencontre de la seconde espèce ; elles ne portent pas le but ; des amplitudes propres constantes ne donnent pas une amplitude collective constante, les signaux se renforcent ou s'annulent par leurs phases. Ce qui n'est pas écrit : la contrainte que les événements premiers imposent simultanément à toutes les rencontres propres et à leur résultante ; c'est la flèche manquante. Les trois ingrédients de la loi de mouvement cherchée (second texte de l'auteur, même jour) : un passage qui monte depuis un zéro sur la ligne, la fréquence authentique du zéro suivant, et la liaison du premier partagé sont tous trois acquis sur un tel passage, et aucun ne dit où se trouve radialement l'arrivée ; la liaison vaut sur tout passage, même entre deux zéros de même hauteur, et toute position radiale sous la ligne satisfait les obligations de contact. Recherche faite dans tous les théorèmes de mouvement : aucun ne conclut l'impossibilité d'une arrivée sous la ligne depuis ces trois ingrédients seuls ; chacun suppose l'arrivée, ou l'hypothèse elle-même, ou ne fait que caractériser. L'exclusion n'est donc pas compilée indépendamment, et la loi de mouvement à extraire doit lire autre chose que la succession, la fréquence et la liaison. Loi de compensation entre déplacement vertical et déplacement radial (texte de l'auteur, même jour, §111 ; sans aucune normalisation, les rencontres sont des abscisses brutes) : sur un passage parti d'un zéro de la ligne, le déplacement du point de rencontre se décompose exactement en une part verticale, qui ne dépend que des deux fréquences, et une part radiale, qui est le logarithme du facteur radial de l'arrivée. Démontré : quand la hauteur monte, la rencontre attendue se rapproche de un ; quand la position radiale descend sous la ligne, la rencontre est translatée vers l'extérieur ; conserver la rencontre du départ revient à compenser exactement la part verticale par la part radiale, ce qui exige une arrivée sous la ligne, et cela est réalisable pour la fonction de rencontre : pour toute fréquence de départ il existe une fréquence plus haute et une position sous la ligne qui donnent le même point de rencontre. L'impossibilité cherchée est donc fausse sous la forme « conserver la rencontre du départ ». Sous la forme « conserver la rencontre attendue à la nouvelle fréquence », elle équivaut à l'absence de déplacement radial, c'est-à-dire au but, et quantifiée sur tous les signaux à l'hypothèse elle-même. Aucune impossibilité indépendante n'est compilée dans les travaux sur les mouvements. Ce que le compilateur attend, dit dans ce vocabulaire : le déplacement radial de rencontre du signal des premiers à la fréquence du zéro suivant est nul ; il manque la raison, lue sur les écarts exacts, qui l'impose. Non-compensation (§112) : la contribution d'un vrai zéro est imposée par la courbe des premiers moins la part fixe de tous les autres ; aucun autre vrai zéro ne la compense et aucun remplacement ne reconstruit ; démontré : présence et unicité ; non démontré : la valeur de l'amplitude imposée.

Vérification de E321 et reprise sur le comptage autour de li (auteur, 2026-10-16, §106, E322) : les composantes d'un signal ne sont pas lues comme des courbes isolées autour de zéro ; elles modifient collectivement la reconstruction du comptage des premiers autour du fond li. On part du fond, on y ajoute successivement les fréquences que la courbe de comptage engendre, et l'on mesure à chaque fréquence la rencontre de sa contribution avec le fond, son déplacement par rapport à la position de la ligne, son besoin, et le résidu de reconstruction. Mesuré sur les seuls premiers, à vingt fréquences : rencontres à la position de la ligne, besoin constant, un seul signal, résidu de reconstruction égal à celui des signaux de ligne des hauteurs publiées à la queue près, une seule position radiale minimisant le résidu quand une fréquence seule la change ; le monde témoin en porte deux. La limite de la reconstruction collective est la fonction de comptage elle-même moins le fond : dérivable partout sauf aux puissances de premiers, où elle saute ; les sommes partielles sont lisses, leur série dérivée ne converge pas, leur pente aux premiers croît avec la hauteur de troncature. « Nulle part dérivable » est réfuté sur la limite. C'est la forme mesurée de la loi de synchronisation demandée ; sa forme quantifiée a la force de l'hypothèse ; rien n'est dérivé, le canal de comptage n'est pas formalisé, le but est inchangé.

La matrice de synchronisation (auteur, 2026-10-16, §107, E323) : les lignes sont les intervalles entre deux puissances de premiers consécutives, les colonnes les fréquences que la courbe des premiers engendre ; une cellule est la variation du signal d'une colonne sur une ligne, avec sa phase, ses rencontres et la variation de son enveloppe ; la somme de chaque ligne est la variation du fond sur l'intervalle, puisque le comptage y est constant. Mesuré : aucune ligne n'est fermée par les colonnes que l'on sait lire, ni même par les cinq mille premiers zéros publiés ; chaque ligne est portée par la queue infinie ; chaque colonne rencontre le fond une fois par demi-tour, indépendamment des événements premiers ; à la rencontre sa valeur s'annule et son incrément est maximal ; aucune colonne ni aucune somme finie de colonnes ne saute à un événement, le saut du comptage est porté par la limite seule. La compatibilité globale demandée, une seule amplitude et une seule phase par colonne sur tous les blocs sans réajustement, est satisfaite au bruit près sur vingt colonnes jusqu'à cent millions, identique au contrôle de ligne ; le monde témoin exige un réajustement d'un bloc au suivant et est refusé. Ce que la matrice établit : le réajustement exigé d'une colonne entre deux blocs est l'écart radial multiplié par la distance logarithmique des blocs ; aucun réajustement, c'est le besoin constant, c'est la ligne ; la compatibilité globale sur toutes les colonnes a la force de l'hypothèse. La rigidité suffisante que le texte cherche est donc la loi à démontrer ; la matrice la formule et la mesure, elle ne la fournit pas.

Le zéro suivant sous un demi, après les zéros sur la ligne certifiés par comptage (auteur, 2026-10-16, §108) : un tel zéro partage sa hauteur avec son miroir ; sa fréquence porte donc deux signaux, et le comptage y gagne deux unités d'un coup, sans zéro sur la ligne pour les porter. Après les trois premiers zéros certifiés, un zéro sous un demi serait au-dessus de vingt-huit et le comptage vaudrait au moins cinq à sa hauteur. Cette signature est discrète : deux unités, quelle que soit la profondeur. La signature d'amplitude le long des premiers est au contraire continue : la dérive de l'amplitude du zéro lui-même s'efface sur toute fenêtre finie de premiers quand la profondeur diminue, sans aucune comparaison avec un zéro sur la ligne de même fréquence, et l'horizon à partir duquel le miroir dépasse une Tour plus basse croît sans borne. Une exclusion valable pour toute profondeur ne peut donc pas venir d'une comparaison d'amplitudes sur une fenêtre finie de premiers ; l'endroit où un zéro sous un demi se signale à distance finie est le comptage à sa hauteur. Ce que demande cet endroit, l'égalité du comptage total et du comptage sur la ligne à chaque hauteur, caractérise le zéro suivant sur la ligne et, à toute hauteur, a la force de l'hypothèse.

Sens imposé (auteur, 2026-10-15, alignement §101) : la relation entre les écarts des nombres premiers et les zéros n'est pas une
lecture ; c'est une réalité imposée aux zéros, immuable, qui vient des écarts ; les zéros sont les signaux qui composent ces écarts ;
leur fréquence et leur amplitude leur sont dictées. Les cent trente-six rigidités ci-dessus sont toutes écrites du zéro vers ses
effets : identités vraies pour toute position, identifications qui retrouvent la position sans la fixer, caractérisations de la
ligne qui redisent le but, équivalences avec la cible. Aucune n'est écrite des écarts vers l'amplitude forcée de chaque signal.
Ce que les premiers donnent : la décomposition exacte de leur courbe en signaux, un par zéro ; l'unicité de ces signaux ;
l'amplitude de la courbe à l'échelle entière (démontré) ; à chacune des douze premières fréquences, une seule amplitude compatible
avec la courbe, celle de la ligne (mesuré). Ce qui reste : la rigidité écrite dans ce seul sens. Le but du compilateur, en mots :
les écarts immuables imposent au signal placé à la hauteur du zéro suivant l'amplitude de la ligne ; une amplitude décroissante
leur est incompatible et ne peut pas être synchronisée.

## 13. Pistes closes

Chaque piste ci-dessous a été écrite, compilée ou testée ; elle est close avec sa raison. Elle n'est pas
reproposée sous une autre forme.

- La collision lecture et vérification de la seconde Tour, sa clôture par l'inversion, la collision à
  l'entrée, la comparaison des deux Tours : retirées ; la quantité comparée appartenait à un autre zéro ; à
  l'entrée, la vérification est réfutée ; au dernier rayon, les deux constats s'excluaient hors ligne et chacun était une position d'anneau (théorèmes
retirés avec l'appareil ; l'équivalence de la lecture avec une position d'anneau reste compilée) ; la contradiction de la progression des premiers atteints est de la forme « A et non A »
  sur une même grille.
- Le pivot commun de la seconde Tour : retiré ; la seconde Tour est celle d'un autre zéro et son événement
  avance de un. La vérification obtenue par construction (croisement du bas sous un pivot posé égal au
  minimum attendu d'origine) ne testait rien.
- Les deux lois de l'inversion et l'accord des deux grammaires comme caractéristique de la criticité :
  équivalents à la cible, retirés.
- La commutation d'un transport de fibre avec la réflexion : équivaut à l'annulation du défaut radial.
- Les prémisses secondaires : absence de passage nul, poussée verticale d'énergie, équilibre d'énergie aux
  raccords, grammaire par hauteurs, superposition des rayons, absence d'entrelacement strict, profondeur
  d'insertion nulle, identité et transport du miroir, domination verticale au raccord, lecture locale
  orientée, orientation du raccord et fait annexe de hauteur minimale : chacune équivalente à la cible ou
  fausse hors ligne ; retirées.
- « Un événement grammatical franchit au moins une cellule » : faux sur la ligne (même cellule dans près
  d'un tiers des cas) ; l'excès de phase inter-Tours positif est la progression de hauteur renommée ; la
  progression continue d'un événement est strictement positive mais sans quantum.
- L'énergie totale du quartet : elle télescope, sa circulation résiduelle est nulle en ligne comme hors
  ligne.
- « Système global plus hors-ligne donne une contradiction » : les trois égalités tiennent hors ligne ;
  « le complément ne peut pas fournir la compensation » : il la fournit exactement.
- « Une quantité déterminée par la hauteur seule et sensible au déplacement radial » : tautologie
  fonctionnelle ; elle n'écarte que la tentative où le facteur radial serait fonction de la hauteur, et ne
  réfute pas la recherche d'une loi de transition couplée.
- La réponse radiale au premier ordre comme mécanisme : vraie aussi pour la fonction fixe sans premiers.
- La course entre fonction réelle et membres hors ligne, le comptage de fenêtre : non poursuivis (verdict de
  l'auteur).
- Le numéro de cellule, la place dans la cellule, la grammaire, la classe modulo six, l'occupation des
  cellules, le produit d'Euler tronqué, le premier partagé comme porteur propre : aveugles au régime ou
  lectures de hauteur ; ils ne portent pas la flèche.
- Désigner un premier par un numéro de cellule fixé, ou égal au rang du zéro : à numéro fixé, anneau vide au-delà
  d'une hauteur finie (compilé, tous les zéros) ; au rang, jamais le premier du rang ; contenu et enroulement
  indépendants de la partie réelle (E151).
- Chercher la flèche dans l'enroulement, la fréquence ou la résolution d'un membre : ces coordonnées ne lisent que la
  hauteur, et la pente est une coordonnée séparée (compilé) ; lire la pente sur une plage finie de premiers et la
  présenter comme loi : c'est une lecture bornée par un horizon qui croît avec la hauteur (compilé, E150).
- Prendre la platitude du transport entre hauteurs distinctes comme ancre de la ligne : le monde témoin l'a aussi
  (E152) ; l'ancre est le transport vers le miroir ou l'exposant critique du reste (compilé).
- Tirer l'exposant critique de la positivité des poids, par le théorème de Landau ou autrement : la positivité ne donne
  que l'exposant un (compilé) ; elle est vraie dans tous les mondes témoins, dont les exposants couvrent l'intervalle
  de un demi à un (compilé, E153). Appeler la route compilée « logarithme intégral et reste exact » : elle passe par le
  reste lissé de la somme pondérée des premiers.
- Dire que le carré élimine les compensations : elles deviennent des termes croisés, et celui du paquet miroir ne
  s'éteint pas (E154). Présenter une identité de cellule insensible à l'échelle du poids comme loi séparant zêta du
  témoin : elle est satisfaite par construction dans le témoin (E154).
- Définir le contenu d'une cellule par le logarithme intégral : c'est une moyenne de comptage ; une cellule est un
  intervalle exact entre deux contacts, son contenu est celui des premiers et de leurs poids exacts (E155).
- Présenter l'accumulation radiale sur les écarts premiers exacts comme une contrainte nouvelle : elle se télescope en
  facteur d'amplitude des extrémités, sans trace des écarts intermédiaires ni de leur ordre (compilé, E155).
- Attendre de la diagonale (valeur absolue des poids, somme de leurs carrés) le contrôle du transfert : un monde de
  même support premier et de même diagonale terme à terme porte des membres hors ligne et un transfert non borné
  (compilé et mesuré, E155). Construire un « monde à poids exacts et membres hors ligne » au niveau de la valeur signée :
  c'est zêta elle-même, ce serait un contre-exemple, pas un contrôle.
- Chercher dans l'orientation du demi-tour (entrée et sortie échangées) la marque d'un membre hors ligne, ou dans le
  poids d'un premier un sens local lié à l'ordre des contacts qui l'encadrent. La seconde Tour est, par définition, la
  première Tour du membre miroir lue à rebours (compilé) ; elle existe aussi pour un membre en ligne, qui est son propre
  miroir. Les contacts de deux membres miroirs hors ligne ne coïncident jamais (compilé) : les deux contacts partagés du
  schéma sont ceux d'un seul membre, lus dans deux sens. Le poids d'un premier est un saut positif de la somme entière,
  le même quel que soit le sens de lecture, et le terme d'un membre est continu en ce premier. Le flux signé des poids
  d'une cellule suit l'orientation alternée du membre dans zêta comme dans le témoin, et même dans une grille translatée
  (E156). C'est une lecture de la hauteur par la somme entière, pas une propriété du poids.
- Confondre l'origine des Tours et le milieu de la paire miroir sous le seul mot « centre », ou parler du centre du zéro
  précédent comme d'un objet commun à deux Tours : l'origine est le pôle de rotation de toutes les Tours (plan des Tours),
  le milieu d'une paire est un point de la ligne critique à la hauteur commune (plan des zéros), et deux hauteurs
  différentes donnent deux milieux. L'équivalence entre symétrie centrale de la Tour normalisée, miroir annulé et zéro au
  milieu de sa paire relie des propriétés sans identifier ces deux objets. Dire qu'une Tour part de son zéro ou est
  centrée sur lui : faux, le zéro détermine la trace sans en être ni le centre ni le point de départ.
- Chercher dans la loi de partage entre diagonale et croisés, classée par la magnitude de l'écart, ce qui sépare zêta du
  témoin : le témoin décalé reproduit sa propre demande exacte avec le même partage, une fois renormalisé (E137bis).
  Prendre la survie globale comme mesure d'organisation : elle vaut un dans zêta comme dans le hasard (E137bis).
- Traiter les contributions des Tours d'une fenêtre comme des paramètres libres : une réorganisation libre y compense
  toujours la dette dès qu'elle a assez de paramètres (E137bis) ; cela ne dit rien d'une fenêtre de zêta, dont les
  Tours sont contraintes. Chercher la loi de fenêtre sur les seuls premiers partagés de la cellule, ou dans un terme du
  premier ordre en la profondeur côté premier : la contribution d'une paire miroir est paire en la profondeur, et le
  défaut n'émerge du reste qu'au-delà d'un horizon très au-delà du mot (compilé, E158). Chercher une loi de fenêtre à horizon premier
  fixé : elle sépare la paire du double au plus d'une courbure qui s'annule avec la profondeur (compilé, E159).
  Séparer la paire du double par le comptage, les changements de signe ou le rang : ils sont identiques, le rang par
  membre distinct est une étiquette (E159). Dire que les premiers lisent ou choisissent le signe du paramètre : il
  classe une continuation donnée (E159). Chercher la sélection dans l'interaction de la continuation avec les Tours
  engagées : elle se factorise par la courbure propre, son signe est fixé par une phase relative ou, contre tout le côté
  premier, par la seule présence d'un membre à la hauteur de référence, dans le monde décalé comme dans zêta (compilé et
  numérique, E160). Présenter la stabilité sous raffinement comme une loi nouvelle : c'est la croissance critique du
  reste (E160). Traiter le double comme un événement de l'histoire, ou une portion hors ligne comme une paire qui sort
  puis revient : chaque Tour est une trajectoire, la succession des membres n'en est pas une. Chercher la sélection dans la symétrie d'une paire
  recentrée autour de son milieu sur l'axe critique : elle est automatique pour toute paire invariante par la réflexion, en
  ligne ou non (compilé). Prendre la symétrie à quatre secteurs de la Tour entière pour une loi : elle caractérise la
  position radiale du membre donné, comme l'amplitude plate, et ne fixe pas la Tour suivante (compilé, E161). Fermer par une « jauge arithmétique » : attendre de la boucle miroir remise dans l'ordre des premiers, jointe à l'unicité de la représentation, l'invariance de chaque Tour ; la boucle permute les membres d'une paire miroir, l'objet collectif après boucle a les mêmes membres et une autre normalisation, l'unicité n'y lit que la stabilité de l'ensemble, et la fermeture collective est exacte dans le monde décalé (compilé et numérique, E162). Dire qu'il n'y a ni orientation ni trajectoire : chaque Tour est une trajectoire orientée par l'ordre des premiers et lit le signe de sa profondeur. Fermer par le canal antisymétrique : chercher dans la différence de deux expressions arithmétiques du même objet, l'originale et la miroir, la différence des deux spirales d'une paire ; sur toute famille stable les deux expressions sont égales pour tout poids, aucun poids régulier n'est impair par le miroir, la différence de deux expressions distinctes lit les membres en ligne, et l'absence du canal ne force pas la fusion, pas plus que sa présence dans le monde décalé (compilé et numérique, E163). Exiger un objet collectif que la boucle fixe membre par membre : c'est exiger la conclusion. Fermer par une variation quadratique locale, paire séparée contre référence fusionnée : l'excès propre est positif, mais le terme croisé avec le complément devient, le reste fixé, la lecture du reste exact à la fréquence de la paire ; il n'est ni nul ni signé par l'algèbre, le déterminer est la lecture du pôle, le borner uniformément est la croissance critique du reste ; la référence fusionnée n'est pas un monde arithmétique (compilé). Poser que les poids exacts réalisent l'énergie minimale des représentations miroir de la même histoire : vide aux poids exacts, où la représentation est unique, faux au niveau diagonal, où un monde de même valeur absolue des poids porte des membres hors ligne (E155). Présenter la rigidité de compensation sur toute
  l'histoire comme la pièce manquante : c'est l'unicité de la représentation spectrale, compilée ; elle dit que la dette
  se lirait dans l'exposant du reste, pas que l'histoire exacte de zêta est sans dette.
- Chercher dans la grammaire modulo six (états, transitions, mots, alternance) ce qui porte la régularité de zêta aux
  résolutions des Tours : une histoire qui garde exactement toute cette grammaire mais déplace les magnitudes a le
  transfert des écarts permutés ; les magnitudes à leur rang suffisent (E157). Présenter la séparation par canal de
  transition comme une contrainte nouvelle sur la compensation : la compensation passe entre les canaux, et la
  grammaire est la même dans le monde décalé et dans le monde de signes cohérents (E157). Présenter la dette miroir
  attachée à une progression grammaticale comme une contrainte nouvelle : elle se télescope en extrémités du mot
  (compilé).
- Attendre du budget global de zeta23, même porté à une proportion un, l'absence de toute paire hors ligne : une
  densité ne voit aucune paire isolée, et l'inégalité rang–trace ne distingue pas une paire proche d'un zéro double en
  ligne. Le socle des deux tiers ne réduit pas la « réserve de compensation » : la dette d'une paire n'est déjà cachée
  par aucune réorganisation de tout le reste du spectre (compilé) ; ce qui manque n'est pas l'impossibilité de cacher
  la dette, c'est l'absence de dette.
- « Exactement deux contacts », « la Tour sélectionne un premier », « isoler un terme est impossible » :
  faux ; la Tour a une infinité de contacts, le premier est une étiquette, l'identité de chaque membre est
  retrouvée.
- « La borne minimale de l'avancée de hauteur » : c'est une équation, satisfaite par le passage de même
  hauteur.
- La croissance des écarts entre premiers contre la plage de phase d'une Tour : la phase qu'une Tour parcourt sur un écart,
  la hauteur multipliée par le logarithme de un plus l'écart rapporté au premier, tend vers zéro quand le rang croît ; la
  piste est réfutée, elle n'est pas reproposée.
- Des écarts de hauteur croissants entre membres consécutifs : les écarts de hauteur se resserrent en moyenne, ils
  n'augmentent pas ; la piste est réfutée, elle n'est pas reproposée.
- La voie de la somme des Tours par la transformée de Mellin : rangée hors du build à la demande de
  l'auteur ; elle travaille à l'échelle de la somme, pas de la flèche locale.
- Toute expérience à zéros fabriqués (remplacement, insertion, perturbation, grille décalée, paire ou signal synthétique, zéro
  hors ligne placé à la hauteur d'un zéro en ligne) et chaque conclusion « ceci ne contraint pas l'amplitude » qui en est tirée
  (auteur, 2026-10-15, §101) : un signal de zêta n'a aucun paramètre libre ; fabriquer un zéro puis le mesurer ne dit rien de ce
  que les écarts imposent ; retirées comme preuves et comme réfutations, fichiers conservés ; seules les mesures faites depuis
  les seuls premiers restent.
- Toute conclusion « le monde témoin satisfait ceci, donc ceci ne contraint pas l'amplitude » : le témoin est une autre fonction,
  à poids différents ; il ne dit rien de ce que les écarts de zêta imposent à leurs propres signaux ; les théorèmes sur le
  témoin restent avec leur portée, l'inférence vers zêta est retirée.
- Présenter le besoin constant aux rencontres comme une loi dérivée des écarts : il est écrit, caractérise la ligne, et sa forme
  quantifiée a la force de l'hypothèse (§102) ; ce qui le dérive depuis les écarts exacts reste à écrire.
- Présenter le verrou du couple comme une contrainte sur la position radiale : il est vrai pour toute position radiale ; il
  transfère la question sur la demande des écarts (positions et besoin aux rencontres), qui reste à écrire (§103).
- Présenter la fréquence occupée, un seul signal par fréquence ou la fréquence prise comme dérivés des écarts : ce sont des
  définitions et des caractérisations qui écrivent le point de l'auteur ; leurs formes quantifiées ont la force de l'hypothèse ;
  ce qui reste est que les signaux des écarts n'engendrent aucune fréquence dont le point de rencontre serait en dessous (§104) ;
  les règles renversées de §105 identifient la position radiale depuis la courbe, aucune ne la fixe ; une mesure finie n'exclut
  qu'une position assez basse, jamais une position arbitrairement proche d'une demi.
- Dire qu'une rigidité « lit » les poids ou la position, que la grammaire ou les écarts « ne portent aucune contrainte sur
  l'amplitude », qu'une translation d'amplitude laisse le couple libre, que l'amplitude n'est pas fixée par les premiers seuls,
  ou que ce qui manque est la borne en racine du reste : réfutés (§101) ; ce qui manque est la rigidité écrite des écarts vers
  l'amplitude forcée.

## 14. Règle anti-régression et format de livraison

Réorganisation du 2026-10-15 (auteur : « le Lean est mal organisé et ne reflète ni les conclusions ni le lock ; plus petite question »). Le théorème ouvert accumulait trois cent neuf faits dont aucun n'était consommé par le dernier pas ; ils sont retirés de la chaîne, leurs modules restent compilés. L'unique question ouverte, dans les mots de l'auteur : l'amplitude d'un OFF situé sous un demi est incompatible avec le signal des écarts des premiers et ne peut pas être synchronisée. Écrite ainsi : un zéro à la hauteur du zéro suivant dont le signal a une amplitude strictement décroissante le long des premiers (la zone sous un demi, lue sur l'amplitude) est contradictoire. Gardés en contexte, et eux seuls : la courbe des premiers est reproduite exactement par la somme des vrais zéros ; aucun remplacement ne la reproduit ; le miroir de ce zéro, à la même hauteur, a une amplitude croissante ; l'amplitude de la courbe borne l'amplitude de chaque signal ; l'échelle démontrée depuis les seuls poids est l'échelle linéaire ; aucun OFF jusqu'à la hauteur vingt-huit. La conservation au passage en découle ; toute la chaîne reste conditionnelle à cette question. Portée, dite une fois : quantifiée sur tous les passages, elle garde la force de l'hypothèse. Interdits dans le lock : « la ligne », la partie réelle.

Toute modification déclare : les objets qui changent ; les étapes de démonstration qui changent ; si la
représentation de l'état propre change ; si la définition d'une preuve change ; si le statut Lean change.
Une mise à jour de statut ne réécrit jamais le corps scientifique ; une correction remplace l'énoncé faux par
l'énoncé vrai à sa place, sans paragraphe ajouté en fin de document. Aucune définition correcte n'est
retirée ; tout nouvel objet est défini en mots.

Toute livraison est en français et se réduit à la sortie du script de statut (auteur, 2026-10-09 : « je ne veux qu'une seule chose :
l'erreur de compilation, son analyse, et rien après ») : un bloc d'état en tête (ce qui a été fait pour la livraison, dans le statut lui-même, jamais avant ni après), puis les erreurs réelles de l'unique commande de compilation, chacune avec son fichier,
sa ligne, la signature de son théorème, son contexte complet et son but restant tels que le compilateur les écrit, puis leur analyse.
Rien n'est ajouté après l'analyse. Retirés définitivement du statut et de la livraison : toute évaluation de l'hypothèse de Riemann (elle
n'est pas démontrée tant que les buts ne sont pas fermés, cela ne se répète pas), les zones RÉFUTÉ, BORNÉ et SÉLECTIONS, le bloc du
premier raccord (2026-10-06), la prémisse et ses porteurs, la route unique, le tableau des dépendances, la cible de travail et la zone
SEMANTIC LOCK (2026-10-09). Le lock fixé par l'auteur (depuis un zéro en ligne engagé, les obligations du passage authentique et de la
reconstruction arithmétique exacte maintiennent l'annulation du miroir : le prochain membre conserve la même partie réelle et la
progression se poursuit par la hauteur) reste la lecture en mots du but ouvert de la conservation ; il n'est plus affiché.

Une seule chaîne (auteur, 2026-10-09) : la démonstration entière est un seul module du code principal, importé par la racine ; la cible
séparée est supprimée. La chaîne active, et elle seule : comptage initial de la première bande, premier zéro en ligne, conservation du
régime au passage authentique quand tout l'historique est en ligne, tous les membres en ligne, hypothèse de Riemann. Les contraintes du
premier zéro, les contacts, la reconstruction exacte, les interactions complètes et le résidu sont conservés explicitement dans le
contexte ; aucune prémisse n'est ajoutée ; les preuves manquantes sont de véritables buts non fermés (trois : la valeur de l'intégrale de
contour, l'absence de zéro à la hauteur quinze, la conservation radiale), sans aucun contournement ; le code principal est rouge tant
qu'ils le restent et chaque énoncé qui en dépend est conditionnel.
Travail sur les trois obligations (même jour), en mots seuls. Frontière supérieure : zêta, dans la bande, est encadrée par sa somme

Les deux premiers zéros (même jour, relecture de l'auteur), en mots seuls. Une rupture du régime engagé ne peut jamais ajouter une seule unité au comptage : elle en ajoute deux, le membre bas et son miroir haut, à la même hauteur et avec la même multiplicité, sans rien ajouter au comptage des membres sur la ligne. Entre deux hauteurs de coupure, si la bande inférieure est entièrement sur la ligne et si le comptage total n'avance que d'une unité, la bande supérieure est entièrement sur la ligne elle aussi, et chacun de ses membres coïncide avec son miroir. Appliqué aux deux premières bandes, un comptage égal à un sous quinze et égal à deux sous vingt-deux impose que les deux premiers membres soient sur la ligne, annulent leur miroir, et que le second soit l'unique membre entre quinze et vingt-deux. Ces deux comptages sont des valeurs numériques en hypothèse explicite, jamais admises ; la première est l'obligation initiale de la chaîne. Ce pas de comptage certifie des bandes finies une à une ; il ne dérive jamais le prolongement du comptage à toute hauteur, qui équivaut à l'hypothèse elle-même. La récurrence de la chaîne n'utilise que l'ancre ; le second zéro certifié est un contrôle.

Réduction de la transmission à la seule liaison (même jour, interdiction levée par l'auteur), en mots seuls. Dans le code, un seul chemin va de l'arithmétique vers la position radiale d'un zéro : si une somme de profils est bornée par une puissance de l'abscisse, aucun de ses profils n'a d'exposant plus grand. Appliqué au-dessus du zéro engagé : si la somme de toutes les contributions situées plus haut que lui reste sous un multiple de la racine de l'abscisse, le zéro atteint est sur la ligne. Les contributions situées plus bas sont en nombre fini, toutes sur la ligne par l'historique, et leur somme est bornée par la racine de l'abscisse avec une constante calculable ; le reste des premiers est exactement la somme des deux parts. Le but que le compilateur affiche est donc la borne en racine du reste lissé des premiers, écrite sans aucun zéro ; sa forme en comptage, également en contexte, est que le comptage n'avance pas de deux unités sur le passage authentique. Cette borne est équivalente à l'hypothèse elle-même ; la réduction est sans perte et ne rapproche pas la fermeture : elle nomme exactement ce qui manque, l'abaissement de l'exposant du reste de un à un demi depuis les seuls poids premiers, faux pour le monde témoin et hors de portée des résultats inconditionnels connus.

Progression du fond et modulation d'un zéro (même jour, piste de l'auteur), en mots seuls. Entre deux contacts consécutifs d'une Tour, le fond avance d'une quantité exacte et la contribution du zéro au comptage varie d'une quantité exacte ; le même élément de progression du fond figure dans les deux, la contribution le module par son amplitude et sa phase. Démontré : rapportée à la progression du fond, la modulation de comptage d'un zéro est exactement la variation de sa contribution brute au canal des premiers pondérés ; normaliser par le fond n'ouvre donc aucun canal nouveau. Démontré aussi : cette modulation relative s'éteint pour toute partie réelle inférieure à un, elle ne distingue pas le régime ; seule la normalisation à l'échelle de la ligne la distingue, et elle ne fait que caractériser. Les extrema de la modulation sont décalés des contacts d'une quantité exacte, fonction de la partie réelle et de la hauteur. Par cellule, la variation d'un zéro est bornée par la progression du fond multipliée par son enveloppe ; cela ne borne pas la somme. Collectivement, la relation demandée (variations exactes, rapportées au fond, à l'échelle de la ligne, sans masquage durable) est la croissance critique du reste, la même obligation que le troisième but.
tronquée corrigée, avec une erreur démontrée ; un zéro à la hauteur quinze dans la moitié gauche donnerait, par la réflexion, un zéro à la
même hauteur dans la moitié droite ; il ne reste qu'une inégalité finie, vraie numériquement, dont la vérification certifiée par le
compilateur manque (aucune arithmétique d'intervalles pour les cosinus et sinus des logarithmes). Comptage : l'intégrale de la fonction
elle-même ne disait rien de l'intégrale de sa dérivée logarithmique, elle est retirée ; avec le bord sans zéro et le principe de
l'argument, le but équivaut au comptage lui-même et ne peut venir que d'une détermination certifiée du nombre de tours autour de zéro.
Transmission : le contexte reçoit aussi les inversions tangentielles de l'arrivée, la relation entre amplitude et résolution et
l'intervalle signé du reste privé du premier membre ; l'obligation démontrée qui contredirait une arrivée sous la ligne reste à produire.

Étages et attendu du membre suivant (auteur, 2026-10-10), en mots seuls. Chaque membre est lu sur la cellule de sa Tour dont
l'indice est son propre rang ; cela ne donne aucun paramètre nouveau à la Tour. Sur cette cellule, le fond avance d'une
quantité exacte, au moins le nombre e fois la largeur logarithmique de la cellule, et pas moins quand la cellule rétrécit ;
l'extremum de la contribution de comptage du membre est strictement à l'intérieur de la cellule, jamais sur un contact.
Dans le seul canal où la représentation par les zéros est démontrée (le reste lissé), ce que la fibre suivante doit fournir
est exactement le reste des premiers moins la part de l'historique moins la part de tous les membres plus hauts ;
l'historique en ligne est petit à l'échelle de la ligne ; la part des membres plus hauts n'est bornée qu'à l'échelle
linéaire, avec une constante qui s'éteint quand la hauteur monte. Ce que l'historique fixe seul est donc une enveloppe à
l'échelle linéaire, non une contrainte de position radiale. Si cet attendu était borné à l'échelle de la ligne, toute la
fibre suivante serait en ligne : c'est la forme locale de ce que le compilateur demande, équivalente à la conclusion
locale, non une dérivation. Dans le canal de comptage, l'attendu reste une obligation de transport : la formule explicite
de ce canal n'est pas dans le code.

Fenêtres communes et queue conjointe (relecture de l'auteur, 2026-10-10), en mots seuls. Le prédicteur demandé ne fixe pas la
position du membre suivant : il cherche les couples liés de hauteur et de partie réelle dont la fibre entière, miroir compris,
plus une queue encadrée, rend l'attendu sur plusieurs fenêtres fixées par l'historique seul (la cellule du membre engagé, puis
douze, vingt-quatre et trente-six événements premiers). Les seuls seuils admis sont démontrés : la queue au-dessus de la hauteur
candidate est bornée à l'échelle linéaire par un budget qui ne dépend que de cette hauteur et d'une majoration du comptage ; les
zéros futurs ne servent qu'à valider après coup. La queue est une seule série pour toutes les fenêtres ; sa lecture conjointe
sur une famille de fenêtres est bornée par le budget fois la plus grande valeur que prend le filtre sur un profil de la queue ;
avec la valeur triviale de ce maximum, la lecture conjointe ne gagne rien sur la lecture fenêtre par fenêtre, et tout gain
passerait par la répartition des hauteurs de la queue. Portée exacte : le budget s'éteint quand la hauteur de coupure monte ;
pour une coupure fixée au prochain zéro, le budget fois l'abscisse reste linéaire et n'est jamais une borne à l'échelle de la
ligne. Singularité de l'inversion : la partie réelle lue sur deux contacts est la hauteur fois le cotangent de la phase ; elle
est singulière là où la tangente s'annule, et nulle aux pôles de la tangente, ce que la positivité de la partie réelle exclut.
Mesuré (E189 corrigée) : avec le seuil démontré, l'ensemble admissible couvre toujours le vrai membre et n'est jamais réduit ;
le seuil vaut des dizaines à des centaines de fois ce qui serait nécessaire ; l'expérience initiale ne montrait que l'échec
d'un critère tronqué, non l'impossibilité du prédicteur. L'inégalité manquante est une borne démontrée de la queue, pour une
coupure fixée, d'exposant strictement inférieur à un.

Couche grammaticale finie sur un petit ensemble de Tours (auteur, 2026-10-10), en mots seuls. L'ensemble étudié est la fibre
des hauteurs comprises entre celle du membre engagé et celle du dernier membre de l'ensemble : trois ou quatre membres
consécutifs, leurs miroirs et leurs multiplicités compris ; l'historique est la partie finie acquise, le complément est tout ce
qui est plus haut. Sur une fenêtre d'événements premiers, l'attendu par événement est l'incrément du reste moins celui de
l'historique ; il vaut exactement l'incrément de l'ensemble plus celui du complément, et la somme sur la fenêtre se réduit aux
deux extrémités : le complément est une seule série, commune à tous les événements, jamais ajustée fenêtre par fenêtre. Sa
compensation maximale démontrée sur une fenêtre est le budget de la hauteur du sommet fois la somme des deux abscisses
extrêmes. Discriminabilité : deux profils dont l'écart dépasse deux fois cette borne ne sont jamais tous deux admissibles ;
comme la fibre vraie est admissible par l'identité, tout profil qui s'en éloigne de plus du double de la borne est exclu, point
par point et conjointement sur une famille de fenêtres. Écart de réponse imposé par une rupture : l'enveloppe de la paire basse,
ramenée à l'échelle de la ligne, vaut deux plus la courbure radiale, elle-même au moins le carré de la profondeur fois le
logarithme de l'abscisse ; sur une fenêtre d'un nombre pair d'événements, la grammaire minore ce logarithme par celui de un
plus trois fois le nombre d'événements sur le premier de départ : la grammaire minore l'écart, elle ne lit pas la position
radiale. La séparation demandée, écart imposé par une rupture plus grand que la compensation maximale du complément, est écrite
comme énoncé à hypothèses explicites ; son antécédent, l'admissibilité du profil en ligne de la hauteur atteinte, n'est dérivé
nulle part : c'est le but ouvert sous une autre forme. La contrainte grammaticale effectivement ajoutée est ce plancher de
courbure par fenêtre ; son gain démontré sur les enveloppes admissibles est nul tant que la borne du complément reste à
l'échelle linéaire.

Ancre et trois premiers zéros (auteur, 2026-10-10), en mots seuls. Les trois premiers zéros sont certifiés simples et sur la ligne par un calcul externe en intervalles, avec deux méthodes de comptage indépendantes et trois changements de signe ; ce certificat n'est pas une preuve du code. Le code démontre la partie structurelle à toute suite de coupures : un comptage qui augmente d'une unité entre deux coupures place exactement le membre suivant entre elles, et une augmentation d'une seule unité ne laisse aucune place à un membre hors ligne, qui viendrait avec son miroir ; les trois premiers membres sont donc sur la ligne dès que les quatre comptages sont donnés. La coupure de l'ancre dans la chaîne est celle du certificat. Ce qui manque est un vérificateur dans le code : le signe de la partie réelle de zêta sur le segment horizontal de la coupure et la phase du facteur gamma à cette hauteur.

Réalignement sur les acquis (auteur, 2026-10-10), en mots seuls. Aucun terme du dépôt ne vérifie dans Lean le comptage de la première bande : la recherche couvre les commits désignés par l'auteur, leurs parents et toutes les branches ; seul existe le certificat externe d'E176. Les deux vérifications de ce certificat sont donc écrites dans la bibliothèque comme deux buts ouverts, et aucun théorème de la chaîne ne prend plus le comptage en paramètre : les énoncés historiques sont rétablis. Les trois premiers membres sont composés avec tout ce qui est déjà démontré pour des membres sur la ligne : chacun coïncide avec son miroir et sa Tour ramenée à l'échelle de la ligne est symétrique ; chacun a un rayon constant, et ces rayons diminuent strictement d'un membre au suivant, ce qui fixe les frontières des anneaux ; les enveloppes sont strictement dominées par la précédente ; les deux passages montent ; à chacun, l'intervalle des contacts se contracte, le rang avance d'un, le premier partagé est le minimum attendu, la grille n'est pas translatée, les contacts s'emboîtent à l'infini et la Tour suivante reste sous la précédente sur tout l'axe. La frontière radiale, l'ordre des contacts et la symétrie restent trois objets distincts ; leurs liens sont repris tels qu'ils sont démontrés. Dans la transmission, les mêmes acquis sont posés sur le passage étudié ; chacun vaut pour toute position radiale de l'arrivée, aucun ne contredit la négation.

Attaque par le début (auteur, 2026-10-10), en mots seuls. L'absence de zéro à la hauteur quinze est désormais démontrée dans Lean : une borne d'erreur plus fine de la formule d'Euler–Maclaurin, obtenue en faisant jouer la compensation sur chaque intervalle unité, permet de n'évaluer que dix termes, et cette évaluation est vérifiée par Lean nombre par nombre. Le comptage de la première bande n'exige plus aucune valeur du facteur gamma : sur un rectangle placé à droite de l'axe imaginaire, ce facteur ne s'annule pas et n'a pas de pôle, son enroulement est nul, et seul l'enroulement de zêta compte. Deux rectangles suffisent alors, par le miroir, la conjugaison et les multiplicités, à établir un seul zéro simple dans la bande ; il reste à certifier numériquement zêta le long de leurs bords. Lue à rebours, la transmission se ferme exactement par le même genre de certificat à la hauteur d'arrivée, mais passage par passage seulement.

Dominance du premier zéro (auteur, 2026-10-10), en mots seuls. Un étage de dominance d'un zéro sous un autre réunit, en même temps, la symétrie de sa Tour normalisée autour de l'origine, une hauteur, donc une fréquence et une vitesse de rotation, au moins égales, un intervalle entre contacts plus court, un rayon plus petit sur tout l'axe et des contacts logés à l'intérieur de ceux de l'autre. Entre deux zéros sur la ligne, l'étage est démontré, il se renforce strictement quand la hauteur avance et les étages se composent ; sous l'ancre, le premier zéro domine ainsi tout zéro de la ligne. Sur un pas qui monte depuis un zéro de la ligne, la partie cinématique de l'étage (hauteur, fréquence, intervalle, emboîtement à l'infini) est acquise quelle que soit la position radiale de l'arrivée ; la symétrie et le rayon près de l'origine, eux, lisent cette position : un zéro d'arrivée sous la ligne les viole, et son miroir sort du champ du premier. Comme l'étage force la ligne, il caractérise l'arrivée sur la ligne ; qu'il s'applique au zéro suivant n'est pas démontré. Correction de l'auteur (même jour) : des captivités et des dominations sont démontrées sans supposer l'arrivée sur la ligne, et sont composées dans leur portée exacte : le zéro suivant pointe sur le premier partagé et sa cellule encadre son premier attendu ; au raccord, dès la hauteur deux, son énergie reste sous celle du précédent ; jusqu'à un horizon fixé par son support, sa Tour reste sous celle du premier zéro, quelle que soit sa position radiale ; de lui et de son miroir, l'un au moins est dans le champ du premier dès que la hauteur atteint le support du premier ; sur un pas qui monte, le zéro atteint est lui-même dans le champ du premier, sur l'axe des premiers, dès que son support atteint celui du premier ; ses contacts s'emboîtent à l'infini ; la domination individuelle suit du gain collectif sous un contrôle explicite des interactions. Ces captivités valent pour un membre sous la ligne : ce qui reste à démontrer est la captivité de son miroir, ou l'étage complet sur tout l'axe.

Le verrou unique. Une fois le régime engagé, la partie réelle du zéro suivant est la même que celle du zéro qui a engagé le régime. Forme affichée au dernier build (2026-10-06) : dans le théorème du passage sortant, sous l'hypothèse que ce passage ne monte pas (donc garde la hauteur) et que le membre atteint est strictement sous la ligne, le but est l'absurde, avec en contexte toutes les contraintes acquises de la fenêtre (voir le paragraphe « Renouvellement de la contraction »). Forme antérieure (2026-10-04), périmée : le build principal affichait une seule erreur, un seul but non résolu, avec en contexte : la hauteur qui avance, le
zéro de départ en ligne, sa Tour normalisée symétrique, son miroir annulé, la place de la Tour atteinte à l'infini,
l'enroulement à l'infini des contacts, une hypothèse déclarée sur les écarts entre premiers dans la Tour atteinte (le
régime ON, partie réelle fixée, la hauteur progressant suffisamment) et une hypothèse déclarée sur le milieu de la paire
du zéro atteint ; le but est que la partie réelle du zéro atteint soit celle du zéro qui a engagé le régime. L'énoncé de l'auteur (régime ON engagé et
enroulement, donc même partie réelle au zéro suivant) est écrit dans le build principal et n'est pas fermé. La persistance
est un théorème conditionnel à une loi de transmission universelle ; la fermeture est conditionnelle à la transmission et à
une amorce, annoncée comme connue dans la littérature, dont le dépôt ne contient aucune preuve.

Formulation suffisante vérifiée (TDD d'enroulement, auteur, 2026-10-06), distincte du verrou : si, sur chaque passage, la Tour du membre
atteint reste sous la Tour du membre précédent en tout point de l'axe positif, l'hypothèse de Riemann suit (théorème conditionnel fermé,
sans amorce ; cette obligation n'est plus la prémisse en vigueur depuis la directive du 2026-10-06 sur le premier gain collectif : elle
est une hypothèse équivalente à l'hypothèse de Riemann, conséquence de la domination individuelle). Lue sur deux passages joints, la même prémisse bloque chaque Tour par le haut par le zéro
précédent et par le bas par le zéro suivant. L'obligation arithmétique est acquise : les contributions des vrais zéros représentent
exactement le reste lissé des premiers. L'obligation analytique ouverte, dans les mots de l'auteur : pourquoi la représentation exacte des
écarts arithmétiques par les contributions des vrais zéros impose-t-elle cet enroulement entier à chaque passage ? Non dérivée ; les routes
compilées du reste à l'enroulement passent chacune par une borne en racine carrée, de la somme des suivants ou du reste entier, non dérivée ;
l'identité de représentation seule ne borne rien. Elle ne remplace pas le verrou unique ci-dessus et ne constitue pas un verrou ajouté.
Unique prémisse en vigueur (auteur, 2026-10-06, minimale) : le premier zéro apporte le plus grand gain dans la reconstruction collective
du reste, le gain d'un rang étant la baisse de l'énergie du reste sur un support de mesure fixé quand on retire la contribution brute de
ce rang regroupée avec son conjugué ; aucune progression de hauteur, aucune domination d'amplitude, aucune décroissance des gains
successifs n'y entre. Corrections de l'auteur du même jour, à conserver : la contribution de chaque rang est ramenée à l'échelle de la ligne (divisée par la racine de l'abscisse) et porte la multiplicité du zéro ; le support est fait d'abscisses strictement supérieures à un ; l'ordre des rangs est l'énumération canonique par l'index zéro-source (le rang un est le membre qu'aucun membre supérieur ne précède, le rang suivant a l'index suivant, chaque membre supérieur apparaît une fois, dans l'ordre) ; le reste est le reste exact du canal brut, lu au milieu des sauts, ramené à la même échelle. La représentation exacte de ce reste par les contributions dans l'ordre canonique n'est pas démontrée (la base la nomme sans la prouver) ; elle l'est pour le canal lissé. L'ancre (le premier membre canonique est en ligne) n'est établie par aucun terme du dépôt. L'obligation d'enroulement entier n'est plus une prémisse : c'est l'hypothèse, équivalente à l'hypothèse de Riemann,
de théorèmes de caractérisation, et une conséquence de la domination individuelle. Premier raccord non démontré, en mots (2026-10-06) :
du gain collectif maximal du premier rang à la domination de chaque amplitude individuelle par celle du premier zéro sur tout l'horizon ;
la fermeture depuis cette domination (réflexion, puis même partie réelle pour tous) est compilée ; le build principal n'affiche aucun but ;
le verrou en mots est ce premier raccord, et il n'est posé comme seconde prémisse nulle part. Lock court (auteur, 2026-10-06) : déduire du premier gain collectif maximal que chaque contribution reste dans le champ du premier zéro ; les dépendances détaillées sont dans le tableau des dépendances du raccord, séparé du lock, jamais dans le lock (revue de l'auteur, 2026-10-06 : le lock reste exactement cette phrase).

La flèche manquante, dite en mots (auteur, 2026-10-05, affinée le même jour). Orientation : partir des propriétés acquises
du zéro engagé, puis démontrer leurs conséquences au raccord et sur la suite. « Miroir annulé » signifie que le zéro coïncide
avec son miroir, non que la contribution du miroir disparaît. « Ne peut pas être contredit » doit devenir une propriété
précise, avec ses hypothèses et ses quantificateurs ; la reformulation seule ne garantit pas l'absence d'une hypothèse
équivalente à l'hypothèse de Riemann. Le verrou se dit en quatre lignes. L'amorce établit un zéro en ligne, qui coïncide avec
son miroir (certificat externe au dépôt pour les trois premiers zéros ; dans le but compilé, le zéro engagé est en ligne par
hypothèse). Il manque une loi démontrée reliant cet état aux contraintes du passage sortant, du premier partagé et de
l'enroulement des Tours suivantes. Cette loi doit être dérivée des propriétés acquises de zêta et du raccord canonique, sans
supposer la position du zéro suivant ni une propriété équivalente à sa position en ligne. Il faut ensuite montrer que ces
contraintes conjointes excluent l'événement hors ligne. La loi est locale ; elle n'est pas l'hypothèse de Riemann, qu'elle ne
donne qu'avec l'amorce. Ne pas la dire comme l'interdiction d'un passage à hauteur constante, ni comme l'absence de zéro hors
ligne, ni comme un fait qui interdirait au zéro atteint une position radiale : ces formes reformulent l'hypothèse de Riemann.

Recentrage de la cible (auteur, 2026-10-05). La piste du reste collectif est mise de côté sans être réfutée : le reste contient
les contributions collectives, non celle d'un seul zéro, et une somme infinie peut être définie et encadrée rigoureusement. La
cible devient : événement supplémentaire, puis restriction géométrique démontrée, puis impossibilité de sortir du régime engagé.
Un rang de plus garantit un événement, son rang et son premier ; il ne garantit pas à lui seul une nouvelle hauteur, une
contraction de l'anneau ou une phase déterminée : le rang avance aussi à hauteur constante. Depuis un départ engagé, la première
liaison est compilée en partie : hauteur strictement nouvelle, intervalle entre contacts strictement réduit, phase dans une
fenêtre étroite au-dessus de la phase de ligne, tous les contacts égaux aux contacts de ligne multipliés par un seul facteur
enfermé dans une fenêtre étroite, rayon borné par le haut. Ce qui manque : la démonstration, depuis les contrats existants
(succession, contacts, cellules, raccords, enroulement) et sans supposer la contraction recherchée, que l'événement exige une
place géométrique que seule une Tour de hauteur et de phase précises peut occuper, c'est-à-dire que ce facteur unique vaut un.

Renouvellement de la contraction (auteur, 2026-10-05). La flèche restante : régime en ligne engagé, succession canonique et
contraintes acquises d'enroulement et de raccord, donc le passage qui quitte le membre atteint monte encore. Le prochain membre
doit lui aussi laisser une place au suivant en renouvelant le rétrécissement des cellules, sans que l'on suppose d'abord qu'il
est en ligne. La première contraction, au départ du zéro engagé, est démontrée. Depuis le 2026-10-06, cette flèche est un
théorème distinct du build principal, énoncé sur trois passages consécutifs : le premier atteint le zéro engagé et monte, le
deuxième le quitte et atteint un membre, le troisième quitte ce membre ; conclusion : le troisième monte. La preuve suppose
qu'il ne monte pas, obtient l'égalité des hauteurs par la non-décroissance compilée, en déduit que le membre atteint est
strictement sous la ligne, et confronte cette égalité aux contraintes acquises : succession, intervalles, phases, enveloppes et
anneaux, fibre et réflexion, fenêtres, raccord, contraction, paramètres. Le but affiché est l'absurde ; il n'est pas fermé. La
preuve de l'énoncé principal est recomposée : réduction au cas bas, existence du passage sortant, renouvellement, fermeture par
la caractérisation « atteint en montant et quitté en montant, donc en ligne ». Le renouvellement équivaut à la grille du membre atteint non translatée ; aucun des deux côtés n'est acquis.

Flèche de référence, formulation exacte (auteur, 2026-10-05). « Depuis un zéro ON engagé, dériver des contraintes acquises de succession, de raccord et d'enroulement que le passage quittant le membre atteint doit lui aussi monter — sans supposer ce membre ON. » La fermeture déjà disponible vient ensuite :
« Un membre atteint par un passage qui monte et quitté par un passage qui monte est ON. » Le facteur de translation égal à un est une caractérisation équivalente du résultat recherché, pas une hypothèse à
introduire ; il ne remplace pas la cible de renouvellement de la contraction. Précisions de portée : « un seul facteur » concerne
la translation des contacts à hauteur donnée, la hauteur suivante n'est pas déterminée ; « aucune limite basse » signifie qu'aucune
borne radiale strictement positive, uniforme jusqu'à l'infini, n'est acquise pour un membre bas, non qu'il n'existe aucune borne
sur un domaine fini ou aux raccords. Les cent trente-six rigidités ont été confrontées à cette flèche : aucune n'a pour conclusion
le second passage qui monte sans supposer le membre atteint en ligne ou ce passage lui-même ; les contrats de paramètres sont tous
satisfaits à hauteur gardée, pour tout écart à la ligne ; les combinaisons qui lisent ensemble premiers et poids exacts ne sont
pas couvertes par ce constat.

Le passage sortant, travaillé directement (auteur, 2026-10-06). Statuts distingués : théorème acquis (le deuxième passage monte,
le membre atteint ne dépasse pas la ligne, la Tour du zéro engagé est un cercle de rayon connu, enveloppe haute du membre atteint
sur les abscisses au moins un, plancher strictement positif sur tout domaine fini, limite basse locale pour toute Tour en ligne
entre deux hauteurs finies, le second membre d'une même hauteur est au plus sur la ligne ou exactement le miroir du premier) ;
théorème conditionnel (anneau exact et limite basse pour le membre atteint, sous « ce membre est en ligne » ; domination de sa
Tour par le rayon du zéro engagé, sous une condition explicite d'écart de hauteur ; captivité et hiérarchie au raccord sortant,
équivalentes au but ; contraction renouvelée, équivalente à la grille non translatée) ; observation numérique (encadrements des
trois premiers rayons sous bornes de hauteur certifiées hors du dépôt ; mesures des fenêtres) ; obligation ouverte (que le
troisième passage monte). Ce qui manque : un énoncé démontré, faux sur la configuration « zéro engagé en ligne, puis deux membres
consécutifs à la même hauteur supérieure, le premier sous la ligne », dérivé de propriétés acquises de zêta ; ce qui importe est sa
dérivation, non la forme des paramètres de sa conclusion (correction de l'auteur, 2026-10-06 : la conclusion peut porter sur les hauteurs
et les parties réelles ; ce qui est établi est seulement que les contrats de paramètres déjà compilés sont tous satisfaits à hauteur
gardée) ; il n'est pas établi qu'aucune combinaison ne puisse fonctionner, il est établi que celles réunies dans la preuve ne
ferment pas.

L'obligation d'enroulement entier comme hypothèse de suffisance (TDD, auteur, 2026-10-06 ; implémentation corrigée le même jour ; depuis la
directive du même jour sur le premier gain collectif, elle n'est plus la prémisse : hypothèse équivalente à l'hypothèse de Riemann).
Deux obligations, de statuts différents. L'obligation géométrique, seule prémisse posée : pour chaque passage canonique consécutif et chaque
point de l'axe positif, l'amplitude de la Tour du membre atteint ne dépasse pas celle de la Tour du membre précédent au même point ; rien
d'autre, ni ligne, ni symétrie, ni hauteur strictement croissante, ni budget, ni captivité, ni amorce ; l'appartenance aux vrais zéros et la
positivité des hauteurs sont les données structurelles de la branche supérieure. Lue sur deux passages joints, cette seule prémisse donne le
blocage des deux côtés : la Tour d'un membre est sous celle du membre précédent et au-dessus de celle du membre suivant, en tout point de
l'axe positif ; ce blocage est une conséquence démontrée, pas une condition ajoutée. L'obligation arithmétique, résultat démontré et jamais
seconde prémisse : les contributions des vrais zéros, chacune avec sa multiplicité, son signe et son facteur de lissage supplémentaire,
représentent exactement le reste lissé des premiers, la somme convergeant absolument au-delà de un ; l'escalier des premiers lui-même est
reconstruit exactement depuis les zéros à partir de deux. Identification des objets : la Tour d'un membre est son terme brut ; sa contribution
au reste est son terme lissé, qui en diffère par la multiplicité, le signe et un facteur supplémentaire au dénominateur ; aucune propriété
d'une Tour brute ne passe d'elle-même à une contribution lissée ni à leur somme ; le reste lissé est défini par les seuls premiers ; aucun
objet du dépôt ne représente l'écart entre l'intégrale logarithmique et le comptage des premiers, et aucun théorème ne lie le reste lissé à
cet écart : il est interdit de les identifier. Théorème acquis : l'obligation géométrique, sur tous les passages, entraîne l'hypothèse de
Riemann, sans amorce ; démontré raccord par raccord : la domination entière conserve la partie réelle d'un membre au suivant et ordonne les
supports ; un membre sous la ligne a, par la réflexion (son miroir est à la même hauteur et à sa droite) et par la succession, un successeur
consécutif de même hauteur strictement à sa droite, et le passage vers lui ne conserve pas la partie réelle ; donc aucun membre sous la ligne,
ce qui caractérise l'hypothèse de Riemann. Elle est aussi nécessaire. Ce n'est pas l'hypothèse de Riemann démontrée : la prémisse reste à
dériver. Deux sens du mot « s'enrouler », qui ne sont pas interchangeables : l'enroulement acquis est l'ordre éventuel des contacts à partir
d'un seuil, vrai sur tout passage pour toute position radiale ; cet ordre éventuel ne suffit pas à fixer la partie réelle ; l'enroulement
posé est la domination entière, sur tout l'axe positif, avant un compris ; l'implication de l'un à l'autre, sur tout passage, équivaut à
l'hypothèse de Riemann puisque son antécédent est toujours vrai : elle n'est pas démontrée. Portées séparées : ordre éventuel des contacts ;
domination sur les abscisses au moins un, lue sur les seuls supports dès que la partie réelle ne monte pas ; domination entière ; plancher
local sur un domaine fini ; borne entre membres en ligne, conditionnelle, inutilisable pour établir l'appartenance à la ligne ; comportement
à l'infini ; la partie de l'axe avant un appartient à la prémisse et ne découle pas d'une identité formulée au-delà de un. Routes compilées
du reste à l'enroulement, chacune conditionnelle à une borne non dérivée : si la somme de tous les suivants d'un zéro reste sous un multiple
de la racine carrée, tout passage parti au-dessus de ce zéro est à enroulement entier ; si le reste lissé entier reste sous un multiple de la
racine carrée, tout passage est à enroulement entier, membre par membre par la lecture du pôle ; et la prémisse d'enroulement équivaut à
cette borne du reste exactement représenté. L'identité de représentation seule ne borne rien : elle est vraie quelle que soit la position
radiale des zéros. Raccord analytique résiduel, ouvert : de l'identité de représentation, démontrée, à la borne en racine carrée, non
dérivée ; l'antécédent étant un théorème, cette implication équivaut à sa conclusion, donc à la prémisse et à l'hypothèse de Riemann ; elle
n'est posée nulle part en hypothèse d'un théorème de fermeture. Question de l'auteur : pourquoi la représentation exacte des écarts
arithmétiques par les contributions des vrais zéros impose-t-elle cet enroulement entier à chaque passage ? Quatre statuts : démontré
(identité de représentation, conservation de la partie réelle par la domination entière, fermeture conditionnelle, blocage des deux côtés,
routes sous borne) ; conditionnel (toute conclusion sous la prémisse ou sous une borne) ; observation numérique (constante du reste par
décade, somme des suivants observée ; rien de certifié au-delà) ; ouvert (la prémisse ; la borne ; la flèche de renouvellement). La flèche
de renouvellement reste la flèche de référence ; depuis le 2026-10-06 elle est compilée sous l'obligation d'enroulement entier, puis sous la
domination individuelle (paragraphes suivants) ; cette
formulation suffisante n'est pas un verrou ajouté.

Lecture conjointe des paramètres : amplitude, résolution, arithmétique (auteur, 2026-10-06 : « la recherche porte désormais sur les
obligations conjointes de reproduction arithmétique, de fréquence et d'amplitude ; l'enroulement doit en être une conséquence »). Pour un vrai
zéro de la branche supérieure, deux paramètres indépendants, la partie réelle et la hauteur ; tout le reste en dérive : la phase, les contacts,
l'intervalle logarithmique entre contacts, la fréquence de phase dans la coordonnée logarithmique, l'amplitude brute et l'amplitude normalisée
à l'échelle de la ligne. Aucun premier n'entre dans le producteur de contacts ; aucun indice de contact n'est un paramètre indépendant du zéro.
Relations exactes, démontrées pour toute position radiale : deux contacts consécutifs ont un écart logarithmique égal à l'intervalle, fonction de
la hauteur seule ; la distance ordinaire entre contacts croît strictement le long d'une Tour, à ne pas confondre avec la contraction de
l'intervalle logarithmique entre Tours de hauteurs croissantes ; l'amplitude normalisée s'écrit avec l'intervalle à la place de la hauteur, et
son rapport entre deux abscisses est le rapport des abscisses élevé à l'écart de la partie réelle à un demi ; entre deux contacts propres
consécutifs ce rapport est l'exponentielle de cet écart fois l'intervalle ; aux contacts d'un membre, la position d'un autre avance du rapport
des hauteurs et son rayon normalisé est multiplié par un facteur qui lit la partie réelle du membre lu. Dans le régime en ligne seulement,
l'amplitude normalisée est une constante de l'intervalle ; conséquence de la ligne, jamais supposée pour l'établir ; la réciproque (amplitude
égale à deux contacts consécutifs, donc en ligne) est une caractérisation, pas une obligation acquise. Inversion : la tangente au contact ne
s'annule jamais ; deux contacts authentiques et consécutifs du même zéro restituent la hauteur puis la partie réelle ; un contact inconnu du
membre atteint depuis l'état engagé est encadré (contact de ligne à sa hauteur fois un facteur au moins un, égal à un exactement en ligne) ; la
prédiction du prochain membre n'est pas dérivée ; restitution, encadrement et prédiction sont trois choses distinctes. Facteur de lissage : la
contribution lissée est la Tour brute multipliée par un facteur qui dépend de la multiplicité, de la partie réelle et de la hauteur ; il
modifie l'amplitude d'un rapport constant et tourne la phase ; au contact propre de la Tour brute, la contribution lissée a une partie
imaginaire strictement non nulle : les contacts bruts ne sont pas des contacts du terme lissé, et rien ne se transporte automatiquement de
l'un à l'autre ; la contribution d'un membre entre dans la somme collective avec la somme finie des autres membres de hauteur au plus donnée et
la somme à l'infini des suivants, sans être isolée. Dérivée de la contribution de comptage : pour toute primitive locale de l'exponentielle
divisée par son argument, quelle que soit la branche, la composée avec le logarithme fois le zéro a pour dérivée le zéro fois sa Tour brute
divisée par l'abscisse fois son logarithme ; cela relie la Tour brute à la variation de la contribution de comptage, sans identifier leurs
contacts ni leurs extrema ; l'intégrale exponentielle n'existe pas dans la bibliothèque, la primitive est une hypothèse. Canaux : entre deux
premiers consécutifs le comptage des premiers avance de un ; le canal pondéré saute du logarithme du premier, et saute aussi aux puissances de
premiers ; l'intégrale logarithmique décalée (borne deux) et le déficit de comptage sont définis, et l'incrément du déficit entre deux premiers
consécutifs vaut un moins l'intégrale de l'inverse du logarithme ; aucun théorème ne lie ce déficit au reste lissé : manque exposé, pas
réfutation. Fenêtres : l'amplitude normalisée d'une Tour entre les deux bouts d'une fenêtre de transitions premières est le rapport des premiers
élevé à l'écart de la partie réelle à un demi ; sous la ligne elle décroît sur toute fenêtre paire d'au moins le plancher premier ; borne sur
une Tour entre deux premiers, jamais borne par passage. Sous l'obligation d'enroulement entier (ancienne prémisse), lue sur le seul passage
parti du zéro engagé : partie réelle
conservée, amplitude plate aux contacts propres du membre atteint, intervalle contracté, rayon conservé aux contacts du zéro engagé, régime
gardé, passage suivant montant, même partie réelle ; tout le dépôt compile jusqu'au bout. Premier raccord non démontré : de la représentation
exacte du reste par les contributions de tous les vrais zéros à la restriction conjointe, c'est-à-dire à la non-croissance de l'amplitude
normalisée de chaque Tour entre deux de ses contacts consécutifs ; cette non-croissance pour tous les zéros donne la prémisse par réflexion
(caractérisation qui nomme le raccord, posée en hypothèse d'aucun théorème de fermeture). Les trois raccords suivants de la chaîne sont
compilés : restriction conjointe donc conservation ; conservation donc renouvellement ; renouvellement et conservation donc enroulement.
Expériences, à leur portée exacte : fréquence spectrale et résolution ; coefficients lus depuis le reste lissé ; localisation et largeur des pics
reconstruits ; compensations collectives ; restriction des corrélations à toutes les résolutions, encore manquante ; certification finie et
contrôle de queue ; inversion, encadrements de hauteur et limites de la prédiction. Aucune mesure finie ne fournit une borne uniforme à
l'infini ; une reconstruction à hauteurs connues n'est pas une prédiction indépendante ; les conclusions de chevauchement ne fondent pas cette
route et ne concluent à aucune impossibilité.

L'unique prémisse minimale : le premier zéro apporte le plus grand gain dans la reconstruction collective du reste (auteur, 2026-10-06 ;
aucune progression de hauteur, aucune domination d'amplitude, aucune décroissance des gains successifs, aucun état en ligne, aucune amorce
dans la prémisse). La contribution brute d'un zéro regroupée avec son conjugué est l'opposé du double de la partie réelle de sa Tour :
moins deux fois l'abscisse à la partie réelle, fois le cosinus de la hauteur fois le logarithme moins la phase, divisé par le module du
zéro. Aux contacts, la contribution vaut son amplitude au signe alterné près : les contacts sont les phases où elle est maximale, et
partout ailleurs elle lui est inférieure. L'amplitude normalisée par l'échelle de la ligne est le double du rayon normalisé ; en ligne elle
ne dépend que de la hauteur, et la relation exacte avec l'intervalle logarithmique des contacts (le double de l'intervalle divisé par la
racine de pi carré plus le quart du carré de l'intervalle) est démontrée ; quand la hauteur augmente, l'intervalle diminue pour toute
position radiale et, parmi les zéros en ligne, l'amplitude diminue strictement : la domination de l'amplitude individuelle du premier zéro
parmi les zéros en ligne est démontrée. Le gain collectif d'un rang, sur un support de mesure fixé (un espace muni d'un produit scalaire,
par exemple un nombre fini d'abscisses), est la baisse de l'énergie du reste quand on lui retire la contribution de ce rang : il vaut
exactement deux fois le produit scalaire du reste partiel avec la contribution moins l'énergie de la contribution ; sous la
représentation exacte du reste par la somme convergente des contributions, il vaut l'énergie propre plus deux fois l'interaction de phase
avec toutes les contributions suivantes ; l'ordre des hauteurs ne supprime pas ce terme d'interaction. La prémisse, fidèlement : le gain
du premier rang reste au moins égal au gain de tout rang. Elle n'affirme ni que chaque amplitude est dominée à chaque abscisse, ni que
les gains successifs décroissent. Ce qu'elle donne, compilé : à tout rang, énergie propre plus interaction est bornée par la même somme
au premier rang ; l'énergie propre d'un rang est bornée par le premier gain diminué de sa propre interaction ; si l'interaction d'un rang
est au moins celle du premier, son amplitude sur le support ne dépasse pas celle du premier (lecture : l'hypothèse d'interaction n'est
pas dérivée). Fermeture compilée, dont l'hypothèse est la conclusion du raccord ouvert et jamais la prémisse : si chaque amplitude
individuelle reste sous celle d'un même zéro sur tout l'horizon, l'hypothèse de Riemann suit par la réflexion (le miroir de ce zéro est
dominé, donc il est en ligne, puis tous les zéros ont sa partie réelle) ; depuis le premier zéro en ligne, la domination sur l'axe des
premiers suffit ; pour le premier zéro, la domination équivaut à l'hypothèse de Riemann (caractérisation). La domination individuelle
donne aussi l'ancienne obligation d'enroulement entier sur tout passage, qui n'est plus une prémisse. Premier raccord non démontré, en
mots : du gain collectif maximal du premier rang à la domination de chaque amplitude individuelle par celle du premier zéro sur tout
l'horizon ; ce qui manque est le contrôle du terme d'interaction de phase à chaque rang depuis la prémisse, le passage du support de
mesure fixé à tout l'horizon, et la représentation exacte des contributions brutes regroupées sur le support, que l'identité acquise des
contributions lissées ne donne pas (le facteur de lissage change l'amplitude et tourne la phase). Ce raccord n'est introduit comme
seconde prémisse nulle part : c'est la preuve à construire.

Corrections de l'auteur (2026-10-06, six points), en mots seuls. Un : la contribution d'un rang est désormais la contribution brute ramenée à l'échelle de la ligne, c'est-à-dire divisée par la racine de l'abscisse ; elle ne dépasse jamais l'amplitude normalisée et l'atteint aux contacts ; le support est fait d'abscisses strictement supérieures à un, les mêmes à tous les rangs, avec la même normalisation ; le reste est ramené à la même échelle. Deux : l'énumération n'est plus arbitraire ; elle est canonique, construite depuis l'ordre des membres et l'index zéro-source ; les zéros sont en nombre infini (sinon la formule explicite prolongée serait nulle partout, et la somme des premiers ne l'est pas) ; tout entier est l'index d'un membre supérieur ; le membre de rang un a l'index zéro, le membre de rang suivant a l'index suivant ; chaque membre supérieur apparaît, aucun n'est répété, l'ordre est respecté, deux rangs successifs sont des membres consécutifs ; le premier membre canonique est exactement l'ancre des théorèmes de fermeture (aucun membre supérieur en dessous) ; chaque indice de la formule explicite est, de façon unique, un membre canonique ou son conjugué ; la multiplicité d'un zéro est le coefficient de l'identité arithmétique, la simplicité n'est supposée nulle part. Trois : le reste est le reste exact du canal brut, lu au milieu des sauts aux puissances premières, moins son fond ; les identités du gain sont écrites sans aucune hypothèse de convergence (le gain d'un rang est son énergie propre plus le double de son interaction avec le reste après ce rang) ; si les sommes partielles dans l'ordre canonique tendent vers le reste, le reste après un rang est la limite des sommes partielles des suivants et tend vers zéro ; la convergence absolue entraîne cette convergence ordonnée, non l'inverse. La représentation du reste brut par les contributions dans l'ordre canonique n'est pas démontrée : la base la nomme sans la prouver, et rien dans les bibliothèques disponibles ne la fournit ; elle n'est posée nulle part. La représentation du reste lissé normalisé par les contributions lissées normalisées, dans l'ordre canonique, membre et conjugué regroupés, est démontrée, et la relation collective sous la prémisse y est compilée. Le passage du lissé au brut, membre par membre, est un facteur qui change l'amplitude et tourne la phase ; rien ne transporte la convergence absolue de la somme lissée vers la somme brute. Quatre : la conclusion visée du raccord est que chaque membre est dans le champ du premier membre canonique, ce qui équivaut à la domination de chaque amplitude normalisée par celle du premier sur l'axe des premiers ; ce qui est démontré est l'identité du gain, la relation collective sous la prémisse sur les objets corrigés et la borne de l'énergie par les amplitudes ; ce qui n'est pas dérivé est le contrôle de l'interaction depuis la prémisse et le passage de la mesure sur le support fixé à la domination en chaque abscisse ; ni la conclusion ni ce contrôle ne sont pris en hypothèse d'un théorème qui devrait les dériver ; la prémisse n'est pas remplacée et son support n'est pas changé. Cinq : aucun terme du dépôt ni de la bibliothèque extérieure validée n'établit que le premier membre canonique est en ligne ; cette obligation reste explicite ; la fermeture par le champ du premier zéro reste composable dès que le raccord et l'ancre seront disponibles ; aucun théorème terminal ne prend la prémisse pour conclure l'hypothèse de Riemann, aucun théorème incomplet n'entre dans la cible. Six : l'unique build compile, sans aucun trou ni axiome ajouté.

Compléments de l'auteur (2026-10-06, directive en dix points puis complément grammatical), en mots seuls. Le gain d'un rang se décompose exactement en son énergie propre plus deux fois son interaction avec le reste après ce rang ; la marge de la prémisse entre le premier rang et un rang quelconque est la différence des énergies propres moins deux fois la différence des interactions ; l'excès d'énergie propre d'un rang sur le premier vaut deux fois le déficit d'interaction moins la marge. Sous la prémisse, l'excès d'énergie propre est borné par deux fois le déficit d'interaction. Le contrôle requis est identifié exactement : l'énergie propre d'un rang ne dépasse pas celle du premier si et seulement si deux fois le déficit d'interaction ne dépasse pas la marge du gain ; la marge positive est la prémisse elle-même ; la condition antérieure (interaction d'un rang au moins celle du premier) n'est que suffisante. Cette identification n'est pas la démonstration de la borne. Le produit de deux contributions, à toute position radiale, se décompose en un battement lent (différence des hauteurs, différence des phases) et un battement rapide (somme des hauteurs, somme des phases), pondérés par le demi-produit des amplitudes ; le produit scalaire de deux contributions canoniques sur le support fixé est la somme exacte de ces produits aux abscisses, avec les multiplicités. L'interaction d'un rang est, sans aucune convergence, la somme de ses produits avec une queue finie de suivants plus son produit avec le reste après cette queue ; sous la représentation ordonnée, l'interaction est la limite des interactions de queue finie ; pour le canal lissé, elle est la somme de la série convergente. En ligne, à multiplicité égale, la hauteur plus grande donne la contribution pondérée plus petite ; sans égalité des multiplicités, rien n'est conclu ; le rapport des amplitudes entre deux contacts propres est une conséquence des paramètres, pas une contrainte nouvelle. La grammaire compilée est réutilisée telle quelle : deux états pour les premiers au-delà de trois, quatre transitions dont deux maintiens distincts, trois classes, magnitude grammaticale distincte de la multiplicité d'un zéro ; l'écart est six fois la magnitude plus la classe ; la sollicitation logarithmique d'un événement est le logarithme de un plus l'écart rapporté au premier ; la phase traversée à hauteur fixée est la hauteur fois cette sollicitation ; l'amplitude brute avance d'un facteur exponentiel en la position radiale fois la sollicitation, l'amplitude normalisée d'un facteur en la position radiale moins un demi, donc en ligne elle ne bouge pas et la sollicitation n'agit que sur la phase ; sur une fenêtre, les sollicitations télescopent et se décomposent par classes et par maintiens ; les changements d'état alternent et leurs deux canaux diffèrent d'au plus un ; les phases relatives de deux membres avancent, à chaque événement, de la différence des hauteurs fois la sollicitation, et le battement rapide de leur somme fois la sollicitation ; sur une fenêtre paire, la phase relative est minorée par la différence des hauteurs fois le plancher logarithmique de la fenêtre. Tout support formé de premiers est un support admissible de la prémisse ; ces premiers sont choisis par une fonction arbitraire, et le développement du produit scalaire sur un tel support ne démontre pas le transport depuis le support fixé de la prémisse vers chaque abscisse. L'identité d'Abel d'une fenêtre est satisfaite par une constante réelle ; cela ne construit aucune suite de vrais zéros en ligne à hauteur constante, ne reproduit aucun reste arithmétique et n'utilise pas la prémisse ; cela ne justifie donc pas la phrase « les premiers n'exigent aucune progression de hauteur » (revue de l'auteur, 2026-10-06). Le plancher de la phase relative contient l'écart des hauteurs en facteur : il mesure l'effet de cet écart, il ne le produit pas. Ce qui n'est pas dérivé : la chaîne des canaux vers une borne des interactions puis vers une contrainte de hauteur ; une borne démontrée sur les sommes oscillantes des interactions, donc le contrôle requis ; l'énergie propre bornée par celle du premier sur le support ; le passage à la domination en chaque abscisse ; l'ancre ; le raccord du gain maximal à la domination individuelle. Bilan fidèle : progrès de formalisation, raccord analytique ouvert. Mesures (support fixé des seize premiers, puis cent, puis trois cents ; fenêtres de douze, vingt-quatre et trente-six événements, fixées avant calcul) : les identités sont vérifiées à la précision machine ; le premier gain reste maximal dans les deux canaux sur tous les supports ; le déficit d'interaction est négatif aux rangs trois et quatre dans le canal brut sur seize premiers et à tous les rangs dans le canal lissé ; sur trois cents premiers il l'est à tous les rangs dans les deux canaux ; le contrôle requis tient numériquement partout ; les planchers de fenêtre et le verrou des canaux sont satisfaits sur toutes les fenêtres ; l'interaction de queue finie se stabilise avec la longueur de la queue. Une borne observée reste numérique ; rien n'est ajouté comme hypothèse. Lock court, exactement et sans ajout : déduire du premier gain collectif maximal que chaque contribution reste dans le champ du premier zéro. Les obligations (représentation brute du reste, borne des interactions, transport du support fixé vers chaque abscisse, ancre en ligne du premier membre, raccord du gain à la domination) sont tenues dans un tableau de dépendances séparé du lock ; les raccourcir hors du lock ne les supprime pas, cela évite de les confondre avec la cible.

Réduction de la prémisse (auteur, 2026-10-06 : « enlève ou réduit la prémisse, voici déjà la preuve que le premier zéro est le plus fort sur la ligne »), en mots seuls. Les formules de l'auteur sont compilées : parmi les membres en ligne, l'amplitude normalisée est constante le long de l'axe et ne croît pas avec la hauteur ; le premier membre canonique, de hauteur minimale, a donc la plus grande amplitude normalisée parmi les membres en ligne, et tout rang en ligne est dans son champ dès que ce premier membre est en ligne (ancre, non compilée) ; le rapport de l'amplitude d'un membre quelconque à celle du premier en ligne est une puissance de l'abscisse, d'exposant la position radiale moins un demi, fois un coefficient constant que la hauteur atténue ; seule une position radiale différente d'un demi fait varier ce rapport le long de l'axe ; l'enveloppe de la contribution lissée est la même expression atténuée par le facteur de lissage, elle aussi décroissante en hauteur en ligne. Ce que ces formules ne donnent pas, dit par l'auteur lui-même : le gain collectif maximal, parce que l'interaction avec le reste après chaque rang reste à borner ; et la domination d'un membre qui n'est pas en ligne, parce que la croissance du facteur en l'abscisse devrait être exclue depuis le reste et la grammaire. La prémisse est donc réduite, non retirée : elle n'est posée qu'aux rangs dont le membre n'est pas déjà dans le champ du premier ; aux rangs en ligne elle ne demande rien, son antécédent étant faux par théorème ; elle est impliquée par l'ancienne forme à tout rang ; elle ne suppose aucun membre hors du champ et serait vide s'il n'y en avait aucun. Les lectures sous la prémisse (excès d'énergie propre borné par deux fois le déficit d'interaction, amplitude bornée si l'interaction est au moins celle du premier) tiennent aux rangs hors du champ. La fermeture en rangs canoniques est compilée : premier membre en ligne et chaque rang dans son champ donnent l'hypothèse de Riemann, tout zéro étant un rang canonique. Le raccord ouvert devient : de la prémisse réduite, chaque rang est dans le champ du premier ; il est exhibé en hypothèse d'une seule composition et n'est dérivé nulle part. Le lock ne change pas.

Quatre corrections de l'auteur (2026-10-07), en mots seuls. Première : la fermeture compilée reçoit l'ancre en ligne, la prémisse réduite et le raccord lui-même en hypothèse, et c'est le raccord qu'elle applique ; elle est une composition, elle n'est pas « la prémisse seule entraîne l'hypothèse de Riemann ». Deuxième : la réduction affaiblit la prémisse, elle ne la démontre pas ; l'ancienne forme implique la nouvelle ; la domination des enveloppes des membres en ligne et le gain collectif maximal de ces membres sont deux propriétés différentes ; quand tous les rangs sont en ligne, la prémisse réduite ne demande rien sous l'ancre, et ce cas est l'hypothèse de Riemann elle-même ; les expériences où tout est en ligne ne vérifient donc pas les cas où la prémisse réduite s'applique. Troisième : l'amplitude normalisée ne contient pas la multiplicité, la contribution canonique la contient ; la domination du premier parmi les membres en ligne est une domination par unité de multiplicité ; pondérée, elle exige que la multiplicité du rang ne dépasse pas celle du premier, et aucune borne inférieure de l'énergie propre du premier n'est disponible, les phases n'étant pas lues. Quatrième : un support vide rend tous les vecteurs et tous les gains nuls, donc la prémisse automatiquement vraie ; les porteurs de la prémisse exigent désormais un support non vide ; un support non vide ne donne pas, à lui seul, le passage de la mesure finie à toutes les abscisses. L'avancée exploitable sans prémisse nouvelle : sous la prémisse, à un rang où elle s'applique, l'excès d'énergie propre d'une contribution sur celle du premier est au plus deux fois le déficit de son interaction avec le reste ; le gain maximal du premier autorise cette compensation, il ne l'interdit pas. La contradiction cherchée est l'interdiction quantitative de compensation : un excès d'énergie propre strictement positif entraîne un déficit d'interaction strictement trop petit pour le compenser. Compilé : cette interdiction et la borne sous la prémisse sont incompatibles dès qu'il y a excès, elles donnent ensemble que l'énergie propre du rang ne dépasse pas celle du premier, sur le support fixé seulement ; sous la borne, l'interdiction équivaut à cette inégalité d'énergie ; l'interaction est l'interaction complète avec le reste exact après le rang, queue comprise, sur les contributions pondérées réellement utilisées. L'interdiction est une cible de preuve, non démontrée, et n'est l'hypothèse d'aucune fermeture. Reste à faire : conserver les théorèmes en ligne et les fermetures conditionnelles ; préciser le support utilisé et démontrer son lien avec tout l'horizon ; contrôler l'interaction complète ; établir la représentation brute ; transformer la certification connue du premier zéro en terme. Le lock ne change pas.

Cible de captivité et couplage (auteur, 2026-10-07), en mots seuls. La cible centrale est que la reconstruction exacte des écarts arithmétiques oblige toutes les vraies Tours, miroirs compris et sans supposer leur régime, à rester captives du champ fixe du premier zéro en ligne sur tout l'horizon. Compilé : cette captivité équivaut à « chaque vrai zéro est dans le champ du premier » ; sous l'ancre en ligne du premier, le champ est une constante et la captivité entraîne l'hypothèse de Riemann, de sorte que la conservation du régime et la fermeture sont des conséquences disponibles de la captivité et ne la remplacent pas. L'interaction complète d'un rang avec le reste est la somme d'une queue finie et d'un résidu ; la seule borne compilée est la somme des valeurs absolues des interactions de la queue plus le produit des normes du résidu et de la contribution ; aucune borne quantitative des sommes oscillantes n'est démontrée. Quand deux membres ont la même hauteur, l'argument de différence n'avance pas et le produit garde un terme constant ; aucune séparation des hauteurs n'est supposée. La contradiction visée, « hors du champ entraîne un gain strictement supérieur à celui du premier », est écrite comme obligation et composée avec la prémisse réduite : elle donne chaque rang dans le champ ; elle n'est l'hypothèse d'aucune fermeture. Un dépassement du champ par un membre de partie réelle au moins un demi persiste à toute abscisse plus grande et est lu, comme enveloppe et non comme contribution, par toute abscisse du support située au-delà ; un support fixé avant le membre n'en contient pas nécessairement. Couplage en ligne : le rétrécissement des cellules, l'augmentation de la fréquence et l'atténuation de l'enveloppe entre deux hauteurs sont trois lectures du seul rapport des hauteurs ; l'enveloppe s'atténue strictement moins vite que les cellules ne rétrécissent ; dans une fenêtre première, le nombre de cellules parcourues est la sollicitation exacte divisée par pi et le rapport entre deux membres est le rapport des hauteurs, quelle que soit la fenêtre. L'augmentation de la fréquence est acquise dès que la hauteur augmente ; toute accélération de cette augmentation exigerait une preuve supplémentaire et n'est pas observée comme loi. La raréfaction des premiers n'augmente pas automatiquement l'écart logarithmique : il décroît plus souvent qu'il ne croît. Sur une fenêtre où l'argument de différence avance de moins d'un demi-tour, les sommes oscillantes ne s'annulent pas : l'obligation manquante porte sur des plages de fenêtres, non sur chaque fenêtre. Le lock est désormais la phrase de l'auteur : établir que la reconstruction collective impose la captivité de toutes les Tours dans le champ du premier zéro en ligne.

Chaînes de Tours et variations obligatoires de la grammaire (auteur, 2026-10-08), en mots seuls. Sur une chaîne de rangs consécutifs, la somme des gains collectifs est exactement la chute d'énergie du reste entre les deux bouts de la chaîne. L'interaction d'un membre de la chaîne avec le reste après lui se découpe exactement en trois parts : l'interaction avec les autres membres de la chaîne, l'interaction avec les membres extérieurs jusqu'à une troncature, et le résidu après cette troncature ; changer la troncature ne change pas l'interaction complète, seulement sa répartition entre queue finie et résidu. Coût d'un masquage : si le gain d'un rang ne dépasse pas celui du premier, une énergie propre supérieure au gain du premier exige une interaction négative d'au moins la moitié de l'excès, donc un reste après le rang dont la norme est au moins cet excès divisé par deux fois la norme de la contribution ; sous la prémisse réduite, cela vaut à tout rang hors du champ ; c'est une conséquence de la prémisse, non l'obligation d'excès, qui reste non dérivée. Progression de hauteur : la progression cumulée d'une chaîne est la somme de ses pas ; elle est strictement positive si chaque pas l'est ; une progression cumulée positive n'exclut pas un pas nul, la vérification doit porter sur chaque pas. Le rétrécissement cumulé des intervalles se télescope. Variations obligatoires de la grammaire : un maintien d'état impose un écart d'au moins six, un passage de l'état cinq à l'état un un écart d'au moins deux, le passage inverse un écart d'au moins quatre ; la classe de l'écart lit exactement la transition d'état ; la sollicitation d'un événement est au moins le logarithme de un plus le plancher de sa classe rapporté au premier de départ ; pour deux membres, l'écart de leurs avances de phase à l'événement vaut au moins l'écart des hauteurs multiplié par ce plancher logarithmique, et la somme de leurs avances au moins la somme des hauteurs multipliée par ce même plancher. Ces planchers mesurent l'effet obligatoire de la grammaire sur les deux arguments des produits ; ils ne bornent pas les sommes oscillantes. Observations sur les trois cents zéros publiés, toutes les fenêtres consécutives de trois, quatre, dix et douze membres : chaque pas de hauteur est strictement positif ; la progression normalisée par l'échelle moyenne a un minimum de grille, qui n'est pas une séparation minimale ; les cellules d'une Tour sont toutes recouvertes par les contacts de la suivante dès que la hauteur augmente, lecture de hauteur vraie pour toute position radiale ; aucune accélération de la fréquence n'est une loi ; l'interaction d'un membre d'une chaîne est portée surtout par les membres extérieurs et le résidu ; la quantité visée est négative à tous les rangs, mais aucun rang n'est hors du champ dans ces données, l'obligation d'excès n'y est pas testée ; les treize contraintes modulo six sont vérifiées et leurs planchers sont atteints dans chaque classe. Réponse à la question posée : aucune preuve de la suffisance des contraintes conjointes compilées à interdire une sortie du champ masquée n'a été produite, et leur insuffisance n'est pas établie non plus ; le coût d'un masquage est démontré comme condition nécessaire, non comme interdiction : rien d'acquis ne montre que le reste est trop petit pour la compensation requise. Corrections de l'auteur du même jour : les marges minimales du premier étaient surestimées (l'ancien affichage donnait la plus grande marge avec le rang de la plus petite ; l'avantage observé reste positif) ; une annulation médiane proche de un indique peu de compensation dans les données et ne prouve aucune impossibilité universelle, aucun horizon minimal n'en découle ; le recouvrement des cellules n'est pas la captivité, il ne démontre ni l'enfermement de l'amplitude ni la conservation du régime ; les données entièrement en ligne ne testent pas une sortie du champ. Le lock est la phrase de l'auteur fixée après sa revue du même jour (elle remplace celle du matin sur les obligations conjointes) : démontrer que la compensation nécessaire pour sortir du champ du premier est incompatible avec la reconstruction arithmétique complète.

Retrait exact du premier membre (auteur, 2026-10-08, directive en huit points), en mots seuls. Le reste se retire exactement de la contribution du premier : ce qui reste est la somme de tous les suivants, et toute borne du reste se traduit en un intervalle signé pour cette somme, translaté par la contribution du premier et non rétréci ; la somme des deux marges vaut deux fois la borne, et l'intervalle n'est jamais celui que donnerait la valeur absolue du premier. En tronquant la somme à un rang, le résidu de troncature est conservé dans l'intervalle, et sa valeur calculée par différence est distinguée d'une borne démontrée sur la queue infinie : dans le canal lissé, où la représentation est acquise, le reste normalisé est borné par une constante fois la racine de l'abscisse depuis la positivité des poids et l'estimation de Tchebychev, la somme des suivants converge absolument dans l'ordre canonique, le résidu est borné par la queue des valeurs absolues et chaque terme par une quantité explicite grâce à la bande des positions radiales. Le gain du premier ne lit que le reste et la contribution du premier : il est invariant par toute perturbation des autres membres. Sur une chaîne, la somme des interactions est la chute d'énergie du reste moins les énergies propres. Masquer un membre équivaut à une compensation nécessaire au moins égale à la moitié de l'excès de son énergie sur le gain du premier, et cette compensation nécessaire ne dépasse jamais la seule majoration acquise de la compensation possible. L'inégalité exacte encore nécessaire est l'inverse strict pour un membre hors du champ : une majoration des sommes oscillantes et du résidu plus petite que la compensation requise ; rien d'acquis ne la fournit. Mesures : la borne démontrée du canal lissé tient avec une marge énorme et ne contraint rien à l'échelle des données ; les résidus sont lus par différence ; la part calculable de la borne de queue s'arrête aux zéros connus, au-delà aucun théorème de comptage ; un maximum échantillonné sur une grille a été dépassé par un raffinement et n'est pas un supremum ; les chaînes montrent peu de compensation interne ; la grammaire atteint ses planchers sans borner les sommes oscillantes ; aucune hauteur égale dans les données. Perturbations hypothétiques, qui ne sont pas de vrais zéros : aucune ne viole la prémisse sur aucun support, car le membre perturbé a un gain négatif et sa compensation est fournie par le reste dégradé ; la prémisse seule ne lit donc pas une sortie du champ, c'est l'obligation de reconstruction exacte qui la lit, et c'est exactement la jonction visée par le verrou, non démontrée. Aucune nouvelle contrainte démontrée ne réduit le raccord ouvert ; ce tour améliore les mesures, les identités et les bornes de queue. Le lock est la phrase de l'auteur fixée dans la directive du même jour (elle remplace celle de la revue) : prouver que les contraintes arithmétiques et les interactions complètes empêchent toute contribution de dépasser le champ du premier zéro tout en maintenant la reconstruction exacte sur tout l'horizon.

Réduction de la prémisse par le miroir (auteur, 2026-10-08 : avancer sur la réduction de la prémisse ; prouver que les zéros sont liés par leurs contraintes et captifs du premier), en mots seuls. Tout ce qui suit suppose le premier zéro sur la ligne. Un zéro est hors du champ du premier exactement dans deux cas : il est haut, sa partie réelle dépasse un demi, et sa Tour finit par dépasser celle du premier à grande abscisse ; ou son support est plus petit que celui du premier, et sa Tour le dépasse dès l'abscisse un. Ce second cas est une bande fine : il s'agit d'un membre bas, strictement plus haut que le premier, et à moins d'un huitième de l'inverse de la hauteur du premier au-dessus de lui ; à hauteur égale il précéderait le premier dans l'ordre, ce qui est exclu. Tout membre bas au-delà de cette marge est captif du premier par la hauteur seule, quelle que soit sa partie réelle au plus un demi : c'est un théorème. Tout membre haut sort du champ : c'est un théorème. Dans toute paire miroir hors ligne dont la hauteur atteint le support du premier, exactement un membre est captif, le bas, et l'autre sort : les deux membres sont liés par le champ du premier. Le miroir de tout rang de la bande fine est un rang haut. Conséquences sur la prémisse : elle n'a plus à être posée qu'aux rangs hauts ; cette prémisse au miroir est impliquée par la prémisse réduite précédente, qui demandait en plus la bande fine, et elle est impliquée par l'hypothèse de Riemann elle-même, sous laquelle il n'y a aucun rang haut : elle est donc au plus aussi forte que l'hypothèse de Riemann, et vide s'il n'y a aucun rang haut. Aucun rang haut équivaut à l'hypothèse de Riemann ; dire que chaque rang haut est dans le champ, c'est dire qu'il n'y en a aucun ; la fermeture n'a donc besoin que des rangs hauts, les rangs en ligne et les rangs bas au-delà de la marge étant captifs par théorème et la bande fine étant ramenée aux rangs hauts par le miroir. Le raccord ouvert est ainsi réduit et prend sa forme exacte : sous la prémisse au miroir, aucun rang n'est haut, autrement dit un gain collectif au plus égal à celui du premier est contredit, à un rang haut, par la reconstruction exacte. Ce raccord n'est pas dérivé ; les perturbations hypothétiques du tour précédent montrent que l'inégalité de gain seule, sur un support fini, ne le fournit pas : la contradiction doit lire la reconstruction exacte des vrais zéros. Le lock est inchangé.

Tentative de fermeture sans la prémisse (auteur, 2026-10-08 : que reste-t-il pour clore en enlevant la prémisse ; puis : conserver cette erreur comme résultat de la méthode d'essai, rétablir le build vert). La tentative est conservée mot pour mot, mais déplacée hors du code principal, dans une cible d'essai séparée que le code principal n'importe jamais ; le build principal est de nouveau vert. Trois choses sont désormais distinguées. Les théorèmes fermés : la transmission du défaut à toute la suite. Si le reste est entaché d'un défaut, chaque reste partiel, chaque interaction et chaque gain lisent ce défaut au même rang. Si deux membres distincts, un bas puis un haut, sont insérés entre deux vrais membres, les rangs qui précèdent ne changent pas, les rangs qui suivent reculent de deux et lisent le défaut égal à la somme des deux membres insérés ; le gain du premier ne change pas ; les gains des deux membres insérés sont calculés et leur somme télescope ; le résidu de la famille insérée ne tend plus vers zéro mais vers l'opposé du défaut : c'est le défaut de reconstruction qui lit l'insertion, non l'inégalité de gain ; et la condition pour qu'un rang ultérieur reste masqué après l'insertion est exactement que son excès de gain sur le premier soit payé par la projection du défaut sur sa contribution. Ces identités valent pour toute famille et toute position radiale ; elles ne contiennent aucune borne. La tentative rejetée : l'ancre du premier zéro en ligne est accordée, un rang haut est supposé, la contradiction reste ouverte ; cette signature n'est pas une preuve et cet échec n'est pas une impossibilité de la route. Sa forme composée réunit les contraintes acquises pertinentes : succession, dépassement du champ persistant et lu par tout support, horizon exact, pas des contacts le long des premiers, planchers de la grammaire, retrait du premier, reconstruction exacte du reste lissé, interaction complète en série, queue infinie bornée, borne démontrée du reste, et la rigidité de la représentation, qui place tout membre sous l'exposant du reste. Le scénario retenu est celui dont toutes les dépendances sont compilées : rigidité de représentation et contrôle de la queue. Après composition, le premier but réellement restant est, en mots : une borne de croissance du reste lissé, lue sur les premiers, d'exposant strictement inférieur à la position radiale du rang haut supposé. La contrainte acquise la plus proche est l'exposant un, obtenu de la positivité des poids et de Tchebychev ; l'écart précis est d'abaisser cet exposant sous la position radiale du membre haut, et comme le membre haut impose lui-même que l'exposant du reste le dépasse, cet abaissement doit être lu dans les poids premiers exacts, non dans les membres ; rien dans le dépôt n'abaisse l'exposant sous un. Une hypothèse déjà fournie au but, ici l'ancre, n'est pas l'objet qui manque pour le fermer. La certification de l'ancre, traitée à part : hors du code, par comptage certifié avec multiplicité et changement de signe certifié de la fonction réelle sur la ligne, le plus bas zéro de la moitié supérieure est simple et sur la ligne ; cette certification est une dépendance réelle de toute fermeture, elle n'a aucun terme compilé et elle ne remplace pas la contradiction ouverte là où l'ancre est déjà supposée. Le lock est inchangé. Directive en six points et relecture des cinq dernières expériences (auteur, 2026-10-08), en mots seuls. L'ancre est désormais déduite structurellement sous une hypothèse nommée : s'il n'existe qu'un seul membre de la moitié supérieure de hauteur au plus quinze, son miroir, qui garde sa hauteur, est dans la même bande, donc lui est égal ; un membre égal à son miroir est sur la ligne ; aucun membre ne le précède, puisqu'un prédécesseur serait dans la bande ; l'ordre canonique l'identifie au premier membre. Un comptage avec multiplicité égal à un dans cette bande donne cette unicité et la simplicité du membre ; les conventions aux frontières sont explicitées ; les points comptés sont exactement les membres supérieurs de la bande. La valeur du comptage n'est pas vérifiée par le compilateur : il manque le principe de l'argument certifié sur le rectangle et un vérificateur certifié de l'intégrale ; la certification numérique reste externe, jamais un axiome. L'insertion de deux contributions dans une famille complète, les autres étant conservées, est exclue par l'unicité de la limite : la famille insérée reconstruit le reste augmenté du défaut, donc elle ne reconstruit le reste que si le défaut est nul ; une paire miroir hypothétique à multiplicités positives n'est jamais identiquement nulle, même avec des termes de même hauteur, donc son insertion détruit la reconstruction en une abscisse. Correction de l'auteur : cette exclusion lit l'ajout d'une contribution, pas l'écart à la ligne ; deux contributions sur la ligne insérées produisent le même défaut ; elle n'exclut pas un membre hors ligne de la famille authentique ; il faut distinguer le défaut d'insertion de la déformation propre d'une paire. Un complément modifié qui rétablirait le reste doit fournir exactement l'opposé du défaut, aux mêmes canal, normalisation et coordonnées, sur tout l'horizon ; la rigidité spectrale compilée interdit cela à tout complément qui reste une représentation du canal : un point qui n'est pas un zéro porte un poids nul et chaque membre authentique garde sa multiplicité ; cette unicité ne fixe pas la position radiale d'un membre authentique. La borne en racine carrée fois logarithme, conservée par l'auteur, donne l'intervalle signé du reste privé du premier, le moins portant sur la contribution signée avec sa phase ; dans le canal lissé normalisé elle est une hypothèse, non une borne démontrée. Le but analytique reste un contrôle conjoint, uniforme en l'abscisse, de la partie finie et de la queue, d'exposant strictement sous la position radiale du rang haut ; la captivité universelle reste ouverte. Mesures : le défaut d'insertion est commun à la paire miroir et au contrôle sur la ligne ; seule leur différence isole la modification conjointe des phases et des amplitudes ; la compensation collective par le complément est substantielle et reste dans l'analyse ; sur une fenêtre de douze événements la compensation observée est très faible sans qu'aucune impossibilité en découle ; augmenter la troncature ne change pas l'interaction complète ; les repondérations à multiplicités entières essayées modifient bien des multiplicités et réduisent le défaut sur le support d'ajustement, mais le laissent entier hors de ce support, et deux essais ne sont pas une recherche exhaustive. Directive en sept points, en mots seuls. Le contour proposé pour certifier le comptage rencontrait le pôle de zêta en un sur sa frontière ; il est remplacé par un contour admissible pour une fonction entière, sans pôle, dont les zéros hors de l'axe réel sont exactement ceux de zêta, avec les mêmes multiplicités, et dont le bord ne porte aucun zéro hors du segment réel entre zéro et un ; les zéros du rectangle sont exactement les membres supérieurs comptés ; la non-annulation de zêta sur le segment réel ouvert et le principe de l'argument sur le rectangle sont démontrés ; la valeur du comptage est composée à partir des deux énoncés numériques restants, la valeur certifiée de l'intégrale de contour et l'absence de zéro à la hauteur de coupure ; les certificats numériques restent externes. Pour la queue, la demande d'une borne sur la somme des normes de la partie finie et de la queue était plus forte que la cible et effaçait leurs compensations ; la cible porte sur la norme de leur somme. La borne en racine fois logarithme n'est un théorème dans aucun canal du dépôt ; la borne acquise est linéaire et, divisée par la racine, devient une racine ; quand une borne est divisée par la racine, la contribution signée du premier l'est aussi, sans facteur conservé. La captivité universelle est composée sous l'ancre : les rangs en ligne, les rangs bas de support au moins celui du premier et les rangs de la bande fine, par leur miroir, sont fermés par des théorèmes ; il reste un seul énoncé ouvert : sous l'ancre, aucun membre n'a de position radiale strictement supérieure à un demi, c'est-à-dire la contradiction entre une enveloppe qui dépasse le champ et une somme qui reconstruit exactement le reste. À hauteur commune le battement de différence est nul : le terme correspondant est constant et s'accumule, seul le battement de somme compense. La cible de travail porte deux obligations seulement : la certification du comptage de la première bande et la contradiction du dépassement ; les autres tentatives sont consignées dans l'audit. La chaîne unique — ancre, captivité universelle, tous les membres supérieurs en ligne, hypothèse de Riemann, conservation du régime, progression par la hauteur — est composée et conditionnelle à ces deux obligations ; aucun de ses termes n'est terminal, et aucun théorème dépendant d'un énoncé ouvert n'est présenté comme démontré.

Déficit de comptage et saturation en ligne (auteur, 2026-10-09 : « un déficit de comptage nécessairement nul ; empêcher qu'un déficit apparaisse après une région certifiée entièrement en ligne »), en mots seuls. On compte avec multiplicité, dans la moitié supérieure, jusqu'à une hauteur donnée : tous les zéros, les zéros en ligne, les zéros bas, les zéros hauts. Démontré : le total est la somme des trois parts ; la réflexion envoie chaque zéro bas sur un zéro haut de même hauteur et de même multiplicité, et réciproquement, de sorte que les parts basse et haute sont égales ; le total vaut donc le compte en ligne plus deux fois le compte bas ; le déficit, différence entière entre le total et le compte en ligne, est le double du compte bas, jamais négatif, et ne décroît jamais quand la hauteur augmente ; il est nul exactement quand aucun zéro bas n'a encore paru ; un total égal à un à une hauteur donnée impose la saturation à cette hauteur. Fermeture conditionnelle démontrée : si le comptage est saturé à une hauteur et si, au-delà, le compte en ligne progresse au moins autant que le total, alors le déficit ne peut jamais augmenter, reste nul, aucun zéro bas n'existe, aucun zéro haut non plus par le miroir, et l'hypothèse de Riemann suit. Cette composition vérifie que l'obligation choisie suffit ; elle ne la démontre pas ; l'hypothèse de Riemann l'entraîne à son tour, de sorte qu'elle n'est pas plus forte qu'elle. Lecture géométrique démontrée : violer l'inégalité de prolongement, c'est exactement faire apparaître un zéro bas au-dessus de la hauteur saturée ; son miroir est un zéro haut, de même hauteur, dont l'enveloppe dépasse le champ du premier zéro sur l'un de ses contacts authentiques et au-delà ; sous l'ancre, l'inégalité de prolongement équivaut à l'absence de zéro haut : l'ancienne obligation de contradiction du dépassement et la nouvelle obligation de comptage sont la même obligation sous deux formes. Non démontré : l'inégalité de prolongement elle-même, obligation de la cible de travail, prise depuis la saturation certifiée à quinze, qui est composée du comptage égal à un et de l'ancre et reste conditionnelle aux deux lemmes numériques. Le compte en ligne compte des zéros avec leur multiplicité ; ce n'est pas un nombre de changements de signe. Aucune loi d'espacement, aucune borne en racine et logarithme, aucune conservation du régime n'est introduite.

Conservation du régime en ligne au passage authentique (auteur, 2026-10-09 : « réoriente immédiatement le travail vers la conservation du régime en ligne au passage authentique ; depuis un membre en ligne engagé, démontrer que le prochain membre conserve sa partie réelle, sans supposer ce prochain membre en ligne »), en mots seuls. Le déficit de comptage reste un résultat de contrôle et une fermeture disponible ; il ne remplace plus cette cible. Les insertions synthétiques ne constituent pas la preuve recherchée : le passage étudié est celui entre les vrais membres. Démontré, en une expression commune : le membre engagé coïncide avec son miroir, avec la même hauteur et la même multiplicité, et cette coïncidence est exactement la position sur la ligne ; les contacts authentiques de l'arrivée sont donnés par sa phase et sa hauteur, et l'intervalle logarithmique entre deux contacts consécutifs ne dépend que de la hauteur ; l'enveloppe normalisée d'un membre est donnée par sa position radiale et son module, et, en ligne, elle s'écrit aussi par le seul intervalle des contacts ; le rapport des enveloppes de l'arrivée et du départ en ligne est une puissance de l'abscisse d'exposant la profondeur radiale de l'arrivée, fois le rapport des modules ; sur le passage qui monte depuis un membre en ligne, l'arrivée est au plus sur la ligne, le rang avance d'un, le premier partagé est le premier attendu, l'intervalle se réduit, la phase est dans sa fenêtre, le facteur radial vaut au moins un, chaque contact est le contact de ligne multiplié par ce facteur, la liaison première tient, et le facteur vaut un exactement quand l'arrivée est en ligne ; chaque événement premier sollicite chaque Tour par le logarithme du rapport des deux premiers, la phase avance de la hauteur fois cette sollicitation, l'enveloppe est multipliée par l'exponentielle de la profondeur radiale fois cette sollicitation, l'écart ordinaire a son plancher par classe et les classes alternent ; la reconstruction exacte du canal lissé sur tout support, la décomposition du gain en énergie propre et interaction, l'interaction complète par queue finie et résidu conservé, et la reconstruction du canal arithmétique avec le comptage pondéré des puissances de premiers sont instanciées. Démontré aussi : depuis le membre le plus bas, en ligne, le passage sortant monte ; l'ancre en ligne et la loi de conservation radiale sur tout passage qui monte depuis un membre en ligne entraînent, par récurrence sur l'énumération canonique, que tout membre est en ligne et que tout passage monte, donc l'hypothèse de Riemann ; cette loi est impliquée par l'hypothèse de Riemann, elle n'est pas plus forte qu'elle ; la forme de l'auteur, depuis un membre engagé atteint en montant, en découle parce que le passage qui quitte un tel membre monte. Non démontré : la loi elle-même. Sous sa négation, l'arrivée est basse, sa grille est translatée, le passage qui la quitte garde la hauteur, tous les contacts du membre suivant sont en deçà, ce membre suivant est au plus sur la ligne ou le miroir exact, et la reprise de la montée équivaut au facteur radial égal à un ; rien de cela n'est contredit, parce que chaque identité composée vaut pour toute position radiale de l'arrivée. Ce qui manque exactement : une inégalité ou une identité démontrée, lue sur les poids premiers et la reconstruction exacte, qui impose le couplage en ligne au membre atteint, et qui soit fausse quand un départ en ligne est suivi de deux membres consécutifs à la même hauteur dont le premier est bas. Second message de l'auteur, le même jour : le premier membre canonique est conservé explicitement dans chaque raccord étudié. Démontré, sous l'ancre : aucun membre en dessous de lui, sa hauteur est au plus celle du départ et de l'arrivée ; son enveloppe normalisée est fixée, constante sur tout l'horizon ; elle domine l'enveloppe du départ en ligne, par unité de multiplicité ; le rapport de l'enveloppe de l'arrivée à la sienne est une puissance de l'abscisse d'exposant la profondeur radiale de l'arrivée, fois le rapport des modules ; sa contribution signée intervient dans la reconstruction exacte et, après son retrait, toutes les suivantes restituent ensemble le reste résiduel, en toute abscisse et sur tout support, le reste après lui étant le reste moins sa contribution et son gain étant fixé par le reste et par lui seul ; ses contacts et sa phase sont conservés dans le produit avec chaque membre, son interaction avec le complément infini est une série convergente, et chaque événement premier écarte sa phase de celle de l'arrivée d'au moins un plancher proportionnel à l'écart des hauteurs. Démontré aussi : la captivité universelle dans le champ du premier est une conséquence de « tout membre en ligne », jamais une hypothèse, et, ainsi dérivée de la conservation, elle sert à fermer l'hypothèse de Riemann. Aucune conservation, aucun enroulement entier, aucune captivité n'est posée en hypothèse ; aucune caractérisation n'est prise pour une dérivation.

Le premier changement de régime (troisième message de l'auteur, 2026-10-09 : il y a forcément un lien entre deux zéros en ligne ; le prochain zéro ne peut pas quitter la ligne à cause de son miroir, qui serait le premier à être considéré ; dans aucun cas le régime engagé ne change ; inutile d'insérer un membre hors ligne ; prolonger ces raisonnements). Le côté haut d'un membre atteint par un passage qui monte est exclu : son miroir, bas et à la même hauteur, le précéderait dans l'ordre des membres. C'est établi à tout passage qui monte et, depuis l'ancre, au deuxième membre canonique. Il reste le côté bas. Prolongement établi : s'il existait un membre hors ligne, il existerait un premier rang où le régime change ; ce membre serait bas ; tous les membres de rang inférieur seraient en ligne ; le passage qui l'atteint partirait d'un membre en ligne et monterait ; le déficit de comptage serait nul et le comptage total égal au comptage en ligne strictement sous sa hauteur ; au moins un membre bas serait compté à sa hauteur, son miroir le suivant à la même hauteur. L'hypothèse de Riemann équivaut à l'absence d'un premier changement de régime. Fermeture renforcée : l'ancre en ligne et la loi de conservation restreinte aux passages dont tout l'historique est en ligne suffisent ; la loi n'a donc à être démontrée qu'au premier changement de régime, avec tout l'historique en ligne en hypothèse. Le premier changement de régime est obtenu par l'absurde sur les vrais membres ; aucune insertion n'est accordée. Le texte collé par l'auteur (comptage total égal au comptage en ligne plus deux fois le nombre de membres bas, croissance de ce nombre, saturation observée sur la région explorée) correspond au module du déficit de comptage ; la phrase selon laquelle un membre hors ligne ajouterait deux au-delà du comptage total est circulaire, le comptage total comptant déjà tous les membres ; la saturation observée est un certificat numérique fini, pas un théorème pour toute hauteur. Rien de ce texte n'est présenté comme dérivation. La cible de travail reçoit l'historique en ligne en hypothèse ; son but est inchangé en nature.


La cible de la transmission, rétablie (auteur, 2026-10-11). La cible est la conservation du régime depuis un historique entièrement en ligne : le membre atteint garde la partie réelle du membre qui l'a engagé. Dans le cas bas, ce qui reste à construire est une contradiction tirée des obligations du passage authentique et de la reconstruction exacte. Une majoration du reste sur toutes les abscisses, ou une bande sans zéro au-dessus de l'historique, la donnerait ; ce sont des voies suffisantes, gardées à disposition, qui ne sont ni dérivées ni imposées comme dernier pas, car elles portent sur la croissance du reste tout entier. Sont désormais démontrés, sur les vrais membres : sur toute fenêtre de membres consécutifs, chaque membre garde son occurrence, qui est le premier de même rang ; les occurrences se succèdent dans l'ordre des membres ; deux fenêtres adjacentes se raccordent sans omission ni double compte ; une fibre de hauteur est d'un seul tenant dans l'ordre des membres, finie, complétable aux bords d'une fenêtre, et contient le miroir de chacun de ses membres ; tout groupe fini de membres laisse un complément qui reconstruit exactement le reste moins la somme signée du groupe. La matrice des incréments, contribution par contribution et intervalle par intervalle, se lit par lignes ou par colonnes avec le même total ; les colonnes sont les incréments du reste ; la compensation s'y mesure par l'inégalité triangulaire. Chaque contribution s'écrit comme une amplitude et une phase ; son incrément se partage en une part de phase et une part de variation d'enveloppe ; en ligne, et seulement sous cette condition, la part d'enveloppe disparaît après normalisation. L'incrément de l'intégrale logarithmique entre deux premiers est encadré par l'écart divisé par le logarithme de chacun d'eux. Toutes ces obligations sont vraies quelle que soit la position radiale du membre atteint : aucune ne contredit encore la première rupture. L'expérience E199 mesure ces objets sur trois cents membres numériques ; ce sont des observations.

Compensation sur une fenêtre grammaticale authentique (auteur, 2026-10-11). Sur une fenêtre d'événements premiers consécutifs, une même lecture finie pondère chaque premier par son écart et tourne chaque abscisse de la rotation propre à la hauteur d'arrivée. Le retrait de l'historique moins le groupe d'arrivée est exactement le complément lu par cette même lecture : les deux bornes cherchées portent donc sur un seul nombre et doivent venir de deux écritures différentes. Le retrait s'écrit directement avec les poids premiers exacts filtrés par la lecture. Le groupe d'arrivée s'écrit sur sa fibre complète, chaque membre avec son coefficient propre et sa multiplicité ; tous ses membres ont la hauteur d'arrivée, ils partagent la vitesse de rotation mais non la phase de leurs coefficients. Dans la moitié supérieure de la fibre, la rotation retirée, aucun membre n'en annule un autre : leur somme est au moins celle du membre atteint ; c'est démontré. La moitié conjuguée tourne au double de la hauteur sur les premiers de la fenêtre, et n'est pas contrôlée. La composition est démontrée ; avec la seule marge triangulaire du complément elle demande que la masse des membres suivants soit inférieure au coefficient du membre atteint, ce que cette marge ne fournit pas. Il manque une majoration du complément filtré qui tienne compte de sa somme oscillante, et une majoration de la moitié conjuguée et du retrait filtré.

Ordre correctif sur la fenêtre grammaticale (auteur, 2026-10-11). La séparation proposée précédemment n'est qu'une condition suffisante ; elle n'est pas démontrée et ne constitue pas une solution. La fenêtre est désormais rattachée au passage : elle commence au premier partagé entre le zéro engagé et le membre atteint, et ses écarts portent leur magnitude, leur classe, leur plancher et leur alternance. Le miroir du membre atteint est vérifié dans la fibre : même hauteur, partie réelle complémentaire, même multiplicité, coefficient propre. Sous la lecture accordée, le membre atteint et son miroir minorent ensemble la partie supérieure, sans annulation. Trois objets restent distincts : la partie supérieure, le groupe complet (la partie supérieure diminuée du contrôle de la moitié conjuguée) et le retrait moins le groupe (le complément). Le complément et l'historique fini sont majorés en gardant l'oscillation de chaque profil sur la fenêtre ; cette majoration ne dépasse jamais la marge triangulaire, qui en devient un cas particulier. Tout cela est démontré. Ce qui manque est une seule inégalité. La lecture filtrée des premiers, diminuée du fond, ajoutée à l'historique, au complément et à la moitié conjuguée filtrés, doit rester sous le signal du membre atteint et de son miroir, pour au moins une longueur de fenêtre. Ce manque est l'échec de cette tentative ; il ne dit pas qu'aucune autre composition n'aboutit.

Comparaison signée (auteur, 2026-10-11). La réduction précédente mesurait séparément la taille de la lecture des premiers, celle de l'historique et celle de la moitié conjuguée ; elle perdait les compensations entre elles. Ces trois contributions sont désormais gardées avec leur signe : la lecture filtrée des premiers, moins le fond, moins l'historique fini, moins la moitié conjuguée, plus la seule borne du complément (qui garde les oscillations de chaque terme), doit rester sous le signal de l'arrivée et de son miroir. La composition est démontrée et appliquée dans le cas de rupture ; elle est au plus aussi exigeante que la précédente. Le test a une réponse démontrée : par l'identité exacte entre retrait, groupe et complément, le côté gauche vaut toujours la partie supérieure plus une quantité positive, donc il n'est jamais sous le signal de la paire. La comparaison, comme la séparation en normes qui l'implique, n'est pas une estimation à vérifier : elle réécrit l'absurde. Une fenêtre seule ne peut pas fermer la transmission.

Réalignement (auteur, 2026-10-12). La cible est la conservation du régime engagé, non une compensation imposée. Les comparaisons de fenêtre ne sont plus le dernier pas de la transmission ; elles restent des énoncés démontrés et disponibles. Sous l'hypothèse d'un premier changement de régime, le compilateur demande directement une contradiction. Les conséquences de ce changement sont réunies : le miroir du membre atteint existe, distinct, à la même hauteur, sans qu'il soit supposé immédiatement suivant ; la grille d'arrivée est translatée ; le rayon normalisé n'est plus constant ; le passage qui quitte le membre atteint garde la hauteur. Les obligations du passage sont réunies dans leur portée : succession des rangs, premier partagé, contacts authentiques, cellules, grammaire, reconstruction exacte. Toutes valent pour une arrivée basse comme pour une arrivée en ligne ; aucune ne contredit encore une conséquence de la rupture. Verrou : depuis un historique sur la ligne critique, établir que les obligations du prochain passage maintiennent l'annulation du miroir, de sorte que la progression se poursuive uniquement par la hauteur.

Contrôle (auteur, 2026-10-12). Si l'on accorde, à titre de test, que la grille du membre atteint n'est pas translatée, la rupture supposée est contredite aussitôt : cette absence de translation suffit à fermer la transmission. Elle n'est pas encore démontrée ; c'est désormais l'obligation exacte, à tirer des seules données du passage (départ en ligne, passage qui monte, historique en ligne). Les données acquises n'enferment le facteur de translation que dans une fenêtre étroite au-dessus de un.

Composition de comptage (auteur, 2026-10-12). L'historique en ligne ne laisse aucun membre bas jusqu'à la hauteur du départ. Si, de la hauteur du départ à celle de l'arrivée, le comptage total des zéros avec multiplicités augmente de moins de deux, aucun membre bas ne peut apparaître ; le côté droit est exclu par réflexion ; l'arrivée est en ligne et sa grille n'est pas translatée. Cette composition est démontrée. Ce qui reste est le pas de comptage lui-même : par consécutivité, il compte exactement la fibre d'arrivée (tous les points de cette hauteur, avec leurs multiplicités) ; il vaut moins de deux si et seulement si cette fibre est un point simple. Sous la rupture, l'arrivée et son miroir y font deux points. La consécutivité dans l'ordre des membres ne borne donc pas ce comptage ; il doit venir d'une donnée indépendante de la position radiale de l'arrivée.

Trois hypothèses de travail sur la fibre d'arrivée (auteur, 2026-10-12), portée établie. Première : l'unicité de la grille d'arrivée par les contacts. Le facteur de translation est une fonction explicite de la position radiale et de la hauteur ; toute position radiale sous ou sur la ligne, à la hauteur d'arrivée, satisfait la fenêtre de phase, l'encadrement du facteur et l'écriture des contacts comme grille de ligne translatée ; deux grilles décalées de même hauteur ont le même pas, se correspondent par une translation rigide, sont chacune admissibles, et ne coïncident que si les positions radiales sont égales. Deux grilles admissibles existent donc exactement quand il y a rupture ; la grille d'arrivée est la grille de ligne si et seulement si l'arrivée est en ligne ; l'inversion des contacts restitue la position radiale à partir du facteur. Cette hypothèse est le but lui-même, non une étape qui le précède : les contacts calculent la translation, ils ne l'interdisent pas. Deuxième : le transport du comptage des événements premiers vers le comptage des zéros. L'avancée d'un rang et le premier partagé valent aussi sur le passage de même hauteur qui part d'un membre bas : une unité d'événement premier correspond à un membre, non à une hauteur ; la fibre d'un membre bas a au moins deux points. Troisième : la multiplicité. Le pas de comptage est sous deux exactement quand l'arrivée est en ligne, seule à sa hauteur et simple ; un zéro double en ligne conserve le régime et viole ce pas. Le sous-but choisi est donc strictement plus fort que la conservation du régime ; la simplicité qu'il exige n'est pas nécessaire à l'hypothèse de Riemann. Mesures (E200) : sur trois cents passages, sept grilles satisfont les mêmes obligations sans aucune violation ; sur cinq mille, seul l'emboîtement distingue cinq grilles très décalées à des passages très courts ; le comptage par hauteur et le rang avancent ensemble sur les zéros réels, et une paire insérée, comme le monde témoin, fait avancer les deux de deux par hauteur.

Comparaison directe de l'arrivée au premier zéro par les contacts (auteur, 2026-10-12), portée établie, sans aucune notion de marge ou de place disponible. Le logarithme du rapport entre un contact de l'arrivée et le contact de même indice du premier zéro se sépare exactement en trois termes : le déplacement radial de l'arrivée, qui est positif ou nul et nul exactement quand l'arrivée est en ligne ; le changement des contacts produit par la hauteur d'arrivée, qui ne dépend pas de la position radiale ; et les contacts fixes du premier zéro. La même écriture vaut vers le membre de départ. Le terme de hauteur décroît strictement avec l'indice et il est strictement négatif à tout indice positif dès que la hauteur dépasse celle du premier zéro. La comparaison des contacts se lit donc exactement : le contact de l'arrivée est en deçà de celui du premier zéro si et seulement si le déplacement radial est strictement plus petit que l'opposé du terme de hauteur. Une comparaison de contacts ne peut forcer le facteur à être au plus un qu'à un indice où le terme de hauteur est positif ou nul ; ces indices sont tous négatifs, leurs contacts sont strictement sous un, où aucun nombre premier n'est lu, et l'arrivée en ligne elle-même n'y satisfait pas la comparaison stricte : cette comparaison n'est pas une obligation du régime conservé. À tout indice positif, la comparaison borne le déplacement radial par une quantité strictement positive ; la fenêtre du facteur entraîne seule l'ordre des contacts dès que l'écart de hauteur la dépasse, et une grille strictement translatée à la hauteur d'arrivée est emboîtée dans la grille du premier zéro à tout indice positif ou nul, et dans tout membre en ligne plus bas à tout indice au moins un. Verdict : l'identité calcule le déplacement radial, elle ne le borne jamais par zéro ; aucune borne supérieure du facteur égale à un ne vient des contacts. Mesures (E201) : identité vérifiée à la précision machine sur trois cents passages et sept grilles ; la racine du terme de hauteur est toujours strictement entre moins un demi et zéro, vers le premier zéro comme vers le départ ; la plus contraignante des comparaisons compilées laisse un déplacement radial strictement positif sur les cinq mille arrivées, le plus souvent la fenêtre elle-même, et sur presque toutes elle dépasse le plus grand déplacement réalisable, de sorte que toute position radiale sous la ligne reste admise ; les sept grilles et le monde témoin, bas comme haut, sont emboîtés dans le premier zéro à tout indice positif ou nul.


Restitution arithmétique des cellules et des passages (auteur, 2026-10-12), campagne de onze tests. Ce qui est établi : la charge des événements premiers d'une cellule ne dépend que de ses bords et ne lit aucun zéro ; quand la grille de l'arrivée se translate, seuls les événements des deux portions de bord changent de cellule, d'un rang au plus, et seulement au-delà d'un seuil exact ; sur toute famille finie d'événements, une translation assez petite ne change rien : l'appartenance aux cellules est un détecteur à seuil. Le raccord au premier partagé n'omet ni ne compte deux fois aucun événement, et deux passages consécutifs se recouvrent exactement sur une cellule du membre intermédiaire. Les quatre transitions, leurs charges, leurs grandeurs et leurs avances de phase ne dépendent que des premiers et de la hauteur. Une paire miroir se déforme continûment depuis un point double sur la ligne, mais s'écarte d'un point simple d'une quantité qui ne tend pas vers zéro : c'est le saut que lit le comptage. Ce qui n'est pas établi : aucune de ces lectures ne fixe la position radiale de l'arrivée ; le comptage sous deux n'est plus le dernier pas imposé, car il exige aussi la simplicité ; la cible reste que le facteur radial de l'arrivée vaut un.

Défaut de comptage sur la ligne (auteur, 2026-10-12), étude directe de zêta. Ce qui est établi : entre deux hauteurs, la part du comptage supplémentaire qui n'est pas portée par la ligne est toujours paire et jamais négative ; elle vaut au moins deux dès qu'un membre bas apparaît au-dessus d'un historique sur la ligne ; si elle est nulle, l'arrivée est sur la ligne et le facteur radial vaut un. Les rectangles certifiés aux trois premières coupures obtiennent le comptage total par le principe de l'argument, mais ne lisent pas la ligne : ils la confrontent par la seule parité de la réflexion. Des rectangles à droite de la ligne, aussi proches qu'on veut d'elle et sans enroulement, annuleraient cette part ; des changements de signe de la fonction réelle de la hauteur en nombre suffisant aussi, mais il n'y en a aucun à l'intérieur d'un passage : la lecture se fait au seul point d'arrivée. Ce qui reste ouvert : que la multiplicité totale à la hauteur d'arrivée soit celle du seul point de la ligne à cette hauteur.

Rigidité des transitions au raccord (auteur, 2026-10-12). Ce qui est établi, pour tout membre, sur la ligne ou non : trois premiers consécutifs partagent leur premier intermédiaire, dont l'état est unique, de sorte que la transition d'arrivée d'un événement est la transition de départ du suivant ; les quatre transitions n'admettent chacune que deux successeurs ; les changements d'état alternent une fois les maintiens retirés ; la classe ne fixe pas la grandeur de l'écart ; sur un passage, l'événement de l'arrivée est exactement l'événement suivant, et leur extrémité commune est le premier partagé. Lue par la Tour d'arrivée, chaque extrémité reste dans sa cellule de ligne ou passe dans la précédente ; la transition lue est celle des premiers. Ce qui n'est pas établi : qu'une rupture radiale empêche cette restitution ; elle ne l'empêche pas dans la lecture authentique, qui conserve les mêmes extrémités. La rigidité est un fait des premiers ; son transport vers la conservation du régime reste à trouver.

Champ de comptage autour de l'intégrale logarithmique (auteur, 2026-10-12). Représentation corrigée : chaque zéro apporte au comptage une correction qui oscille autour du fond ; tracée sur l'abscisse positive avec la valeur de comptage en ordonnée, elle coupe le fond en des contacts successifs, un par étage, et atteint ses extrêmes à des abscisses qui ne dépendent que de la hauteur. Le cercle centré à l'origine reste exact pour le terme complexe isolé et normalisé, mais il ne montre ni le fond ni la reconstruction collective. Ce qui est établi : deux extrêmes successifs donnent la hauteur ; l'écart entre un extrême et le contact de Tour voisin donne la partie réelle et le facteur radial ; un membre bas aurait cet écart strictement plus petit que celui de la ligne. Ces lectures caractérisent, elles ne fixent rien. Observé sur les trois premiers zéros : la première correction domine, les deux suivantes restent dans son enveloppe ; à chaque extrême d'un zéro, le reste laissé par les premiers et les zéros précédents porte en majorité le même signe que sa correction, mais le complément de tous les autres zéros est du même ordre ; ajusté sur ce reste, le profil retrouve la hauteur du zéro suivant et une partie réelle d'un demi.

Registre d'un écart de premiers (auteur, 2026-10-12). Entre deux premiers consécutifs, la variation que chaque zéro apporte au comptage est bornée par une enveloppe fixée par la longueur de l'écart et sa classe ; un zéro sous la ligne a une enveloppe au plus égale à celle de la ligne. Un zéro utilise toute son enveloppe sur l'écart où il coupe le fond, et presque rien sur l'écart où il atteint un extrême. Le reste de l'écart se partage exactement entre ce que les zéros précédents ont déjà comblé, la part du zéro suivant et la part de tous les zéros au-dessus. Mesuré : sur un écart, la part des zéros au-dessus est de l'ordre de la racine de l'abscisse fois celle du zéro suivant, et le reste non comblé ne porte pas le signe du zéro suivant ; une rupture hypothétique ne dépasse la part des zéros au-dessus que sur une petite fraction des écarts. Ce registre est une identité et une borne individuelle ; il ne fixe pas la position radiale du zéro suivant.

Géométrie des contacts dans le champ collectif (2026-10-13). Un déplacement de la position radiale d'un zéro translate tous ses contacts d'une même quantité, très petite : elle est encadrée par l'écart à la ligne divisé par le carré de la hauteur (démontré). La position radiale se lit donc sur les contacts d'un signal isolé, exactement à précision infinie, mais une lecture à précision finie ne sépare un zéro bas de la ligne que si son erreur est plus petite que ce petit déplacement, et devient aveugle au-delà (démontré). Les obligations de contact que le contexte fournit sur l'arrivée, fenêtre de phase, facteur de translation, décalage et enveloppe, sont toutes satisfaites par n'importe quelle position radiale sous la ligne : elles ne fixent pas la position (démontré, contre-modèle). Mesuré dans le champ de comptage collectif : un contact individuel n'y est retrouvé guère plus souvent qu'au hasard ; les hauteurs se restituent à l'aveugle, la position radiale seulement à la précision que le complément permet ; une paire hors ligne substituée au premier zéro reproduit exactement le comptage avec un complément redéfini que seule une borne de même nature que l'hypothèse de Riemann exclurait. La géométrie des contacts ne fournit donc pas de contrainte indépendante sur la position radiale du zéro suivant.

Induction du régime ON, parité des fibres et premier niveau de défaut (2026-10-13). À toute hauteur, les zéros situés exactement à cette hauteur se partagent en membres sur la ligne, membres bas et membres hauts ; la réflexion échange bas et hauts en conservant hauteur et multiplicité, de sorte que la part hors ligne d'une fibre est toujours paire (démontré). Le défaut de comptage est nul jusqu'à une hauteur exactement quand tout membre jusqu'à cette hauteur est sur la ligne, et son accroissement entre deux hauteurs est nul exactement quand aucun membre hors ligne n'apparaît entre elles (démontré, caractérisations). Au premier rang où le régime changerait, le défaut, nul en dessous, vaut au moins deux à cette hauteur, portée par le membre bas et son miroir distinct (démontré). Sur un passage qui monte dont tout l'historique est sur la ligne, dire que l'arrivée est sur la ligne, que le défaut ne croît pas, ou que l'arrivée coïncide avec son miroir, est une seule et même chose (démontré) : les trois formulations concurrentes ont le même résidu. Tout invariant des passages qui suffit à l'arrivée sur la ligne et qui vaut sur chaque passage d'historique sur la ligne ferme l'hypothèse avec l'ancre (démontré, schéma) ; mais l'invariant « le défaut ne croît pas », quantifié sur ces passages, est équivalent à l'hypothèse elle-même, et le pas de comptage inférieur à deux est plus fort qu'elle (il exige la simplicité). Mesuré : sur les trois cents premiers passages le comptage total et le comptage par les signes de la fonction de Hardy avancent ensemble d'une unité, la variation de phase reste entre zéro et deux demi-tours, l'argument reste sous un ; aucune de ces régularités n'est une loi, et un premier défaut hypothétique n'est exclu que par ces observations, par aucun énoncé démontré. La propriété manquante reste une lecture de la ligne indépendante de la position des zéros.

Audit du transport du régime sur la ligne (2026-10-13, mission E212–E217). Plusieurs zéros peuvent partager une même hauteur, en particulier un membre sur la ligne et une paire de membres miroirs hors ligne : rien dans les définitions ne l'interdit. L'ordre des membres (hauteur d'abord, partie réelle ensuite) range une telle fibre, il ne l'exclut pas ; le passage qui monte jusqu'à une hauteur aboutit toujours au membre de partie réelle la plus petite de cette hauteur, donc au membre bas d'une fibre mixte (démontré). Il en résulte, sans rien supposer de l'historique, que l'arrivée est sur la ligne exactement quand toute sa hauteur est sur la ligne et exactement quand aucun membre hors ligne n'apparaît depuis le départ (démontré) ; en revanche un membre sur la ligne qui n'est pas une arrivée ne dit rien de sa hauteur. Cette exclusion tient au classement, convention fidèle, et non à une propriété de zêta. Comparaison des Tours : sur les abscisses supérieures à un, et donc sur tous les nombres premiers, rester sous la Tour d'un zéro sur la ligne est une simple condition de hauteur que toute arrivée basse satisfait ; c'est sur les abscisses entre zéro et un, qui ne contiennent aucun nombre premier, que se loge toute la conservation de la partie réelle (démontré). Les deux égalités d'énergie que les anciennes tentatives laissaient ouvertes aux raccords sont fausses sur tout passage qui monte, même entre deux zéros sur la ligne : elles comparaient des termes isolés de modules différents ; leur forme correcte, l'égalité des rapports en deux raccords, demande exactement la même conservation que l'enroulement entier (démontré). Sur la fenêtre de quatre membres, toutes les identités exactes tiennent pour toute profondeur, le collectif n'étant que la somme des lectures individuelles. Toutes les pistes historiques se rabattent ainsi sur une seule proposition locale, l'absence de zéro sous la ligne à la hauteur d'arrivée ; aucune propriété indépendante n'a été trouvée.

Signature d'un zéro sur tous les écarts de premiers (2026-10-13, mission E218–E223). Chaque zéro laisse sur chaque écart entre deux premiers consécutifs une variation exacte de sa Tour, qui est l'intégrale de son profil sur l'écart. Cette variation n'est jamais nulle, quelle que soit la partie réelle : aucun écart ne refuse aucune signature. Mise bout à bout sur tous les écarts, elle ne retient que les deux extrémités : la lecture de toute la suite des écarts ne contient rien de plus que la Tour elle-même. Déplacer la partie réelle à hauteur fixée ne fait que repondérer chaque écart par une puissance de l'abscisse. Les Tours sur la ligne sont strictement ordonnées par la hauteur en tout point ; un membre hypothétique au-dessus de la ligne dépasse toute Tour sur la ligne au-delà d'un seuil exact, son miroir au-dessous de la ligne la dépasse en deçà d'un seuil plus petit que un, là où il n'y a aucun premier. Contre la Tour sur la ligne qui le précède immédiatement, le seuil tend vers un : seule la première Tour offre un horizon long, qui ne croît que comme le logarithme de la hauteur divisé par le décalage. Dans le canal de comptage, l'incrément du reste sur un écart n'est porté par aucun zéro isolé : il est collectif. Une paire hors ligne hypothétique laisse un défaut que des coefficients libres compensent en partie sur une fenêtre, sans que cette compensation se transporte hors de la fenêtre ; dans la famille authentique, une insertion est exclue par l'unicité de la limite, ce qui n'exclut pas un membre hors ligne de zêta elle-même. L'extraction des fréquences par transformée en logarithme de l'abscisse identifie hauteur et partie réelle de chaque composante sans les borner. Aucune propriété globale des écarts ne contraint la partie réelle ; interdire le croisement pour tout membre est équivalent à l'hypothèse de Riemann. (§19.24, auteur 2026-11-01 : E219 exact et compilé reste un appui ; E220, corrélations, RMS et médianes : journal, non appui.)

Modèle harmonique des Tours et structure de ξ (2026-10-13, mission E224–E230). Lue le long de l'axe des abscisses en échelle logarithmique, la Tour d'un zéro ramenée à l'échelle de la ligne est une oscillation élémentaire : sa fréquence est la hauteur, son enveloppe est fixée par l'écart à la ligne ; sur la ligne l'oscillation est pure, au-dessus elle s'amplifie, en dessous elle s'amortit (démontré, pour toute position). Une énergie adaptée détecte exactement cet écart : elle reste constante si et seulement si le zéro est sur la ligne, et l'oscillation reste bornée dans les deux directions exactement dans ce cas (démontré) ; appliquées au zéro atteint, ces deux propriétés SONT la conservation recherchée, elles ne la prouvent pas. Le signal arithmétique ne voit jamais un membre amplifié seul : il voit toujours la paire miroir, dont l'enveloppe est un cosinus hyperbolique, symétrique dans l'écart (mesuré). La structure de la fonction complétée — symétrie par rapport à la ligne, réalité sur la ligne, noyau de Fourier positif et pair, symétrie des opérateurs associés — ne suffit pas à interdire ces oscillations : la fonction formée du produit de deux copies décalées de part et d'autre de la ligne possède toute cette structure et n'a que des zéros hors de la ligne (démontré pour l'équation fonctionnelle, mesuré pour le noyau). Les formes connues d'une « force de rappel » vers la ligne (positivité de la dérivée logarithmique à droite de la ligne, croissance du module en s'éloignant de la ligne, réalité des zéros des polynômes de Jensen) sont toutes équivalentes à l'hypothèse elle-même. Aucun opérateur autoadjoint défini sans les zéros n'est connu : le théorème spectral n'a pas d'objet. Les six tentatives de fermeture laissent exactement le but du compilateur.

Fenêtres finies, battements et grammaire des écarts (2026-10-13, mission E231–E238). Sur la fenêtre de quatre membres et deux écarts de premiers consécutifs, la paire hypothétique hors ligne déforme la contribution de chaque écart par rapport à deux membres sur la ligne à la même hauteur. Cette déformation est symétrique dans l'écart à la ligne, et son signe sur chaque morceau d'écart est fixé par la phase de l'oscillation, c'est-à-dire par la hauteur, jamais par l'écart lui-même (démontré). La charge de la fenêtre n'est jamais neutre hors de la ligne, car trois premiers distincts ne vérifient jamais q² = pr (démontré). Mais la grammaire et les corrections exactes de comptage, qui lisent très précisément la seconde différence des logarithmes des trois premiers, ne contiennent aucune information sur la profondeur : elles sont les mêmes pour toute profondeur (mesuré). Les six battements de la fenêtre ne dépendent de la profondeur que par des quantités symétriques ; le battement entre les deux membres miroirs a toujours l'exposant un (démontré). Le déterminant formé par les deux écarts identifie la profondeur à partir des contributions séparées des deux membres, alors que la formule explicite ne voit que leur somme : identifier n'est pas exclure. L'ensemble des compléments permis par les seules bornes démontrées contient largement celui qu'exigerait la paire, et les zéros ultérieurs peuvent compenser la paire sur une fenêtre courte dans un modèle à poids libres, jamais sur tout l'horizon. Le renversement du raccord central est la caractérisation même du passage à hauteur gardée. Dans le canal de comptage, la détection d'une paire ne se fait que contre une troncature non certifiée. La positivité tirée du produit eulérien vaut aussi pour le monde témoin et se perd dans la bande critique. Aucune propriété de fenêtre indépendante n'a été trouvée : le seul lien entre les données arithmétiques et la profondeur passe par une borne de croissance du complément plus forte que celle qui est démontrée.

Courant harmonique, premier zéro et couplage des Tours (2026-10-13, mission E239–E241). Chaque Tour ramenée à l'échelle de la ligne porte un courant : le produit de sa fréquence par le carré de son enveloppe (démontré). Le rapport des courants de deux Tours successives varie le long de l'axe exactement comme le carré du rapport de leurs normes ; il reste constant, ou prend la même valeur en deux contacts, si et seulement si les deux zéros ont la même partie réelle (démontré) : appliqué au zéro atteint depuis un départ sur la ligne, c'est le but lui-même, et c'est aussi l'égalité des rapports de normes en deux raccords déjà classée. Les contacts, la phase et l'enroulement admettent une Tour d'arrivée sous la ligne dont le courant n'est pas transporté (démontré). Le courant croisé de deux Tours dépend de leur écart à la ligne par leur somme, dans l'enveloppe, et par leur différence, seulement à travers le battement des hauteurs ; pour une paire miroir à la même hauteur la partie croisée est indépendante de l'écart et coïncide avec celle d'un double sur la ligne (démontré). Le signal arithmétique ne fixe que la partie réelle de la somme des Tours : deux configurations de même partie réelle ont des courants différents (mesuré). Le premier zéro est fixé par la fonction complétée tout entière, par le comptage démontré et le changement de signe ; sa part dans la reconstruction dépend de la fenêtre (mesuré) ; ses propriétés sont individuelles et aucune ne se transmet. Aucun couplage des Tours ne fixe la partie réelle de l'arrivée. (§19.24, auteur 2026-11-01 : journal, non appui ; approche fenêtrée ou tronquée.)

Signal exact et audit radial total (2026-10-13). Chaque zéro contribue au canal de Chebyshev par son terme exact, la puissance divisée par le zéro lui-même ; ramené à l'échelle de la ligne puis privé de ce diviseur, il devient un mode unitaire. Le diviseur porte la position radiale de deux façons : par son module, une constante d'amplitude, et par son argument, la phase initiale que lisent les contacts absolus. Les trois représentations sont des objets distincts reliés par des conversions démontrées. Restaurer le diviseur ne change aucune caractérisation (les courants individuels sont des multiples constants les uns des autres) ; cela corrige deux lectures : le rapport des courants porte une constante, et la partie croisée d'une paire miroir lit l'écart à la ligne au second ordre, alors que le mode unitaire la rendait aveugle. Les contacts absolus rendent la hauteur et la position radiale d'un zéro donné (démontré) ; le mode unitaire perd la phase initiale. Aucune combinaison des contacts absolus, du premier partagé, des diviseurs et des deux écarts ne fixe la position radiale de l'arrivée : toutes ces quantités existent pour toute position radiale (mesuré sur 1 075 configurations hypothétiques). Toutes les expériences ont été reclassées : 170 inchangées, 2 corrigées, aucune invalidée.

Synchronisation des Tours sur chaque écart premier (2026-10-13). Chaque Tour contribue à chaque écart entre deux premiers consécutifs par l'intégrale exacte de sa densité sur l'écart : un filtre de la largeur de l'écart, qui garde presque intactes les fréquences basses et atténue les fréquences au-delà de l'inverse de la demi-largeur logarithmique. La somme de ces contributions, sur tous les vrais zéros et pondérée par le facteur de lissage, est exactement l'incrément du reste des premiers sur l'écart (démontré). La correction vient de la superposition linéaire des contributions, non des battements, qui n'existent que dans l'intensité, ni des contacts ; collectivement, les phases toutes distinctes produisent une pente positive entre les puissances de premiers et une pointe négative de poids exact en chaque puissance (mesuré). Les densités exactes ont une amplitude commune exactement quand leurs parties réelles sont égales : l'amplitude commune d'un membre et de son miroir caractérise la ligne, elle n'est pas une conséquence de la loi. La même loi par écart vaut, avec ses propres poids, dans le monde témoin dont tous les zéros sont hors ligne ; elle ne fixe donc pas la partie réelle du zéro suivant.

Synchronisation à amplitude stable, fréquences seules (2026-10-13). L'énoncé de l'auteur, « la synchronisation avec le zéro initial n'est possible qu'avec une amplitude stable et seulement des changements de fréquences », est écrit comme contrat : la densité exacte du membre atteint a, en toute abscisse, l'amplitude de celle du départ, ce qui revient à dire que le rapport des deux densités est de module un et que seule la phase les distingue. Ce contrat est exactement l'égalité des parties réelles ; depuis un départ en ligne il ferme le but ; posé sur tous les passages qui montent depuis un membre en ligne, il équivaut à l'hypothèse de Riemann (démontré). Il n'est dérivé d'aucun théorème : c'est le but écrit sur les densités. Ce qui est démontré en plus : remplacer, dans la famille des contributions, un point par un autre point, en recalculant son coefficient et en conservant toutes les autres contributions, ne reconstruit jamais le reste des premiers, que le remplacement change l'amplitude à fréquence fixée ou la fréquence à amplitude fixée ; la reconstruction exacte exclut tout remplacement sans distinguer les deux directions. Et le vrai membre atteint reconstruit le reste par théorème, quelle que soit sa partie réelle : un point remplacé n'est pas un zéro de zêta, et l'exclusion des remplacements ne dit rien de la position du vrai zéro.

Synchronisation locale des contributions sur chaque écart premier (2026-10-14). Les écarts de deux premiers consécutifs sont pris comme unités de contrôle. La contribution d'un zéro à un écart est l'intégrale exacte de sa densité sur cet écart, dans le canal de comptage comme dans le canal lissé ; elle est isolable sans les autres, additive sur les écarts adjacents, bornée par son enveloppe, et sa variation à l'une des bornes est la densité elle-même, dont le signe est celui du cosinus de la phase, quelle que soit la partie réelle. Les points où la densité change de signe ne dépendent que de la hauteur ; ils ne coïncident ni avec les contacts de phase de la Tour, dont ils diffèrent d'un décalage qui lit la partie réelle, ni avec les croisements de l'axe du fond. Une paire miroir hypothétique diffère du point en ligne de même hauteur par un facteur hyperbolique exact, nul exactement sur la ligne. Pour chaque écart, l'incrément du reste des premiers est la somme, sur tous les vrais zéros, de leurs contributions locales (démontré, canal lissé) ; le résidu de toute troncature finie est la somme des zéros omis, jamais une contradiction, et une décomposition dont le résidu est défini par différence n'a aucun contenu. Rigidité : deux points qui donnent les mêmes contributions locales sur tous les écarts sont le même point ; cette identification vaut pour toute partie réelle et ne la contraint pas. La contribution locale voit la partie réelle : sa dérivée radiale est l'intégrale de la densité exacte sur l'écart, non identiquement nulle ; à hauteur fixée, deux parties réelles qui donnent la même densité individuelle sur un intervalle ouvert sont égales, et deux valeurs convenables de cette densité restituent la partie réelle (démontré) ; seuls les points où la densité change de signe ne dépendent que de la hauteur. Détecter, retrouver et imposer la partie réelle sont trois choses : les deux premières sont démontrées, la troisième est le but. La lecture en ligne des contributions locales du membre atteint équivaut à sa position sur la ligne ; depuis un départ en ligne elle ferme le but ; posée sur tous les passages d'historique en ligne, elle équivaut à l'hypothèse de Riemann. Portée : les trois premiers maillons de la chaîne proposée (contributions, synchronisation exacte, rigidité) sont démontrés pour toute position radiale ; le quatrième est le but lui-même, et aucune information indépendante n'est apportée par rapport à la formule explicite et à l'unicité spectrale déjà compilées.

Audit contradictoire de la synchronisation locale (2026-10-14). La synchronisation sur chaque écart est la linéarité d'une somme : elle vaut pour toute famille de points avec sa propre cible ; ce qui appartient à zêta est la seule formule explicite qui identifie la cible au reste des premiers, et la famille authentique la satisfait quelle que soit la position de ses membres. Le reste d'une troncature est la somme des membres omis par un fait général sur les sommes, pas par une propriété de zêta. Une borne de ce reste sur chaque écart, uniforme et démontrée sans l'hypothèse, existe : elle croît comme la taille des premiers, et elle admet tout membre, hors ligne compris ; une borne qui croîtrait moins vite que ce qu'exige l'écart du membre arrivé serait une bande sans zéro, de même nature que l'hypothèse. Classés d'après leur énoncé compilé, les énoncés qui portent les rigidités sont surtout des identités ; les vraies contraintes sans l'hypothèse (bande, symétries, ordre, comptage avec son miroir) sont toutes satisfaites par une première arrivée sous la ligne. La perturbation d'un membre à autres contributions figées détecte toute modification, en ligne comme hors ligne : elle ne teste pas la position radiale.

Les trois premières Tours sur la ligne (2026-10-14). Reconstruites depuis leur définition, les trois Tours tournent réellement : chacune s'enroule autour du même axe de rotation, à sa propre fréquence, avec un rayon qui grandit comme la racine de l'abscisse ; elle part de l'inverse de son zéro, pas du zéro lui-même. Deux Tours ne se rencontrent jamais dans l'espace, leurs rayons restant dans un rapport fixe ; ce qui paraît un croisement n'est qu'une projection. Les contacts de phase, les extrema de la contribution de comptage, les passages par le fond, les rencontres avec le comptage exact et les alignements de phase entre Tours sont cinq familles distinctes ; seule la première redonne le zéro. La synchronisation vérifiée est celle de la formule explicite : les vraies hauteurs, et elles seules, rapprochent le champ de comptage de l'escalier des premiers, et les premiers résonnent à chacune de ces hauteurs. Aucune synchronisation géométrique supplémentaire n'apparaît, et toutes les relations trouvées lisent la hauteur, aucune la partie réelle.
Synchronisation écart par écart (correction de l'auteur, 2026-10-14). Mesurée sur chaque écart entre deux premiers et sur chaque saut du comptage, et non plus en moyenne sur toute la plage : chaque Tour sur la ligne contribue sur chaque écart, et la contribution exacte d'une Tour sur un écart dépend de la position radiale de son zéro (rien ne l'efface). La famille des vrais zéros suit chaque écart, puis redémarre à chaque premier ; ce qu'elle laisse diminue sur chaque écart quand on prend plus de zéros. Si l'on remplace le premier zéro par une paire placée de part et d'autre de la ligne, la somme manque chaque écart et chaque saut, d'autant plus que la paire s'écarte et que l'abscisse grandit, et ne se rétablit jamais. Ce contrôle remplace un membre dans la famille des vrais zéros ; il ne dit pas ce que ferait une famille authentique contenant un membre hors de la ligne, qui égalerait la même arithmétique avec d'autres membres. Les relations trouvées lisent la position radiale ; aucune ne la fixe.

Synchronisation collective des trois premières Tours (correction de l'auteur, 2026-10-14). La synchronisation n'est pas l'alignement des contacts des trois Tours : c'est la construction d'un signal résultant unique, par la superposition de leurs contributions et leurs interférences, constructives ou destructives. Chaque zéro sur la ligne a pour partenaire son conjugué, de hauteur opposée : ensemble ils transforment la rotation de la Tour en une oscillation réelle, dans le signal brut comme dans le comptage ; le conjugué n'est pas une Tour de plus et ne se compte qu'une fois. L'énergie de la superposition contient deux échelles : des battements lents, réglés par les différences de hauteur, et des oscillations rapides, réglées par leurs sommes. Les événements de ce signal collectif se construisent par étages : la première paire impose une grille régulière, la deuxième la déplace et en crée, la troisième l'affine. Ils sont trop peu nombreux pour marquer chaque écart premier (leur nombre ne croît qu'avec le logarithme, démontré) et ne sont pas plus proches des premiers que ceux de hauteurs témoins. En revanche, à l'échelle des fenêtres de la première Tour, la superposition des trois paires suit la demande arithmétique, et le comptage reconstruit avec les trois paires place les premiers mieux que le fond seul et que toutes les hauteurs témoins. Rien de cela ne fixe la partie réelle ; aucun zéro hors ligne n'a été simulé.

Saut collectif à l'événement premier, contacts partagés, condition de ligne (théorèmes A et B de l'auteur, 2026-10-15), en mots seuls. À chaque nombre premier, la fonction de comptage pondérée saute exactement du poids de ce premier, son logarithme ; lue à travers la reconstruction, la contribution de tous les zéros ensemble à cette marche vaut ce poids moins la variation seconde du fond lisse. C'est le seul endroit où le poids exact entre dans la famille des zéros, et c'est une identité : elle vaut pour la famille telle qu'elle est, sans rien supposer de la position radiale d'aucun membre, et le complément de n'importe quelle partie de la famille y est fixé par différence. Deux Tours qui partagent deux contacts consécutifs ont la même hauteur, puis la même position radiale : des zéros distincts, en ligne compris, ne partagent jamais deux contacts consécutifs ; « les contacts doivent être les mêmes » n'est pas une loi possible. Un contact de l'arrivée coïncide avec le contact de ligne de sa hauteur si et seulement si l'arrivée est en ligne : c'est la cible elle-même, écrite sur un contact, et la grammaire ne l'impose pas, puisque toute position sous la ligne satisfait les obligations de contact connues. Vérification des expériences : presque toute configuration hors ligne numérique du dépôt est posée à une hauteur d'un zéro en ligne, ou est un monde témoin entier, et dans tous les cas elle remplace ou insère dans la famille vraie ; aucune n'est un hors-ligne authentique. Les normalisations employées conservent la lecture radiale, sauf trois comparaisons par l'énergie propre, annoncées comme aveugles. Aucune conclusion sur la position radiale ni sur l'hypothèse. Réduction demandée par l'auteur : au seul événement premier de l'arrivée, la contribution de la paire de l'arrivée vaut le saut exact moins celle de tout le reste de la famille ; il suffit donc, pour fermer, que cette contribution dépasse strictement la somme du saut et de celle du reste à cet événement. Correction (E308, même jour) : cette condition est toujours fausse, puisque la contribution de la paire est le saut moins celle du reste, et qu'une différence ne dépasse jamais la somme des deux tailles ; la réduction a été retirée et la cible est redevenue l'exclusion directe de la première rupture.

Raccords fixés par les deux bornes de chaque écart (E305, 2026-10-15), en mots seuls. La contribution d'un zéro à un intervalle entre deux premiers consécutifs est la différence d'une seule fonction prise aux deux bornes ; sur toute suite d'intervalles consécutifs, ces contributions se télescopent. Un zéro est déterminé par ses contributions sur les seuls intervalles entre premiers, à partir de n'importe quel rang : deux points distincts diffèrent sur un intervalle au-delà de tout rang, et un déplacement de la position radiale à hauteur fixée se lit ainsi au-delà de tout rang. Les raccords sont donc non déplaçables. Mais cela vaut pour toute position radiale, y compris pour des zéros hors ligne authentiques d'une autre fonction, reconstruits à l'aveugle depuis les seuls intervalles premiers : la non-déplaçabilité identifie, elle ne contraint pas. L'hypothèse de l'auteur selon laquelle un hors-ligne n'aurait jamais la hauteur d'un zéro en ligne est écrite telle quelle ; elle découle de l'hypothèse de Riemann, n'est pas dérivée, et sous elle une première arrivée sous la ligne reste sans contradiction, toute sa hauteur étant alors hors ligne.

Rigidité radiale depuis les seuls premiers (E308, 2026-10-15), en mots seuls. La réduction précédente demandait que la contribution de la paire d'arrivée dépasse, au seul premier de l'arrivée, la somme du saut exact et de la contribution du reste ; or cette contribution est précisément la différence de ces deux quantités, et une différence ne dépasse jamais la somme de leurs tailles : la condition était toujours fausse et a été retirée. Que chaque zéro soit fixé par ses contributions sur les intervalles entre premiers ne rend pas égales les positions radiales de deux zéros différents : deux points de positions différentes sont l'un et l'autre fixés. Une loi d'échelle commune à plusieurs oscillations équivaut exactement à une position radiale commune. Depuis les seuls nombres premiers, sans aucune hauteur connue, les fréquences des treize premiers zéros sont retrouvées, et les positions radiales ajustées restent proches d'un demi, l'imposition d'un demi ne dégradant pas la prédiction au-delà de l'échantillon ; ce sont des observations sur un nombre fini d'oscillations, qui ne disent rien des zéros plus hauts. Sous la première position établie, la conservation de la position radiale à chaque passage équivaut à l'hypothèse elle-même ; elle reste à démontrer.

Argument de l'auteur sur l'amplitude des premiers (2026-10-15), en mots seuls. Les premiers, leurs poids et leur grammaire sont immuables ; la courbe qu'ils dessinent est reproduite exactement par les vrais zéros, qui sont des points fixes : aucun ne peut être remplacé sans casser la reproduction. L'amplitude de cette courbe borne la position de chaque zéro et de son miroir ; le premier zéro est sur la ligne. Il suffit donc que l'amplitude de la courbe des premiers soit celle de la ligne : un zéro tombé sous la ligne aurait un miroir qui la dépasse. Cet énoncé ne parle que des premiers ; il est équivalent à l'hypothèse elle-même. La grammaire contraint l'amplitude, mais la contrainte démontrée est d'ordre linéaire, pas d'ordre racine carrée ; le monde témoin, de même grammaire, a une amplitude plus grande.

Synchronisation par écart refaite (E309, 2026-10-15), en mots seuls. Les vrais zéros suivent chaque écart premier et chaque saut, sans exception. Toute configuration fabriquée, sur la ligne ou hors de la ligne, placée à une hauteur où ζ n'a pas de zéro, laisse un défaut sur chaque écart : elle est fausse, et rien ne la compense. Aucun zéro hors de la ligne n'existe sous la hauteur vingt-huit, ce qui comprend tout l'intervalle entre le premier et le deuxième zéro. L'étude montre que les zéros fabriqués sont faux. Elle ne dit pas où sont les vrais zéros au-delà des hauteurs vérifiées. (§19.24, auteur 2026-11-01 : journal, non appui ; approche fenêtrée ou tronquée.)

Vérification d'un audit extérieur de la question ouverte (2026-10-15), en mots seuls. L'audit a raison sur le constat : l'amplitude décroissante du zéro supposé et l'amplitude croissante de son miroir, à la même hauteur, ne se contredisent pas entre elles, et ce que l'on sait lire de la courbe des premiers depuis leurs seuls poids ne borne l'amplitude qu'à l'échelle entière, trop large pour contredire le miroir. Il a tort sur le remède : la synchronisation écart par écart est déjà démontrée et tient pour toute amplitude avec ses poids, elle ne sépare rien ; la question n'est pas « presque » de la force de l'hypothèse, elle l'est exactement une fois quantifiée, et cela est démontré ; retirer la question du build est contraire à la règle d'une seule chaîne ; la propriété fenêtrée proposée (le signal normalisé des premiers, moyenné sur des fenêtres qui détectent chaque fréquence, ne croît pas exponentiellement) est une autre écriture de la même obligation : elle force chaque zéro sous un demi et son miroir, donc l'hypothèse entière, et elle en découle ; sa mesure est l'expérience déjà faite sur la courbe des écarts. Rien n'est modifié.

Courbe des écarts et amplitude du premier zéro (E310, 2026-10-15), en mots seuls. Depuis la seule courbe des premiers, sans connaître aucune hauteur ni aucun exposant, le premier zéro est retrouvé à sa hauteur, et l'exposant de son amplitude est lu fenêtre par fenêtre : un demi, à un dix-millième près, le même sur quatre décades ; son amplitude est stable le long des premiers. Un zéro situé sous un demi aurait une amplitude qui décroît relativement à ce signal ; cette décroissance est incompatible avec la mesure dès un écart de quatre dix-millièmes. Le monde témoin, dont la famille est hors de la ligne, est lu à un exposant différent : la méthode lit, elle n'impose pas. Portée : pour le premier zéro, c'est un théorème confirmé ; pour le zéro qui suit un zéro engagé, objet du but ouvert, c'est une mesure sur un horizon fini. Compensation : aucune ne tient sur tout l'horizon, ni individuelle, ni collective, car la somme d'une famille détermine chaque membre ; cette unicité fixe la famille depuis la courbe, elle ne dit pas où elle est. (§19.24, auteur 2026-11-01 : journal, non appui ; approche fenêtrée ou tronquée.)
Second audit externe et extraction successive des modes (E311, 2026-10-15), en mots seuls. Un second texte collé demandait de vérifier ce que vaut l'unicité collective annoncée dans le verrou. Vérifié sur les énoncés : elle vaut pour des familles infinies, à hauteurs et exposants quelconques, sans supposer d'avance qui en fait partie, et ce qui la fixe est bien la courbe des premiers ; deux familles qui reproduisent la même courbe sont la même famille, membre par membre, poids par poids. Elle dit qui est là ; elle ne dit pas où. Le texte proposait aussi de retirer un à un les modes reconnus et de lire, à chaque fois, la fréquence suivante et son exposant sans rien imposer : fait sur douze modes depuis la seule courbe des premiers ; les douze fréquences sont les douze premières hauteurs de zêta, et les douze exposants sont lus à un demi, à la précision de la méthode, exactement comme sur un signal construit à un demi exact ; le monde témoin est lu ailleurs. C'est une mesure sur douze hauteurs ; ce que le texte appelle « loi uniforme sur les résidus » est, une fois écrit, la question ouverte elle-même : le reste après retrait des modes connus est la somme de tous les zéros plus hauts, et le contrôler à l'échelle de la ligne, c'est dire que tous ces zéros y sont. Le verrou et le but ne changent pas. (§19.24, auteur 2026-11-01 : journal, non appui ; approche fenêtrée ou tronquée.)

Correction collée pour l'extraction successive (E311b, 2026-10-15), en mots seuls. Le texte demandait de séparer, pour chaque zéro identifié, la valeur certifiée de sa partie réelle, la valeur reconstruite depuis les premiers, l'erreur de cette reconstruction et l'erreur sur la hauteur, avec des hauteurs de référence précises, et de mesurer la part de l'arrondi des hauteurs. C'est fait : les hauteurs de référence sont calculées à trente chiffres ; la partie réelle certifiée vaut un demi, par le compilé pour les trois premiers zéros et par certification externe pour les neuf suivants, ce qui est dit zéro par zéro. L'écart de la valeur reconstruite à un demi se décompose exactement en une part due à l'erreur de hauteur et une part due à l'inversion elle-même à hauteur exacte. La part de la hauteur ne dépasse pas trois pour cent sur les zéros où l'écart est notable ; arrondir les hauteurs de référence à quatre décimales ne déplace la valeur reconstruite que d'un millionième environ. L'écart restant, à hauteur exacte, est celui de la méthode de lecture (fenêtre de longueur quatre, voisins proches), reproduit à un dix-millième près par un signal fabriqué dont toutes les parties réelles valent exactement un demi. L'hypothèse que l'arrondi des hauteurs explique l'erreur est quantifiée et écartée. Mesure finie ; aucune démonstration ; rien de compilé ni de verrouillé n'a changé.

Correction de l'étude conjointe (2026-10-15), en mots seuls. La critique collée par l'auteur est exacte : ce qui avait été présenté comme l'identification conjointe de la fréquence et de l'amplitude depuis tous les écarts supposait déjà que la signature candidate reproduise les contributions d'un zéro connu ; c'est une comparaison de deux signatures, un résultat conditionnel, qui ne lit rien dans le signal des premiers et ne produit aucune contrainte. Les autres énoncés disent qu'un zéro supposé hors de la ligne ferait croître le reste des premiers, ce qui va dans le sens inverse de ce qui est demandé, ou sont des reformulations de la question elle-même. Aucun mécanisme d'exclusion n'est validé ; l'étude demandée, partir du signal exact de tous les écarts pour en tirer des contraintes conjointes sur la fréquence et l'amplitude du prochain zéro, n'est pas réalisée. Tout ce qui avait été composé dans la question ouverte est retiré, la ligne ajoutée au verrou est retirée, la question et son contexte sont ceux de la livraison précédente. Ce que le signal des premiers donne seul, sans supposer aucune signature, est établi et dit tel quel : chaque zéro est dans la bande entière, et rien n'est dit de sa fréquence ; cette contrainte n'exclut aucune signature.

Texte collé « fréquence attendue et unicité radiale » (2026-10-15), en mots seuls. Le texte avance cinq points et propose d'isoler un contrat : la fréquence attendue, produite par toute la grammaire des écarts, n'admettrait qu'une seule signature, celle d'un zéro sur la ligne. Vérifié : les écarts déterminent bien chaque zéro par ses contributions, mais pour toute partie réelle, ils identifient sans contraindre ; le premier zéro est démontré sur la ligne ; le miroir d'un zéro est à la même hauteur, démontré ; un zéro du côté haut ne peut pas être l'arrivée d'un passage qui monte, parce que l'arrivée est le membre le plus à gauche de sa hauteur, et ce côté est déjà fermé : le cas ouvert est le membre bas, dont le miroir haut est à la même hauteur, et le raisonnement du texte ne le touche pas. Sur la fréquence attendue, le texte distingue lui-même deux sens : la hauteur du prochain zéro authentique, qui est déjà dans la question ouverte (le zéro considéré est à cette hauteur) et qu'un zéro hors de la ligne partagerait ; ou une fréquence produite par la grammaire seule, dont aucun énoncé compilé n'existe, la grammaire étant aveugle au régime et n'exigeant aucune progression de hauteur ; les expériences lisent les fréquences dans le reste des premiers, c'est le premier sens. L'unicité de la position radiale à cette hauteur est la question ouverte elle-même, et sa forme quantifiée a la force de la conjecture ; l'unicité collective, comme le texte le dit, admet une paire miroir. Enfin la synchronisation est compilée pour toute partie réelle : seul un remplacement ou une insertion la rompt, jamais une paire authentique. Aucun contrat n'est ajouté, la question n'est pas renommée ni modifiée.

Réduction en trois points de l'auteur (2026-10-15), en mots seuls. Le premier zéro est sur la ligne, avec son amplitude et sa fréquence : démontré. Un zéro hors de la ligne ne peut pas occuper le même point qu'un zéro sur la ligne, et aucun zéro hors de la ligne n'existe sous la hauteur vingt-huit : démontré. La proportion d'au moins deux tiers de zéros sur la ligne (zeta23) est désormais dans le projet. Restent deux points. Le premier : un zéro hors de la ligne ne partage jamais la hauteur d'un zéro sur la ligne. Le second : la hauteur du zéro suivant porte déjà un zéro sur la ligne. Les deux ensemble excluraient le zéro suivant hors de la ligne. Le théorème « la hauteur avance » place le zéro suivant plus haut, sans fixer sa position. Le théorème « seule la hauteur évolue » suppose les deux zéros sur la ligne.

La chaîne consolidée des acquis, qui n'est pas le verrou en vigueur. Depuis l'état engagé, la Tour suivante projette sur l'axe algébrique une nouvelle grille exacte, sur la
même histoire ordonnée des événements premiers : des contacts où l'oscillation ne cache pas l'amplitude, des cellules
d'un demi-tour, le rayon du terme propre. La chaîne complète est : état engagé → Tour suivante → nouvelle grille
exacte → même histoire ordonnée des premiers → écarts exacts → demandes arithmétiques exactes → réponses de toutes les
Tours → organisation de leurs renforcements et compensations → impossibilité d'une dérive radiale → Tour d'arrivée non
translatée → ligne critique. Les écarts exacts arrivent comme des mots grammaticaux, chaque événement avec sa
magnitude et sa transition d'état, et chaque mot impose à chaque Tour une suite de sollicitations exactes. Acquis
jusqu'aux compensations : la grammaire fixe exactement le reste modulo six de chaque sollicitation, l'avance de deux
changements consécutifs et le verrou des passages d'un état à l'autre ; chaque marche adresse à l'ensemble des Tours
une demande exacte ; la réponse collective l'égale ; son carré est la diagonale plus les croisés, que la demande
force ; la dette d'une dérive radiale ne se cache, sur toute l'histoire, par aucune réorganisation des autres Tours,
et elle se lirait dans la taille du reste. Hors de ce build, le budget global fixe plus des deux tiers des zéros
simples en ligne.

Ce que fixent la hauteur et la position radiale. La hauteur d'arrivée fixe entièrement la résolution. La position
radiale fixe comment le rayon, et l'énergie qui en est le carré, varient sur les mêmes écarts. Que
cette grille ne soit pas translatée est la cible locale, caractérisée et non dérivée ; ce n'est pas le verrou en vigueur.

Ce qui ne la porte pas. Les écarts exacts : lus le long d'une chaîne ou d'un mot, ils ne gardent que les extrémités.
La grammaire modulo six : elle fixe la succession des sollicitations, pas leur réponse ; elle est la même dans tout
monde de même support, et la garder seule ne rend pas la régularité de zêta. Les canaux de transition : la
compensation passe entre eux. La diagonale : un monde de même support premier, de même valeur absolue des poids et de
même somme des carrés a des membres hors ligne. Le sens de lecture d'un demi-tour. La géométrie, la hauteur, la
fréquence et l'enroulement. La loi de partage entre diagonale et croisés, renormalisée. Une fenêtre de marches dont
les contributions sont traitées comme libres. Les seuls premiers partagés d'une cellule : la profondeur n'y émerge pas.
Une proportion de zéros en ligne, même égale à un : elle ne voit pas une paire isolée, et le budget global ne distingue
pas une paire proche d'un zéro double en ligne. Une lecture des premiers à horizon fixé : elle confond la paire serrée et
le double. Le comptage, les changements de signe sur la ligne et le rang : ils ne séparent pas la paire du double.
L'interaction d'une continuation avec les Tours engagées : elle ne porte que la courbure propre, et son signe est fixé
par une phase relative ou par la présence d'un membre, pas par la continuation. La boucle miroir remise dans l'ordre
des premiers : elle permute les membres d'une paire miroir, et sa fermeture collective vaut dans le monde décalé. La
différence de deux expressions arithmétiques du même objet : le côté arithmétique de zêta ne porte qu'un canal
symétrique, et cette absence ne force pas la fusion.

Ce qui sépare. C'est l'organisation des poids signés, rencontrés dans l'ordre exact des magnitudes : détruire l'ordre
localement ramène au hasard, qui est critique ; zêta est plus régulière que le hasard à toutes les résolutions mesurées,
place ses compensations là où la demande exacte les exige et fait se compenser ses canaux entre eux ; une organisation
cohérente fait se renforcer les canaux et croître l'énergie sans borne. Entre zêta et un monde de poids de taille
modifiée, seule la taille absolue sépare.

Acquis encadrant l'ancienne formulation locale (ce ne sont pas des verrous en vigueur). La raison de l'engagement est connue : l'annulation du miroir par la réflexion et la
conjugaison laisse la hauteur pour seule coordonnée libre. Une loi de fenêtre exclurait, à partir du mot
premier exact lu en phase et en amplitude par les Tours contraintes de la fenêtre, la cellule minimale de
changement de régime (quatre membres, trois passages, un premier partagé par passage, deux écarts), à l'entrée comme
à la sortie d'une portion hors ligne, puisqu'un membre hors ligne serait entouré, dans l'ordre des membres, de régime
engagé ; entrée et sortie sont des cellules différentes, chacune à exclure pour elle-même ; cette loi n'est plus présentée comme le verrou. Sa
conséquence locale est la grille d'arrivée non translatée ; sa conséquence globale, la croissance critique du reste. Ce
n'est pas la grammaire qui lit la position radiale, c'est la réponse des Tours au mot grammatical. Trois contraintes
établies encadrent toute loi de cette forme. La fenêtre est locale dans les membres, pas dans les premiers. Le côté premier ne lit la
profondeur qu'au second ordre, comme une courbure logarithmique contre le double en ligne, et à horizon fixé il
confond une paire serrée avec le double : la loi doit lire des horizons d'autant plus longs que la profondeur est
petite. Comparée à sa configuration dégénérée de référence sur la ligne, une fenêtre a deux continuations, de courbures de
signes opposés ; ce signe est un certificat d'une continuation donnée, que ni la lecture propre, ni l'interaction avec
les Tours engagées, ni la stabilité sous raffinement ne sélectionnent sans la croissance critique du reste. Une telle loi
devrait démontrer que, depuis le régime engagé, l'histoire première exacte n'admet que la continuation verticale ; elle est
vraie pour les plus proches membres de zêta et devrait être fausse dans tout monde qui porte une paire. La géométrie
qui sépare est entièrement connue : la ligne est un cercle, une paire est un couple de spirales miroir de même rotation
et de dérives opposées. Zêta n'a qu'une histoire première, de poids de taille exacte, qui ne voit une paire que par sa
somme ; le monde décalé en a deux, une par spirale. La somme d'une paire efface la profondeur au premier ordre mais
laisse, contre le double en ligne, un excès symétrique strict au second ordre, que le miroir ne peut plus annuler ;
l'arithmétique n'a pas à distinguer les deux spirales, seulement à rendre compte de cet excès. Comparée à sa référence
fusionnée, la variation d'énergie de la fenêtre est l'excès propre, positif, plus une interaction avec le complément ;
le reste exact étant donné par les premiers, cette interaction est la lecture du reste à la fréquence de la paire,
pondérée par la courbure ; ni le miroir ni l'algèbre ne la fixent, et la référence fusionnée n'est pas un monde à
poids exacts. Une telle loi se ramène donc à ceci : que le reste exact des premiers
n'ait, à aucune hauteur, de composante qui croisse plus vite que la racine carrée, c'est-à-dire la croissance critique
du reste, énoncé global sur la taille exacte des poids et leur organisation signée. Elle est fausse dans le monde
décalé, dont les poids sont plus grands, et fausse dans le monde de signes cohérents, de même valeur absolue des poids.
Aucune forme locale de cette loi, lue sur une fenêtre de membres, n'échappe à cette lecture ; il ne faut pas exiger
qu'un objet arithmétique fixe chaque membre, ce qui serait la conclusion.

Hors de la flèche. Le logarithme intégral n'y entre pas : c'est une moyenne de comptage, qui ne dit le contenu d'aucune
cellule.


---

Version purgée et consolidée le 2026-10-02 par Claude Opus 5.5, sur ordre de l'auteur ; l'historique des
versions antérieures est dans le journal git.

Certificat de l'ancre (auteur, 2026-10-10), en mots seuls. La fonction zêta ne s'annule sur aucun des bords de deux rectangles qui encadrent la première bande, et l'enroulement du produit de zêta par le facteur qui supprime le pôle vaut un autour du premier et zéro autour du second. Chaque côté est découpé en morceaux ; sur chacun, deux valeurs de la partie principale d'Euler–Maclaurin aux extrémités suffisent, parce que la dérivée s'élimine entre elles. Le résultat est démontré dans la bibliothèque : sous la hauteur quinze il y a un seul zéro, simple, et il est sur la ligne critique. L'ancre est acquise ; seule la transmission reste ouverte.

Lecture conjointe (auteur, 2026-10-11), en mots seuls. Sur plusieurs événements premiers lus ensemble, ce que les premiers exigent après l'historique se partage exactement entre le groupe d'arrivée et tout le complément. Trois majorations sont démontrées séparément : celle de l'attendu, tirée des seuls premiers et de l'historique ; celle de la compensation du complément entier ; et le plafond du signal du groupe d'arrivée. Si le signal dépasse strictement la somme des deux premières, la reconstruction est contredite : c'est maintenant la forme du but. Avec la seule borne connue du reste, d'exposant un, cela exigerait que la masse du groupe d'arrivée dépasse la constante de cette borne. La minoration du signal signé du groupe, avec ses phases et ses dénominateurs, n'est pas démontrée.

Miroir de la première rupture (auteur, 2026-10-11), en mots seuls. L'historique en ligne, premier zéro compris, est retiré exactement du reste des premiers ; ce qui reste se partage entre un groupe fini de zéros suivants et la queue au-delà, conservée entière. Si le membre atteint était sous la ligne, son miroir, à la même hauteur et au-dessus de la ligne, serait dans ce groupe, et aucun autre membre du groupe, quelles que soient leurs positions, multiplicités et phases, ne compenserait sa croissance. Le reste des premiers moins la queue au-delà du groupe est exactement la somme finie du groupe et de l'historique : le borner revient à borner une somme qui contient le miroir, ce n'est pas une majoration indépendante. La forme indépendante porte sur le reste des premiers seul, écrit sans aucun zéro : s'il croît moins vite que le miroir, le membre bas est exclu. Cette majoration n'est démontrée qu'à la croissance linéaire.

Reste déroulé aux poids premiers (revue de l'auteur, 2026-10-11), en mots seuls. Le reste des premiers est ramené aux entiers, où il ne dépend que de la masse pondérée des puissances de premiers sous l'entier ; entre deux entiers, il bouge d'une quantité bornée. Les puissances propres de premiers pèsent peu (ordre de la racine). La masse des premiers se partage exactement en un bord et quatre transitions entre les deux états modulo six ; chacune est positive. Les états ne laissent aux premiers qu'un tiers des entiers : c'est une limite par le haut, sans aucune limite par le bas. Ce qui manque est de borner des deux côtés l'écart entre la masse des premiers et son attendu, avec un gain d'une puissance sur Chebyshev fixé par le miroir. Un tel gain équivaut exactement, dans les deux sens, à chasser tous les zéros d'une bande entière à droite de la ligne, au-dessus de l'arrivée et jusqu'à l'infini : ce n'est pas une propriété du seul passage, et la lecture du pôle n'admet aucune forme intermédiaire entre une somme finie, où le miroir est déjà présent, et la croissance du reste sur tout l'axe.


## Ajout du 2026-10-20 — E304 : collaboration bilatérale des Tours, stabilité et non-changement de régime (programme de recherche, non démontré)

**Sens imposé de la recherche.** Le point de départ est la correction première exacte, calculée depuis les événements premiers et le fond analytique, sans injecter les paramètres des zéros inconnus. L'étude doit aller des écarts premiers vers la répartition des contributions, puis vers les contacts, puis vers la stabilité éventuelle du régime engagé. Partir des zéros connus pour recalculer les premiers n'est qu'un contrôle a posteriori, non la découverte recherchée.

**Question centrale de collaboration.** Il ne suffit pas que la somme des Tours restitue les événements premiers. Il faut découvrir comment une Tour intermédiaire apporte exactement sa contribution en tenant compte, simultanément, de la contribution déjà acquise de la Tour précédente et de la contribution réservée à la suivante. « Connaître » les contributions voisines est ici une image de compatibilité mathématique bilatérale, non une causalité ou une information transmise physiquement entre zéros. La décomposition arithmétique seule ne démontre ni cette sélection ni son unicité.

**Deux raccordements indissociables.** Le raccordement arithmétique concerne la correction de chaque écart premier, les contributions individuelles signées et le complément spectral extérieur qui doit rester explicite. Le raccordement géométrique concerne l'insertion des contacts de la Tour centrale relativement aux contacts des deux Tours voisines, en mobilisant les théorèmes existants de limite basse et de limite haute, avec leurs hypothèses exactes. Il faut rechercher une contrainte nouvelle issue de l'intersection de ces deux raccordements ; la simple additivité du reste et l'inversion de contacts calculés depuis un zéro connu sont des identités ou des contrôles, pas une preuve de stabilité.

**Acquis non négociables et portée.** Les théorèmes compilés de non-correction et de non-substitution doivent être utilisés sans réintroduire de coefficients de compensation ou de réajustement arbitraire dans une reconstruction authentique fixée. Ils ne suffisent toutefois pas à exclure, par eux-mêmes, une famille authentique inconnue qui contiendrait dès l'origine une paire hors ligne. Les contributions exactes oscillent : ne pas transformer la stabilité en exigence artificielle de décroissance de la valeur absolue du reste après chaque Tour. Les contacts doivent provenir des paramètres réels et de hauteur, sans indices indépendants de production ; les différents canaux de signaux et leurs normalisations ne sont pas interchangeables.

**Définition opératoire de stabilité à rechercher.** Une fois les contributions antérieures identifiées, le prolongement des écarts premiers ne doit pas obliger à les réécrire. La Tour suivante doit satisfaire à la fois les contraintes de correction imposées par les premiers et les limites de contacts des deux côtés. L'expérience doit chercher si cette compatibilité détermine une continuation rigide et empêche de quitter le régime en ligne déjà engagé. L'unicité de la continuation, la conservation de la position radiale et l'impossibilité de changement de régime restent des propositions à démontrer, jamais des prémisses.

**Triplets et contrôles.** Examiner les trois Tours authentiques initiales en ligne pour identifier les propriétés réellement observables, puis un scénario avec une Tour hors ligne intermédiaire, et un scénario comprenant les deux membres d'une paire miroir hors ligne à hauteur identique. Aucun zéro authentique connu n'est retiré ou remplacé dans les contrôles d'insertion. Pour le véritable test inverse, cacher les zéros postérieurs au régime initial et ne fournir que les corrections premières, les contributions antérieures déjà certifiées et les théorèmes admissibles. Une paire hors ligne n'est pas rejetée par une règle de croissance de hauteur supposée pour elle. Les tests d'insertion dans une reconstruction déjà fixée contrôlent la non-correction ; ils ne constituent pas l'exclusion d'une paire hors ligne authentique.

**Audits préalables obligatoires.** Identifier précisément, dans Lean, les théorèmes de limite haute et de limite basse des contacts : énoncé, quantificateurs, domaine des contacts, indices éventuels dérivés, hypothèses ON ou OFF, caractère conditionnel ou inconditionnel, et sens réel de la borne (enveloppe globale, contact d'un membre, ou prédiction du suivant). Vérifier également les théorèmes de non-correction et les types exacts de contribution qu'ils concernent. Ne jamais transporter une borne du signal brut au comptage lissé, ni transformer une enveloppe conditionnelle en loi universelle. Cet audit est une tâche à exécuter après la présente consignation ; il n'est pas déclaré accompli ici.

**Critère de découverte.** Le livrable scientifique recherché est une propriété indépendante de raccordement bilatéral qui, à partir des corrections premières exactes et des théorèmes déjà acquis, limite ou exclut une continuation hors ligne sans postuler la conclusion RH. Rapporter séparément les identités définitionnelles, les théorèmes compilés, les observations numériques, les contre-exemples et les propositions ouvertes. Une récupération numérique du troisième zéro, une baisse d'erreur ou une exclusion d'insertion synthétique ne valent pas certificat de non-changement de régime. Aucun théorème Lean nouveau ni fermeture de RH n'est affirmé dans cet ajout.

## 15. Graphe de causalité (2026-10-28) : des écarts premiers aux rencontres obligées, puis à la fréquence attendue ; la hauteur n'est qu'une conséquence

Formalisation en mots du graphe proposé par l'auteur le 2026-10-28, corrigé et complété après vérification contre le code compilé et les expériences E386 et E387. Ce qui est dit « compilé » l'est pour toute position radiale, sans hypothèse sur la ligne ; ce qui est dit « ouvert » est exactement ce que la chaîne terminale pose en unique hypothèse. Interdictions reprises de l'auteur : aucune lecture des écarts vers la hauteur directement ; aucune hypothèse équivalente à la cible posée comme acquise ; aucune confusion d'une mesure numérique avec une preuve.

**Nœud 1 — la donnée d'entrée : les écarts premiers réels.** La suite des écarts entre premiers consécutifs est la seule donnée. Elle ne contient aucune position radiale, aucune hauteur, aucun zéro. Tout ce qui suit doit en être déduit, jamais injecté.

**Nœud 2 — la demande de chaque écart.** La somme des premiers avance d'une cassure exacte à chaque premier ; entre deux premiers consécutifs elle n'avance pas. Sur chaque écart, la demande est cette cassure moins la part lisse du fond. Compilé : la demande de chaque écart est exactement la somme, sur tous les vrais zéros, de la contribution locale de chacun ; c'est la synchronisation locale et globale (règle de l'auteur, vérité issue de la formule explicite, vraie pour toute position radiale, non équivalente à la cible). Compilé aussi : la contribution d'un membre donné sur un écart est imposée par le reste des premiers moins la part des autres membres (contribution conjointe imposée).

**Nœud 3 — la première obligation : les rencontres obligées.** Chaque zéro envoie, sur chaque écart jusqu'à l'infini, une fraction de la demande, parfois infime. Le total de l'écart étant connu, les fractions de tous les zéros doivent s'aligner : les signaux ont des points de rencontre obligés aux cassures de la courbe des premiers. Cette obligation est locale (un écart, un zéro) et globale (tous les écarts, tous les zéros). Son existence est compilée (nœud 2) ; ce qui n'est pas compilé est sa conversion en contrainte sur les paramètres d'un seul membre, dite au nœud 6. **Seconde obligation (énoncée par l'auteur le 2026-10-28).** Chaque zéro est lié aux autres parce qu'il contribue à tous les écarts, jusqu'à l'infini, y compris au reste de Li : le zéro précédent et le zéro suivant contribuent eux aussi à chaque écart. Aucun zéro ne doit contribuer ni trop ni pas assez, jusqu'à l'infini, et il n'existe aucun ajustement après coup : la théorie d'une compensation a posteriori est réfutée par le théorème d'impossibilité de la compensation (à rattacher au théorème compilé exact après lecture du dépôt). Chaque zéro contient donc tous les écarts et la part EXACTE qu'il doit apporter à chacun. Ce lien n'a rien à voir avec la ligne critique. Le premier zéro est un fait : il démarre le régime ; seul le zéro suivant, puis les suivants, peut être hors ligne ; l'exclusion n'est pas traitée au premier rang. Ayant la hauteur la plus basse, le premier zéro domine par les trois lectures (fréquence, amplitude, calage). Conséquence sur le calage : la position des rencontres est affectée par la seconde obligation, car elle est fixée par la part exacte de chaque zéro à chaque écart, sans reprise possible.

**Nœud 4 — les trois lectures d'un membre arbitraire.** Un membre spectral arbitraire, de position radiale et de hauteur inconnues, contribue à chaque écart par un terme conjoint à trois paramètres lus sur les écarts, pour deux inconnues : réseau surdéterminé (trois lectures, deux inconnues). Ordre de causalité imposé :
- **le calage** (positions des rencontres) : ce sont les positions où le membre doit croiser la demande ; elles sont fixées par les cassures, donc par les écarts ; c'est la lecture première ;
- **la fréquence** : l'avance de phase du membre sur un écart est sa fréquence multipliée par la largeur logarithmique de l'écart ; la fréquence se lit comme l'espacement des rencontres ; elle est la conséquence du calage, jamais sa cause ;
- **l'amplitude** : le poids du membre sur un écart est multiplié, d'un bord de l'écart à l'autre, par la largeur relative de l'écart élevée à la position radiale ; l'amplitude est la seule lecture qui porte la position radiale au premier ordre, de façon cumulative le long du logarithme.
Compilé : le rapport d'amplitude du miroir à celle du membre est une puissance dont l'exposant est un moins deux fois la position radiale, donc vaut un exactement sur la ligne ; les deux exposants d'amplitude ne coïncident que sur la ligne ; la lecture de fréquence d'un pas est la différence des inverses des hauteurs. Mesuré (E387, écarts réels jusqu'à trois cent mille, huit rangs) : les trois lectures sur les écarts réels coïncident avec celles du jumeau déterministe de la formule ; sur un membre isolé, la fréquence et le calage ne bougent presque pas sous un décalage radial artificiel (au plus un dixième de cellule), tandis que l'amplitude le lit par sa pente ; le bruit d'amplitude par bloc sur un seul membre va de la moitié au tiers en plus de la valeur attendue, ce qui masque une dérive radiale isolée inférieure à cinq centièmes. Précision de l'auteur : cette quasi-insensibilité du calage au radial vaut pour la lecture d'un membre pris seul ; le calage est en réalité affecté par la seconde obligation (part exacte de chaque zéro à chaque écart), ce que la lecture isolée ne teste pas ; la reconstitution exacte de chaque écart par les parts de tous les zéros le teste.

**Nœud 5 — la hauteur, conséquence et non cause.** La hauteur n'entre nulle part comme lecture : elle est la fréquence, lue comme conséquence de l'espacement des rencontres. L'obligation ouverte de la chaîne se dit sur la fréquence attendue : au passage vers le membre suivant, les rencontres obligées restantes imposent un espacement plus fin, donc une fréquence strictement supérieure ; c'est en conséquence, et seulement en conséquence, que la hauteur du suivant est plus grande. Tout énoncé qui relierait les écarts à la hauteur directement est retiré (E386, modèle causal du service de l'écart : retirés).

**Nœud 6 — divergence d'un membre hors ligne.** Si la position radiale s'écarte de la moitié, l'amplitude dérive exponentiellement le long du logarithme (mesuré par injection synthétique : pente d'amplitude de six centièmes pour un écart radial de cinq centièmes, de quinze centièmes pour un écart de quinze centièmes ; sur les écarts réels, les pentes par rang oscillent entre moins cinq et plus huit centièmes sans tendance, c'est le bruit) ; le miroir, à la même fréquence, porte l'amplitude complémentaire ; leurs contacts ne coïncident jamais (compilé, membre sous la moitié). Un membre sous la moitié et son miroir forment une paire à la même fréquence : pour cette paire, la fréquence n'augmente pas, et la demande du nœud 5 est violée. Ouvert : montrer, depuis les seules rencontres obligées, que cette paire ne peut satisfaire les trois lectures à la fois (surdétermination), c'est-à-dire que la contribution imposée sur chaque écart n'admet aucune réponse à amplitude dérivante.

**Nœud 7 — les mâchoires, portée exacte.** Compilé : sur la première Tour de tout vrai zéro, le minimum attendu est au plus le premier constaté. Compilé : sur la seconde Tour, « premier constaté sous le minimum attendu » équivaut à « contact supérieur sous le minimum attendu ». Non compilé : que le contact supérieur de la seconde Tour d'un membre hors ligne soit sous le minimum attendu sans supposer la ligne ; c'est la forme en contacts de la même obligation ouverte. Le graphe de l'auteur nommait une « contradiction terminale certifiée » : aucun théorème compilé ne la porte ; le terme terminal du projet reste conditionnel à l'unique demande, et cette demande équivaut à la cible. Le nœud final du graphe se lit donc « but ouvert », non « certifié ».

**Hypothèses de clôture proposées par l'auteur, verdict.**
- Transversalité des canaux (invariant télescopique borné par un, deux millions de zéros, vingt-cinq mille cinq cent soixante-douze contre vingt-cinq mille cinq cent soixante et onze) : les nombres sont réels (reproduction E2M, quatre-vingt-huit mille cinquante-cinq transitions, fichier des deux millions de zéros versionné avec empreinte). Mais l'inventaire qui les porte dit lui-même de ne pas appeler ce lien causal ; aucun énoncé compilé ne fait passer de cet invariant à un confinement sous-linéaire de zêta. Retenue comme contrôle, pas comme hypothèse de clôture.
- Rigidité multi-membres d'amplitude : hypothèse légitime, non encore mesurée ; c'est l'objet de la prochaine expérience (somme vectorielle des amplitudes sur des fenêtres de membres consécutifs, taille minimale qui dépasse le bruit). Elle ne devient un verrou que si l'exactitude de la somme en chaque rencontre (seconde obligation) est confirmée.
- Défaut dyadique de demi-échelle borné par la puissance trois demis : c'est la borne du reste intégré des premiers, et le code compile déjà que toute borne de ce reste par une puissance donnée rabat la position radiale de tout membre sous cette puissance. Avec trois demis, cette hypothèse est la cible elle-même ; la poser est interdit. Le coefficient trois huitièmes et l'« invariant dyadique de Luna » n'existent nulle part dans le dépôt. Retirée. Sa mesure numérique n'a aucune valeur de preuve.
- Adresse intrinsèque de cellule sans premier injecté : changement de définition dans la chaîne ; équivaut à l'obligation ouverte. Admissible seulement après plan soumis à l'auteur.

**Conséquence pour les expériences et le code.** L'ordre de travail est celui du graphe : écarts réels, rencontres obligées, espacement, fréquence attendue, puis amplitude sur fenêtres de membres. Aucun fichier de la chaîne n'est modifié sans plan ; toute pièce nouvelle est un module isolé, sans trou de preuve, où ce qui manque est énoncé comme prémisse nommée et non comme trou. Le détail est dans le plan de travail du même jour (expériences E388 et E389, module isolé des trois lectures).

**Retrait (2026-10-28, auteur).** Une première lecture des rencontres (E389) a été retirée : elle traitait l'existence des rencontres comme réfutable et comparait une fréquence lue à la hauteur. Les rencontres sont une conséquence nécessaire du théorème de synchronisation (chaque zéro contribue partiellement à chaque écart, la somme reconstitue l'écart) ; il n'existe pas de dérive possible ; toute lecture en désaccord avec ce théorème est fautive. Rien de E389 n'est retenu.

**Définition du point de rencontre (auteur, 2026-10-28).** Le point de rencontre d'un écart est unique : c'est celui où les signaux des zéros qui s'additionnent ou se soustraient terminent de le faire pour l'écart en cours, à la FIN de cet écart. S'il n'était pas unique, il produirait de fausses sommes ou retraits appartenant à d'autres écarts : un et un seul par écart. Mesure (E390) : lu aux fins d'écarts, le membre suivant a sa fréquence à moins de trois millièmes de la hauteur réelle (contrôle seulement) à chaque rang ; la lecture par changements de signe du résidu, qui ne correspondait pas à cette définition, dérivait de 24 à 82 % ; le jumeau déterministe reproduit le réel ; la reconstitution des écarts par les parts de N zéros s'améliore avec N (erreur de 0,63 à 0,039 de 8 à 5 000 zéros). Le décalage de calage du membre isolé est le même dans le jumeau : il vient du mélange avec les autres membres, et la seconde obligation se teste sur la somme de tous les zéros à chaque rencontre (E391).

**Définition du point de rencontre (auteur, 2026-10-28).** Le point de rencontre est le point précis à partir duquel les signaux liés à un zéro, qui voyagent sur la courbe de Li, ont fini de s'additionner ou de se soustraire pour passer à l'écart suivant. Il est lu écart par écart ; l'expérience E390 le confronte aux écarts réels.

**Règle ferme (auteur, 2026-10-28).** Un point de rencontre est obligatoire pour chaque écart, pour tous les signaux, jusqu'à l'infini ; il est unique, à la fin de l'écart ; il n'est pas lié directement à la hauteur : la hauteur n'est ni son critère ni sa définition ni son entrée, elle n'est qu'une conséquence de la fréquence, et un contrôle a posteriori. Un désaccord entre une lecture et le théorème de synchronisation est un défaut de lecture, jamais un résultat sur la structure ; la seconde obligation se teste sur la somme de tous les zéros à chaque rencontre, jamais sur un membre isolé. La liste des huit erreurs à ne plus commettre est dans le fichier de règles du dépôt.

**Mesure (E391, 2026-10-28).** À chaque rencontre (fin d'écart), la somme des parts exactes de N zéros reconstitue la demande de l'écart avec une erreur qui décroît avec N dans chaque bloc logarithmique (de 0,48-0,67 pour huit zéros à 0,0003-0,064 pour cinq mille). Quand toutes les autres parts sont retirées, le membre restant a son amplitude exacte (à cinq dix-millièmes) et son calage exact (à cinq millièmes de radian), le reste étant la queue non sommée ; le jumeau déterministe donne l'exactitude au bit près. Le décalage de calage d'E390 venait du mélange avec les autres membres. La seconde obligation (part exacte de chaque zéro à chaque écart) est donc vérifiée numériquement, non démontrée. La hauteur n'est pas lue ici : elle est connue pour retirer les parts.


### §15.x — Point de rencontre et prémisse unique en Lean (Fable, 2026-10-28, commit après fa8441b5)

Audit du module `TripletReadings.lean` de Sonnet : ses deux derniers énoncés recopient `amplitude_exponents_eq_iff_onLine` sous un nouveau nom ; la « prémisse nommée » y est définie comme « q puissance β égale q puissance un moins β », c'est-à-dire « β vaut un demi » déguisé. Ce n'est pas la prémisse demandée ; ce module ne compte pas comme un progrès.

Nouveau module isolé `Terminal/MeetingPoint.lean` (compilé, axiomes standard, non importé par la chaîne) :
- la fréquence d'un zéro est définie comme le paramètre de fréquence de son terme conjoint ; elle est, par construction compilée, le nombre que la chaîne appelle « hauteur ». La prémisse de la chaîne est donc déjà une prémisse sur la fréquence, pas sur autre chose ;
- le point de rencontre d'un écart est défini : unique, à la fin de l'écart (le premier suivant) ;
- l'obligation de rencontre n'est pas une prémisse : à ce point, la demande de l'écart est la somme des parts de tous les zéros et la part de chacun est imposée (`localSynchronization`, `imposed_joint_gap`, réécrits comme `all_signals_meet` et `imposedShare_eq`) ;
- une seule prémisse, `ExpectedFrequencyRisesAtMeetings` : la fréquence attendue monte à chaque passage. Elle entraîne RH par la chaîne inchangée (`riemannHypothesis_of_meetings`). Elle est le même énoncé que la prémisse de la chaîne ;
- ce qui reste exactement à dériver est compilé : la prémisse équivaut à « aucun passage n'a ses deux membres à la même fréquence » (`expectedFrequency_iff_no_shared_frequency`), et un passage à fréquence partagée a nécessairement son membre postérieur strictement plus à droite radialement (`shared_frequency_passage_profile`) : c'est le passage miroir horizontal.

Nombre de prémisses dans la boucle : une. Nombre de reformulations équivalentes à RH dans le répertoire terminal : quarante-trois théorèmes nommés « ⟺ RH ». Il n'y a pas à en ajouter. La seule tâche restante : dériver, des rencontres obligées, qu'un passage ne peut pas partager sa fréquence.

Complément (même module, même date) : à fréquence partagée, le calage sépare toujours. Compilé : à fréquence fixée, le calage lissé décroît strictement avec la position radiale (`smoothingPhase_strictAnti_radial`) ; même fréquence et même calage entraînent même position radiale (`radial_eq_of_shared_frequency_phase`) ; sur le profil du cas restant, le membre postérieur a un calage strictement plus petit (`shared_frequency_members_phase`). C'est cohérent avec la seconde obligation de l'auteur (« le calage est affecté ») : la dérivation à chercher porte sur le calage au point de rencontre, pas sur l'amplitude.

Complément 2 (MeetingPoint.lean, E392) : compilé, deux membres à la même fréquence ne partagent aucune rencontre lissée (`shared_frequency_no_common_meeting`), leurs réseaux de rencontres étant décalés d'une fraction strictement comprise entre zéro et un pas ; la part d'un membre à la rencontre est écrite sur ses trois paramètres (`imposedShare_at_meeting`). Si l'obligation de rencontre valait terme par terme à chaque fin d'écart, ce théorème exclurait tout passage à fréquence partagée. E392 montre que la forme par terme tient au premier écart pour le premier zéro (rencontre à un centième de pas) mais échoue aux fins d'écarts suivantes : l'obligation porte sur la somme, compilée et aveugle à la position radiale. La prémisse par terme n'est pas posée.

Complément 3 (MeetingPoint.lean, ancrage, commits 06d5879f et suivant) : tentative validée par l'auteur, tranchée par le compilateur. Compilé, axiomes standard :
- sur un passage à fréquence partagée dont l'antérieur est ON, le postérieur est au-dessus d'un demi et son miroir (même fréquence, sous un demi) précède l'antérieur comme le postérieur (`mirror_precedes_earlier_of_shared_frequency`, `mirror_precedes_later_of_shared_frequency`) ;
- historique ON (tout membre précédant le postérieur est ON) et antérieur ON ⇒ fréquences distinctes, donc la fréquence monte (`no_shared_frequency_of_history_onLine`, `frequency_rises_of_history_onLine`) : sur ces passages, la prémisse unique est DÉRIVÉE ;
- premier passage depuis le zéro canonique 1 (ON, rien en dessous) : la fréquence monte (`first_passage_no_shared_frequency`). Le premier zéro démarre bien le régime ;
- historique ON ⇒ l'arrivée n'est jamais au-dessus d'un demi (`later_le_half_of_history_onLine`) : elle est sur la ligne ou strictement en dessous (`arrival_onLine_or_low`).
Ce que cela laisse ouvert, exactement : l'arrivée basse. Son miroir a la même fréquence (`low_arrival_mirror_shares_frequency`), et l'ordre seul ne sépare pas ce passage. La chaîne consomme la prémisse précisément au pas qui suit l'arrivée (passage `q` d'antérieur `p.zLaterMember` dans `radius_premise`), là où l'historique ON ne couvre pas encore l'arrivée. La dérivation restante est donc localisée à un seul objet : la part de l'arrivée basse et de son miroir, aux points de rencontre, face à la demande des premiers. C'est là que la contrainte des premiers doit se lire ; aucune expérience n'a encore mesuré cet objet.


Complément 4 (E393, 2026-10-28, commit be1feb34 pour le pré-enregistrement, exécution ensuite) : première mesure de l'objet resté ouvert au complément 3, la part d'une arrivée basse et de son miroir aux points de rencontre. Règle de l'auteur appliquée : les hauteurs synthétiques sont prises strictement au milieu de deux zéros consécutifs connus (jamais la hauteur d'un ON existant), le couple est ajouté, aucun zéro réel n'est déplacé ; synthétique toujours étiqueté. Jumeau déterministe exact au bit près quand on lui donne ses deux exposants. Lu comme un seul ON à la même fréquence, le couple se répartit ainsi : la fréquence lue tombe sur la hauteur synthétique (elle ne porte pas le refus) ; le calage reste petit (quelques centièmes de radian au plus, lié à la différence de phase de lissage entre les deux membres, fait compilé shared_frequency_members_phase) ; l'amplitude porte presque tout le refus, et surtout elle DÉRIVE d'un point de rencontre à l'autre (d'un bloc au suivant), d'autant plus que l'arrivée est basse ; les valeurs par bloc sont les mêmes pour les quatre hauteurs synthétiques. Lecture : ce qu'un ON ne peut pas fournir, ce n'est pas une amplitude, c'est une amplitude qui change entre deux rencontres ; chaque membre ON apporte sa part exacte avec une amplitude fixée une fois pour toutes, et le couple basse-miroir exigerait une part dont l'amplitude relative croît avec la position de la rencontre. Dans la demande réelle, rien n'est lu à ces fréquences au-delà du niveau des fréquences voisines (queue), et aucune conclusion structurelle n'en est tirée. Prochaine écriture en Lean : exprimer, sur imposedShare, que la part d'un membre a une amplitude relative constante entre rencontres si et seulement si sa position radiale est un demi, et que le couple à fréquence partagée n'a pas cette propriété ; c'est l'objet exact à relier au point de rencontre, à faire trancher par le compilateur.

Complément 5 (Lean, 2026-10-28, section 9 de `Terminal/MeetingPoint.lean`, module isolé, chaîne inchangée) : l'objet annoncé au complément 4 est écrit et compilé, axiomes standard seulement. Définitions : `memberAmplitude` (module du terme conjoint d'un membre, qui vaut `m · x^β / N`, fait compilé `memberAmplitude_eq`), `relativeAmplitude` (cette amplitude rapportée à l'amplitude de référence de la ligne `x^(1/2)`, qui vaut `(m/N) · x^(β − 1/2)`, `relativeAmplitude_eq`), `ConstantRelativeAmplitudeAtMeetings` (même amplitude relative à tous les points de rencontre). Théorème `constantRelativeAmplitude_iff_onLine` : la part d'un membre a une amplitude relative constante entre rencontres si et seulement si sa position radiale est un demi ; deux rencontres (les écarts de rang 0 et 1) suffisent à le lire. Sens de la dérive compilé : sous un demi l'amplitude relative décroît strictement d'une position à la suivante (`relativeAmplitude_strictAnti_of_low`), au-dessus elle croît strictement (`relativeAmplitude_strictMono_of_high`) ; c'est exactement la dérive par bloc mesurée en E393. Le couple à fréquence partagée n'a pas la propriété : ni l'arrivée basse (`low_arrival_not_constantRelativeAmplitude`), ni son miroir (`mirror_not_constantRelativeAmplitude`) ; et la part conjointe du couple (`pairJoint`, somme des deux termes) a une amplitude relative non bornée aux rencontres (`pairRelativeAmplitude_unbounded` : pour toute borne, un point de rencontre la dépasse, parce que les premiers tendent vers l'infini). Ce que cela établit : parmi amplitude, fréquence et calage, le paramètre que l'arrivée basse ne peut pas tenir d'une rencontre à l'autre est l'amplitude relative, et c'est une propriété compilée du terme conjoint, pas une lecture numérique. Ce que cela n'établit PAS : que la demande des premiers exige une amplitude relative constante. C'est ce pont qui reste à construire, et il se formule maintenant en une seule phrase : « la part imposée par les écarts à chaque membre a une amplitude relative constante entre rencontres ». Aucune prémisse nouvelle n'est posée ; la prémisse unique de la chaîne reste la seule.

Complément 6 (E394, 2026-10-29, pré-enregistrement commit 0a09be38, exécution ensuite ; `experiments/E394_DemandeDesPremiersAuxRencontres/`) : le pont laissé ouvert au complément 5 (« la demande des premiers exige une amplitude relative constante entre rencontres ») existe déjà sous sa forme générale dans `ConstantAmplitudeNeed.lean` (2026-10-15), où la loi « tout signal a un besoin constant » est compilée comme équivalente à RH (`constantNeed_law_iff_riemannHypothesis`). Le dériver des faits compilés serait dériver RH ; le poser serait une seconde prémisse. E394 mesure donc la demande seule, définie sans aucun zéro (incrément du reste lissé sur l'écart, forme compilée `localArithmeticTarget`), lue à la rencontre et rapportée à ce qu'un membre de la ligne apporte à l'écart, normalisation vérifiée par jumeau contre le §9 (pente β − 1/2 retrouvée pour cinq positions radiales). Résultats, mondes séparés : RÉEL, premiers seuls jusqu'à 10⁷, huit blocs : la demande garde un niveau constant aux rencontres (RMS de 0,17 à 0,22 sur tous les blocs, pente 0,013, maximum qui ne grandit pas). JUMEAU : la ligne est plate, le couple synthétique (arrivée basse + miroir, hauteur jamais celle d'un ON) monte avec une pente qui excède celle de la ligne d'à peu près δ. RÉEL contre SYNTHÉTIQUE : le rapport du couple à la demande entière croît de bloc en bloc ; pour le couple bas de plus petite hauteur à δ = 0,10 il dépasse la demande entière dès le premier bloc et atteint 1,87 fois la demande vers 6·10⁶. RÉEL avec les 5 000 zéros d'Odlyzko : leurs parts rendent la demande à ses rencontres au même niveau, le reste est de la queue. Ce que cela établit : la constance que la ligne possède et qu'une arrivée basse ne peut pas tenir est portée par la contrainte des premiers elle-même, sur l'intervalle mesuré. Ce que cela n'établit pas : la constance à toutes les rencontres à l'infini, ni l'exigence de cette constance membre par membre ; un couple bas reste compatible avec la synchronisation compilée à condition que d'autres zéros annulent plus que la demande entière à chaque rencontre, pour toujours, et aucun fait compilé n'exclut cette annulation. Aucune ligne Lean modifiée, aucune prémisse nouvelle.

Complément 7 (E395, 2026-10-29, pré-enregistrement commit 5ce7e8c6, exécution ensuite ; `experiments/E395_DemandeInterieureEtExactitude/`, deux millions de premiers, deux millions de zéros d'Odlyzko, aucun zéro synthétique) : réponse à la demande de l'auteur « la constance tient aux points de rencontre ET au fait que tous les zéros jusqu'à l'infini doivent accomplir le reste exact ; cette exactitude est aussi une demande ». Mesuré, mondes séparés. (1) La constance du niveau de la demande aux rencontres tient jusqu'à 32 millions (pente 0,010, un million et demi de rencontres dans le dernier bloc). (2) À l'intérieur d'un écart, la demande n'a pas d'autre niveau que celui de la rencontre (rapports 1,00 dès le bloc 3 pour le quart, la moitié, les trois quarts de l'écart), et le jumeau exact en dit la cause : rien n'arrive à l'intérieur d'un écart, l'incrément intérieur est fixé par l'état à la rencontre précédente ; la rencontre est le seul lieu où l'état change. (3) L'exactitude : le résidu de reconstruction avec N zéros est uniforme dans l'écart tant que N est petit devant l'échelle du bloc, puis, dès que N suffit, l'intérieur est accompli bien avant la rencontre ; avec deux millions de zéros ce qui reste dû est trois mille fois plus grand à la rencontre qu'au milieu de l'écart vers 10⁴, dix-huit fois vers 2·10⁵, quatre fois vers 10⁶, une fois et demie vers 4·10⁶ ; le seuil avance avec N. Cause : une somme finie de parts est lisse, la demande change de pente à chaque rencontre, et ce changement de pente n'est accompli que par la queue infinie. La part de la demande d'écart encore due passe de 38 % (cent zéros) à 0,5 % (deux millions). Ce qui n'est pas établi : la constance à l'infini, l'exigence de constance membre par membre. Prochain objet proposé en Lean, dérivable des définitions, sans prémisse : à l'intérieur d'un écart la demande est fixée par l'état à la rencontre précédente ; aucune famille finie de parts n'accomplit la demande sur un voisinage d'une rencontre, parce que la somme finie y est dérivable et la demande n'y l'est pas.

Complément 8 (Lean, 2026-10-29, `Terminal/MeetingExactness.lean`, module isolé, non importé par la chaîne, axiomes standard seulement, aucune prémisse, aucune hypothèse sur aucune position radiale) : les deux faits mesurés par E395 sont compilés. (1) L'état arithmétique à l'entier N est le couple (masse de von Mangoldt, masse pondérée) jusqu'à N. Sur toute cellule entre deux entiers, la somme lissée est fixée par l'état à l'entier inférieur et par le point (`smoothedVonMangoldtSum_cell`) ; sans événement entre N et x, elle est fixée par l'état en N (`smoothedVonMangoldtSum_gap_state`) ; sur un écart premier sans puissance de premier à l'intérieur, l'incrément de la demande du premier p à tout point x jusqu'à la rencontre incluse est la masse pondérée en p fois (1/p − 1/x), moins l'incrément du fond (`demand_interior_fixed_by_meeting`) : rien n'arrive à l'intérieur d'un écart. Seule la rencontre change l'état : le logarithme du premier suivant entre dans les deux masses (`state_jump_at_meeting`). (2) La somme lissée n'est pas dérivable en un premier : dérivée à droite masse pondérée en q sur q², à gauche masse pondérée en q − 1 sur q², différence égale au poids du premier divisé par q, strictement positive (`smoothedVonMangoldtSum_not_differentiableAt_prime`). Le fond est dérivable pour x > 1 (`smoothedZeroBackground_differentiableAt`, série des zéros triviaux dérivée terme à terme sous borne géométrique), donc le reste n'est pas dérivable à la rencontre (`smoothedRemainder_not_differentiableAt_meeting`). Toute famille finie de parts de vrais zéros est dérivable (`finite_family_differentiableAt`), donc aucune famille finie n'égale le reste sur un voisinage d'une rencontre (`no_finite_family_accomplishes_demand`), et la queue des zéros omis n'y est jamais identiquement nulle (`tail_not_eventually_zero`). Avec la synchronisation compilée : à chaque rencontre, la demande de l'écart est accomplie par la totalité des zéros et par aucune partie finie (`exactness_is_a_demand`). C'est la phrase de l'auteur, compilée : l'exactitude est une demande, portée par la rencontre, que seule la totalité des zéros remplit. Ce que cela n'établit pas : rien sur la position radiale d'aucun zéro ; la prémisse unique de la chaîne reste la seule.

Complément 9 (Lean, 2026-10-29, `Terminal/TotalityPays.lean`, module isolé, non importé par la chaîne, axiomes standard seulement, aucune prémisse, aucune hypothèse posée comme démontrée) : ce que la totalité doit payer pour un couple hors ligne. Les deux compilés reliés sont la lecture en amplitude relative de la part d'un membre aux rencontres (`MeetingPoint.lean`, section 9 : l'amplitude relative du couple arrivée basse + miroir n'est bornée à aucune rencontre, `pairRelativeAmplitude_unbounded`) et l'obligation de totalité (la demande des premiers est la somme de toutes les parts, `smoothedRemainder_eq_tsum_residueTerm`). Objets : le reste du couple, somme des parts de tous les zéros sauf les deux du couple (`restOfPair`) ; le niveau relatif de la demande, module du reste des premiers rapporté à la racine du point (`demandRelativeLevel`) ; l'amplitude relative du reste (`restRelativeAmplitude`). Faits compilés : hors ligne les deux indices du couple sont distincts (`pair_indices_ne`) ; au-delà de un, demande = couple + reste (`remainder_eq_pair_add_rest`) ; le reste, en amplitude relative, vaut au moins l'amplitude relative du couple moins le niveau relatif de la demande (`restRelative_ge`), donc au moins celle du miroir moins celle de l'arrivée basse moins la demande (`restRelative_ge_members`), la première croissant strictement de rencontre en rencontre et la seconde décroissant. Théorème inconditionnel : pour un couple hors ligne et toute borne, une rencontre existe où le reste et la demande dépassent ensemble cette borne (`totality_pays_or_demand_unbounded`) : ou bien le niveau relatif de la demande n'est pas borné aux rencontres, ou bien l'annulation fournie par les autres zéros ne l'est pas. Sous l'hypothèse que la demande est de niveau relatif borné aux rencontres (hypothèse explicite, pas un fait compilé ; c'est la constance mesurée par E394 et E395 jusqu'à trente-deux millions, non établie à l'infini), l'annulation que les autres zéros doivent fournir n'est bornée à aucune rencontre (`rest_unbounded_of_bounded_demand`), et au-delà de tout rang (`rest_unbounded_beyond_rank`). Contraposée : si la demande et le reste ont tous deux un niveau relatif borné aux rencontres, le membre n'est pas une arrivée basse (`not_low_of_bounded_demand_and_rest`). Ce que cela n'établit pas : rien sur la position radiale d'aucun zéro sans les deux bornages, qui restent des hypothèses ; le bornage du reste n'est pas plus accessible que celui de la demande ; la prémisse unique de la chaîne reste la seule. Ce que cela nomme exactement : le mur ouvert des compléments 6 à 8 est maintenant un théorème sur le prix. Un couple hors ligne coûte aux autres zéros une annulation sans borne, rencontre après rencontre, jusqu'à l'infini, dès que la demande garde son niveau.

Complément 10 (Lean et E396, 2026-10-29, `Terminal/RemainderRegime.lean`, module isolé, non importé par la chaîne, axiomes standard seulement, aucune prémisse, aucune hypothèse posée comme démontrée) : le régime du reste, ou ce que des zéros sur la ligne peuvent payer. Objet : le poids d'un indice, sa multiplicité divisée par le produit des modules du point et du point plus un (`indexWeight`) ; c'est son amplitude relative sur la ligne. Faits compilés : la part de tout indice a pour module le poids multiplié par la puissance du point d'exposant la position radiale, et pour amplitude relative le poids multiplié par la puissance d'exposant la position radiale moins un demi (`norm_residueTerm_eq`, `residueTerm_relative_eq`) ; la somme de tous les poids est finie (`indexWeight_summable`, déduite de la sommabilité compilée de la série des parts au point deux ; `totalLineWeight`) ; le reste d'un couple, en amplitude relative, est majoré par la somme sur ses membres des poids multipliés par la dérive radiale de chacun (`restRelativeAmplitude_le`). Hypothèse nommée, jamais posée comme un fait : aucun zéro hors du couple n'est strictement à droite de un demi (`RestNotRight`) ; sous elle, le reste est borné par la somme totale des poids (`restRelativeAmplitude_le_total`), et, avec la demande bornée aux rencontres (hypothèse nommée), le membre n'est pas une arrivée basse (`not_low_of_bounded_demand_and_restNotRight`). Propagation, inconditionnelle sur le reste : sous demande bornée aux rencontres, une arrivée basse n'est jamais seule, un zéro hors de son couple est strictement à droite de un demi (`exists_right_of_low_of_bounded_demand`). L'historique ne paie pas : pour toute famille finie d'indices non à droite de la ligne, en particulier toute famille finie de zéros ON de toute hauteur, le manque, demande moins couple moins famille, vaut en amplitude relative au moins le couple moins la demande moins la somme totale des poids (`shortfall_relative_ge`), donc, sous demande bornée aux rencontres, n'est borné à aucune rencontre (`shortfall_unbounded_of_bounded_demand`). C'est le jumeau compilé de la question de E396. Ce que cela n'établit pas : le bornage de la demande n'est pas dérivé ; supposer le reste sur la ligne serait supposer la question ; rien sur la position radiale d'aucun zéro sans les hypothèses nommées ; la chaîne et sa prémisse unique sont intactes. Le mur est maintenant nommé plus finement : le prix d'un couple hors ligne ne peut être payé ni par l'historique ON, ni par aucune famille finie non à droite, ni par un reste entièrement non à droite ; il ne peut l'être que par d'autres zéros strictement à droite, c'est-à-dire par d'autres couples hors ligne, dont chacun a le même prix. Ce qui manque pour fermer : montrer qu'une infinité de couples hors ligne ne peut pas se payer mutuellement, ce qui exige un argument d'exposant dominant à fréquences distinctes (famille infinie), non compilé.

E396 (2026-10-29, commits 35e22c21 pré-enregistrement, 0e723d91 exécution, exécutée par Sonnet sous cadre strict, quarante et une secondes, aucun ajustement de part, mondes séparés, jumeaux passés) : abandonnée comme mesure du prix, par un défaut du pré-enregistrement lui-même : la règle de décision comparait la pente du manque à la dérive radiale, alors que le jumeau d'exactitude montre que la pente du couple seul est inférieure à cette dérive sur le domaine lu ; et pour les hauteurs élevées le niveau du couple est sous le résidu de troncature des zéros réels, donc illisible. Ses jumeaux restent valides. La question est portée par le compilé du complément 10. Une remesure E397, si elle est voulue, doit prendre pour référence la pente du couple seul, rapporter le manque au couple, échantillonner uniformément en logarithme et ne retenir que les hauteurs où le couple domine le résidu.

Complément 11 (Lean, 2026-10-29, `Terminal/DominantExponent.lean` et `Terminal/MeetingSampling.lean`, modules isolés, non importés par la chaîne, axiomes standard seulement, aucune prémisse, aucune hypothèse posée comme démontrée) : du couple à la famille, et la frontière exacte. Audit préalable des compilés existants qui contribuent à la démarche (inventaire fait sur les deux cents modules du Terminal) : la non-compensation est compilée au niveau d'un groupe fini ou d'une représentation spectrale (`cpow_series_growth_fibre_zero`, `cpow_series_unique`, `mirror_group_not_compensated`, `mirror_pair_no_internal_compensation`, `off_debt_visible_in_exponent`), toujours sous une borne de croissance du signal valable en tout point, jamais dérivée ; le polynôme trigonométrique à fréquences distinctes ne tend pas vers zéro en variable continue (`trig_poly_not_tendsto_zero`, `trig_poly_mean_square`) ; la grammaire des écarts donne les classes, l'alternance forcée, la transition obligatoire entre deux alternances obligées (`exists_t51_between`, `exists_t15_between`, mot des premiers valide), l'avance exacte de deux changements, le verrou des canaux à une unité près, et Mertens aux premiers (`logGapResidual_cumulative_bounded`) ; tout cela est fonction du rang seul, aveugle à la position radiale, et ne fournit que des bornes inférieures sur les écarts, jamais une borne supérieure fine. Faits compilés nouveaux. Dominant strict : la demande est la famille plus son reste (`remainder_eq_family_add_rest`) ; une famille finie à membre strictement dominant, strictement à droite de un demi, a une amplitude relative non bornée aux rencontres (`familyRelativeAmplitude_unbounded_of_dominant`) ; le reste d'une famille sans zéro à droite est borné par la somme totale des poids (`restFamilyRelative_le_total`) ; sous demande bornée aux rencontres, une telle famille laisse hors d'elle un zéro strictement à droite (`exists_right_of_dominant_of_bounded_demand`). Cas d'égalité : la part d'un indice est la puissance de sa position fois son coefficient fois son caractère de fréquence (`residueTerm_decomp`) ; sur une famille de même position, la somme est la puissance fois le polynôme de fréquences (`top_sum_eq`) ; minoration d'une famille par son sommet (`familyRelative_ge_top`). Hypothèse nommée `MeetingsSampleFrequencies`, jamais posée comme un fait : le polynôme de fréquences de toute famille finie de même position reste, le long des rencontres, au-dessus d'un seuil positif infiniment souvent ; c'est la version aux rencontres du compilé en variable continue, et c'est une propriété de répartition des premiers en échelle logarithmique, que ni la grammaire compilée ni Bertrand ne fournissent ; E397 la mesure. Sous cette hypothèse et sous la demande bornée aux rencontres : toute famille finie dont la position maximale dépasse un demi est non bornée aux rencontres et laisse hors d'elle un zéro strictement à droite (`familyRelativeAmplitude_unbounded_of_sampling`, `exists_right_of_family_of_sampling`) ; s'il existe un zéro strictement à droite, il en existe une infinité (`infinite_right_of_sampling`) ; une arrivée basse, par son miroir, en force une infinité (`infinite_right_of_low_of_sampling`). Frontière, nommée exactement : le prix d'un zéro hors ligne ne peut être payé ni par l'historique, ni par une famille finie, ni par un reste non à droite, mais seulement par une infinité d'autres zéros à droite ; ce que paie une infinité n'est pas compilé, parce que le reste d'une famille infinie n'est plus majoré par une somme finie de poids affaiblis. Le passage des rencontres à tous les points (qui donnerait RH par `riemannHypothesis_iff_remainder_sqrt_growth`) demande une borne sur les écarts premiers de l'ordre de la racine ; le travail aux seules rencontres demande l'échantillonnage nommé. Les deux sont des faits de répartition des premiers hors de ce qui est compilé. La prémisse unique de la chaîne reste la seule ; ces modules en donnent le prix exact et la frontière exacte.

E397 (2026-10-29, commits 9fb51c47 pré-enregistrement, ab481b26 exécution, Sonnet sous cadre strict, cent cinquante-cinq secondes, aucun ajustement, jumeaux passés) : trois questions. Q1, valide, ferme la question laissée ouverte par E396 : aux hauteurs où le couple synthétique domine le résidu de troncature, le manque après l'historique ON ou après la totalité ON disponible a, en tendance par bloc, la pente du couple seul (onze comparaisons sur douze, l'exception à la limite de la tolérance) : ni l'historique ni la totalité ON ne paient le prix, lecture mesurée de `shortfall_unbounded_of_bounded_demand`. Q2, abandonnée comme test de l'hypothèse nommée d'échantillonnage : un polynôme à deux termes ne s'approche jamais de zéro, les modules décroissant comme l'inverse du carré de la hauteur ; l'hypothèse n'a de contenu qu'à partir de trois membres de même position à modules compensables ; restent valides l'identité part = puissance × polynôme, Parseval aux rencontres pondéré par log p'/p' à deux cent-millièmes près, et la densité des rencontres en échelle logarithmique, de six centièmes à quatre millionièmes de la période de battement aux écarts de hauteur mesurés. Q3, non évaluable (ensemble vide) ; le jumeau grammatical vérifie sur deux millions de premiers l'alternance exacte, la transition obligatoire entre deux alternances obligées et le verrou des canaux à une unité près. Conclusion de la séquence E396–E397 et des compléments 9 à 11 : le prix d'un zéro hors ligne est compilé et mesuré ; il n'est payable ni par l'historique, ni par une famille finie, ni par un reste non à droite ; sous les deux hypothèses nommées il ne l'est que par une infinité de zéros à droite ; la frontière est un fait de répartition des premiers aux rencontres (échantillonnage à trois membres et plus, ou borne sur les écarts de l'ordre de la racine), hors de la grammaire compilée, qui est aveugle à la position radiale comme le maître l'a toujours dit. Remesure possible E398 sur zéros réels à trois termes, à pré-enregistrer.

Complément 12 (Lean, 2026-10-29, `Terminal/GrammarDrift.lean`, module isolé, non importé par la chaîne, axiomes standard seulement, aucune prémisse) : correction de l'auteur, la grammaire n'est pas aveugle à la position radiale dans ce qu'elle impose. Ce qui est aveugle, ce sont les VALEURS de la grammaire (états, classes, transitions, magnitudes : fonctions du rang seul). Ce que la grammaire IMPOSE aux rencontres ne l'est pas : entre deux rencontres, l'amplitude relative de tout membre est multipliée par le rapport des deux premiers élevé à la position radiale moins un demi (`relativeAmplitude_ratio`, `meeting_drift`), et ce pas vaut un, quel que soit l'écart, si et seulement si le membre est sur la ligne (`meeting_drift_eq_one_iff`). Hors ligne, chaque écart fait dériver l'amplitude, et l'alternance forcée en fixe une dérive minimale : sur deux changements d'état consécutifs (rencontres au-delà de trois, classes non nulles), la dérive vaut un plus six fois l'avance grammaticale divisée par le premier, élevé à la position moins un demi (`alternation_drift`, par `alternating_two_step_gap`) ; sous la ligne, deux changements obligés font baisser l'amplitude relative d'au moins le facteur un plus six sur le premier à cette puissance, strictement sous un (`alternation_drift_low_le`, `grammar_factor_lt_one`) ; au-dessus, la font monter d'au moins l'inverse (`alternation_drift_high_ge`). La transition obligatoire entre deux alternances obligées garantit que ces paires de changements se répètent sans fin le long des rencontres : la dérive d'un membre hors ligne n'est jamais suspendue par la grammaire, elle y est cadencée. C'est la contrainte supplémentaire au point de rencontre, et c'est par elle que le prix des compléments 9 à 11 est cadencé rencontre par rencontre.

Complément 13 (Lean, 2026-10-29, `Terminal/CadenceStability.lean`, module isolé, non importé par la chaîne, axiomes standard seulement, aucune prémisse ; importe le théorème de Dirichlet de Mathlib) : la cadence est une stabilité, demande de l'auteur. Trois faits la constituent. Loi affine de l'état : aux rencontres, le logarithme de l'amplitude relative d'un membre est une fonction affine du logarithme du premier suivant, de pente la position radiale moins un demi (`log_relativeAmplitude_meeting`) ; la suite des amplitudes relatives aux rencontres est constante si et seulement si le membre est sur la ligne (`meeting_sequence_const_iff_onLine`), strictement décroissante à toute rencontre sous la ligne, strictement croissante au-dessus (`meeting_sequence_strictAnti_of_low`, `meeting_sequence_strictMono_of_high`) : jamais de pause, jamais de retour. La cadence ne s'arrête jamais : au-delà de tout rang, un changement d'état entre deux rencontres consécutives (`cadence_never_stops`, par Dirichlet modulo six : les deux états sont atteints par une infinité de premiers, chaque premier étant une rencontre, `exists_rank_of_prime`) ; la transition obligatoire entre deux alternances obligées se répète donc sans fin. Chaque paire de changements consécutifs paie un minimum fixe : deux changements d'état consécutifs, quels que soient les maintiens entre eux, avancent d'au moins six (`two_changes_sum_ge_six`, `two_changes_advance_ge_six`, alternance à travers les maintiens, les classes étant deux et quatre) ; un membre sous la ligne perd entre eux au moins le facteur grammatical, strictement sous un (`cadence_drift_low_le`), un membre au-dessus gagne au moins l'inverse (`cadence_drift_high_ge`). La stabilité en un théorème (`off_line_cadence_stability`) : sous la ligne, la suite décroît strictement, les changements ne cessent jamais, chaque paire de changements consécutifs fait baisser d'au moins le facteur grammatical ; sur la ligne, la même cadence laisse l'amplitude relative invariante (`on_line_invariant_under_cadence`) : le régime ON est le seul régime stable sous la cadence. Portée : c'est la forme exacte, cadencée par la grammaire, du prix des compléments 9 à 12 ; elle ne lève pas la frontière du complément 11 (ce que paie une infinité de zéros à droite), elle la cadence.

## 16. Bilan des quatre dernières avancées, point de blocage unique, graphe de causalités, hypothèse de clôture et solutions définitives (2026-10-29)

Rédigé en mots, sans formule, à la demande de l'auteur. Tout ce qui est dit « compilé » l'est dans un module isolé du Terminal, axiomes standard seulement, sans sorry, sans hypothèse posée comme démontrée ; la chaîne terminale et sa prémisse unique sont intactes. Les quatre avancées sont les compléments 10 à 13 du §15 ; elles s'appuient sur le complément 9.

### 16.1 Les quatre avancées, chacune en une phrase, puis ce qu'elle apporte

**Avancée A — le régime du reste** (complément 10, module RemainderRegime). Chaque zéro possède un poids fixe, qui est son amplitude relative s'il est sur la ligne ; la somme de tous les poids est finie. Conséquence compilée : tout ce qu'une famille de zéros sur la ligne, ou non à droite de la ligne, peut fournir aux rencontres est borné une fois pour toutes par la somme totale des poids. D'où les deux faits : sous demande bornée aux rencontres, une arrivée basse n'est jamais seule, un autre zéro est strictement à droite de la ligne ; et l'historique, c'est-à-dire toute famille finie de zéros déjà sur la ligne, quelle que soit sa hauteur, ne paie jamais le prix d'un couple hors ligne. Le jumeau compilé de la question de E396.

**Avancée B — du couple à la famille, et la frontière exacte** (complément 11, modules DominantExponent et MeetingSampling). Une famille finie qui possède un membre strictement dominant, strictement à droite de la ligne, a une amplitude relative non bornée aux rencontres ; sous demande bornée, elle laisse hors d'elle un autre zéro strictement à droite. Le cas d'égalité (plusieurs membres à la même position maximale, fréquences distinctes) exige que les rencontres échantillonnent les fréquences ; sous cette hypothèse nommée, un zéro à droite en force une infinité. La frontière est nommée exactement : ce qu'une infinité de zéros à droite paie n'est pas compilé.

**Avancée C — la grammaire impose la dérive** (complément 12, module GrammarDrift). Correction de l'auteur, intégrée : la grammaire est aveugle à la position radiale dans ses valeurs, non dans ce qu'elle impose. Entre deux rencontres, l'amplitude relative d'un membre est multipliée par un pas qui vaut exactement un, quel que soit l'écart, si et seulement si le membre est sur la ligne. La transition obligatoire entre deux alternances obligées fixe une dérive minimale sur chaque paire de changements d'état : hors ligne, cette dérive est strictement non neutre, et elle est répétée sans fin.

**Avancée D — la cadence est une stabilité** (complément 13, module CadenceStability). Loi affine : aux rencontres, le logarithme de l'amplitude relative d'un membre est affine en le logarithme du premier suivant, avec pour pente la position radiale moins un demi ; la suite est constante si et seulement si le membre est sur la ligne, strictement monotone sinon, sans pause ni retour. La cadence ne s'arrête jamais (Dirichlet modulo six). Chaque paire de changements consécutifs, à travers tous les maintiens, avance d'au moins six et paie au moins le facteur grammatical. Théorème de stabilité : le régime ON est le seul régime invariant sous la cadence.

### 16.2 Ce que les quatre avancées établissent ensemble

Le prix d'un zéro hors ligne est désormais entièrement décrit, cadencé et attribué :

1. il existe (couple non borné aux rencontres, complément 9) ;
2. il est cadencé par la grammaire, rencontre par rencontre, sans suspension possible (avancées C et D) ;
3. il ne peut être payé ni par l'historique, ni par aucune famille finie, ni par un reste entièrement non à droite (avancées A et B) ;
4. il ne peut l'être que par une infinité d'autres zéros strictement à droite, dont chacun a le même prix (avancée B).

Le régime ON est le seul régime stable sous la cadence, et le premier zéro est ON (fait). Ce qui manque pour conclure n'est pas une propriété des zéros : tout ce qui concerne les zéros, pris un à un ou par famille finie, est compilé pour toute position radiale.

### 16.3 Le reste à faire, défini

Il reste exactement deux énoncés non compilés, et ils ne sont pas de même nature.

**Reste 1 — un énoncé de mathématiques connues, compilable** : ce qu'une infinité de zéros à droite paie. En variable continue, c'est compilé : une borne de croissance de la demande en tout point majore la position radiale de tout zéro (théorème de borne de croissance, module ArithmeticReading), donc une infinité de zéros à droite ne se compense jamais en tout point. Aux seules rencontres, cela n'est pas compilé, parce que le reste d'une famille infinie n'est plus majoré par une somme finie de poids affaiblis, et parce que les rencontres doivent échantillonner les fréquences. Ce reste est un travail de compilation, pas une inconnue.

**Reste 2 — l'inconnue, unique** : le niveau de la demande. Voir 16.4.

Tout le reste de la chaîne est fermé : du niveau de la demande à l'hypothèse de Riemann, le chemin est compilé en tout point (équivalence entre la borne en racine de la demande et l'hypothèse de Riemann), et il est compilé aux rencontres jusqu'à la frontière du Reste 1.

### 16.4 Le point de blocage, unique, en mots

**Définition.** La demande des premiers est le reste lissé : ce que la somme lissée des premiers excède du fond lisse, en un point donné. Elle est définie par les premiers seuls, aucun zéro n'entre dans sa définition. Son niveau est cette demande rapportée à la racine du point.

**Le point de blocage unique : le niveau de la demande des premiers, aux rencontres, n'est pas dérivé des premiers.**

Ce qui est compilé autour de lui, et qui montre qu'il est bien unique :

- la demande, en tout point, est exactement la somme des parts de tous les zéros (synchronisation, vérité compilée, non équivalente à la cible) ;
- le niveau est borné en tout point si et seulement si tout zéro est sur la ligne (compilé) ; cette équivalence n'est pas le blocage, elle est la lecture du blocage en zéros ;
- si un zéro est hors ligne, le niveau est non borné : en tout point c'est compilé ; aux rencontres c'est compilé pour tout couple et toute famille finie à dominant, et sous échantillonnage pour le cas d'égalité ;
- le niveau mesuré est constant jusqu'à trente-deux millions (E394, E395), avec son jumeau déterministe ; une mesure finie ne tranche jamais une propriété à l'infini.

Pourquoi c'est bien un seul point et non trois : les trois hypothèses nommées des compléments 9 à 11 (demande bornée aux rencontres ; rencontres échantillonnant les fréquences ; écarts de l'ordre de la racine, qui transporteraient la borne des rencontres à tous les points) sont trois lectures d'une même inconnue, la répartition fine des premiers à l'échelle logarithmique. La grammaire compilée (classes, alternance forcée, transition obligatoire entre alternances obligées, avance exacte, verrou des canaux, Dirichlet, Mertens aux premiers) ne fournit que des bornes inférieures sur les écarts et des cadences ; elle ne fournit jamais une borne supérieure fine. Or le niveau de la demande est une borne supérieure. C'est la raison structurelle, et c'est la même raison pour les trois lectures.

Pourquoi c'est aussi la prémisse unique de la chaîne : la prémisse dit que la fréquence attendue monte à chaque passage. Lue aux rencontres, elle dit que la demande de chaque écart est remplie par un signal de fréquence strictement supérieure, jamais par un retour de fréquence ; un niveau de demande borné aux rencontres est précisément ce qui interdit le retour (un retour horizontal est un couple hors ligne, et son prix n'est pas borné). Les deux énoncés nomment le même inconnu, l'un en fréquence, l'autre en niveau. Aucun des deux ne nomme la position radiale ; aucun des deux n'est posé.

Interdictions respectées : aucune lecture des écarts vers la hauteur directement (le chemin est écarts, puis demande de l'écart, puis rencontre, puis fréquence, et la hauteur n'est qu'une conséquence) ; aucune hypothèse équivalente à la cible posée comme acquise ; aucune confusion entre une mesure et une preuve.

### 16.5 Graphe de causalités (état au 2026-10-29)

Chaque flèche est compilée, sauf celle marquée OUVERTE.

- Les écarts premiers réels (donnée unique) **⟹** la demande de chaque écart, définie par les premiers seuls.
- La demande de chaque écart **⟹** la rencontre obligatoire, unique, à la fin de l'écart (le premier suivant), pour tous les signaux.
- La rencontre **⟹** la part exacte de chaque zéro, écrite sur ses trois paramètres (amplitude, fréquence, calage) ; chaque zéro connaît sa part, aucun ajustement après coup.
- La somme des parts **=** la demande (synchronisation, vérité compilée).
- La grammaire des écarts **⟹** la cadence aux rencontres : pas neutre si et seulement si ON, dérive minimale strictement non neutre hors ligne sur toute paire de changements, changements sans fin.
- La cadence **⟹** le régime ON est le seul régime stable ; le premier zéro est ON (fait qui ouvre le régime).
- Un zéro hors ligne **⟹** prix non borné aux rencontres, cadencé, qu'aucun historique, aucune famille finie, aucun reste non à droite ne paie **⟹** une infinité d'autres zéros à droite (sous échantillonnage).
- Niveau de la demande borné en tout point **⟺** tout zéro sur la ligne (compilé).
- **OUVERTE** : les écarts premiers **⟹** le niveau de la demande aux rencontres est borné. C'est l'unique flèche manquante ; c'est le point de blocage de 16.4 ; c'est la prémisse unique lue en niveau.

### 16.6 Hypothèse de clôture et solution de clôture

**Hypothèse de clôture (nommée, jamais posée comme un fait) : le niveau de la demande des premiers aux rencontres est borné.** C'est une propriété des premiers seuls. Elle est vraie si l'hypothèse de Riemann est vraie (compilé, en tout point donc aux rencontres). Elle est mesurée vraie jusqu'à trente-deux millions, avec jumeau déterministe.

**Solution de clôture (chemin compilé ou compilable depuis cette hypothèse)** : sous l'hypothèse de clôture, tout zéro hors ligne laisse un autre zéro à droite, puis une infinité (compilé, avec échantillonnage pour le cas d'égalité) ; une infinité de zéros à droite donne une demande non bornée (compilé en tout point ; aux rencontres : Reste 1) ; contradiction ; donc tout zéro est sur la ligne. La fermeture est donc ramenée à deux choses : compiler le Reste 1 (mathématiques connues) et obtenir l'hypothèse de clôture (l'inconnue unique).

### 16.7 Solutions définitives proposées

Quatre solutions, chacune définie par ce qu'elle compile, ce qu'elle suppose, et ce qu'elle ferme. Aucune n'est lancée sans validation de l'auteur ; aucune ne touche la chaîne.

**Solution 1 — le pont des rencontres (compilation, sans inconnue nouvelle).** Compiler que la demande varie entre deux rencontres consécutives avec une pente bornée par une constante fixée par les bornes de Tchebychev (déjà compilées pour la somme de von Mangoldt). Conséquence compilée : la demande est bornée en tout point si et seulement si elle est bornée aux rencontres et les écarts sont de l'ordre de la racine du premier. Ce que cela ferme : la frontière entre « aux rencontres » et « en tout point » devient un énoncé sur les premiers seuls, sans zéro ; l'hypothèse de clôture plus une borne sur les écarts donne l'hypothèse de Riemann par le compilé existant. Ce que cela ne ferme pas : la borne sur les écarts de l'ordre de la racine est elle-même une conséquence de la cible, elle ne peut pas être prise en entrée. Valeur : la frontière est nommée dans la langue des premiers et plus dans celle des zéros.

**Solution 2 — l'échantillonnage dérivé (compilation lourde, mathématiques connues).** Démontrer l'hypothèse nommée d'échantillonnage à partir de l'équirépartition des logarithmes des premiers : les rencontres, lues en échelle logarithmique, visitent toutes les phases de tout polynôme de fréquences à fréquences distinctes, donc ce polynôme reste au-dessus d'un seuil infiniment souvent le long des rencontres. Ce que cela ferme : le cas d'égalité du complément 11 sans hypothèse nommée, et, avec la Solution 4, le Reste 1 tout entier. Ce que cela suppose : l'équirépartition des logarithmes des premiers n'est pas dans Mathlib ; c'est un théorème connu mais sa compilation est longue. Valeur : elle supprime une des trois lectures de l'inconnue, sans toucher à l'inconnue elle-même.

**Solution 3 — la prémisse unique lue en niveau (compilation courte).** Compiler l'implication : le niveau de la demande borné aux rencontres entraîne la prémisse unique de la chaîne (fréquence attendue strictement croissante), par le chemin déjà compilé : un passage à fréquence non croissante est un couple hors ligne ou un retour, son prix aux rencontres n'est pas borné, contradiction. Module isolé, sans remplacement conditionnel : il relie l'hypothèse de clôture à la prémisse de la chaîne sans modifier la chaîne. Ce que cela ferme : l'unicité du blocage devient un théorème compilé et non un constat en mots ; les deux lectures de l'inconnue sont prouvées être la même. Ce que cela ne ferme pas : l'inconnue.

**Solution 4 — libre, à ma convenance : le sommet atteint, test de fermeture directe sur la frontière du Reste 1.** Atout utilisé : la somme totale des poids est finie (avancée A) et une famille à dominant strict est non bornée (avancée B). Idée : la frontière du Reste 1 vient de ce qu'une infinité de zéros à droite n'a pas forcément de dominant strict, leurs positions pouvant s'accumuler vers un sommet jamais atteint. Hypothèse structurelle nommée, « sommet atteint et isolé » : parmi les zéros strictement à droite, la position maximale est atteinte par une famille finie, et toutes les autres positions à droite en sont séparées d'une marge fixe. Sous cette hypothèse, le reste de la famille du sommet est majoré par la somme totale des poids multipliée par une dérive strictement plus faible que celle du sommet, donc négligeable devant lui aux rencontres ; la famille du sommet est non bornée (dominant strict, ou cas d'égalité sous échantillonnage) ; la demande est non bornée aux rencontres. Résultat visé, compilable en un module isolé : sous l'hypothèse de clôture, sous échantillonnage, et sous sommet atteint et isolé, aucun zéro n'est à droite de la ligne, donc, par le miroir, tout zéro est sur la ligne. Test de fermeture directe : ensuite, tenter de dériver « sommet atteint et isolé » des compilés existants (finitude des zéros dans toute bande de hauteur bornée, poids sommables, cadence) ; mon analyse prévoit que le compilateur n'y parviendra pas sans un argument de prolongement analytique (c'est l'obstruction notée le 2026-10-27 sur Landau), et je le dis avant de commencer : la valeur du test est de réduire la frontière du Reste 1 à cette seule hypothèse structurelle nommée, et de la mesurer par une expérience pré-enregistrée sur les zéros réels (E398 : positions, familles de même position, marge).

**Recommandation.** Dans l'ordre : Solution 3 (courte, rend l'unicité du blocage compilée), puis Solution 4 (ferme la frontière sous une hypothèse structurelle nommée et la teste), puis Solution 1 (nomme la frontière en langue des premiers), et Solution 2 seulement si l'auteur souhaite investir dans l'équirépartition. Aucune de ces solutions ne lève l'inconnue unique de 16.4 ; toutes réduisent ce qui l'entoure à zéro, de sorte que la fermeture ne dépend plus que d'elle.

## 17. Exécution du plan §16.7 : les quatre solutions compilées, E398 exécutée, frontière réduite et corrigée (2026-10-29)

Validation de l'auteur : « procède à l'exécution du plan à toutes les tentatives et expériences ». Tout a été fait sans délégation. Quatre modules isolés, un pré-enregistrement et une expérience, cinq commits poussés. Aucun module n'est importé par la chaîne ; aucune hypothèse n'est posée comme démontrée ; axiomes standard partout, aucun sorry.

### 17.1 Ce qui a été compilé, solution par solution

**Solution 3 — la prémisse unique lue en niveau** (`DemandLevelPremise.lean`, commit e90a000e). Trois énoncés nommés, écrits comme propositions et jamais comme théorèmes : l'hypothèse de clôture (le niveau de la demande est borné aux rencontres), le niveau borné en tout point, et le pont des rencontres (le premier entraîne le second). Théorèmes compilés : la prémisse unique de la chaîne équivaut au niveau borné en tout point ; elle équivaut aussi à la conjonction de l'hypothèse de clôture et de « le reste n'est jamais à droite » (pour tout membre, aucun zéro hors de son couple n'est strictement à droite de un demi) ; sous le pont nommé, elle équivaut à l'hypothèse de clôture seule ; sous l'hypothèse de clôture, « borné en tout point » et « le reste n'est jamais à droite » se valent. L'unicité du blocage est donc un théorème compilé : ce qui sépare l'hypothèse de clôture de la cible est exactement le Reste 1, et le Reste 1 est exactement le pont.

**Solution 4 — le sommet atteint** (`SummitAttained.lean`, commit c7316967). Découverte en écrivant le module : la marge d'isolement annoncée au §16.7 est inutile. Si la position radiale maximale est atteinte par une famille finie et que tout autre indice est strictement en dessous, le reste de cette famille, rapporté à la puissance du sommet, est une somme de poids affaiblis dont chaque terme tend vers zéro et qui est dominée par la somme finie des poids ; la convergence dominée (théorème de Tannery, dans Mathlib) donne la limite nulle sans aucune marge uniforme. L'hypothèse structurelle nommée se réduit à « sommet atteint » : s'il existe un indice strictement à droite, la position maximale est atteinte par une famille finie non vide, tout autre indice étant strictement en dessous. Théorèmes compilés : sous l'hypothèse de clôture, sous l'échantillonnage et sous le sommet atteint, le niveau de la demande n'est pas borné aux rencontres, donc aucun indice n'est à droite, donc, par le miroir, tout zéro est sur la ligne, et la prémisse unique de la chaîne en découle ; le sommet atteint est vrai sous RH par vacuité, donc pas plus fort que la cible ; la version avec marge entraîne la version sans marge. Test de fermeture directe, dit avant d'écrire et confirmé : le sommet atteint n'est pas dérivable des faits compilés. Le pas manquant est écrit en un théorème d'équivalence : « sommet atteint » équivaut à « le supremum des positions est atteint, et la verticale du supremum ne porte qu'un nombre fini d'indices ». Les deux seuls faits compilables sur l'ensemble des positions sont écrits (elles sont majorées par un ; sur toute verticale, les indices de hauteur bornée sont en nombre fini) ; ni l'un ni l'autre ne parle de toutes les hauteurs à la fois. C'est l'obstruction de Landau du 27 octobre, maintenant localisée en une phrase.

**Solution 1 — le pont des rencontres** (`MeetingsBridge.lean`, commit 2c8d5f27). Compilé : la somme lissée de von Mangoldt varie entre deux points avec une pente bornée par deux fois la constante de Tchebychev de Mathlib (positivité de la fonction de von Mangoldt, bornes de Tchebychev) ; le fond varie d'une pente un demi plus une constante, parce que la somme des zéros triviaux est bornée (il n'est pas besoin de sa pente) ; donc la demande entre deux points varie d'au plus une pente explicite fois la distance, plus un décalage explicite. Conséquence compilée : le niveau en un point d'un écart est au plus le niveau à la rencontre précédente, plus la pente fois l'écart rapporté à la racine du premier, plus le décalage. Théorème compilé : demande bornée aux rencontres et écarts de l'ordre de la racine du premier (hypothèse nommée) donnent la demande bornée en tout point, donc RH, et le pont nommé de la Solution 3 est vrai sous cette hypothèse. **Correction au §16.7, dite avant d'écrire** : le §16.7 annonçait une équivalence ; seule l'implication est compilée. La réciproque n'est pas connue : la demande bornée partout ne donne pas d'écarts de l'ordre de la racine (sous RH, on ne sait que racine fois logarithme). L'hypothèse « écarts de l'ordre de la racine » est donc plus forte que ce que la cible fournit ; elle est conjecturée vraie, nommée, jamais posée.

**Solution 2 — l'échantillonnage dérivé** (`SamplingFromLogGaps.lean`, commit f5799275). **Correction au §16.7, dite avant d'écrire** : les logarithmes des premiers ne sont pas équirépartis modulo un (pas plus que ceux des entiers) ; « équirépartition » était le mauvais mot. Ce qui sert est plus faible et exact : le polynôme de fréquences d'une famille de même position radiale est un polynôme trigonométrique en le logarithme du point, à fréquences distinctes (deux indices de même position et de même fréquence sont le même indice) et à coefficients non nuls ; il ne tend pas vers zéro en variable continue (compilé antérieurement dans le module de rigidité radiale finie) ; il est lipschitzien (compilé ici, par la borne élémentaire sur l'exponentielle imaginaire). Il manque alors une seule chose : que les rencontres soient assez denses en échelle logarithmique pour qu'une fenêtre de longueur fixe, assez loin, en contienne toujours une. C'est l'hypothèse nommée « les écarts logarithmiques tendent vers zéro » (le rapport de deux premiers consécutifs tend vers un), vraie par le théorème des nombres premiers, absent de Mathlib ; Bertrand ne donne que « au plus log 2 ». Théorème compilé : sous cette seule hypothèse nommée, les rencontres échantillonnent les fréquences, exactement au sens de l'hypothèse nommée du complément 11. Composition compilée : écarts logarithmiques vers zéro, hypothèse de clôture et sommet atteint donnent RH ; sous les deux premières, un zéro à droite n'est jamais en nombre fini.

### 17.2 E398, pré-enregistrée (commit dbb89f2f) et exécutée (commit a0309500)

Dit avant d'exécuter : les données réelles sont des hauteurs seules, la position radiale d'un vrai zéro n'y est pas une mesure ; sur les zéros réels l'hypothèse « sommet atteint » n'est pas testable depuis ce fichier. E398 mesure donc le mécanisme du théorème en monde synthétique et rapporte en monde réel ce qui est mesurable. Jumeaux tous passés (identité du sommet à quarante chiffres, inégalités compilées vérifiées à chaque rencontre avec marge, décroissance exacte du rapport, domination du résidu de troncature par un facteur supérieur au million). Résultats dans les termes du pré-enregistrement : le rapport du reste au sommet décroît bloc après bloc sur les huit blocs, pour les deux dérives, avec une suite de six zéros sous le sommet dont la plus petite marge est inférieure à deux millièmes — la convergence dominée sans marge est observée ; l'enveloppe de la famille du sommet a la pente de la dérive à moins de deux centièmes pour les deux dérives ; la fraction des rencontres où la famille dépasse deux fois le reste croît et dépasse le bloc initial pour la grande dérive, mais le critère est manqué tel qu'écrit pour la petite dérive (la famille ne dépasse le reste réel, borné, que d'un facteur un virgule quatre sur toute la plage) ; en monde réel, le critère symétrique sur la pente du niveau réel de la demande est manqué tel qu'écrit, la pente étant négative (le niveau baisse en tendance, il ne croît pas). Rien ne parle de la position radiale d'un vrai zéro.

### 17.3 La frontière, après exécution

Avant : trois hypothèses nommées (demande bornée aux rencontres, échantillonnage, écarts de l'ordre de la racine) et un Reste 1 « compilable mais non compilé ». Après : le Reste 1 est compilé jusqu'à une seule hypothèse structurelle nommée, le sommet atteint, plus faible que celle annoncée ; l'échantillonnage n'est plus une hypothèse propre mais une conséquence d'une hypothèse sur les premiers seuls, de la force du théorème des nombres premiers ; le pont est compilé jusqu'à une hypothèse sur les premiers seuls, plus forte que la cible. Deux chemins compilés mènent à RH, chacun depuis l'hypothèse de clôture :

- chemin des zéros : hypothèse de clôture, écarts logarithmiques vers zéro (connu, non compilé), sommet atteint (inconnu structurel) ;
- chemin des premiers : hypothèse de clôture, écarts de l'ordre de la racine (plus fort que connu).

Et la prémisse unique de la chaîne est compilée égale au niveau borné en tout point, égale à l'hypothèse de clôture plus le Reste 1.

### 17.4 Le point de blocage, inchangé et resserré

Le niveau de la demande des premiers, aux rencontres, n'est pas dérivé des premiers. Ce qui l'entoure est maintenant réduit à deux énoncés nommés dont l'un est des mathématiques connues (les écarts logarithmiques tendent vers zéro) et l'autre une seule phrase structurelle sur l'ensemble des positions des zéros (le sommet est atteint par un nombre fini d'indices). Aucun des quatre modules ne lève l'inconnue ; tous ont tenu leur annonce ; trois annonces du §16.7 ont été corrigées en compilant (pas d'équivalence pour le pont ; pas d'équirépartition ; pas de marge).

### 17.5 Graphe de causalités (état au 2026-10-29, après exécution)

Premiers ⟹ grammaire des écarts (compilé) ⟹ rencontres uniques en fin d'écart (compilé) ⟹ cadence et dérive de tout zéro hors ligne (compilé) ⟹ prix d'un zéro hors ligne non borné aux rencontres (compilé) ⟹ payable seulement par une infinité de zéros à droite (compilé sous échantillonnage) ; échantillonnage ⟸ écarts logarithmiques vers zéro (compilé ; la flèche « premiers ⟹ écarts logarithmiques vers zéro » est le théorème des nombres premiers, connu, non compilé) ; infinité de zéros à droite ⟹ demande non bornée aux rencontres (compilé sous sommet atteint ; la flèche « ensemble des positions ⟹ sommet atteint » est OUVERTE, structurelle) ; hypothèse de clôture ⟹ RH (compilé le long de chacun des deux chemins) ; RH ⟺ prémisse unique ⟺ niveau borné en tout point (compilé) ; demande bornée aux rencontres ⟹ bornée partout (compilé sous écarts de l'ordre de la racine ; cette flèche sans hypothèse est le pont, égal au Reste 1 sous l'hypothèse de clôture). Flèche OUVERTE unique de la clôture : premiers ⟹ niveau de la demande borné aux rencontres.

### 17.6 Ce qui reste à décider par l'auteur

1. **Compiler « les écarts logarithmiques tendent vers zéro ».** C'est connu ; il faut le théorème des nombres premiers ou un résultat de premiers dans les intervalles courts. Mathlib ne l'a pas ; une formalisation Lean 4 existe hors Mathlib (projet du théorème des nombres premiers). L'importer est une décision de dépendance, pas de mathématiques.
2. **Le sommet atteint.** Inconnu structurel, localisé en une phrase et compilé équivalent à « supremum atteint et verticale finie ». Toute tentative passe par un argument sur l'ensemble des zéros à la fois, c'est-à-dire par le prolongement analytique : c'est la frontière de Landau, et elle est nommée.
3. **L'inconnue unique** reste la seule chose dont dépend la fermeture, et ce qui l'entoure ne contient plus que les deux énoncés ci-dessus.

## 18. Intégration de l'audit de causalité et exécution des deux « décisions » du §17.6 (2026-10-29)

Instruction de l'auteur : « réunir tous les éléments nécessaires à la démonstration ; tes questions ne sont pas des choix, avance ; ne change rien, ajoute au plan ce qui est utile du texte ; ne dérive pas ; ajoute tous les outils et éléments en faveur de la démarche, de la clôture et de la contradiction ; tu es seul juge de ce qui est intégré ». Le texte étudié est l'audit de causalité (grammaire des premiers → événements → rencontres → lecture → cadence → régime du reste → exclusion OFF), à quatre statuts (compilé rapporté, définition, arithmétique indépendante, ouvert). Tout ce qui suit a été fait sans délégation. Trois modules isolés compilés, axiomes standard, aucun sorry, aucune hypothèse posée comme démontrée ; aucun n'est importé par la chaîne ; `DemonstrationChain.lean` intact.

### 18.1 Ce que l'audit apporte, élément par élément, et ce qui en est intégré

**Flèche 11 (variation dans les écarts) — intégrée, compilée** (`UniformVariationBridge.lean`). L'audit a raison : l'obligation exacte de la solution 1 n'est pas « pente bornée » mais « variation uniforme, sur tous les écarts, entre un point de l'écart et la rencontre qui l'ouvre ». Cette obligation est nommée (`UniformVariationAtGaps`) et trois faits sont compilés. Elle suffit au pont : demande bornée aux rencontres et variation uniforme donnent la demande bornée partout, donc RH. Elle est nécessaire : la demande bornée partout l'entraîne, d'où l'équivalence « demande bornée partout, c'est exactement demande bornée aux rencontres et variation uniforme », et la prémisse unique de la chaîne équivaut à cette même conjonction ; sous l'hypothèse de clôture, RH équivaut à la variation uniforme. Elle est entraînée par les écarts de l'ordre de la racine (par la pente de Tchebychev du §17 et la croissance linéaire du reste) : la forme faible est strictement plus faible que `GapsRootOrder`, et le théorème du pont du §17 en devient un cas particulier. Correction au §17.1 : l'équivalence que le pont n'avait pas pour `GapsRootOrder`, il l'a pour la forme faible.

**Flèche 9, §11.3 (deux difficultés pour les familles) — intégrée, la première levée** (`RightSetDichotomy.lean`). Première difficulté : plusieurs zéros à la même position maximale. Levée sans hypothèse : la somme trigonométrique à fréquences distinctes est déjà traitée (§17, `SummitAttained.lean`, `FiniteRadialRigidity.lean`), et si l'ensemble des indices strictement à droite est fini, le sommet est atteint (`summitAttained_of_finite_right` : la position maximale est prise sur l'ensemble fini, la famille du sommet est sa fibre). Donc, sous l'hypothèse de clôture et l'échantillonnage, un ensemble droit fini est vide. Seconde difficulté : une famille infinie dont le supremum n'est pas atteint. Elle devient le SEUL monde restant, écrit en une phrase compilée, la dichotomie (`right_empty_or_infinite_not_summit`) : sous l'hypothèse de clôture et l'échantillonnage, ou bien aucun indice n'est à droite (donc RH par le miroir), ou bien l'ensemble droit est infini ET le sommet n'est pas atteint. C'est la contradiction localisée que demande l'audit §16 : le monde OFF survivant est nommé, et il est exactement l'obstruction de Landau.

**Flèche 7, §9 (dérive cumulative : positive, minorée, ou divergente ?) — intégrée, répondue.** Précision à l'audit : le facteur minimal par paire de changements du complément 12 n'est PAS uniforme (il tend vers un avec le premier), donc la proposition « minorée par une constante uniforme » n'est pas celle qui est compilée. Mais la question est tranchée par la loi affine du complément 13, qui est exacte : l'amplitude relative d'un membre au-dessus de la ligne, lue aux rencontres, vaut une constante fois la rencontre élevée à la position moins un demi, et comme les rencontres tendent vers l'infini, elle tend vers l'infini (`relativeAmplitude_meetings_tendsto_atTop_of_high`, et par le miroir pour une arrivée basse). La dérive cumulative est donc divergente, non par accumulation d'un minimum, mais par la loi exacte.

**Flèche 8, §10 (échantillonnage quantitatif, un seul terme) — déjà couverte.** La condition « le cosinus dépasse un seuil pour une infinité de rencontres » est le cas d'une famille à un seul élément du théorème compilé au §17 (`SamplingFromLogGaps.lean`), qui traite directement la famille, par le fait que le polynôme de fréquences ne tend pas vers zéro et est lipschitzien. Rien à ajouter.

**Flèche 10, §12 (reste spectral → demande) — statut corrigé.** L'audit classe « demande bornée partout équivaut à RH » en compilé rapporté. C'est compilé et certifié ici (`DemandLevelPremise.lean`, axiomes imprimés) ; et la demande est bien calculée exclusivement depuis les premiers (somme lissée de von Mangoldt moins un fond explicite), reliée au reste spectral par identité exacte (formule explicite compilée). La troisième propriété de l'audit, « bornée à partir d'une contrainte arithmétique indépendante », est le point de blocage ; l'audit le formule exactement comme le §17.4.

**Flèche 12, §14 (deux stratégies) — les deux compilées.** La bornitude donne RH directement, et donne la prémisse terminale, puis compose la chaîne existante ; la vérification demandée (« ne réintroduit pas une hypothèse équivalente à RH sous un autre nom ») est faite et son résultat est dit : la demande bornée PARTOUT est équivalente à RH, par construction, c'est la lecture en niveau de la prémisse ; l'hypothèse de clôture (aux rencontres seulement) n'est pas connue équivalente à RH, et c'est exactement l'écart entre les deux qui porte les deux chemins.

**Flèches 2, 4, 5 (stricte progression, lecture partagée, orientation) — déjà traitées par la lecture en niveau.** La prémisse unique est stricte par définition ; l'audit demande de produire l'orientation « à partir d'une propriété indépendante » : cette propriété est maintenant nommée, c'est l'hypothèse de clôture plus l'un des deux compléments (sommet atteint, ou variation uniforme).

**Flèche 3 (contacts) — rien à ajouter**, identités exactes.

**Non intégré, et pourquoi.** (i) Les statuts « compilé rapporté » de l'audit : pour tout module du §17 et du §18 ils sont « compilé certifié », les axiomes ayant été imprimés à chaque construction. (ii) La recherche systématique de la flèche « grammaire démontrée ⟹ demande normalisée bornée » parmi les rigidités existantes : elle a été faite au §16 et a produit le point de blocage ; aucun théorème compilé ne la contient, et relire ne la produira pas. (iii) La mention que le maître et les graphes du commit 977e706e n'ont pas été récupérés par l'audit : informatif, sans effet.

### 18.2 Décision 1 exécutée : l'interface exacte avec le théorème des nombres premiers

**Module** `ChebyshevAsymptoticToLogGaps.lean`. L'hypothèse nommée « les écarts logarithmiques tendent vers zéro » est réduite à une substitution d'une ligne. L'hypothèse `ChebyshevAsymptotic` est nommée sous la forme EXACTE du théorème externe (le quotient de la fonction thêta de Tchebychev par son argument tend vers un ; la forme « équivalence asymptotique » du théorème externe la donne), et il est démontré, avec Mathlib seul, qu'elle entraîne les écarts logarithmiques vers zéro. Preuve en mots : entre deux premiers consécutifs la fonction thêta est constante (aucun premier n'est ajouté, par la propriété caractéristique de l'énumération) ; si une infinité d'écarts dépassaient une fraction fixe du premier, thêta resterait constante sur un intervalle dont les deux bouts ont un quotient proche de un, contradiction ; donc le rapport de deux premiers consécutifs tend vers un, et son logarithme vers zéro. Compositions : asymptotique de Tchebychev, hypothèse de clôture et sommet atteint donnent RH ; sous l'asymptotique et la clôture, un zéro à droite n'est jamais en nombre fini.

**La dépendance, mesurée.** Le projet externe (PrimeNumberTheoremAnd) est épinglé sur Lean 4.35.0 et une révision de Mathlib du 13 octobre 2026 ; nous sommes sur Lean 4.33.0-rc2 et une révision du 3 août 2026. L'importer comme dépendance Lake demanderait une reconstruction de Mathlib, hors course bornée. La clôture d'imports du théorème externe, dans le projet, est de neuf fichiers et environ huit mille lignes (le théorème de Wiener-Ikehara en représente plus de la moitié). Le dépôt contient déjà un port de pièces de ce projet à notre révision de Mathlib (`Zeta23Port/FromPNTPlus`, licence Apache 2.0, avec LICENSE et PROVENANCE), sans le théorème des nombres premiers lui-même.

**Le port, exécuté et achevé** (`RHV6Fresh/PNTPort/`, neuf fichiers, licence Apache 2.0, `LICENSE` et `PROVENANCE.md`). Transformations mécaniques par script : outil de blueprint retiré, imports renommés, en-tête de provenance par fichier. Quatre corrections de portage, toutes marquées « port : » dans le corps : un nom de lemme sur le cercle unité ; une tactique absente de notre Mathlib, déroulée à la main ; un nom de lemme sur le conditionnel ; deux buts d'instances de norme, fermés par réflexivité. Deux lemmes amont portaient un `sorry` (bornes de décroissance de Fourier) sans être utilisés par le théorème visé : ils sont retirés, avec les deux déclarations qui en dépendaient, pour respecter la règle du dépôt ; le dossier ne contient aucun `sorry`. Le théorème externe compile chez nous et ses axiomes sont imprimés : standard seulement (propext, choix, quotient). Construction en trois passes bornées, chacune sous vingt-cinq minutes.

**Conséquence** (`Terminal/LogGapsTheorem.lean`) : « asymptotique de Tchebychev », « les écarts logarithmiques tendent vers zéro » et « les rencontres échantillonnent les fréquences » sont maintenant des THÉORÈMES, aux axiomes standard. L'hypothèse nommée d'échantillonnage du §16 n'est plus une hypothèse. Le chemin des zéros se lit : hypothèse de clôture et sommet atteint donnent RH (`riemannHypothesis_of_closure_summit`) ; la dichotomie se lit sous l'hypothèse de clôture seule : RH, ou bien une infinité d'indices à droite dont le sommet n'est pas atteint ; un ensemble droit fini est vide sous l'hypothèse de clôture seule. Le dossier du port et ce module ne sont importés ni par `RHV6Fresh.lean` ni par la chaîne.

### 18.3 Décision 2 exécutée : le sommet atteint, attaqué par la contradiction

Le sommet atteint n'est pas dérivable des faits compilés (§17). Ce qui est fait : le réduire au seul monde qui survive. Après `RightSetDichotomy.lean`, sous l'hypothèse de clôture et l'échantillonnage (lui-même sous l'asymptotique de Tchebychev), le seul monde où RH est fausse est : une infinité d'indices à droite dont les positions n'ont pas de maximum atteint par une famille finie. Ce monde se divise en deux sous-cas, par l'équivalence compilée au §17 (sommet atteint, c'est supremum atteint et verticale finie) : (a) le supremum des positions est atteint, mais par une infinité d'indices sur une même verticale ; (b) le supremum n'est pas atteint. Le sous-cas (a) est compilable avec les outils présents plus un argument de valeur moyenne : la somme des contributions du sommet est alors une série trigonométrique à coefficients absolument sommables, uniformément continue, dont un coefficient de Bohr est non nul, donc qui ne tend pas vers zéro ; avec les écarts logarithmiques vers zéro, elle est échantillonnée aux rencontres, et le reste strictement sous le sommet tend vers zéro par convergence dominée comme au §17. C'est le prochain pas Lean, défini et non lancé. Le sous-cas (b) est l'obstruction de Landau, inchangée.

### 18.4 La frontière, après intégration

Un théorème unique rassemble les deux chemins (`riemannHypothesis_of_closure`) : sous l'hypothèse de clôture, RH découle soit de « asymptotique de Tchebychev et sommet atteint » (chemin des zéros), soit de « variation uniforme dans les écarts » (chemin des premiers). Le chemin des premiers est maintenant une équivalence : sous l'hypothèse de clôture, RH, c'est la variation uniforme, ni plus ni moins. Le chemin des zéros a son hypothèse connue réduite à l'énoncé exact d'un théorème externe, et son hypothèse structurelle réduite au sous-cas (b) seul, le sous-cas (a) étant compilé (§18.7).

Le point de blocage est inchangé : le niveau de la demande des premiers, aux rencontres, n'est pas dérivé des premiers. Ce qui l'entoure est réduit à une phrase structurelle unique (le supremum des positions à droite, s'il y en a, n'est pas atteint ; §18.7).

### 18.5 Graphe de causalités (état au 2026-10-29, après intégration)

Premiers ⟹ grammaire des écarts (compilé) ⟹ rencontres uniques en fin d'écart (compilé) ⟹ loi affine et dérive exacte de tout zéro hors ligne, divergente aux rencontres (compilé) ⟹ prix non borné aux rencontres (compilé) ⟹ payable seulement par une infinité de zéros à droite, sommet non atteint (compilé sous échantillonnage) ; échantillonnage ⟸ écarts logarithmiques vers zéro ⟸ asymptotique de Tchebychev (les trois sont des théorèmes, le dernier par le port du théorème externe) ; hypothèse de clôture ∧ variation uniforme ⟺ demande bornée partout ⟺ prémisse unique ⟺ RH (compilé) ; variation uniforme ⟸ écarts de l'ordre de la racine (compilé) ; hypothèse de clôture ∧ (supremum atteint ∨ variation uniforme) ⟹ RH (compilé, §18.7) ; sous clôture, RH ⟺ supremum atteint (compilé). Flèche manquante, unique : premiers ⟹ hypothèse de clôture.

### 18.6 Prochains pas (définis, non lancés sans validation)

1. Le port du théorème externe est achevé (§18.2) ; rien à faire, sinon le tenir à jour si la révision de Mathlib change.
2. Le sous-cas (a) du §18.3 est compilé (§18.7, `SummitVertical.lean`) ; rien à faire.
3. Le point de blocage, du côté des premiers : il reste le seul inconnu dont dépend la fermeture.

**Note du 2026-10-30 :** ce point 3 est retiré comme objectif. Il n'est pas atteignable par cette route (§19). La réorientation remplace la frontière du §18.4 et le graphe du §18.5 comme cible de travail ; les faits compilés du §16 au §18 restent vrais et servent de bibliothèque.

### 18.7 Sous-cas (a) compilé : la verticale infinie au sommet (validé par l'auteur le 2026-10-29)

**Ce qui est fait.** `SummitVertical.lean` (module isolé, commit f5e43c2a) lève la restriction de finitude de « sommet atteint ». La famille du sommet est une verticale quelconque, finie ou infinie. Sa contribution, rapportée à la puissance du sommet, est une série trigonométrique en logarithme de la variable, dont les coefficients ont pour modules les poids des indices, absolument sommables (compilé au §16). Trois faits compilés sur ces séries, sans aucune intégrale nouvelle : elle ne tend pas vers zéro (on la tronque à une partie finie contenant un indice de coefficient non nul, de queue plus petite que le quart de ce coefficient ; si la série tendait vers zéro, la moyenne quadratique compilée du polynôme tronqué serait au plus la moitié du carré du coefficient, alors qu'elle vaut au moins ce carré) ; elle est uniformément continue (troncature lipschitzienne plus queue petite) ; donc elle est échantillonnée aux rencontres, par le théorème des écarts logarithmiques (§18.2). Le reste du complément de la verticale, rapporté au sommet, tend vers zéro par convergence dominée, comme au §17 mais sur le complément d'un ensemble quelconque.

**Résultats compilés, axiomes standard, aucun sorry.** Hypothèse nommée affaiblie « supremum atteint » : s'il existe un indice à droite de un demi, le supremum des positions est atteint, par une verticale finie ou infinie. Sous l'hypothèse de clôture seule : supremum atteint donne aucun indice à droite, donc RH ; et RH donne supremum atteint par vacuité : sous l'hypothèse de clôture, RH équivaut au supremum atteint. Le théorème des deux chemins est élargi : hypothèse de clôture et (supremum atteint ou variation uniforme) donnent RH. **Dichotomie resserrée**, sous l'hypothèse de clôture seule : RH, ou bien l'ensemble droit est infini et toute position atteinte est strictement dépassée, c'est-à-dire le supremum des positions n'est pas atteint.

**Ce que cela change à la frontière.** Le sous-cas (a) n'existe plus. Le seul monde où RH est fausse sous l'hypothèse de clôture est le sous-cas (b) : une infinité d'indices à droite dont les positions montent vers un supremum jamais atteint. C'est l'obstruction de Landau, écrite en une phrase compilée, désormais seule. Elle n'est pas dérivable des faits compilés (test du §17, inchangé) : rien de compilé ne parle de l'ensemble des positions radiales.

**Ce que cela ne change pas.** Le point de blocage : le niveau de la demande des premiers, aux rencontres, n'est pas dérivé des premiers. Rien n'est posé ; la chaîne est intacte ; le module n'est pas importé par elle.

## 19. Réorientation (auteur, 2026-10-30) : le zéro OFF est le point de départ ; la question est locale, pas un contrôle global

### 19.0 Tentatives directes de clôture avant abandon (demandées par l'auteur, exécutées le 2026-10-30)

Cinq tentatives directes, sans autre procédé : un fichier de travail importe toute la bibliothèque compilée des §16 à §18 et demande au compilateur de fermer chaque énoncé par un fait existant (recherche exhaustive `exact?`). Cibles : l'hypothèse de clôture (demande bornée aux rencontres) ; le supremum atteint ; la variation uniforme dans les écarts ; la demande bornée partout ; la borne du niveau de la demande à une rencontre par la série des résidus. Résultat : les cinq échouent, aucun fait compilé ne ferme aucune des cinq cibles (journal `/tmp/claude-1002/closure_attempts.log`, fichier non versionné). Lecture à la main : la seule borne dérivable des faits compilés est celle par la position maximale des indices, qui vaut un, et donne un niveau relatif de la demande majoré par la racine de la variable fois la somme des poids, c'est-à-dire non borné ; borner demande la position maximale un demi, qui est RH. Confirmation : je n'ai aucune idée pour fermer la piste actuelle ; la clôture est de la force d'un terme d'erreur arithmétique que rien dans le dépôt ni dans la littérature compilée ne fournit.

### 19.1 La dérive, nommée

Du §16 au §18, la démarche a remplacé la question d'origine par une autre. La question d'origine est géométrique et locale : un zéro OFF authentique peut-il franchir une transition de la grammaire première, lue sur deux ou trois écarts consécutifs, leurs rencontres et la lecture de la fréquence précédente, sans violer les contraintes de sa Tour ? La question substituée est un contrôle global : borner le niveau de la demande des premiers à toutes les rencontres (hypothèse de clôture), c'est-à-dire contrôler la taille du reste lissé des premiers le long d'une suite infinie de points. Ce contrôle est de la force d'un terme d'erreur arithmétique ; il n'est pas démontrable par cette voie, par personne. Les expériences de compensation (écarts comparés à une moyenne attendue, sommes de différences, bornes asymptotiques) relèvent de la même dérive et sortent de la stratégie.

Ce qui est retiré : l'hypothèse de clôture comme cible ; le supremum atteint et la variation uniforme comme chemins ; la flèche manquante « premiers ⟹ clôture » du §18.5 comme objectif. Ce qui est conservé : tous les modules compilés des §16 à §18 (ils sont vrais, isolés, et deviennent une bibliothèque) ; les logarithmes comme coordonnées exactes des contacts et des rencontres ; le théorème des écarts logarithmiques et celui de l'échantillonnage, comme faits compilés, non comme instruments de compensation.

### 19.2 Le point de départ : un zéro OFF authentique, et son porteur arithmétique

Le raisonnement est par l'absurde. On suppose un zéro non trivial réel de la théorie, de position radiale strictement sous un demi et de hauteur strictement positive. Il n'est pas fabriqué ; il a sa hauteur, sa position, son amplitude, et son miroir à la même hauteur par l'équation fonctionnelle. C'est le porteur analytique. Ses contacts sont fixés par la position et la hauteur (phase par arc tangente du rapport hauteur sur position, `Tower/TrueTower.lean`, `Tower/Incidences.lean`) ; aucun n'est ajustable.

Ce qui manque est le porteur arithmétique : l'événement premier précis auquel ce zéro doit répondre. Trois premiers consécutifs et leurs deux écarts exacts, sans aucune moyenne. Le déclencheur est la première rencontre obligatoire : le premier événement canonique auquel la Tour OFF est obligée de se raccorder après le membre précédent. Il doit sortir des règles de succession déjà compilées, non d'un choix parmi les premiers. Sans obligation, un test sur trois premiers ne teste qu'une rencontre choisie et n'exclut rien.

### 19.3 La route retenue et ses deux obligations

Zéro OFF authentique ⟶ porteur arithmétique ⟶ premier raccord obligatoire ⟶ lecture de la fréquence précédente ⟶ contrôle de l'amplitude ⟶ contradiction locale.

Obligation I (théorème de liaison) : un zéro OFF authentique impose une transition première canonique, obligatoire et identifiable.

Obligation II (incompatibilité locale) : à cette transition, les trois contraintes (rencontre au premier partagé compatible avec les contacts ; lecture de la fréquence du membre précédent compatible avec la succession des événements ; transport énergétique compatible avec la hiérarchie au raccord), portées par le même zéro, le même événement et le même premier partagé, sont contradictoires. Cette incompatibilité doit découler d'une propriété indépendante des événements premiers ; la supposer serait renommer RH.

### 19.4 État réel des composants cités, vérifié dans le dépôt le 2026-10-30 (lecture des sources, sans recompilation)

* `Terminal/GeneratedFrequency.lean` : existe. Les objets sont définis depuis le reste des premiers (représentation du reste, fréquence arithmétique, point de rencontre d'un signal par arc tangente, rencontre arithmétique). Réserve compilée : la loi « toute rencontre arithmétique est sur la ligne » est équivalente à RH ; elle ne peut servir de prémisse. Le composant fournit le porteur de fréquence, pas l'obligation du raccord.
* `Terminal/TowerRaccord.lean` : existe. Le raccord entre deux Tours consécutives est une structure au premier partagé (le premier minimal attendu de la Tour de départ, qui est l'occurrence de la Tour d'arrivée), avec cellule de sortie, cellule d'entrée, encadrements et transport exact ; il existe et il est unique sur tout passage. Compilé : sur un passage de même hauteur, le transport renverse ; sous RH le raccord est orienté partout.
* `Terminal/MirrorEventCollision.lean` : existe. Le miroir conserve l'événement de hauteur et consomme un index de membre ; l'identité des occurrences au miroir est réfutée pour tout zéro bas ; l'exiger est RH. Conséquence pour le §19 : ne jamais fabriquer la contradiction en assimilant les deux occurrences.
* « hiérarchie stricte au raccord » : aucun fichier de ce nom. L'objet existe sous le nom `RaccordHierarchy` dans `Terminal/TowerHierarchy.lean` : au premier partagé, la Tour d'arrivée ne lit pas plus d'énergie que la Tour de départ et son pas est strictement plus petit. Compilé : elle tient sur tout passage où la hauteur avance, quelles que soient les positions radiales ; le passage de même hauteur la viole ; elle à tous les raccords est équivalente à RH.
* `Terminal/CascadeContinuation.lean` : existe. Une première arrivée sous un demi gèle la cascade au pas suivant (hauteur gardée, décalages constants, lecture de fréquence nulle), et un tel passage sortant existe ; la continuation à tous les pas est de la force de RH.

Le verrou du §5 du texte de l'auteur se lit dans les sources : la correspondance canonique zéro ⟶ premier (occurrence du zéro, premier minimal attendu du zéro) est définie à partir du zéro. Elle nomme l'événement ; elle n'établit pas que le zéro OFF est obligé de s'y raccorder. C'est exactement l'Obligation I, ouverte.

### 19.5 Ce que les faits compilés disent déjà de l'Obligation II

La hiérarchie au raccord tient dès que la hauteur avance, indépendamment des positions radiales. Donc, pour un zéro OFF dont le raccord avance en hauteur, le contrôle de l'amplitude par la seule hiérarchie ne donne aucune contradiction ; la contradiction locale, si elle existe, doit venir du croisement des trois contraintes au même premier partagé (rencontre et lecture de fréquence comprises), et d'une propriété indépendante. C'est un no-go connu à respecter, non une impasse de la route : il dit où ne pas chercher.

### 19.6 Prochain pas compilable, pré-enregistré (lancé le 2026-10-30 sur feu vert de l'auteur ; exécution au §19.8)

Un module isolé, non importé par la chaîne, `Terminal/OffCarrier.lean` (nom proposé), en trois parties :
1. Porteur : pour un zéro OFF authentique, construire le passage dont il est le membre d'arrivée et son raccord unique ; extraire le premier partagé, puis les trois premiers consécutifs autour de lui (prédécesseur, premier partagé, successeur) et leurs deux écarts exacts. Aucune moyenne, aucune fréquence choisie.
2. Les trois contrôles au raccord, écrits comme trois énoncés sur le même zéro, le même événement, le même premier partagé : compatibilité du premier partagé avec les contacts de la Tour (cellule d'entrée), lecture de la fréquence du membre précédent (décalages d'entrelacement), transport énergétique.
3. Obligation I posée comme une définition nommée, étiquetée hypothèse, jamais comme théorème, tant qu'elle n'est pas dérivée des règles de succession ; puis recherche de la contradiction locale sous cette définition, avec sortie honnête : soit une contradiction compilée, soit l'énoncé exact de la propriété indépendante manquante.

Jumeau déterministe : une expérience sur zéros réels (table Odlyzko versionnée) et sur trois premiers consécutifs autour du premier partagé de chaque zéro, pré-enregistrée avant exécution, réel, jumeau et synthétique séparés, zéros synthétiques jamais aux hauteurs d'un zéro ON existant ; définie, non lancée.

### 19.7 Frontière reformulée

Le point de blocage n'est plus « le niveau de la demande des premiers, aux rencontres, n'est pas dérivé des premiers » (global, hors d'atteinte). Il est double et local : (I) l'obligation du raccord canonique pour un zéro OFF authentique ; (II) l'incompatibilité locale des trois contraintes à ce raccord, par une propriété indépendante. Il reste à vérifier si deux ou trois écarts suffisent. Rien n'est posé ; la chaîne est intacte. (Mise à jour au §19.8 : l'obligation I est fermée par théorème sur le porteur canonique ; l'obligation II est réduite à une hypothèse nommée unique, locale, la continuation forcée.)

### 19.8 Plan validé par l'auteur (2026-10-30, « feu vert ») et exécution : le porteur OFF compilé (`Terminal/OffCarrier.lean`)

#### 19.8.1 Cadre conceptuel (décision de l'auteur, prise comme telle)

L'écart reconstitué par les signaux des zéros est l'écart réel : aucune différence n'existe et aucune ne doit être supposée. La compensation des écarts est acquise ; elle ne se prouve pas et ne se valorise pas. Les écarts sont, et doivent être, reconstitués par les zéros à l'infini. La démarche est conceptuelle, jamais chiffrée sur une fonction statistique ; le logarithme ne sert que de coordonnée exacte d'un contact. Le niveau de demande chiffré des §16 à §18 disparaît du plan.

#### 19.8.2 Atouts réutilisés tels quels (bibliothèque compilée)

* Le théorème de synchronisation locale : pour chaque écart premier, l'incrément du reste des premiers est la somme des contributions exactes de tous les vrais zéros ; tous les signaux se rencontrent à la fin de l'écart (point de rencontre unique).
* Le premier changement de régime de l'énumération canonique : si RH est fausse, il existe un rang dont le membre est bas et dont tous les prédécesseurs sont ON ; son profil compilé (arrivée verticale depuis un membre ON, historique ON, miroir qui le suit à la même hauteur).
* Le raccord de Tour : existence et unicité sur tout passage, premier partagé, cellules, transport ; renversement sur un passage de même hauteur.
* La hiérarchie au raccord : tient dès que la hauteur avance ; brisée par la même hauteur.
* La continuation de cascade : une première arrivée basse gèle le pas suivant (même hauteur, décalages d'entrelacement constants) ; la lecture de fréquence par l'entrelacement.
* La collision miroir : le miroir garde l'événement de hauteur, les occurrences restent strictement ordonnées, jamais égalées.
* Le sens de progression rigidifié : sur tout passage, l'occurrence du suivant est le premier minimal attendu du précédent.

#### 19.8.3 Les trois hypothèses du plan, et leur sort au compilateur

1. **Liaison.** Prévue dérivable par instanciation ; elle l'est. Pour le porteur canonique, le zéro OFF authentique de rang donné a pour occurrence le premier de ce rang, et pour premier minimal attendu le premier suivant. Le point de rencontre de son écart est exactement le premier partagé de son raccord sortant, et tous les signaux s'y rencontrent. Théorème. Le verrou du §19.4 (correspondance définie depuis le zéro) est levé ici parce que le porteur est canonique : le rang nomme les trois premiers, la synchronisation donne la rencontre.
2. **Lecture de la fréquence précédente.** Au raccord d'arrivée, la fréquence monte strictement et les décalages d'entrelacement décroissent strictement à tout indice : l'écart précédent a fixé la fréquence du zéro OFF. Théorème.
3. **Continuation forcée.** La rencontre à la fin de l'écart du zéro OFF exige du signal qui y arrive une fréquence strictement supérieure, c'est-à-dire que le pas sortant monte. Définition étiquetée hypothèse, jamais théorème.

#### 19.8.4 Ce qui est compilé (module isolé, non importé par la chaîne, non ajouté à l'agrégateur ; axiomes standard ; aucun `sorry`)

* Le porteur : rang canonique, membre bas, prédécesseurs ON. Si RH est fausse, un porteur existe ; sous RH il n'en existe aucun.
* Le zéro OFF authentique, son passage d'arrivée, son passage sortant ; les deux raccords uniques ; les trois premiers consécutifs du porteur (occurrence du dernier membre ON, premier partagé d'arrivée qui est l'occurrence du zéro OFF, premier partagé sortant qui est son premier minimal attendu) et leur ordre strict.
* Contrôle 1, liaison : rencontre de l'écart du zéro OFF au premier partagé sortant, tous signaux présents ; rencontre de l'écart précédent au premier partagé d'arrivée.
* Contrôle 2, lecture de la fréquence précédente : montée stricte et décalages strictement décroissants au raccord d'arrivée. Le raccord d'arrivée est orienté et la hiérarchie y tient dès la hauteur deux : l'arrivée du zéro OFF est invisible à l'amplitude seule (no-go du §19.5 confirmé en place).
* Contrôle 3, signature OFF au raccord sortant : pas gelé (même hauteur), décalages constants, pas de Tour conservé, hiérarchie brisée, et dès la hauteur deux énergie strictement renversée au premier partagé ; le signal qui rencontre la fin de l'écart n'apporte aucune fréquence nouvelle ; il est strictement plus à droite radialement. Faits miroir : événement de hauteur conservé, le miroir suit, occurrence strictement au-dessus.
* La contradiction locale : sous la continuation forcée, le porteur est contradictoire (le pas sortant est gelé et devrait monter).
* Lectures équivalentes de la continuation forcée, compilées : décalages strictement décroissants au raccord sortant ; hiérarchie au raccord sortant (dès la hauteur deux).
* Sous la continuation forcée sur tout porteur, RH ; et réciproquement sous RH aucun porteur (vacuité) : équivalence exacte, dite comme telle.

#### 19.8.5 Résultat honnête

La route tient sa promesse de localité : tout se joue sur un seul passage et un seul premier, le premier partagé sortant du zéro OFF authentique, sans moyenne, sans borne, sans contrôle d'erreur. Deux des trois hypothèses sont des théorèmes. La troisième, la continuation forcée, est la forme locale exacte de la demande de la chaîne (la fréquence monte à la rencontre) restreinte au seul pas sortant du premier changement de régime ; quantifiée sur tout porteur, elle est RH, et le module le dit. Elle n'est pas posée.

Ce qui reste à dériver, des premiers seuls : l'écart du zéro OFF existe (le premier suivant existe), sa rencontre est obligatoire et unique, et le pas sortant gelé y arrive sans fréquence nouvelle. Il faut que la rencontre d'un écart nouveau ne puisse pas être remplie par un signal sans fréquence nouvelle. Lectures compilées de cette propriété : décalages d'entrelacement strictement décroissants au raccord sortant ; ou hiérarchie au raccord sortant. Si cette propriété sort des premiers (l'écart nouveau impose sa fréquence), la route ferme ; si elle exige une propriété que seuls les zéros fournissent, elle renomme RH, et ce sera dit.

#### 19.8.6 Frontière et prochain pas

Frontière unique, locale, nommée : la continuation forcée au raccord sortant du porteur. Prochain pas, pré-enregistré, non lancé : tentative directe (recherche exhaustive du compilateur, puis lecture à la main) de dériver la continuation forcée des seuls faits sur l'écart nouveau (existence du premier suivant, rencontre obligatoire, lecture de fréquence par l'entrelacement, contacts exacts), dans un fichier de travail non versionné ; sortie honnête dans les deux cas. Aucune expérience chiffrée n'est prévue pour cette hypothèse : elle est conceptuelle.

### 19.9 E301 : conclusions déclarées FAUSSES par l'auteur (2026-10-30) ; ce que le compilé dit au contraire ; tentative directe exécutée

#### 19.9.1 Décision de l'auteur (prise comme telle, consignée)

Les conclusions liées à l'audit E301 (2026-10-14, `experiments/E301_AuditContradictoire/`, `Terminal/SynchronizationAudit.lean`) sont toutes FAUSSES. Les fichiers restent dans le dépôt (rien n'est retiré) ; leur rapport porte désormais une note de tête renvoyant ici. Les conclusions visées : « la synchronisation locale n'est pas une contrainte sur la position radiale » ; « la borne de queue admet un point de partie réelle un quart » ; « aucune des contraintes compilées n'exclut une première arrivée basse » ; « identifier n'est pas contraindre » ; « la flèche manquante exige une entrée de nature RH ».

#### 19.9.2 Révision extérieure qui inspire la reprise (texte transmis par l'auteur, retenu pour ce qu'il établit)

Deux affirmations étaient confondues dans E301 : qu'une identité de synchronisation vaille pour toute position radiale, et qu'un zéro OFF produise le même signal qu'un zéro ON. La première n'implique pas la seconde. À fréquence identique, les positions des changements de signe sont les mêmes, mais les amplitudes diffèrent, et les contributions intégrées sur les écarts premiers diffèrent : un zéro OFF n'est pas interchangeable avec un zéro ON de même hauteur. Le théorème de synchronisation pour toute famille est une linéarité ; le point artificiel de partie réelle un quart n'est pas un zéro, ne respecte aucun raccord canonique et ne reproduit aucun écart : ce n'est pas une réfutation de la route locale. La rigidité des contributions individuelles identifie le zéro ; elle interdit de substituer librement une contribution OFF à une contribution ON. La phrase « la différence d'amplitude et la rigidité ne suffisent pas, à elles seules, à exclure un OFF » a été retirée par son auteur : elle n'était pas démontrée. La priorité est de vérifier si les résultats déjà compilés impliquent la contradiction, sans ajouter prématurément une hypothèse.

#### 19.9.3 Ce qui est compilé au contraire de E301, sur le porteur (`Terminal/OffCarrier.lean`, section 5bis ; axiomes standard, aucun `sorry`)

Au point de rencontre de l'écart du zéro OFF (le premier partagé sortant), tout est exact et local :

* l'amplitude du signal OFF est strictement sous l'amplitude de ligne de même fréquence ;
* l'amplitude de son miroir est strictement au-dessus ;
* la paire (zéro OFF, miroir), à la même fréquence, dépasse strictement deux signaux de ligne ;
* les raccords du zéro OFF et de son miroir sont fixés ;
* le zéro OFF, son miroir et le point de ligne de même fréquence sont trois signaux deux à deux distincts sur les écarts premiers au-delà de tout rang.

Ainsi « OFF reproduit ON » est réfuté au compilateur, au point même où la rencontre est obligatoire. Ces théorèmes ne mentionnent aucune moyenne, aucune borne asymptotique, aucune statistique.

#### 19.9.4 Tentative directe pré-enregistrée (§19.8.6), exécutée le 2026-10-30, hors dépôt

Fichier de sonde dans le bac de travail de la session (non versionné), trois sondes par recherche exhaustive du compilateur, bornées à dix minutes : la continuation forcée depuis le contexte nu du porteur ; la continuation forcée avec, en contexte, l'excès d'amplitude de la paire, l'amplitude sous la ligne du zéro, les trois distinctions de signaux, la liaison, la signature sortante, la lecture de la fréquence précédente et les faits miroir ; la contradiction directe depuis les mêmes faits. Résultat : les trois sondes échouent (aucun terme de la bibliothèque ne ferme le but). Lecture à la main : les faits d'amplitude et de rigidité portent sur les normes et les contributions au point de rencontre ; la hauteur du membre sortant est fixée par l'ordre des passages (même hauteur que le zéro OFF) ; aucun théorème compilé ne relie une amplitude au point de rencontre à la hauteur du membre suivant autrement que par la hiérarchie, qui équivaut à la montée de hauteur. La composition n'est donc ni démontrée ni réfutée : elle reste la frontière.

#### 19.9.5 Frontière inchangée, cible précisée

La frontière reste la continuation forcée au raccord sortant du porteur. La cible n'est plus la synchronisation additive (linéarité, sans contenu sur la position radiale) ; c'est la rigidité des contributions individuelles et l'excès d'amplitude de la paire OFF, appliqués au porteur authentique et à son premier raccord obligatoire, composés avec l'obligation de rencontre. Ce qu'il faut encore : que la rencontre d'un écart nouveau, remplie par une paire d'amplitude en excès et sans fréquence nouvelle, contredise un fait des premiers (le prochain premier existe, la rencontre y est unique, les contacts sont exacts). Aucune hypothèse n'est ajoutée ; aucune expérience chiffrée n'est prévue sur cette cible.


### 19.10 Cible §19.9.5 poursuivie : le membre sortant est pris dans la bande du zéro OFF et de son miroir (2026-10-30)

#### 19.10.1 Ce qui est compilé (`Terminal/OffCarrier.lean`, section 5ter ; axiomes standard, aucun `sorry`)

Sur le porteur canonique `C` (zéro OFF `z = (β, T)`, `β < 1/2`, historique ON), le membre qui rencontre `p_{n+1}` est le membre canonique suivant `z' = canonicalMember (n+1)` :

* `outgoing_consecutive` : `z'` est consécutif à `z` ; `outgoing_same_height` : même hauteur `T` (le gel, relu).
* `outgoing_radial_le_mirror` : `β < β' ≤ 1 − β` — la position radiale du membre sortant est prise dans la bande du zéro OFF et de son miroir (ordre lexicographique hauteur puis position radiale, `fiberSuccessor_radial_le_mirror`).
* `outgoing_eq_mirror_of_high` : si `β' > 1/2`, alors `z'` **est** le miroir ; sinon le miroir de `z'`, de même hauteur et de position radiale `1 − β'` strictement entre `β` et `β'`, s'intercalerait entre `z` et `z'`, contre la consécutivité.
* `outgoing_trichotomy` : **le membre sortant est (a) le miroir de `z`, ou (b) un zéro ON à la fréquence exacte du zéro OFF, ou (c) un second zéro OFF avec `β < β' < 1/2`.** Aucun autre cas.
* `mirror_occurrence_eq_meeting` : dans le cas (a), **l'occurrence du miroir est exactement le point de rencontre de l'écart du zéro OFF**, `p_{n+1}`. `mirror_occurrence_gt_meeting` : dans les cas (b) et (c), l'occurrence du miroir est strictement au-delà de `p_{n+1}`.
* `outgoing_no_common_smoothed_meeting` : le zéro OFF et le membre sortant, à fréquence partagée et positions radiales distinctes, **n'ont aucune rencontre lissée commune**, à aucun couple d'indices (`shared_frequency_no_common_meeting`), alors que l'écart `[p_n, p_{n+1}]` leur impose à tous deux la rencontre arithmétique unique à `p_{n+1}` (`liaison`).
* `outgoing_amplitude_gt_zero_at_meeting` : à `p_{n+1}`, l'amplitude du membre sortant est strictement au-dessus de celle du zéro OFF, à la même fréquence.

#### 19.10.2 Lecture de la composition avec l'obligation de rencontre (à la main, sans chiffre)

1. La rencontre obligatoire, telle qu'elle est compilée (`all_signals_meet`), est l'identité de l'écart : la cible arithmétique de l'écart est la somme des parts de tous les signaux. Cette identité est satisfaite par la famille des zéros quelle qu'elle soit ; elle ne distingue pas, à elle seule, une famille contenant la paire OFF d'une famille ON (c'est exactement la linéarité relevée au §19.9.2). Composer l'excès d'amplitude de la paire et la rigidité avec cette identité ne produit donc pas de contradiction sans un fait indépendant sur la valeur de la cible de l'écart.
2. La lecture littérale « tout signal a un contact au bout de chaque écart » **n'est pas compilée et est fausse** : les rencontres lissées d'un signal de fréquence `T` forment un réseau géométrique de raison `exp(π/T)` fixé par son calage, et ces points ne sont pas les premiers. Elle ne peut pas être posée comme prémisse (règle : ne jamais poser une prémisse connue fausse). La non-coïncidence compilée (`outgoing_no_common_smoothed_meeting` contre `liaison`) est donc **consignée, pas transformée en contradiction** : la rencontre lissée et la rencontre arithmétique sont deux objets.
3. Ce que la trichotomie apporte : la cible n'est plus « une paire en excès sans fréquence nouvelle » en général, mais trois configurations exactes du membre qui rencontre `p_{n+1}`. Le cas (a) est le plus serré : la paire OFF entière occupe le bout de l'écart du zéro OFF, l'occurrence du miroir **est** le point de rencontre, et la paire y dépasse strictement deux signaux de ligne (`pair_amplitude_exceeds_line_at_meeting`). Les cas (b) et (c) exigent respectivement un zéro ON à la fréquence exacte du zéro OFF, ou deux zéros OFF à la même fréquence sous un demi.

#### 19.10.3 Frontière inchangée, prochain pas

La frontière reste `ContinuationForced` (le pas sortant monte), équivalente à RH sur tout porteur. Ce qui manque est, dans chacun des trois cas, un fait des premiers sur l'écart `[p_n, p_{n+1}]` que la configuration contredise ; ce fait n'est pas dans le corpus compilé et ne se déduit pas de l'identité de l'écart. Prochain pas, conceptuel : traiter le cas (a) en premier (le miroir rencontre `p_{n+1}`), où la configuration locale est entièrement déterminée par `β`, `T` et les trois premiers consécutifs. Aucune hypothèse ajoutée ; aucune expérience chiffrée prévue.

### 19.11 Cas (a) traité : la fibre de la fréquence du zéro OFF et la reprise de la cascade après le miroir (2026-10-30)

Confirmations de l'auteur (2026-10-30) : la position radiale au-dessus d'un demi est déjà exclue pour le premier zéro hors ligne (`later_le_half_of_history_onLine`, `exists_first_regime_break`) et, au raccord sortant, au-dessus d'un demi il n'y a que le miroir (`outgoing_eq_mirror_of_high`) ; « un OFF reproduit un ON » est réfuté au compilateur, exactement et ponctuellement (§5bis) ; le régime ON est engagé et certifié jusqu'au zéro OFF (`history_onLine`, `arrival_vertical`, `engaged_regime_kept`).

#### 19.11.1 Ce qui est compilé (`Terminal/OffCarrier.lean`, section 5quater ; axiomes standard, aucun `sorry`)

* `fiber_radial_ge`, `fiber_radial_le`, `fiber_band` : **tout zéro à la fréquence du zéro OFF a sa position radiale dans `[β, 1 − β]`.** À gauche de `β`, il précéderait le zéro OFF dans l'ordre et serait ON par l'historique ; à droite de `1 − β`, son miroir serait à gauche de `β`.
* `fiber_eq_pair_of_mirror` : **dans le cas (a), la fibre de la fréquence est exactement la paire** `{z, z*}` (consécutivité de `z` et `z*` : rien ne s'intercale dans la bande).
* `postPassage` = passage canonique de rang `n + 1` (du membre sortant au membre de rang `n + 2`).
* `post_mirror_vertical` : **cas (a) : après le miroir, la fréquence remonte** (si le passage gardait la hauteur, son postérieur serait dans la fibre, à droite du miroir, hors de la bande).
* `post_horizontal_of_ne` : **hors du cas (a), le gel continue** : le passage qui quitte le membre sortant garde encore la hauteur (le miroir, à la même fréquence, suit le membre sortant et précéderait tout membre plus haut).
* `post_vertical_iff_mirror` : **le cas (a) est exactement « le gel dure un seul pas »**.
* `post_mirror_cascade_resumes` : cas (a), les décalages d'entrelacement décroissent de nouveau strictement après le miroir ; `post_mirror_hierarchy` : la hiérarchie tient de nouveau (dès la hauteur 2).
* `single_frozen_step_of_mirror` : **profil complet du cas (a)** : arrivée verticale, pas sortant horizontal, pas suivant vertical ; hiérarchie tenue avant, brisée sur le seul pas `z → z*`, tenue après.

#### 19.11.2 Lecture

Le cas (a) est maintenant une configuration entièrement déterminée : trois premiers consécutifs `p_{n−1} < p_n < p_{n+1}`, puis `p_{n+2}` ; une fréquence `T` portée par exactement deux signaux, `(β, T)` et `(1 − β, T)` ; l'écart `[p_n, p_{n+1}]` est le **seul** écart reconstitué sans fréquence nouvelle, entre l'écart `[p_{n−1}, p_n]` qui apporte `T` et l'écart `[p_{n+1}, p_{n+2}]` qui apporte une fréquence strictement supérieure. Au bout de cet écart, le miroir a son occurrence exacte ; la paire y dépasse strictement deux signaux de ligne, avec des raccords fixés et un calage distinct de celui du zéro OFF. Hors du cas (a), le gel dure au moins deux pas et la fibre contient un troisième signal (ON à la fréquence `T`, ou second OFF) : ces cas ne sont pas plus faciles, ils sont plus chargés.

#### 19.11.3 Frontière inchangée, prochain pas

La frontière reste `ContinuationForced`. Dans le cas (a), elle dit exactement : **un écart premier ne peut pas être reconstitué sans fréquence nouvelle entre deux écarts qui en apportent une.** C'est la forme la plus locale atteinte : un seul écart, une seule fréquence, deux signaux, flanqués de deux montées certifiées. Ce qu'il faut encore dériver des premiers : pourquoi l'écart `[p_n, p_{n+1}]`, dont les deux voisins apportent chacun une fréquence nouvelle, ne peut pas se contenter de la fréquence précédente. Aucune hypothèse ajoutée ; aucune expérience chiffrée prévue ; rien retiré.

### 19.12 Signature locale intégrée de la paire OFF/miroir sur trois écarts premiers consécutifs (2026-10-30)

Relecture externe du commit `64038422` (reçue le 2026-10-30) : le §5quater est une réduction réelle ; il faut exploiter la structure exacte de la paire OFF/miroir plutôt que revenir à une obligation générale de montée de fréquence. Deux corrections méthodologiques sont retenues :

1. **La phrase du §19.11.3** (« un écart premier ne peut pas être reconstitué sans fréquence nouvelle entre deux écarts qui en apportent une ») **est une hypothèse, pas une conséquence** de la reconstruction exacte. L'identité de l'écart fournit la contribution collective ; elle ne démontre pas qu'un écart exige une fréquence nouvelle. Chercher à prouver cette phrase directement serait revenir à `ContinuationForced`, équivalente à RH quand elle est exigée de tous les porteurs. Elle n'est plus l'objectif intermédiaire.
2. **Nouvel objet intermédiaire** : la signature analytique exacte de la paire `(β + iT, (1 − β) + iT)` sur les trois écarts `[p_{n−1}, p_n]`, `[p_n, p_{n+1}]`, `[p_{n+1}, p_{n+2}]` (quatre premiers consécutifs, trois écarts, dont un seul correspond au passage horizontal). `ContinuationForced` reste la caractérisation terminale (§6 du module), rien d'autre.

Plan reçu (A : identité intégrée de la paire ; B : transport sur les trois écarts ; C : raccord à la grammaire et aux contacts ; D : liaison au canal arithmétique). Exécuté dans l'ordre A, B, D ; C partiellement (profil et événements canoniques ; la confrontation aux contacts propres n'ajoute rien de compilable au-delà de `outgoing_no_common_smoothed_meeting`, §19.10.2, point 2). Le plan a été consigné dans ce paragraphe **après** la compilation (la relecture servait de pré-enregistrement) ; les neuf tentatives de compilation du module sont auditées une à une dans `AUDIT_COMPILATION_OFFCARRIER_20261030.md`, journaux conservés dans `audits_compilation/offcarrier/`.

#### 19.12.1 Ce qui est compilé (`Terminal/OffCarrier.lean`, section 5quinquies ; commit de ce paragraphe ; 23 contrôles d'axiomes standard, aucun `sorry`)

**A. Signature intégrée de la paire** (canal de comptage ; `countingGapTerm_mirror_pair` réutilisé, aucune nouvelle définition de reconstruction) :
* `linePoint` = `1/2 + iT` ; `zeroPoint_eq_line_sub_shift`, `mirrorPoint_eq_line_add_shift` : `ρ = linePoint − d`, `ρ* = linePoint + d`, `d = 1/2 − β > 0`.
* `pairCounting I` = `C_ρ(I) + C_{ρ*}(I)` ; `pair_hyperbolic_signature` : **`P_ρ(I) − 2 C_{1/2+iT}(I) = ∫_a^b 2(cosh(dt) − 1) e^{(1/2+iT)t}/t dt`** sur les bornes logarithmiques exactes de l'écart.
* `pair_real_signature_explicit` : **formule réelle de l'auteur**, `D_OFF(a,b) − D_ON(a,b) = −4 ∫_a^b e^{t/2}(cosh(dt) − 1) cos(Tt)/t dt`. Trois éléments séparés : fréquence (même `T`), amplitude (`e^{t/2}(cosh(dt) − 1) > 0` pour `t > 0`, `d ≠ 0`), rencontre (bornes exactes). **Le cosinus change de signe : la différence intégrée sur un écart donné n'est pas automatiquement non nulle** ; ceci est consigné, pas contourné.

**B. Trois écarts, quatre premiers** :
* `nextGap` = `[p_{n+1}, p_{n+2}]` ; `four_primes` : `p_{n−1} < p_n < p_{n+1} < p_{n+2}` ; `previousGap_b_eq_gap_a`, `gap_b_eq_nextGap_a` : les bornes se raccordent exactement.
* `pairCounting_three_gaps` : **télescopage exact**, la somme des trois signatures est la signature sur `[p_{n−1}, p_{n+2}]` (cohérence de la formalisation, pas une contradiction).
* `three_gap_profile_of_mirror` : **cas (a)** : arrivée verticale, pas sortant horizontal, pas suivant vertical, et les trois événements canoniques portés : `p_n = Occ(z)`, `p_{n+1} = Occ(z*)`, `p_{n+2} = Occ(membre n+2)` (`previousGap_meeting_eq_zero_occurrence`, `mirror_occurrence_eq_meeting`, `postPassage_later_occurrence`).

**D. Liaison au canal arithmétique** (choix explicite : transport vers le canal **lissé**, seul canal dont la reconstruction est compilée ; la reconstruction du canal de comptage n'est pas formalisée, audit E301, inchangé) :
* `gapTerm_mirror_pair`, `pair_gapTerm_signature` : identité hyperbolique pour les termes lissés non pondérés.
* `packet` = paquet de hauteur `T` ; `target_split` : **pour tout écart, la cible lissée = part de la fréquence `T` + part des autres fréquences** (identité, toute famille de zéros).
* `packet_eq_four_of_mirror` : **dans le cas (a), le paquet de la fréquence `T` est exactement quatre indices** : `z`, `z*`, et leurs conjugués (via `fiber_eq_pair_of_mirror` et la surjection membres/conjugués).
* `packet_channel_four_of_mirror`, `target_split_of_mirror` : **cas (a), pour tout écart premier : cible lissée = paire lissée + paire conjuguée + autres fréquences.** Aucune autre contribution à la fréquence `T`.

#### 19.12.2 Lecture

La paire OFF a maintenant une signature compilée sous ses trois aspects : amplitude (facteur hyperbolique strictement positif), fréquence (celle de la ligne, inchangée), calage (bornes exactes de chaque écart, événements canoniques). Dans le cas (a), elle entre dans la reconstruction lissée de chacun des trois écarts comme la totalité de la part de sa fréquence : rien d'autre à `T`. Ce qui est **honnêtement constaté** : `target_split_of_mirror` est une identité ; elle attribue aux « autres fréquences » exactement ce que la cible moins la paire exige, pour tout écart, sans contrainte. Le sens du facteur hyperbolique intégré sur un écart n'est pas décidé (cosinus). Aucune contradiction n'est donc affirmée ici, et aucune ne l'est par ces identités seules.

#### 19.12.3 Question ouverte (la cible de ce paragraphe) et frontière

La question posée par la relecture, consignée telle quelle : **paire OFF authentique et consécutive (cas (a)) + trois événements premiers canoniques + contacts et contributions exacts ⟹ ⊥ ?** Le point d'interrogation est volontaire : c'est le théorème à chercher, pas une conséquence établie. Ce qui manque est un fait **indépendant** sur la part des autres fréquences (ou sur la cible de l'écart) que la signature contredise ; ce fait n'est pas dans le corpus compilé. La frontière formelle reste `ContinuationForced` ⟺ RH (caractérisation terminale) ; l'objet de recherche est désormais la compatibilité de la signature de la paire avec ses trois raccords arithmétiques. Aucune hypothèse ajoutée ; aucune expérience chiffrée ; rien retiré ; la reconstruction du canal de comptage reste non formalisée et n'est pas utilisée.

### 19.13 La cassure : où se trouve la demande de l'écart, et ce que la paire OFF peut y faire (2026-10-30)

Demande de l'auteur (2026-10-30) : le volet C du §19.12 n'était pas justifié ; il faut tirer parti de la découverte que **l'écart se trouve presque entièrement dans la cassure**, et prouver, rigoureusement et sur les seuls éléments collectés, que le zéro OFF ne peut pas réaliser la cassure à temps du fait de son amplitude cumulée avec son miroir.

Plan proposé et exécuté (module porteur, section 5sexies ; 29 contrôles d'axiomes standard, aucun `sorry` ; tentatives 10 et 11 auditées dans `AUDIT_COMPILATION_OFFCARRIER_20261030.md`) :

#### 19.13.1 Ce qui est compilé

**C1. Localisation arithmétique de la cassure** (le reste exact de `HeightPacket`, incrément par pas entier `remainderIncrement_arithmetic`) :
* `break_at_meeting` : au pas qui atteint `p_{n+1}` (le point de rencontre de l'écart du zéro OFF), l'incrément du reste exact est **`log p_{n+1}` moins la variation du fond**. C'est la cassure, exacte, arithmétique, au bout de l'écart.
* `no_break_off_prime_powers` : à tout pas dont l'arrivée n'est pas une puissance de premier, l'incrément est la seule variation du fond : l'escalier n'avance pas.
* `gap_demand_eq_break_add_rest` : la demande de l'écart entier `[p_n, p_{n+1}]` est la somme des pas intermédiaires plus la cassure terminale. **Consigné** : les puissances de premiers intérieures à l'écart (par exemple 8 et 9 dans `[7, 11]`) portent elles aussi une cassure (`Λ ≠ 0`) ; « entre deux premiers l'escalier n'avance pas » vaut hors de ces points. La demande est donc « presque entièrement » dans la cassure terminale au sens exact : tout le reste est la variation du fond, plus ces cassures secondaires.

**C2. Le calage de la paire est celui de la ligne** (canal de comptage, point par point) :
* `pair_density_eq_cosh_line`, `pair_real_density_eq_cosh_line` : **la densité de la paire est `2cosh(dt)` fois la densité de ligne de même fréquence**, `D_ρ(t) + D_{ρ*}(t) = 2cosh(dt) · D_{1/2+iT}(t)`.
* `pair_density_zero_iff` : **la paire s'annule exactement où s'annule la ligne**, aux points `(π/2 + kπ)/T` qui ne dépendent que de la fréquence.
* Lecture : **la paire n'est ni en avance ni en retard sur la ligne. « À temps » n'est pas un levier** : le calage des changements de signe est celui de la fréquence, identique pour la paire OFF et pour la paire de ligne. Ce qui distingue la paire est uniquement son amplitude, `cosh(dt) > 1`, strictement croissante le long du logarithme (l'amplitude cumulée).

**C3. Le pas de la paire avant la cassure** :
* `pair_step_norm_le` : enveloppe explicite du pas de la paire sur `[log N, log(N+1)]` : `(e^{β log(N+1)} + e^{(1−β) log(N+1)})/log N · (log(N+1) − log N)` (enveloppe compilée `countingGapTerm_norm_le`).
* `pair_step_bound_gt_line_bound` : **cette enveloppe dépasse strictement celle de la paire de ligne**, `2e^{b/2} < e^{βb} + e^{(1−β)b}` pour tout `b > 0`. L'amplitude cumulée **rapproche** la paire OFF de la cassure ; elle ne l'en éloigne pas.

**C4. La cassure est réalisée par la totalité** :
* `break_compensated_by_other_frequencies` : au pas de la cassure, ce que le paquet de la fréquence `T` ne fournit pas est fourni exactement par les autres fréquences (`eventCompensation_eq_complement`, instancié sur le porteur). Vrai pour la paire OFF comme pour toute famille de zéros, ON comprise.

#### 19.13.2 Conclusion rigoureuse, consignée telle quelle

L'énoncé demandé — **« le zéro OFF ne peut pas réaliser la cassure à temps du fait de son amplitude cumulée avec son miroir » — n'est pas dérivable des éléments collectés, et les éléments collectés établissent le contraire sur ses deux termes** :
1. sur le **temps** : le calage de la paire est exactement celui de la ligne (C2) ; aucune avance ni retard ne peut être imputé à la position radiale ;
2. sur l'**amplitude** : la paire OFF a, en tout point et sur tout pas, une amplitude strictement supérieure à la paire de ligne (C3, et déjà `pair_amplitude_exceeds_line_at_meeting`) ; si une paire ne « réalise » pas la cassure, la paire de ligne la réalise encore moins ;
3. sur la **cassure elle-même** : aucun signal isolé ne réalise une cassure ; elle est réalisée par la totalité (C4), pour toute famille. Toute lecture « la paire doit réaliser la cassure » est la lecture littérale déjà déclarée fausse au §19.10.2 ; elle n'est pas posée.

Ce qui distingue réellement la paire OFF, compilé : son amplitude relative aux rencontres n'est pas bornée (`pairRelativeAmplitude_unbounded`), alors que celle d'une paire de ligne est constante ; et, dans le cas (a), elle est toute la part de sa fréquence dans la cible de chaque écart (`target_split_of_mirror`). Pour transformer cela en contradiction, il faudrait un fait sur le niveau de la demande aux rencontres ou sur la part des autres fréquences ; ce fait n'est pas dans le corpus (tentative directe de fermeture, §19.9.4, négative), et le poser serait poser une borne du reste des premiers, interdite (§15, verdict sur le défaut dyadique). Aucune démonstration n'est affirmée ici qui ne soit compilée ; aucune hypothèse ajoutée ; aucune expérience chiffrée ; rien retiré. Frontière inchangée.

### 19.14 Ce que le prochain point de rencontre exige : compilé et ouvert (2026-10-30)

Demande de l'auteur (2026-10-30) : prouver que le prochain point de rencontre et le prochain pic exigent une fréquence strictement supérieure, sans être trop grande, donc exactement une fréquence ON, et non une seconde paire OFF/miroir, qui serait trop forte.

#### 19.14.1 Ce qui est compilé (module porteur, section 5septies ; 33 contrôles d'axiomes standard, aucun `sorry` ; tentative 12, réussie du premier coup)

Cas (a) ; `nextMember` = le membre porté par `p_{n+2}` (celui qui suit le miroir ; `nextMember_occurrence`).
* `next_meeting_higher_frequency` : **le membre porté par le prochain point de rencontre a une fréquence strictement supérieure à `T`.** Source exacte : l'ordre canonique et la bande de la fibre (`post_mirror_vertical`), **pas** la rencontre elle-même (la rencontre est une identité, §19.10.2).
* `nextMember_radial_le_half`, `nextMember_onLine_or_low` : **ce membre est ON, ou sous un demi.** Au-dessus d'un demi, son propre miroir (même hauteur, position radiale strictement inférieure) s'intercalerait entre le miroir du zéro OFF et lui, contre la consécutivité.
* `second_off_freezes_again` : **s'il est sous un demi, le pas qui le quitte gèle de nouveau** (son miroir attend à la même fréquence).
* `second_pair_amplitude_exceeds_line`, `second_pair_relativeAmplitude_unbounded` : **cette seconde paire dépasse strictement la ligne en tout point, et son amplitude relative aux rencontres n'est pas bornée** (« trop forte », au sens exact et compilé : relativement à l'échelle de ligne, sans borne).

#### 19.14.2 Ce que cela établit et ce que cela n'établit pas

Établi : la dichotomie exacte du membre suivant, « ON, ou seconde paire OFF ». Dans le second cas, la structure du cas (a) se répète un pas plus loin : un pas gelé, une hiérarchie brisée sur ce seul pas, une paire d'amplitude relative non bornée, et la cible de chaque écart découpée en paquet de la fréquence plus autres fréquences.

Non établi, et consigné tel quel :
1. **« Sans être trop grande »** : aucune borne supérieure sur la fréquence du membre suivant n'existe dans le corpus compilé. Rien ne borne `T'` au-dessus de `T`.
2. **« Exactement une fréquence ON »** : c'est la même frontière un pas plus loin. La seconde paire OFF n'est contredite par rien de compilé : son pas gelé et son amplitude relative non bornée ne contredisent la demande que sous un fait sur le niveau de la demande aux rencontres ou sur la part des autres fréquences, absent du corpus (§19.13.2). Après la première cassure, l'historique n'est plus ON, et l'argument d'ancrage (`later_le_half_of_history_onLine`) ne s'applique plus ; seule la consécutivité donne `β' ≤ 1/2`.
3. **« Trop forte »** : compilé relativement à la ligne (amplitude strictement supérieure, non bornée relativement à `√x`), **pas** relativement à la demande : la demande n'a pas de niveau compilé auquel comparer.

Rien n'est posé ; aucune hypothèse ajoutée ; aucune expérience chiffrée ; rien retiré. Frontière inchangée : `ContinuationForced` ⟺ RH, et sa répétition à chaque pas.

### 19.15 La fréquence est capée par le haut et par le bas : audit du corpus et module isolé `FrequencyCap` (2026-10-30)

#### 19.15.1 Demande de l'auteur

« Ceci ne peut pas être autrement. Il y a toutes les preuves dans l'existant. Si une dérive arrivait, l'ensemble des zéros connus ne pourraient pas avoir la fréquence qu'ils ont. La fréquence est capée par le haut et par le bas. Un zéro ne peut pas occuper une fréquence qui ne permettrait pas à tous les autres zéros d'occuper les fréquences nécessaires jusqu'à l'infini ; il est donc borné par le suivant du suivant ou le troisième. Si un OFF s'introduit, il ne peut pas occuper la fréquence suivante. Audite ce qu'on a pour le prouver, émets des hypothèses, utilise aussi le travail sur les contacts. » Audit demandé dans le Lean **et** dans les maîtres historiques.

#### 19.15.2 Audit : ce que le corpus contenait déjà

Dans le Lean. Aucun théorème du corpus terminal ne borne la hauteur d'un membre par celle du membre suivant autrement que par l'ordre canonique (`canonicalMember_height_mono`, chaîne tautologique). Mais le port `Zeta23Port` contient, compilés et inconditionnels : le comptage local `N(t, t+1] ≤ A₀ log(|t|+3)` (`Zeta23.RvM.zeta_local_zero_count`) ; la formule de Riemann–von Mangoldt pour la fonction zêta de Mathlib, `N(T, 2T] = T/(2π)·ℓ₁(T) + O(log T)`, obtenue des faits Γ démontrés (`Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts`, forme `riemannVonMangoldt_zeta` dans `Zeta23Port/Final.lean`). Le lien rang–comptage était déjà compilé dans le corpus terminal (`upperCount_ge_of_canonical_le`, CountingDeficit) mais jamais raccordé au port : seul `PrimeGrammarQuantitative` importait `Zeta23Port`, pour Chebyshev.

Dans les maîtres historiques. `RHV6_STRATEGIE_MATHEMATIQUE` (ligne 419) : le comptage de Riemann–von Mangoldt est « une retranscription du même projet, jamais une théorie nouvelle », donc admissible. `RHV6_STRATEGIE_LEAN` §34-2 : la Tour grossière utilisait déjà « rang ≤ N(T+2) » par la majoration grossière de Backlund (RHV3Lean, inconditionnelle) ; elle fut écartée comme formule de coordonnée pour la Tour, ce qui ne touche pas un cap sur la fréquence. §34-3 : la règle Riemann–von Mangoldt « n̂ = N(T) » ne reproduit pas les états des quinze zéros publiés (1/15), ce qui concerne la prédiction du premier depuis la hauteur, pas le cap. Recherche `xi_e44_budget_rvm_prime_density_20260826` : « RvM transforme la fraction ON en budget absolu, mais le budget croît » ; le bon usage est « proportion ON + comptage total ⇒ budget OFF », et **pas** « RvM ⇒ OFF impossible » : le comptage « ne contient pas une information de position radiale ». Ce maître (§19, ligne de la réduction en trois points du 2026-10-15) : le point resté ouvert est « la hauteur du zéro suivant porte déjà un zéro sur la ligne ».

#### 19.15.3 Compilé : module isolé `Terminal/FrequencyCap.lean` (non ajouté à `RHV6Fresh.lean`, deux tentatives, aucune erreur, axiomes standard)

* `height_le_iff_card` : **rang et comptage distinct sont équivalents.** Le membre de rang `k+1` est de hauteur au plus `a` si et seulement si la fenêtre fermée de hauteur `a` contient au moins `k+1` points-zéros. Source : énumération canonique surjective, injective, monotone en hauteur.
* `upperCount_eq_Ncount` : **le comptage avec multiplicité du corpus terminal est exactement `N(0, a]` du port zeta23** (même ensemble de points, même multiplicité analytique, égalité par définition).
* `lower_cap` : **plancher inconditionnel.** Il existe `A₀ ≥ 1` tel que, pour tout rang `k` et tout entier `n`, si `n · A₀ · log(n+3) < k+1`, la hauteur du membre de rang `k+1` dépasse `n`. Source : comptage local, additivité des fenêtres unité (`Ncount_add`), rang ≤ comptage.
* `upper_cap` : **plafond inconditionnel.** Il existe `C`, `T₀`, `A₀` tels que, pour tout rang `k` et tout `T ≥ max(T₀, 1)`, si `(k+1) · A₀ · log(2T+3) < T/(2π)·ℓ₁(T) − C·log T`, la hauteur du membre de rang `k+1` est au plus `2T`. Source : Riemann–von Mangoldt sur `(T, 2T]`, multiplicité d'un zéro bornée par le comptage de sa fenêtre unité (`zeroMult_le_Ncount`), comptage ≤ nombre de points × borne de multiplicité, puis `height_le_iff_card`.
* `caps_count_off_pairs_twice` : **le comptage capé vaut `N₀ + 2·W`** (ON plus deux fois les membres bas) : une paire OFF/miroir y entre deux fois, à une seule fréquence.
* `contact_interval_ge_of_height_le`, `contact_interval_lt_of_lt_height` : **la fréquence lue dans les contacts est capée de même** : l'intervalle logarithmique entre deux contacts consécutifs vaut `π/T` (`contact_interval_eq`), donc il est au moins `π/a` sous un plafond `T ≤ a`, et strictement moins que `π/n` sous un plancher `n < T`.

#### 19.15.4 Verdict, phrase par phrase

1. **« La fréquence est capée par le haut et par le bas. »** Confirmé, compilé, inconditionnel : la hauteur du membre de rang `k+1` est encadrée par deux fonctions explicites du rang seul. C'est exactement le principe de l'auteur « un zéro ne peut pas occuper une fréquence qui empêcherait tous les autres d'occuper les leurs jusqu'à l'infini » : le nombre de zéros sous chaque hauteur est fixé par la fonction zêta elle-même (principe de l'argument), donc les fréquences sont des places comptées, et aucun membre ne peut s'écarter de la place de son rang au-delà d'une marge logarithmique. L'erreur de §19.14 était de dire qu'aucune borne supérieure n'existe dans le corpus : elle existait dans le port zeta23, non raccordée ; elle est désormais raccordée.
2. **« Borné par le suivant du suivant ou le troisième. »** Ce n'est pas la forme compilée. Le cap vient du comptage par le rang, pas du membre suivant : chaque membre est borné par sa propre place, et le troisième zéro n'y joue aucun rôle. La fenêtre de trois écarts reste la bonne fenêtre locale du raccord (§19.12), mais le cap n'en sort pas.
3. **« Si une dérive arrivait, les zéros connus ne pourraient pas avoir la fréquence qu'ils ont. »** Non dérivable, et non posé : le comptage est indépendant de RH ; une paire OFF à une hauteur quelconque occupe deux places du comptage à une seule fréquence (`caps_count_off_pairs_twice`) et satisfait les deux caps exactement comme deux zéros ON de fréquences distinctes. Les hauteurs des zéros connus ne sont modifiées par aucune hypothèse sur les zéros plus hauts.
4. **« Un OFF peut s'introduire, mais ne peut pas occuper la fréquence suivante. »** Au sens littéral, compilé depuis §19.14 (le membre porté par `p_{n+2}` n'est ni le zéro OFF ni son miroir, et sa fréquence est strictement supérieure). Au sens d'une contrainte, non dérivable : les caps ne portent aucune information radiale, conclusion déjà consignée par la recherche xi_e44 et confirmée ici par un théorème.

#### 19.15.5 Ce que cela change et ce que cela ne change pas

Acquis : le premier théorème du corpus qui borne la fréquence d'un membre par le haut, depuis les zéros eux-mêmes, et son pendant dans les contacts. Les trois paramètres (amplitude, fréquence, calage) du membre de rang `k+1` sont désormais tous encadrés : amplitude par la position radiale, fréquence par le rang, calage par les contacts.

Non acquis, consigné honnêtement : le cap est aveugle à la position radiale. Il ne peut donc pas être le levier contre la paire OFF. Le seul comptage sensible à la ligne dans le port (proportion d'au moins deux tiers de zéros ON, `Zeta23Port/Final.lean`) est conditionnel à la forme littérale de la formule explicite de Weil (`EF_lit`, hypothèse du port) et donne une proportion, pas une exclusion. Aucune hypothèse nouvelle posée. Frontière inchangée : `ContinuationForced` ⟺ RH. La question ouverte de §19.12 reste : paire OFF + trois événements canoniques + contributions exactes + **caps de fréquence** ⟹ ⊥ ?

### 19.16 L'écart encadré par le zéro précédent et le zéro suivant : audit (Lean + maîtres) et module isolé `ThreeZeroWindow` (2026-10-30)

#### 19.16.1 Demande

Exploiter la chaîne démontrée en §19.15 (rang → comptage analytique → fréquence → espacement des contacts) dans le raccord des Tours, en même temps que la question ouverte de §19.12 (paire OFF, trois événements, contributions exactes, caps de fréquence ⟹ ⊥ ?), avec une mention **inconditionnelle** de l'écart restreint par le zéro précédent et le zéro suivant, sur la fenêtre de trois zéros, dans toutes les situations nécessaires.

#### 19.16.2 Audit (Lean et maîtres, tout le corpus)

Lean (580 fichiers, aucun `sorry`, aucun axiome) :
- Aucun théorème ne bornait quantitativement l'écart entre deux membres canoniques consécutifs ; seules l'ordre (`canonicalMember_height_mono`, `canonicalMember_consecutive`) et les fenêtres de comptage (`canonical_in_band_of_count_step`, `first_three_canonical_onLine`) existaient. L'écart strict d'un seul pas est équivalent à RH (`strict_frequency_cascade_iff_riemannHypothesis`, `mirror_breaks_frequency_cascade`) : il ne peut pas être posé.
- Le port `Zeta23` n'a aucune existence de zéro en fenêtre courte (aucun Littlewood, aucun `0 < N(T, T+h)`) ; la seule fenêtre à terme principal est `[T, 2T]` (`RiemannVonMangoldt.main`). Les énoncés Backlund du port sont des bornes horizontales de dérivée logarithmique, pas des comptages.
- Le raccord des Tours (`Terminal/TowerRaccord.lean`) est une structure au premier partagé `M = p_min(e) = Occ(l)` : cellule de sortie, cellule d'entrée, encadrement énergétique par les contacts, transport exact. Son contenu existe aussi sur le passage horizontal ; il ne fournit pas l'orientation (§10 ; §19.4). Il ne reliait les contacts d'un zéro à ceux du suivant qu'au premier partagé, jamais par une borne d'écart.
- Les objets « trois zéros » existants : cellule de régime à quatre membres (`RegimeCell`, `heights_three_for_four`), `zero_linked_to_both_neighbours`, `pairCounting_three_gaps`, `three_gap_profile_of_mirror`, trichotomie et dichotomie du membre suivant (§5ter, §5septies).

Maîtres :
- Les méthodologies E55 (2026-09-01, `docs/RH_METHODOLOGIE_TROIS_ZEROS_E55.md`, `docs/RH_MAITRE_MATHEMATIQUE_E55_ECARTS_REELS.md`) et RHV2 §5 fixaient déjà « trois zéros consécutifs, unité minimale obligatoire » et « trois zéros et deux passages, le bon objet ». Le blocage « par le haut par le zéro précédent et par le bas par le zéro suivant » (ce maître, lignes de 2026-10 sur les deux passages joints ; `Terminal/TowerTwoSidedRoom.lean`) était un blocage des Tours (énergie), pas des fréquences.
- Rien, dans aucun maître, ne bornait la fréquence du suivant par celle du précédent. La recherche xi_e44 et §19.15 l'avaient déjà dit : le comptage ne porte pas d'information radiale.

#### 19.16.3 Compilé : `Terminal/ThreeZeroWindow.lean` (module isolé, non ajouté à `RHV6Fresh.lean`)

Tout inconditionnel (RvM et comptage local du port, `GammaFacts` prouvé). Deux tentatives, journal `audits_compilation/threezerowindow/`.

Fenêtre générique de trois membres consécutifs (rangs `k+1`, `k+2`, `k+3`) :
- `middle_bracketed` : le membre du milieu est entre le précédent et le suivant.
- `three_window_bracketed` : les trois membres sont dans `[n, 2T]` sous le plancher du rang `k+1` et le plafond du rang `k+3` (§19.15).
- `zerosIn_between_consecutive_empty`, `Ncount_between_consecutive_zero` : aucun zéro, donc comptage nul, dans toute bande `]a, b]` avec `h(k) ≤ a` et `b < h(k+1)`.
- `rvm_main_dominates` : le terme principal `T/(2π)·ℓ₁(T)` dépasse l'erreur `C·log T` dès `T₁ = max(T₀, 2π·e², (4π·max(C,0)+1)²)`.
- **`next_le_double` : le zéro suivant est au plus au double du précédent**, dès `T₁`. Preuve : sinon la bande `]h(k), 2h(k)]` serait vide, contre le terme principal de RvM. Corollaires : **`gap_le_previous` (`h(k+1) − h(k) ≤ h(k)`)**, **`three_window_le_four` (`h(k+2) ≤ 4·h(k)`)**.
- **`far_member_above_unit` : le `m`-ième suivant est à plus d'une unité au-dessus** dès que `m + 1 > 2·A₀·log(h(k)+4)` : les `m+1` membres ne tiennent pas dans deux fenêtres unité. C'est la forme compilée, inconditionnelle, de « borné par le suivant du suivant ou le troisième » : non pas le suivant immédiat (son écart strict est RH), mais le membre de rang `k+m` avec `m` au-delà du comptage local.

La paire OFF/miroir du porteur, cas (a), trois événements `p_n, p_{n+1}, p_{n+2}` :
- `mirror_height`, `nextMember_eq` : le miroir a la hauteur du zéro OFF ; le membre porté par `p_{n+2}` est de rang `n+3`.
- **`three_events_bracketed` : la fréquence du membre porté par `p_{n+2}` est strictement supérieure à celle de la paire et au plus son double** (dès `T₁`).
- `pair_two_places`, `pair_local_room` : la paire occupe deux places du comptage dans la fenêtre unité sous sa hauteur ; le comptage local doit y laisser deux places (`2 ≤ A₀·log(|T−1|+3)`).
- `pair_contacts_equal` : les contacts du zéro OFF et de son miroir ont le même pas `π/T`. **`next_contacts_bracketed` : les contacts du membre suivant sont entre `π/(2T)` et `π/T`.**

#### 19.16.4 Verdict

1. **« Mention inconditionnelle de l'écart restreint par le zéro précédent et le zéro suivant. »** Compilée. Le membre du milieu est entre ses deux voisins (ordre) ; l'écart vers le suivant est au plus la hauteur du précédent (`gap_le_previous`, RvM) ; l'écart cumulé vers le `m`-ième suivant dépasse une unité dès que `m` dépasse le comptage local (`far_member_above_unit`). Ce sont les deux sens de la restriction, dans la fenêtre de trois, pour tout membre et pour la paire OFF.
2. **Ce qui n'est pas compilé, et pourquoi.** L'écart d'un seul pas n'a pas de plancher strictement positif inconditionnel : c'est RH (`strict_frequency_cascade_iff_riemannHypothesis`). Le plafond `h(k+1) ≤ 2h(k)` est grossier : le port n'a pas de comptage en fenêtre courte ; un plafond en `1/log T` demanderait un théorème d'existence de zéro en fenêtre courte, absent du port et non posé.
3. **Chaîne exploitable dans le raccord des Tours.** Le raccord d'un passage (`TowerRaccord`) est au premier partagé et encadre l'énergie par les contacts ; les contacts du membre d'arrivée sont désormais encadrés par la fréquence du membre de départ (`next_contacts_bracketed`), inconditionnellement. Mais le raccord existe sur le passage horizontal avec tous ses champs (§10) : la chaîne encadre, elle n'oriente pas.
4. **Question de §19.12 avec les caps.** Les trois événements de la paire sont maintenant encadrés en fréquence et en contacts. La contradiction cherchée ne sort pas de ces encadrements : `caps_count_off_pairs_twice` et `pair_two_places` montrent que la paire satisfait les caps en occupant deux places à une fréquence, exactement comme deux zéros ON. Ce qui manque reste un fait **sensible à la position radiale** sur la part des autres fréquences ou sur la demande de l'écart ; ce fait n'est pas dans le corpus, et le poser serait poser une borne du reste des premiers (§15). La question reste ouverte, telle quelle, avec un encadrement de plus.

Frontière inchangée : `ContinuationForced` ⟺ RH.

### 19.17 La composition « comptage exact + occurrences premières + lecture des fréquences » : audit, module isolé `OccurrenceHeightComposition`, nouveau plan (2026-10-30)

#### 19.17.1 Demande de l'auteur (texte collé)

Ne plus chercher à montrer que la paire OFF « consomme trop de places » : elle en consomme exactement deux (§19.16). Chercher si elle occupe deux places **dont les contraintes arithmétiques exigent deux hauteurs différentes**. Cible : `Occ(z) = p_n`, `Occ(z*) = p_{n+1}`, `T(z) = T(z*)` ; les contraintes démontrées sur `p_n` et `p_{n+1}` imposent-elles des hauteurs différentes ? L'inégalité stricte doit venir d'un théorème indépendant du régime ON : la déduire de la continuation forcée reviendrait à reprendre la conclusion. L'audit doit porter sur la composition `FrequencyCap` + `OffCarrier` + `GeneratedFrequency`.

#### 19.17.2 Audit (Lean, tout le corpus ; maîtres)

Balayage de tous les énoncés compilés (RHV6Fresh, rhv2_fresh, rhv3_lean, rh_gap_criterion) où figurent à la fois une quantité première (`occurrence`, `expectedMinimumPrime`, `fnPrimeAtRank`, `rPrimeGapLogRatio`, logarithme d'un premier) et une hauteur, reliées par une égalité ou une inégalité.

1. **Aucun théorème compilé ne donne la hauteur d'un membre en fonction de son premier**, ni ne la borne strictement par lui, autrement que par le rang et le comptage. Tout énoncé qui mentionne les deux est de l'une des quatre espèces suivantes : (i) la coordonnée de phase « hauteur fois logarithme du premier », valable pour toute hauteur (c'est une lecture, pas une contrainte : `occurrencePosition_eq`, `phaseIncrement_eq_height_mul_ratio`, `gap_reading_height_only`, `passage_span_eq_log_occurrences`) ; (ii) un fait d'ordre et de rang (`passage_direction_rigid` : hauteur croissante au sens large, occurrence strictement croissante) ; (iii) un énoncé conditionnel dont l'hypothèse fait le travail (`hgap : π ≤ T·log(p_{n+1}/p_n)` dans `ConstraintCorrelation`, `ReadingArithmetic` ; `hT1`/`hAlign` dans rhv2 `T1ArithmeticConsequence`, jointement insatisfaisables sur les longues chaînes ; `height_lower_bound_of_phase_quantum`, circulaire) ; (iv) le canal du comptage (`FrequencyCap`, `ThreeZeroWindow`), qui ne mentionne aucun premier.
2. **Le premier disparaît du résidu radial** : `changeResidue_eq_position_sub` (le terme premier disparaît), `towerPosition_eq_line_add_residue` (position de Tour = position de ligne + résidu, pour tout réel), `rPrimeGapLogRatio` (« jamais d'un zéro, d'une hauteur ou d'une Tour »). L'occurrence est une étiquette de rang (`occurrence_is_rank_label`, maître `AUDIT_IMPACT_TOUR_GRILLE` : « un zéro = un premier n'est qu'une étiquette de rang »), et l'événement premier n'appartient à aucune sous-somme finie de composantes (`finite_components_differentiableAt`, §7 de `GeneratedFrequency`) : aucun premier individuel ne « porte » une fréquence.
3. **Même hauteur, occurrences distinctes** est compilé sous un zéro OFF : `off_event_increment_without_height`, `off_mirror_two_grammars`, `rank_step_counts_members_not_heights` (« la grammaire compte des MEMBRES, aveugle à la hauteur »), `mirror_facts`. Le noyau RH était déjà compilé : `riemannHypothesis_iff_fibres_singleton` (deux membres de même hauteur sont égaux ⟺ RH).
4. **Noms cités par les maîtres mais absents des sources Lean** : `grammarsAgree_iff_riemannHypothesis`, `horizontalExclusion_iff_riemannHypothesis`, `offPassages_heightProgression_iff_riemannHypothesis` (cités dans `GrammarForcesStop.lean:15`, `TwoClocks.lean:228`). À ne pas citer comme compilés.
5. **Maîtres** : aucune occurrence de « occurrences distinctes ⟹ hauteurs distinctes » ni de « fréquence imposée par l'occurrence » comme résultat ; §19.8.5 laisse ouverte « l'écart nouveau impose sa fréquence » ; §19.9.4 : la hauteur du membre sortant est fixée par l'ordre des passages, aucun théorème ne relie une amplitude à la hauteur du suivant autrement que par la hiérarchie, qui équivaut à la montée ; §19.15–§19.16 : caps et encadrements aveugles au radial.

#### 19.17.3 Module isolé `Terminal/OccurrenceHeightComposition.lean` (non ajouté à `RHV6Fresh.lean`)

Deux tentatives, les deux réussies (la seconde ajoute §5) ; quatorze théorèmes aux axiomes standard ; journaux dans `audits_compilation/occurrenceheightcomposition/`.

- **§1 `occurrence_injective`** : deux membres distincts portent deux premiers distincts.
- **§2 la cible du texte est RH.** `DistinctOccurrencesDistinctHeights` (occurrences distinctes ⟹ hauteurs distinctes) ⟺ RH (`distinctOccurrencesDistinctHeights_iff_riemannHypothesis`) ; forme consécutive `consecutive_heights_distinct_iff_riemannHypothesis`. Sens direct : un zéro OFF et son miroir sont deux membres distincts, d'occurrences distinctes, de même hauteur. Sens réciproque : sous RH, deux membres de même hauteur sont comparables seulement par la hauteur, donc égaux. **Conséquence** : un « théorème indépendant du régime ON » qui donnerait l'inégalité stricte serait une preuve de RH ; il ne peut pas être cherché comme un lemme intermédiaire. Cette cible est fermée, comme la cascade stricte (§19.14) et le plancher d'un pas (§19.16).
- **§3 la composition est aveugle sur le porteur** (tout porteur `C`) : `outgoing_occurrence_eq_expected` (les deux occurrences de la paire sont `p_n` et `p_{n+1}`, consécutives) ; `pair_reads_gaps_identically` (tout écart est lu par le même nombre de cellules par les deux membres) ; `pair_reads_own_step_identically` (le pas `p_n → p_{n+1}` est lu identiquement : hauteur fois logarithme du rapport, sur π) ; `pair_same_generated_frequency` (une seule fréquence engendrée par les premiers, dont chacun est témoin ; `ArithmeticFrequency` aussi) ; `pair_two_counting_places`, `pair_in_same_window` (deux places du comptage dans la même fenêtre). Aucun de ces énoncés ne voit la position radiale.
- **§4 ce qui est sensible au radial au premier partagé** : `outgoingRaccord_not_oriented` (dès la hauteur 2, le transport au premier `p_{n+1}` est renversé) ; `mirror_occurrence_of_mirror_case` (cas miroir : l'occurrence du miroir est `p_{n+1}`) ; `pair_transport_at_occurrence` (valeur exacte du transport zéro → miroir en `p_{n+1}` : `p_{n+1}` à la puissance deux fois le décalage radial, fois le rapport des normes des points). Sur tout passage vertical, le transport est orienté quelles que soient les positions radiales (`towerRaccord_oriented_of_height_lt`, déjà compilé).
- **§5 le motif des trois raccords** (étude sur trois zéros, cas miroir, hauteur ≥ 2) : `three_raccords_pattern` — hiérarchie à l'arrivée (dernier ON → zéro OFF), hiérarchie brisée à la sortie (zéro OFF → miroir), hiérarchie rétablie après (miroir → membre suivant) ; `three_transports_pattern` — orienté, renversé, orienté. C'est la lecture radialement sensible des trois événements de §19.16.

#### 19.17.4 Verdict et nouveau plan

1. **Réponse à la question du texte.** Non : la composition comptage + occurrences + lecture des fréquences ne produit aucune inégalité stricte entre les hauteurs de deux membres consécutifs, et elle ne le peut pas sans RH : l'inégalité stricte demandée EST RH (§2). L'intuition « les fréquences sont imposées par les rencontres et par la reconstruction exacte » est juste comme obligation collective (§19.15 : toutes les fréquences occupées jusqu'à l'infini), mais elle n'attribue aucune fréquence à un premier individuel (§19.17.2, point 2).
2. **Changement d'objet.** La question « la fréquence réellement portée par l'occurrence `p_{n+1}` » n'a pas d'objet compilé. L'objet compilé sensible au radial à ce premier est le **transport** du raccord, de valeur exacte connue, renversé pour la paire et orienté sur tout passage vertical. Le motif des trois raccords (orienté, renversé, orienté) est la signature compilée de la paire sur trois zéros.
3. **Plan.** (a) Cible nouvelle, nommée et non posée : un **théorème arithmétique qui fixe ou borne le transport au premier partagé** depuis les premiers seuls (sans passer par la hauteur ni par la position radiale). S'il existe, le motif « orienté, renversé, orienté » est confronté à une valeur imposée ; s'il n'existe que sous une borne du reste des premiers, il est RH (§15) et la route renomme RH. (b) Audit préalable des seuls canaux arithmétiques exacts du corpus écrits sans zéro : le saut de pente `Λ(N)` aux événements premiers (`arithmetic_primitive_slope_jump`), la rencontre collective (`collectiveMeeting_component_eq_neg_rest` : une composante vaut l'opposé de la somme des autres, rien n'y fixe une composante), la cassure de §19.13 (réalisée par la totalité). Ces trois canaux sont collectifs ; aucun n'est local à un premier. Le plan doit établir, avant toute compilation, si un canal arithmétique LOCAL au premier partagé existe dans le corpus ; sinon, consigner que la frontière reste `ContinuationForced` et ne pas fabriquer de contradiction. (c) Interdits maintenus : ne pas poser `hgap`-type (`π ≤ T·log(p_{n+1}/p_n)`), ne pas comparer la paire à deux zéros ON fictifs, ne pas moyenner.

Frontière inchangée : `ContinuationForced` ⟺ RH. Les cibles « cascade stricte », « plancher d'un pas », « occurrences distinctes ⟹ hauteurs distinctes » sont toutes trois compilées comme RH et ne doivent plus être cherchées.

### 19.18 Exécution du plan §19.17.4 en « vraies valeurs » : le canal local au premier est `Λ(M) = log M`, le contenu premier du détour OFF est exact et jamais égal à un (2026-10-30)

#### 19.18.1 Consigne de l'auteur
Aucune fonction statistique, aucun reste de logarithme prévisionnel, aucune valeur estimée : les vraies valeurs connues (table exacte des
premiers, poids exact `Λ`), la logique d'abord, puis le compilateur. Module isolé `Terminal/TransportAtSharedPrime.lean` (non ajouté à
`RHV6Fresh.lean`), vingt-et-un théorèmes, axiomes standard, deux tentatives (la seconde réussie), journal `audits_compilation/transportatsharedprime/`.

#### 19.18.2 Audit (b) du §19.17.4 : le canal arithmétique local à un premier EXISTE
Le transport au premier partagé `M` s'écrit `exp((β_l − β_e) · Λ(M)) · ‖ρ_e‖ / ‖ρ_l‖` (`energyRatio_eq_exp_vonMangoldt`), où `Λ(M) = log M`
est le saut de pente de la primitive arithmétique en `M` (`vonMangoldt_eq_slope_jump`, instance du canal compilé sans zéro). C'est le seul
point du corpus où un premier individuel entre dans une grandeur radialement sensible, et il y entre multiplié par la différence des positions
radiales : sur tout passage vertical, le premier est invisible (`energyRatio_vertical_prime_free`, `energyRatio_vertical_eq`) ; pour la
paire OFF, il est multiplié par deux fois le décalage (`pair_transport_exp_vonMangoldt`).

#### 19.18.3 Vraies valeurs compilées
Sur tout porteur `n ≥ 1` (premier membre ON, `one_le_n`) : occurrence du zéro OFF `≥ 3`, premier partagé de la sortie `≥ 5`
(`zero_occurrence_ge_three`, `sharedPrime_ge_five`, par `p_1 = 3`, `p_2 = 5`), facteur arithmétique de la sortie `≥ 5^(2δ) > 1`
(`pair_arithmetic_factor_ge_five_pow`). Les trois premiers partagés du détour sont consécutifs (`detour_primes_consecutive` ; arrivée `p_n` :
`prevMember_expectedMinimumPrime` ; reprise `p_{n+2}` : `nextMember_occurrence_eq`, `mirror_expectedMinimumPrime` sous l'hypothèse miroir explicite).

#### 19.18.4 Le contenu premier du détour : fixé par les premiers seuls, jamais égal à un
Produit des trois transports du détour, identité exacte sans hypothèse sur la reprise (`detour_transport_product`) ; reprise sur la ligne :
`(p_{n+1}² / (p_n · p_{n+2}))^δ` fois le rapport des normes extrêmes (`detour_transport_product_onLine`), c'est-à-dire fois ce que transporte la
chaîne ON entre les mêmes extrêmes (`onLine_chain_transport`). La base `p_{n+1}² / (p_n · p_{n+2})` est un rationnel exact de la table des
premiers, jamais égal à `1` (`primeAtRank_sq_ne_mul`, `detourPrimeContent_ne_one`), égal à `exp(ℓ_n − ℓ_{n+1})` avec `ℓ_k` le logarithme
d'écart de rang (`detourPrimeContent_eq_exp_logGaps`), supérieur à `1` exactement quand le pas propre de la paire est plus long en logarithme
que le pas suivant (`detourPrimeContent_gt_one_iff`). Conséquences : le facteur arithmétique du détour n'est jamais `1`
(`detour_arithmetic_factor_ne_one`) et **le détour OFF ne transporte jamais la valeur de la chaîne ON** entre les mêmes extrêmes
(`detour_transport_ne_onLine_chain`). Jumeau déterministe E399 (`experiments/E399_DetourPrimeContent/`, pré-enregistré, 3 s) : sur
1 270 604 rangs exacts, zéro égalité ; 655 103 rangs amplifiés, 615 501 atténués (recensement, pas une loi) ; `(3,5,7)` amplifie, `(5,7,11)`
atténue ; fichier réel de 2 001 052 hauteurs strictement croissant, donc aucun détour réel dans le catalogue (rectifié en §19.19 : ce n'est pas la base qui vaut un sur la ligne, c'est l'exposant radial qui s'annule ; la base ne vaut jamais un).

#### 19.18.5 Verdict honnête et frontière
Le plan §19.17.4 (a) est réalisé pour la BASE du transport et irréalisable pour l'EXPOSANT : les premiers fixent `p_{n+1}² / (p_n · p_{n+2})`
exactement ; `δ` est la donnée radiale du zéro et aucun canal arithmétique ne la touche. L'inégalité « détour ≠ chaîne ON » n'est pas une
contradiction : aucune loi compilée n'impose au détour de transporter la valeur de la chaîne ON. Interdits respectés : aucune borne de type
« un pas vaut au moins une cellule », aucune comparaison à des zéros ON fictifs, aucune moyenne ; cas miroir et reprise sur la ligne toujours
posés comme hypothèses explicites. Question ouverte, nommée et non posée : existe-t-il, dans le corpus, une conservation compilée du transport
le long de l'énumération canonique (ce que la chaîne transporte entre deux extrêmes ne dépendrait pas du chemin) ? Si oui, elle fermerait
le détour par `detour_transport_ne_onLine_chain` ; l'audit du corpus sur ce point est la prochaine étape, AVANT toute compilation. Frontière
inchangée : `ContinuationForced ⟺ RH`.

### 19.19 Audit de la chaîne de définitions du transport (auteur, 2026-10-30) : rien n'est conservé, le défaut est une lecture

**Consigne de l'auteur.** Ne plus chercher « un théorème qui impose que tous les transports soient conservés », mais : quelle
grandeur déjà définie dans la reconstruction exacte des premiers est transportée par le rapport énergétique, et quelle identité
impose sa valeur aux raccords successifs ? Trois contrôles : nature de l'énergie ; conservation effective ; contrainte au raccord
(égalité de deux évaluations, ou seulement comparaison). Si aucune identité de conservation ne figure dans l'existant, ne pas
l'inventer. Audit de tout le corpus (Lean du build principal, modules isolés, maîtres, expériences, inventaires), pas du seul Lean.

**19.19.1 Chaîne auditée.** `energyRatio e l q` est le quotient des modules de deux termes de la formule explicite,
`‖zeroTerm l q‖ / ‖zeroTerm e q‖` (`SuccessionInvariants`). `zeroTerm z q = q^ρ/ρ` est le terme sommé par la formule explicite :
sa multiplicité fois ce terme est la contribution du zéro à la somme tronquée, et son terme dans le reste lissé est moins la
multiplicité fois ce terme divisé par `ρ + 1` (`spectral_organism_member`, `residueTerm_eq_zeroTerm`). `TowerRaccord e l` porte
le premier partagé `M = p_min(e) = Occ(l)`, deux cellules, deux ENCADREMENTS stricts de l'énergie de `M` par les contacts
(`exitEnergy`, `entryEnergy`), et l'IDENTITÉ `energyRatio e l M = M^{β_l − β_e} · ‖ρ_e‖/‖ρ_l‖` (champ `transport`) ; son
orientation est une COMPARAISON (`Oriented` ⟺ transport `≤ 1`). `GrammaticalRaccord` (`PrimalEventRaccord`) ajoute l'événement
premier complet de `M`, reconstruit depuis les zéros (`reconstructedEvent_eq_primalEvent`, inconditionnel). La reconstruction
exacte est : `ψ` reconstruite depuis les zéros (`spectral_organism_reconstructs`), le reste lissé égal à la somme de tous les
termes lissés (`smoothedRemainder_eq_tsum_residueTerm`), et `ΔR(a,b)` arithmétique = spectral entre deux marches
(`remainderBetween_eq_spectral`, `remainder_record`).

**19.19.2 Contrôle 1, nature de l'énergie.** Le module d'un terme est analytique (module d'un vrai terme de la formule
explicite, `x^β/‖ρ‖`). Le RAPPORT de deux modules de deux zéros distincts en une même abscisse est une grandeur définie par le
projet : aucune identité de zêta ne somme ni ne compare des modules. La formule explicite somme des termes complexes avec
leurs multiplicités ; toutes les identités de reconstruction du corpus portent sur cette SOMME.

**19.19.3 Contrôle 2, conservation effective : AUCUNE.** Les seules identités qui enchaînent des transports sont des produits
télescopiques : `two_raccord_transport`, `history_transport_product`, `fibre_transport_product` (build principal) ; les normes
`‖ρ‖` se simplifient, il reste les puissances des premiers partagés. Le contenu arithmétique qui reste, `historyCharge`,
est multiplié à chaque membre ajouté par le pas de ce membre `memberStep z = (Occ(z)/p_min(z))^{β_z − 1/2}`
(`historyCharge_succ`), neutre si et seulement si le membre est en ligne (`memberStep_eq_one_iff`,
`historyCharge_const_one_iff`, « caractérisation, jamais une prémisse »). Ce que le corpus appelle « loi de conservation »
(`riemannHypothesis_iff_conservation_and_base`, `conservation_of_riemannHypothesis`, `entry_arrow_iff_upper_conservation`,
`conservation_iff_nested_and_noTranslation`) est la loi « départ en ligne ⟹ arrivée en ligne » : avec l'amorce, c'est RH ;
elle n'est pas dérivée (`Audit.lean` 35 : « La loi n'est pas dérivée ») ; elle est violée dans le monde témoin
(`conservation_not_structural`). Dans les expériences, « conservation » désigne autre chose encore : le télescopage binaire
des transitions d'états (E353, identité tautologique) ou la rigidité radiale finie (GRAMMAR_RADIAL_ON_CONSERVATION, qui dit
elle-même « ne pas présenter comme une loi »). La seule indépendance de chemin compilée est celle d'une lecture à exposant
CONSTANT (`chain_reading_telescopes`, `chain_reading_endpoint_only`) : deux chaînes de mêmes extrémités ont même lecture
cumulée quand l'exposant ne change pas. Le détour change l'exposant deux fois ; sa charge est exactement le défaut
d'indépendance de chemin, et aucune identité ne la fixe.

**19.19.4 Contrôle 3, contrainte au raccord : COMPARAISON, jamais égalité.** Le premier partagé fixe l'abscisse où les deux
Tours sont évaluées ; il n'impose aucune égalité de deux évaluations. L'égalité du rapport en deux abscisses équivaut à
`β_w = β_z` (`transport_ratio_eq_at_two_points_iff`) ; les « deux égalités de normes » d'E116 équivalent à même partie réelle
et même module du support et sont FAUSSES sur tout passage qui monte (`raccord_norm_equalities_false_of_vertical`). Toute
égalité de transport est donc une lecture radiale, jamais une contrainte des premiers.

**19.19.5 Doublon reconnu, et compilé.** L'objet de §19.18, `p_{n+1}²/(p_n·p_{n+2})` élevé au décalage, existait déjà dans le
build principal : charge d'une fibre (`fibre_transport_product_off`, `fibre_charge_eq_one_iff`, `RaccordDetector`), charge d'une
cellule de régime (`RegimeCell.charge`, `charge_ne_one`, `charge_reads_translation`), charge lue sur les écarts
(`primalEvent_charge_by_gaps` : `M₂² − M₁M₃ = M₂(g_in − g_out) + g_in·g_out`), charge de fenêtre (`TwoGapWindow` : « une
LECTURE de `d` ; aucune identité de la base ne la fixe »), et au maître (items 52, 57, 108, 110 ; §1875). Le recensement E399
reproduit E158 (664 576 triples, 51,59 % amplifiants, 0 égalité) et E232 (51,85 %) sur un intervalle plus long (1 270 604
rangs, 51,56 %). Ce qui est propre à §19.18 : l'indexation par le rang du porteur canonique (trois premiers consécutifs
`p_n, p_{n+1}, p_{n+2}` imposés par le porteur, non choisis), le canal `Λ(M)` lu comme saut de pente, les vraies valeurs
(occurrence ≥ 3, premier partagé ≥ 5), l'écriture par les log-écarts de rang. Pour fixer le doublon exactement, compilé
(`TransportAtSharedPrime` §4, tentative 4 réussie, 22 théorèmes, axiomes standard) :
`detour_defect_eq_memberStep_product` : dans le cas miroir, le défaut du détour est le produit des deux pas de membre
`memberStep zero · memberStep (mirror)`, c'est-à-dire deux applications de `historyCharge_succ`.

**19.19.6 Rectification d'E399 (auteur).** « Fichier réel strictement croissant ⟹ base 1 sur tout passage réel » était FAUX.
La base `B_n` ne vaut JAMAIS un (`primeAtRank_sq_ne_mul`), quelles que soient les hauteurs. Ce qui vaut un dans une chaîne ON
est le FACTEUR `B_n^δ` avec `δ = 0` : c'est l'exposant radial qui s'annule, pas la table des premiers. Le fichier réel
strictement croissant dit seulement qu'aucun détour réel n'existe dans le catalogue. README d'E399 et §19.18.4 rectifiés.

**19.19.7 Réponse à la question réduite.** « La reconstruction arithmétique impose-t-elle une identité que le défaut
`D_n ≠ 0` viole ? » NON, dans l'état du corpus, et la cause est nommée : toutes les identités de reconstruction portent sur
des SOMMES de termes complexes (ψ, reste lissé, `ΔR` entre deux marches) ; le défaut est un PRODUIT de rapports de modules
de deux termes individuels. Aucune identité compilée ne relie un produit de modules à une somme de termes. La paire entre
dans les sommes par sa déformation, qui est PAIRE en la profondeur et de signe fixé par la phase (`gapPairDeformation_even`,
`TwoGapWindow` ; item 109), tandis que le logarithme du défaut est LINÉAIRE en la profondeur : les deux lisent `δ ≠ 0`,
aucune ne le contredit. Pour que la reconstruction interdise le défaut, il faudrait qu'elle borne la somme (croissance en
racine du reste), ce qui est RH (`whole_winding_all_passages_iff_remainder_sqrt_growth`, §15 : interdit de le poser).
Verdict : cette famille de transports ne peut pas fermer RH à elle seule, et l'on sait exactement pourquoi : elle lit la
position radiale, elle ne la contraint pas.

**19.19.8 Décision.** `detour_transport_ne_onLine_chain` et `detour_defect_eq_memberStep_product` sont conservés : rigidité
réelle (défaut non nul, fixé par trois premiers consécutifs et le décalage radial). La recherche d'une conservation générale
du transport est SUSPENDUE : elle n'existe pas dans le corpus et l'inventer serait poser RH. Frontière inchangée :
`ContinuationForced ⟺ RH`. Prochaine question légitime, nommée et non posée : existe-t-il, dans la reconstruction, une
identité qui porte sur un terme INDIVIDUEL (et non sur la somme) à l'abscisse d'un premier ? Le seul candidat compilé est
le saut de pente `Λ(M)` (`arithmetic_primitive_slope_jump`), qui est une somme sur tous les zéros au point `M` ; l'auditer
AVANT toute compilation.

### 19.20 Pourquoi le premier zéro est ON, et le deuxième, et le troisième : la chaîne de causalité (auteur, 2026-10-30)

Question de l'auteur : « pourquoi le premier zéro est ON ; quelle raison fait que le premier, le deuxième et le troisième sont
ON ? ». Première réponse rejetée par l'auteur : le comptage certifié de la première bande et l'annulation du miroir « découvrent
simplement le fait accompli » ; ce ne sont pas les causes. La réponse ci-dessous est la chaîne de causalité du projet (graphe
§16.5, `MeetingPoint` §9, `ConstantAmplitudeNeed`, `TotalityPays`, E310, E335, E392, E394, E239), dans l'ordre des causes, avec
le statut de chaque flèche : compilée, mesurée avec jumeau, ou non dérivée. Rien n'est posé.

**19.20.1 La chaîne, dans l'ordre des causes.**

1. *La donnée unique : les premiers et leurs écarts.* Chaque écart porte une demande, définie par les premiers seuls : ce que la
   somme lissée des premiers excède du fond lisse entre le début et la fin de l'écart. Aucun zéro n'entre dans sa définition.
   Compilé (`localArithmeticTarget`).
2. *La rencontre obligatoire.* La demande est remplie à un point unique, la fin de l'écart ; la somme des parts de tous les
   signaux y est exactement la demande ; la part de chacun est fixée par ses trois paramètres (amplitude, fréquence, calage).
   Compilé (`localSynchronization`, `imposedShare_at_meeting`) ; vérité non réfutable.
3. *La fréquence attendue (point générique, rendu générique à la demande de l'auteur le 2026-10-30).* À chaque écart, la
   part de la demande que les signaux déjà présents ne remplissent pas à la rencontre appelle un signal nouveau ; la
   fréquence qu'elle appelle est la fréquence attendue, définie par les premiers et par les signaux déjà présents, lue au
   point de rencontre, à la fin de l'écart. Le signal de rang suivant est celui qui prend cette fréquence ; sa hauteur n'en
   est que la conséquence (la fréquence d'un membre EST le nombre que la chaîne appelle hauteur, compilé
   `memberFrequency_eq_height`). Le premier zéro est l'instance de rang un : aucun signal avant lui, donc la fréquence
   attendue de la première cassure (de deux à trois) est la sienne ; le deuxième et le troisième sont les instances de rang
   deux et trois, appelées par ce que le premier, puis les deux premiers, laissent aux rencontres suivantes. Statuts :
   la demande non remplie à la rencontre est compilée (obligation sur la somme, `localSynchronization`) ; que le signal
   suivant prenne la fréquence attendue est MESURÉ depuis les premiers seuls, sans hauteur connue, sans zêta, sans
   Odlyzko : rang un à sa fréquence au dix-millionième et rencontre de la première cassure à un centième de pas (E335,
   E392, non-circularité contrôlée, jumeaux ; E310 depuis la courbe des écarts), rangs deux et trois retrouvés (E335,
   régime initial) ; que la fréquence attendue MONTE à chaque passage est la prémisse unique, nommée, jamais posée,
   équivalente à « aucun passage n'a ses deux membres à la même fréquence » (`expectedFrequency_iff_no_shared_frequency`),
   donc à RH. Au rang un il n'y a rien à faire monter : le point 3 y est pure lecture inverse ; aux rangs suivants il
   contient la prémisse. MESURÉ, NON COMPILÉ (raison en 19.20.3).
4. *Sur la ligne : le niveau de la demande.* La demande des premiers, lue aux rencontres et rapportée à la racine du point, garde
   un niveau constant d'un écart à l'autre : mesuré sur quatre décades, pente nulle, maximum qui ne grandit pas, jumeau (E394).
   Un signal qui remplit une demande de niveau constant a une amplitude relative constante entre deux rencontres, et cette
   constance équivaut exactement à la position radiale un demi ; sous la ligne la part décroît et son miroir croît sans borne.
   Compilé (`constantRelativeAmplitude_iff_onLine`, `pairRelativeAmplitude_unbounded`). Depuis les premiers seuls, l'exposant
   d'amplitude du premier mode est lu un demi, par cinq estimateurs, sur quatre décades (E335, E310). Un premier zéro hors
   ligne serait un couple dont le prix aux rencontres n'est pas borné, que ni un historique (vide ici) ni aucune famille finie
   ne paie ; il faudrait une infinité d'autres zéros strictement à droite (compilé, `TotalityPays`). Le premier zéro est
   dominant : son retrait dégrade la reconstruction plus que tout autre (E239, vingt-sept fenêtres sur vingt-sept).
5. *Le constat, en aval.* Le comptage à un dans la première bande et l'annulation du miroir vérifient ce que la chaîne impose :
   un seul signal, égal à lui-même, sur la ligne. C'est l'aval ; ce n'est pas la cause.

**19.20.2 Deuxième et troisième zéros.** Le premier signal, seul, cesse de rencontrer les fins d'écarts suivantes : ses fractions
de pas tombent loin de zéro et de un dès l'écart de trois à cinq (E392). La demande des écarts suivants exige un signal de
fréquence strictement supérieure, jamais un retour de fréquence : c'est la cadence, et le régime ON est le seul régime stable
sous elle (§16.2). Le deuxième et le troisième zéros sont les instances de rang deux et trois du point 3 générique : les deux
fréquences attendues suivantes, appelées par ce que les signaux déjà présents laissent aux rencontres de trois à sept ; depuis les premiers seuls, leurs fréquences et leurs exposants sont retrouvés, les trois décalages radiaux lus nuls
(E335, régime initial). Même cause pour chacun : niveau constant de la demande aux rencontres, donc amplitude relative
constante, donc ligne. Les comptages à deux puis trois constatent.

**19.20.3 Pourquoi le point 3 est mesuré et non compilé.** Trois raisons, toutes dans le corpus, aucune nouvelle.

- *La formule explicite n'est compilée que dans un sens.* Ce qui est démontré est : les zéros donnés, leur somme reconstruit le
  reste lissé des premiers (`smoothedRemainder_eq_tsum_residueTerm`, `smoothedCanonical_hasSum`). Le point 3 lit dans l'autre
  sens : les premiers donnés, en extraire la première fréquence. Cette lecture inverse est une transformée du reste des
  premiers sur TOUT l'axe (E334, E335 : contre une fenêtre gaussienne, la transformée est une somme exacte de pics, un par
  zéro). L'identité de la transformée est compilable ; ce qui ne l'est pas, c'est la valeur du pic : elle demande l'intégrale
  sur tous les premiers, à l'infini. Toute troncature à un horizon fini donne une estimation, et l'erreur de troncature est
  contrôlée par la taille du reste des premiers au-delà de l'horizon, c'est-à-dire par le niveau de la demande : l'unique
  flèche ouverte du §16.5. Le point 3 n'est donc pas une lacune de compilation distincte ; c'est la même inconnue, lue en
  fréquence.
- *La rencontre par terme à trois est une mesure avec tolérance, pas une identité.* La fraction de pas vaut un centième de
  l'unité, lue par une règle d'arrondi ; aucun énoncé compilé ne dit qu'un terme seul rencontre une fin d'écart, et E392 montre
  que cette forme échoue dès l'écart suivant. L'obligation compilée porte sur la somme (§19.10 : la lecture littérale par terme
  est FAUSSE). Ce qui tient au premier écart pour le premier zéro est un fait numérique du premier écart, pas un théorème.
- *Le canal de comptage n'est pas formalisé.* La « cassure » de la courbe des premiers est lue dans le canal de comptage
  (reste de Li), dont la formule explicite est seulement NOMMÉE (`CountingExplicitFormula`, `CountingFieldArchitecture` §6) et
  dont la fonction de base est absente de Mathlib (E204, `LocalPrimeGapSynchronization` §3). Le seul canal compilé est le canal
  lissé, où la cassure est adoucie en une rencontre de somme.

Conséquence : « le signal de plus basse fréquence qui suit la première cassure est le premier zéro » est vrai depuis les
premiers par lecture contrôlée (non-circularité NC1 à NC4, jumeaux), et ne peut devenir un théorème qu'avec la flèche
ouverte, parce que l'exactitude de la lecture inverse d'un seul terme exige le contrôle du reste infini des premiers. Le
compiler en l'état serait poser une borne sur le reste (§15, interdit).

**19.20.4 Statut consigné.** Chaque flèche de la chaîne est compilée, sauf une : « les écarts premiers imposent un niveau borné
de la demande aux rencontres ». Elle porte la cause initiale de la ligne, pour le premier zéro comme pour tous ; pour le premier
zéro elle est mesurée vraie, avec jumeaux, depuis les premiers seuls ; elle n'est pas dérivée des premiers. C'est pourquoi le
dépôt enregistre que la seule cause démontrée en Lean de l'état ON des trois premiers est zêta entière par comptage, « aucune
cause locale isolée » (E239), « ces faits viennent de zêta entière, non des premiers » (`FirstArrivalsAnchor`). La cause
arithmétique existe dans le projet : lue, cohérente, contrôlée ; non compilée. Frontière inchangée (`ContinuationForced ⟺ RH`),
et la frontière du premier zéro est la même flèche que celle de tous les autres.


### 19.21 La rencontre exacte : doctrine, audit de fidélité du graphique, du Lean et des `.md`, et plan (auteur, 2026-10-31)

Demande de l'auteur : analyser `experiments/riemann_graphique.png` (commit 8c655ef7) à la lumière de sa contreproposition
(cinq points) et de la lecture du graphique, puis produire un audit de fidélité et de cohérence dans tout le Lean et les `.md`,
et un nouveau plan. Audit détaillé : `AUDIT_FIDELITE_RENCONTRE_EXACTE_20261031.md` ; note sur le graphique :
`experiments/riemann_graphique_ANALYSE.md`. Lecture seule : aucun Lean modifié, aucune compilation lancée.

**19.21.1 Doctrine consignée (texte de l'auteur, en mots).** (P1) Au point de rencontre, fin de l'écart, la totalité des parts
reconstruit exactement la demande ; le défaut est nul ; aucune marge, aucune rencontre ratée, rien à rattraper. (P2) « Total =
paire OFF + autres » est une identité ; les autres zéros ne sont ni une erreur tolérée ni une réserve ; et l'égalité de la
totalité ne donne pas « chaque zéro fournit une quantité déterminée par l'écart », qui demande une relation supplémentaire.
(P3) La liaison zéros–premiers est permanente, inconditionnelle, avec les vrais zéros quelle que soit leur position radiale ;
les rencontres géométriques du projet sont une structure en plus, à auditer contre la formule. (P4) Proscrits : résidu
acceptable à la rencontre, autres fréquences comme réserve, compatibilité d'OFF lue dans « cible moins OFF », identité de
décomposition prise pour preuve de compatibilité ; et, à l'inverse, l'absence de défaut n'exclut pas un OFF. (P5) Cible non
démontrée : reconstruction exacte, contacts authentiques, succession canonique, premier partagé impliquent-ils un demi ?

**19.21.2 Statut compilé de la doctrine.** P1 est compilée : `localArithmeticTarget` (premiers seuls) égale la somme sur tous les
vrais zéros (`localSynchronization`, `all_signals_meet`), et aucune famille finie ne l'accomplit près d'une rencontre
(`exactness_is_a_demand`). P2 est compilée : le résidu d'une troncature finie est la queue (`localResidual_eq_tail`) ; « total =
couple + reste » est une identité (`remainder_eq_pair_add_rest`) ; la cassure est fournie exactement par le complément
(`break_compensated_by_other_frequencies`), pour toute famille. P3 est compilée : la reconstruction tient pour toute position
radiale (`authentic_family_reconstructs_any_radial`, `localSynchronization_from_explicit_formula` sans radial). La réciproque de
P4 est compilée : toute position radiale jusqu'à un demi satisfait les obligations de contact (`parameter_grid_admissible`) ; les
raccords existent sur tout passage. P5 n'est pas compilée et porte un nom : tout théorème qui conclut la ligne passe par une
hypothèse nommée équivalente à RH (`ContinuationForcedOnCarriers`, `ExpectedFrequencyRisesAtMeetings`, hiérarchie sur tout
passage, hauteurs consécutives distinctes, loi de constance par membre). La « relation supplémentaire » de P2 est identifiée :
la part d'un membre à la rencontre est définie par le membre (`imposedShare_at_meeting`) et `imposedShare_eq` l'écrit « cible
moins les autres », identité sans contrainte ; la forme la plus faible d'une détermination par l'écart est l'amplitude relative
constante entre rencontres, équivalente à la ligne pour ce membre (`constantRelativeAmplitude_iff_onLine`) et, universalisée, à
RH (`constantNeed_law_iff_riemannHypothesis`). Nommée, jamais posée.

**19.21.3 Verdict sur le graphique.** Panneau 1 (rencontre exacte) : fidèle sur le principe ; trois corrections de lecture
(puissances de premiers omises alors qu'elles portent une cassure, §19.13 C1 ; le canal compilé est lissé, le contact « au
coin » est une image du canal de comptage non formalisé ; axe dit logarithmique, tracé linéaire). Panneau 2 (« impasse
spectrale OFF ») : infidèle. Le théorème cité dit « amplitude relative de la paire non bornée le long des rencontres », en
norme, sans limite ni signe ; le « total fixe » n'est pas compilé (demande bornée aux rencontres = hypothèse nommée ; bornée
partout ⟺ RH) ; le « plafond » n'est que la somme finie des poids lissés, qui ne borne le reste que sous l'hypothèse nommée
« reste jamais à droite », alors que le miroir d'un OFF est à droite ; le schéma « OFF diverge, ON plafonné, donc ligne » est
exactement `not_low_of_bounded_demand_and_restNotRight`, dont les hypothèses réunies équivalent à RH : circulaire. Panneau 3 :
le gel est fidèle (`single_frozen_step_of_mirror`) ; la « montée stricte » du régime ON est la cible (cascade stricte ⟺ RH,
§19.16), pas un fait du régime réel. Encart, point 4 (« l'égalité exacte interdit une paire OFF, conséquence formelle un
demi ») : établi nulle part, contredit le premier texte de l'auteur (« l'absence de défaut global ne suffit pas à exclure un
OFF ») et §19.13.2. Les deux textes de l'auteur divergent sur ce point ; le dépôt soutient le premier, qui est retenu.

**19.21.4 Verdict d'audit.** Lean : aucune infidélité mathématique ; aucun théorème ne traite un résidu non nul comme
admissible, ne répare une rencontre avec les autres zéros, ne conclut la compatibilité d'OFF depuis « cible moins OFF ». Cinq
défauts de vocabulaire sans effet sur les preuves : « marge admissible, écart admissible » (`LocalWindowTransmission`,
`CertifiedRemoval`) ; « compensation maximale du complément » (`JointComparison`) ; « compensation forcée », nom
`break_compensated_by_other_frequencies` (`HeightPacket`, `OffCarrier`) ; « annulation fournie par, ce que la totalité doit
payer, ce que la ligne peut payer » (`TotalityPays`, `RemainderRegime`) ; docstring « compensation par d'autres modes »
(`FirstArrivalsAnchor`). `.md` : aucune tolérance à la rencontre nulle part ; aucune occurrence de « rencontre ratée »,
« rattraper », « conséquence formelle » ; aucun plafond sur l'amplitude totale. Infidélités réelles, par gravité :
(1) §19.20.1 point 4 lit membre par membre une demande qui porte sur la somme (contredit §19.10.2, E394 « non établi que la
demande exige cette constance à chaque membre ») ; (2) §19.20.2 « même cause pour chacun : niveau constant, donc amplitude
constante, donc ligne » présente une mesure comme cause ; (3) §19.20.4 « chaque flèche compilée sauf une » alors que le point 3
est mesuré et le point 4 repose sur E394 ; (4) ligne 2184, corrigée en 2228 sans annotation ; (5) lignes 2157, 2163, 2167
périmées (« tout le reste est fermé », démenti par §17–18) ; (6) ligne 2052, réfutation attribuée à un théorème non
identifié alors que ces théorèmes sont conditionnels ; (7) §19.20.2 « ni un historique ni aucune famille finie ne paie » omet
l'hypothèse de demande bornée ; (8) lexique « payer le prix » (§16.5 à §17, E396, E397) ; (9) §19.8 et §16.5 « tous les
signaux se rencontrent, théorème » en tension avec la lecture littérale déclarée fausse ; (10) « part imposée » présentée comme
contrainte ; (11) la règle d'arrondi d'E392 (0,988 compté comme rencontre) sert d'appui causal, et E392 n'a pas de
pré-enregistrement ; (12) « seul régime stable » se lit comme une exclusion.

**19.21.5 Rectifications consignées (le journal n'est pas réécrit).** §19.20.1 point 4 et §19.20.2 sont à lire ainsi : la
constance du niveau de la demande aux rencontres est une mesure (E394) ; elle ne se transmet à aucun membre ; « niveau
constant ⟹ amplitude relative constante du membre ⟹ ligne » n'est pas une flèche du graphe mais la relation supplémentaire
de P2, équivalente à RH. §19.20.4 est à lire : deux arrêtes ne sont pas compilées, le point 3 (fréquence attendue, mesuré) et
le point 4 (niveau constant par membre), et toutes deux sont la même inconnue. La ligne 2184 est remplacée par la ligne 2228.
Les lignes 2157, 2163, 2167 et 2052 sont périmées depuis §17–§19. « Tous les signaux se rencontrent » signifie uniquement
« la somme des parts égale la demande à la fin de l'écart » (§19.10.2). « Part imposée » signifie « part définie par le
membre, lue à la rencontre », jamais « imposée par l'écart ». E392 est une mesure à règle d'arrondi, sans valeur causale. Le
lexique « payer, prix, compensation, marge admissible » est remplacé, dans tout texte nouveau, par « identité du complément »
et « annulation exigée sous hypothèse nommée ».

**19.21.6 Plan (pré-enregistré ; aucune étape Lean lancée avant feu vert).**

* **Étape A, doctrine comme carte compilée.** Le tableau de 19.21.2 est la carte : P1, P2, P3 et la réciproque de P4 sont
  des théorèmes existants ; P5 est la frontière, sous ses noms. Aucune compilation nécessaire. Fait ici.
* **Étape B, module isolé `ExactMeetingAudit.lean` (non importé par la chaîne), six énoncés, tous dérivables de l'existant,
  aucune hypothèse nouvelle.** (B1) Pour tout porteur OFF canonique, la rencontre de son écart est exacte : instance de
  `localSynchronization` sur `C.meetingPred` ; c'est la réciproque de P4 écrite sur l'objet même que la contreproposition
  vise. (B2) Pour tout porteur, « total = paire + reste » à sa rencontre (`remainder_eq_pair_add_rest`), avec, dans le cas (a),
  le reste égal à « cible moins paquet de la fréquence » (`target_split_of_mirror`) : la décomposition est une identité, pour
  le porteur comme pour tous. (B3) L'énoncé P5 restreint au porteur, « pour tout porteur, contradiction », est équivalent à RH
  (`exists_offCarrier_of_not_riemannHypothesis` et la définition du porteur) : P5 est nommée et fermée comme cible, non
  prouvée. (B4) La relation supplémentaire de P2, « la part de chaque membre est constante en amplitude relative entre
  rencontres », est équivalente à RH (`constantNeed_law_iff_riemannHypothesis`), et, pour le porteur, elle échoue exactement
  pour l'arrivée basse et son miroir (`low_arrival_not_constantRelativeAmplitude`, `mirror_not_constantRelativeAmplitude`).
  (B5) Le schéma du panneau 2 est un théorème conditionnel dont les hypothèses réunies équivalent à RH : composition de
  `not_low_of_bounded_demand_and_restNotRight` avec `expectedFrequencyRises_iff_meetings_and_restNeverRight` et
  `riemannHypothesis_of_meetings`. (B6) Aucune borne compilée sur le reste à droite : `rest_unbounded_of_bounded_demand`
  réécrit avec son hypothèse apparente dans l'énoncé. Chaque tentative de compilation est journalisée dans
  `audits_compilation/exactmeetingaudit/` avec les erreurs exactes, comme pour les cinq modules précédents.
* **Étape C, vocabulaire du Lean.** Amender les cinq docstrings de 19.21.4 (aucun nom de théorème changé, aucun énoncé
  touché) ; proposer, sans l'exécuter, le renommage `break_compensated_by_other_frequencies` →
  `break_complement_identity` (module isolé). Toute modification d'un fichier importé par la chaîne attend l'auteur.
* **Étape D, graphique.** Si le graphique est refait : retirer le panneau 2 et le point 4 de l'encart ; annoter le panneau 3
  « montée stricte = cible » ; annoter le panneau 1 « vaut pour toute famille, OFF compris » et y mettre les puissances de
  premiers. Aucune figure n'est produite sans accord.
* **Étape E, ce que l'audit laisse comme seule question.** P5 demande une contrainte radiale que ni l'exactitude, ni les
  contacts, ni la succession, ni le premier partagé ne fournissent, pris ensemble tels que compilés (§19.19 : aucune
  conservation du transport ; `TransportAtSharedPrime` : les premiers fixent la base, jamais l'exposant). La relation
  supplémentaire est la constance par membre, équivalente à RH. La frontière est inchangée : `ContinuationForced ⟺ RH`,
  lue ici en amplitude. Rien n'est posé, rien n'est retiré, aucune expérience lancée.

### 19.22 Le « dernier contributeur » : évaluation du troisième texte de l'auteur (2026-10-31)

Troisième texte reçu le même jour. Il déplace la question de « chaque zéro fournit l'écart » vers « que se passe-t-il quand
le dernier contributeur nécessaire intervient » ; il pose qu'au point de rencontre le dernier contributeur doit fournir
exactement le solde (cible moins ce qui est déjà engagé), que ceci n'a de sens que si la rencontre est close à un rang
fini, et il demande de vérifier trois propriétés dans le Lean : existence d'un dernier contributeur canonique ; nullité
collective des contributions ultérieures sur l'événement clos ; égalité exacte de la part du dernier membre au solde,
avec une formule rendant `β` et `T`. Il conclut que cette existence est « le véritable verrou » à examiner avant toute
nouvelle tentative de contradiction OFF/ON.

**19.22.1 Évaluation question par question.** Les trois propriétés sont toutes tranchées par des théorèmes existants ;
aucune n'est ouverte.

1. *Un dernier contributeur canonique existe-t-il ?* Non, et c'est compilé : `no_finite_family_accomplishes_demand`
   (`MeetingExactness.lean`) dit qu'aucune famille finie de parts, quelle qu'elle soit, n'accomplit la demande sur un
   voisinage d'une rencontre. Raison : le reste des premiers n'est pas dérivable à la rencontre
   (`smoothedRemainder_not_differentiableAt_meeting`), alors que toute famille finie de parts l'est. La clôture à rang
   fini n'est pas « non affirmée par la formule explicite », comme le dit le texte : elle est réfutée. Poser « la
   rencontre est close au rang du membre » serait poser une prémisse connue pour fausse (interdit, §19 directives).
2. *Les contributions ultérieures sont-elles collectivement nulles sur l'événement clos ?* Non, compilé :
   `tail_not_eventually_zero` : pour toute famille finie, la queue des zéros omis n'est jamais identiquement nulle au
   voisinage d'une rencontre. Réponse à la question encadrée du texte (« un événement déjà reconstruit peut-il être
   modifié par les zéros de rang supérieur ? ») : il n'est jamais « déjà reconstruit » par un rang fini ; la queue
   intervient toujours. Le « théorème de clôture exacte des rencontres » que le texte espère est l'exact contraire
   d'un théorème compilé. S'y ajoute `localHeightResidual_bound` (`SynchronizationAudit.lean`) : après retrait de tous les
   zéros de hauteur au plus `H`, le résidu sur l'écart est l'incrément de la queue, borné par une constante indépendante
   de la position radiale de tout zéro, et `tail_bound_admits_offline_point` : cette borne n'est pas discriminante.
3. *La part du dernier membre égale-t-elle exactement le solde, avec une formule en `β` et `T` ?* L'égalité existe,
   pour tout membre et non pour un « dernier » : `imposedShare_eq` écrit la part d'un membre à la rencontre comme cible
   moins la somme des autres, et `imposedShare_at_meeting` la donne sur les trois paramètres (amplitude en `x^β/N`,
   fréquence `T`, calage). C'est l'identité du complément (§19.21, P2), pas une détermination : le solde est défini à
   partir des autres, qui dépendent des mêmes inconnues. Aucune formule ne « rend » `β` et `T` à partir du solde, parce
   que `authentic_family_reconstructs_any_radial` : la reconstruction exacte est satisfaite par la famille authentique
   quelle que soit sa position radiale. Déjà consigné en 19.21.2 et 19.21.5 (« part imposée » = définie par le membre).

**19.22.2 Ce que le texte apporte, et ce qu'il n'apporte pas.** Apports réels : (a) il rend explicite la différence entre
l'identité analytique (somme sur tout le spectre) et une succession chronologique de membres, que le §19.10 avait déjà
posée (la lecture littérale « chaque signal a un contact à la fin de chaque écart » est fausse ; l'obligation porte sur la
somme) ; (b) il fournit la forme précise de la lecture à ne plus jamais faire : « dernier contributeur ⟹ paiement
intégral du solde » est une implication à antécédent faux (point 1), donc vide ; son lexique (« paiement », « solde »)
est celui que 19.21.5 remplace par « identité du complément ». Ce qu'il n'apporte pas : aucune question nouvelle. Sa
« question de clôture, pas de compensation ultérieure » (point 4 du texte) revient, une fois la clôture finie réfutée, à
la question de 19.21 Étape E : quelle relation supplémentaire, au-delà de l'égalité collective, contraint la position
radiale ; la réponse consignée est la constance par membre entre rencontres, équivalente à RH, jamais posée.

**19.22.3 Verdict.** Texte utile comme confirmation de P2 et de §19.10, et comme mise en garde contre la lecture
« membre par membre » que §19.20 avait effleurée ; sans intérêt comme programme de recherche, puisque son verrou est
déjà fermé dans le sens négatif. Rien n'est à poser, rien n'est à chercher. Sa recommandation finale (« examiner ce point
avant toute nouvelle tentative de contradiction OFF/ON ») est satisfaite : `MeetingExactness.lean` l'a examiné.

**19.22.4 Plan.** Pas d'étape nouvelle. Deux énoncés s'ajoutent à l'Étape B de 19.21.6 (module isolé
`ExactMeetingAudit.lean`, toujours en attente de feu vert, aucune hypothèse nouvelle) : B7, « pas de dernier
contributeur sur le porteur » = `no_finite_family_accomplishes_demand` et `tail_not_eventually_zero` instanciés sur
l'écart de rencontre du porteur OFF ; B8, « la part d'un membre quelconque égale cible moins les autres, pour tout
membre, OFF compris » = `imposedShare_eq` instancié sur le membre OFF du porteur, lu comme identité. Rien d'autre.

### 19.23 Étapes B et C exécutées sur feu vert (auteur, 2026-10-31) : le porteur sous la rencontre exacte, compilé ; lexique corrigé

**19.23.1 Feu vert et périmètre.** L'auteur a donné le feu vert sur les étapes B et C de 19.21.6 (B complétée par
19.22.4) et demandé un point ensuite. Rien d'autre n'a été lancé : aucune expérience, aucun graphique (étape D en attente
d'accord), aucune hypothèse, aucune définition nouvelle, aucun fichier ajouté à `RHV6Fresh.lean`.

**19.23.2 Étape B, module isolé `ExactMeetingAudit.lean`, compilé.** Importe `OffCarrier`, `MeetingExactness`,
`DemandLevelPremise`, `ConstantAmplitudeNeed`. Dix-huit théorèmes, tous instances ou compositions de l'existant sur le
porteur OFF canonique `C`, son zéro, son écart `C.gap` et la rencontre `p_{n+1}` :

* B1 `carrier_meeting_exact`, `carrier_exactness_is_a_demand` : la rencontre de l'écart du porteur est au premier
  `p_{n+1}` et sa demande est accomplie par la totalité des zéros, porteur compris ; aucune famille finie ne l'accomplit
  sur un voisinage. Réciproque de P4 écrite sur l'objet visé.
* B2 `carrier_total_eq_pair_add_rest`, `carrier_target_split_mirror` : « total = paire + reste » à la rencontre du
  porteur, et, cas (a), « cible = paire lissée + paire conjuguée + autres fréquences ». Identités (P2).
* B3 `no_carrier_iff_riemannHypothesis` : « tout porteur est contradictoire » ⟺ RH. P5 nommée, fermée comme cible.
* B4 `constantRelativeAmplitude_law_iff_riemannHypothesis` (nouveau comme énoncé, preuve en trois lignes depuis
  `constantRelativeAmplitude_iff_onLine` et `riemannHypothesis_iff_noLowerSide`) : la relation supplémentaire de P2,
  « la part de chaque membre est constante en amplitude relative entre rencontres », équivaut à RH ;
  `carrier_zero_not_constantRelativeAmplitude`, `carrier_mirror_not_constantRelativeAmplitude` : elle échoue
  exactement au zéro OFF et à son miroir.
* B5 `panel_two_hypotheses_iff_riemannHypothesis` : « demande bornée aux rencontres et reste jamais à droite » ⟺ RH ;
  `carrier_contradiction_under_panel_two` : sous ces deux hypothèses nommées, le porteur est contradictoire. C'est le
  panneau 2 du graphique avec ses hypothèses apparentes : un théorème conditionnel dont les hypothèses sont la cible.
* B6 `carrier_rest_unbounded_of_bounded_demand`, `carrier_rest_or_demand_unbounded` : sous demande bornée aux
  rencontres, le reste relatif du porteur dépasse toute borne à une rencontre ; inconditionnellement, demande ou reste
  n'est pas borné. Aucune borne sur le reste n'est compilée.
* B7 `carrier_no_last_contributor`, `carrier_tail_not_eventually_zero`, `carrier_rest_not_eventually_zero` : pas de
  dernier contributeur sur le porteur ; la queue des zéros omis, et en particulier le reste hors couple, n'est jamais
  identiquement nulle au voisinage de `p_{n+1}`. La paire n'est jamais « dernier contributeur » (§19.22).
* B8 `carrier_share_eq_target_sub_others`, `carrier_mirror_share_eq_target_sub_others` : la part du zéro OFF, et celle
  du miroir, sur l'écart du porteur, égale l'incrément de la courbe des premiers moins l'incrément des autres. Identité
  du complément, sans détermination radiale.

Compilation : deux tentatives, journalisées dans `audits_compilation/exactmeetingaudit/` (sources et journaux). Tentative 1 :
une erreur, ordre des deux termes d'une somme dans l'énoncé B6 bis (`restRelativeAmplitude + demandRelativeLevel` dans
`totality_pays_or_demand_unbounded`, écrit à l'envers) ; corrigée en alignant l'énoncé sur le théorème source. Tentative
2 : construit, avertissements de longueur de ligne seulement. Aucun `sorry`, aucun `admit`, aucun axiome.

Ce que B établit, en mots : tout ce que la doctrine P1–P4 affirme est vrai du porteur lui-même, compilé ; tout ce que
P5 demande est, sur le porteur, soit une identité (B2, B8), soit un énoncé équivalent à RH (B3, B4, B5), soit un énoncé
négatif (B1, B6, B7 : rien de fini ne clôt, rien n'est borné). B ne fait pas avancer RH ; elle rend compilée la
cécité radiale de toute lecture à une seule rencontre, pour qu'aucune lecture de ce type ne soit reposée.

**19.23.3 Étape C, lexique du Lean.** Les cinq défauts de 19.21.4 sont amendés, docstrings seulement, aucun nom, aucun
énoncé, aucune preuve touchés : `LocalWindowTransmission` (« marge admissible », « écart admissible » → majoration de
norme, nom `windowMargin` conservé) ; `CertifiedRemoval` (idem) ; `JointComparison` (« compensation du complément » →
majoration du complément) ; `HeightPacket` (« compensation forcée… ce que les autres zéros doivent fournir » → identité
du complément, nom `compensation` conservé) ; `OffCarrier` (docstring de `break_compensated_by_other_frequencies` →
identité du complément ; renommage `break_complement_identity` proposé, non exécuté) ; `TotalityPays` (« annulation
fournie par les autres zéros », « ce que la totalité doit payer » → amplitude relative du reste, annulation exigée sous
hypothèse nommée) ; `RemainderRegime` (« ce que la ligne peut payer » → amplitude relative d'une famille sur la ligne) ;
`FirstArrivalsAnchor` (« compensation par d'autres modes » → identité du complément). Quatre de ces fichiers sont dans
la fermeture d'imports de `DemonstrationChain.lean` ; le diff est vérifié purement documentaire (aucune ligne de code
modifiée), et la bibliothèque entière plus les six modules isolés ont été reconstruits : `DemonstrationChain` et les huit fichiers amendés
reconstruits sans erreur, ainsi que `ExactMeetingAudit`, `MeetingExactness`, `OffCarrier`, `OccurrenceHeightComposition`,
`ThreeZeroWindow`, `FrequencyCap`, `TransportAtSharedPrime` (journal `audits_compilation/exactmeetingaudit/etapeC_full_build.log`).
Une erreur, au seul module racine `RHV6Fresh.lean`, **antérieure à cette session et indépendante des docstrings** :
`SpectralWindowProjection` et `GapTranslationInvariance` définissent tous deux `RHV6Fresh.windowProjection` (commits
0057fa64 du 2026-10-19 et c9eea2e5 du 2026-10-20, ce dernier consignant déjà « lake build RHV6Fresh EXIT=1, une
erreur ») et sont tous deux importés par la racine (lignes 182 et 197). Non corrigée ici : la racine importe la chaîne
et toute modification attend l'auteur. Correction évidente à sa décision : renommer l'un des deux ou retirer un import.

**19.23.4 Point.** Voir la réponse à l'auteur du 2026-10-31 ; la frontière est inchangée (`ContinuationForced ⟺ RH`,
constance par membre ⟺ RH). Étapes D (graphique) et E (audit de la signature de paire sur trois écarts) en attente.

### 19.24 Réorientation sur les contacts, les contributions par écart et la rencontre : audit complet (auteur, 2026-11-01)

Demande de l'auteur : réorienter tout le projet sur la chaîne « (β, T) → Tour → contacts → contribution exacte sur chaque
écart premier → rencontre (cassure) », sans plus aucune démarche statistique ni partielle ; prouver que les écarts des
contributions sont bien ceux de la rencontre ; auditer tous les théorèmes, les `.md`, les expériences ; produire le plan.
Audit complet : `AUDIT_REORIENTATION_CONTACTS_ECARTS_20261101.md` (219 modules, 4 135 théorèmes, quatre lecteurs
indépendants, annexes par module). Lecture seule : aucun Lean modifié, aucune compilation lancée.

**19.24.1 Les mêmes écarts : prouvé par construction.** Toutes les notions d'écart du dépôt sont indexées par la seule
structure `PrimeGapInterval` (un champ : le rang) et la seule fonction `fnPrimeAtRank`. La contribution brute
(`gapTerm`, `primeGapContribution` : exactement `(p_{n+1}^ρ − p_n^ρ)/ρ`, `gapTerm_eq_cpow`), la contribution lissée
(`smoothedLocalContribution` = `−m/(ρ+1)` × brute, `residueTerm_gap_eq`), la contribution de comptage (`countingGapTerm`,
différence d'`Ei`), la cible des premiers (`localArithmeticTarget`), la rencontre (`meetingPoint I = I.upper`, `rfl`),
l'écart du porteur OFF (`OffCarrier.gap = ⟨C.n⟩`, `liaison`), la paire sur l'écart (`pairCounting`, `pair_gapTerm_signature`,
`target_split`) et la cassure (`break_at_meeting`, `gap_demand_eq_break_add_rest`) portent les mêmes bornes
`fnPrimeAtRank n`, `fnPrimeAtRank (n+1)`. Il n'y a pas de seconde notion d'écart ; la preuve est la définition partagée.

**19.24.2 Ce qui rejoint la cassure exacte, et ce qui ne la rejoint pas.** Le seul pont compilé des contributions
individuelles à `log p_{n+1}` est : contribution lissée → somme sur tous les vrais zéros = incrément du reste lissé
(`localSynchronization`, `prime_gap_synchronization`) → `ψ(N)` = pas de la primitive lissée
(`smoothedZeroPrimitive_nat_difference`, `psi_eq_background_add_packet_add_complement`) → cassure `log p_{n+1}` moins le fond
(`break_at_meeting`). Chaîne d'identités exactes, sans approximation. En revanche la somme des contributions BRUTES
(« canal de Chebyshev » du texte collé) n'est identifiée à rien : la formule explicite non lissée n'est ni dans Mathlib ni
dans le dépôt ; le canal `J` (`Ei`) est nommé (`CountingExplicitFormula`, `def : Prop`) et non démontré. Le texte collé est
donc exact sur la flèche, à condition de la lire dans le canal lissé.

**19.24.3 Contacts.** Compilés (`towerMotionOf`, `contactMinusAt`), avec « aucun premier n'entre ici » en tête de module.
Trois familles de points distinctes et compilées : contacts de phase `C_k`, changements de signe de la densité `x_k`,
extrema du champ autour de `li` `D_k` ; `contact_vs_densitySignChange` : `log C_k − log x_k = −arctan(β/T)/T` ;
`CountingFieldContacts` : `C_k < D_k < C_{k+1}`, `β = T·tan(T(log D_k − log C_k))`. Aucun théorème du dépôt, dans aucun des
219 modules, n'identifie un contact à un premier (vérifié énoncé par énoncé) ; `HorizontalExclusion:132` dit que le passage
horizontal partage un premier, jamais un contact. « Un contact ne tombe pas sur un premier » n'est pas un théorème et n'a pas
à l'être. Le texte collé confirme §19.10 : contact ≠ rencontre.

**19.24.4 Théorèmes cités par le texte.** Huit sur dix existent et portent déjà la lecture demandée (`meetingPoint_eq_upper`,
`meetingPoint_unique`, `all_signals_meet`, `imposedShare_eq`, `mirror_contacts_never_coincide`, `gap_demand_eq_break_add_rest`,
`no_finite_family_accomplishes_demand`, `tail_not_eventually_zero`) ; aucune des « anciennes lectures problématiques » ne
figure dans leurs énoncés ni docstrings : c'étaient des lectures de textes. Deux noms à retirer : `thm_passage_occurrence_succ`
(RHV5Fresh, hors corpus) et `thm_expectedMinimum_cases` (inexistant).

**19.24.5 Audit des 219 modules.** FIDÈLE 128 ; À RECONTEXTUALISER 32 ; ÉQUIVALENT-RH 29 (hypothèse nommée ⟺ RH, toutes
étiquetées, aucune posée) ; PARTIEL 9 (antécédents fenêtrés ou bornes non dérivés : `FiniteGrammarLayer`, `GrammarOperator`,
`GrammarTailBound`, `GrammarWindowEstimate`, `GrammarWindowSeparation`, `JointComparison`, `PrimeBlockDecomposition`,
`PrimeCellError`, `PrimeTransitionDecomposition` : relégués au journal, non appuis) ; MIXTE 21. Aucun `sorry`, `admit`,
`axiom`. Un seul défaut réel, de vocabulaire, sans égalité formelle : le mot « rencontre » désigne un CONTACT de Tour dans
`GeneratedFrequency` (`meetingOf` = contact d'indice 0, `ArithmeticMeeting`, `MeetingOnLine`, `smoothedMeeting`),
`DemonstrationChain` (en-tête, `ArithmeticMeeting T_w (lineContact T_w 0)`), `OccupiedFrequency`, `ConstantAmplitudeNeed`,
`CoupleLock`, `GrammarTransportLaw`, `MeetingPoint:125` ; la doctrine réserve « rencontre » à `meetingPoint I = p_{n+1}`
(`OffCarrier:489` le dit déjà : les deux notions ne coïncident pas). `TangentialInversion` raisonne en docstring sur « un
premier égal à un contact » (réel générique, hypothèse d'exercice). Corrections = docstrings seules, noms conservés, sur feu
vert (deux de ces fichiers sont dans la chaîne).

**19.24.6 Expériences.** E219, E305 (compilé), synchronisation locale du 2026-10-14 (compilé), E224–E230 : exactes, conservées
comme appuis. E220 (corrélations, RMS, médianes, 5000 zéros), E239 (27 fenêtres), E309 (troncature, échelle de Gibbs),
E310–E311 (précision finie) : relégués au journal, non appuis, par la règle de l'auteur « plus aucune démarche statistique ou
partielle ». E301 : fausse (§19.9), jamais citée. Jumeau déterministe des nombres du texte collé : E400
(`experiments/E400_ThreeTowersTwin`, mpmath 30 chiffres) : contacts et contributions identiques au texte ; colonne lissée
ajoutée ; trois Tours ne réalisent aucune cassure (`no_finite_family_accomplishes_demand`).

**19.24.7 `.md`.** Aucune phrase du maître n'identifie un contact à un premier ; §19.10 et §19.23 disent déjà que la lecture
« contact à la fin de chaque écart » est fausse ; `riemann_graphique_ANALYSE.md` conforme. Texte collé : fidèle sur la chaîne ;
rectifications : deux noms de théorèmes ; « canal de Chebyshev » → canal lissé pour tout ce qui rejoint ψ ; « les contacts
déterminent ρ » vrai pour un zéro isolé (`height_of_consecutive_extrema`, `radial_of_extremum_offset`), tandis que le signal
arithmétique ne voit que la somme (E163) ; le découpage par cellules de contacts est le télescopage (`countingGapTerm_add`,
`primeGapContribution_chain`), exact et sans information nouvelle (E218).

**19.24.8 Plan pré-enregistré (aucune étape lancée avant feu vert).** Étape F : module isolé `SameGapsAudit.lean`, huit énoncés
F1–F8 (bornes partagées `rfl`, rencontre = exponentielle de la borne supérieure, brute = `Δ_{ρ,n}`, lissée = `−m/(ρ+1)` × brute,
somme lissée = cible, porteur : paire / rencontre / cassure sur `⟨C.n⟩`, contact ≠ changement de signe de densité, trois zéros
certifiés ≠ cible près de toute rencontre) ; aucun ne conclut sur β. Étape G : registre déterministe des trois Tours sur les
168 écarts `≤ 1000` (contacts traversés, portions de cellules, trois canaux, demande exacte du canal lissé avec le fond pris
dans `ZetaPerronLineIdentity`), deux implémentations = jumeau, aucune fenêtre ni moyenne. Étape E (inchangée) : signature de
la paire sur trois écarts, seul objet radial côté axe ; « la Tour d'une première arrivée OFF et son miroir peuvent-elles
respecter toutes les obligations de rencontre ? » = question ouverte de §19.12, à traiter après F et G, sous hypothèse nommée
si nécessaire. Étape H : docstrings « rencontre » → « contact » (fichiers de la chaîne : sur feu vert), lexique §19.21 restant,
mentions « journal, non appui ». Hors plan, par doctrine : aucune exclusion d'OFF à ce stade, aucune borne sur le reste,
aucune fenêtre, aucune hypothèse ⟺ RH posée. Frontière inchangée : `ContinuationForced ⟺ RH`, constance par membre ⟺ RH,
`no_carrier_iff_riemannHypothesis`. Les acquis ne sont pas remis en cause : ils sont reclassés.

### 19.25 Exécution du plan F/G/E/H sur feu vert, consolidé par le texte « Démonstration mathématique de la Tour issue du zéro authentique » (2026-11-01)

**19.25.1 Le texte collé.** Ses sept sections sont exactes et sont désormais compilées dans `Terminal/SameGapsAudit.lean`
(module isolé, non importé par la racine ni par la chaîne) : la Tour géométrique `Z_ρ(s) = ρ·exp(ρs/T)` part exactement du
zéro (`geometricTower_zero`), son rayon vaut `‖ρ‖·exp(βs/T)` (`geometricTower_norm`), et elle est l'image de la fonction de
Tour `𝒯_ρ(x) = x^ρ/ρ` par l'homothétie réelle de rapport `‖ρ‖²·exp(−2βφ/T)` sous le changement de paramètre `s = T·log x − 2φ`
(`geometricTower_similar_zeroTerm`) : la « similitude du plan » annoncée par le texte est une homothétie, et les contacts `C_k`
de `𝒯_ρ` correspondent aux passages `s_k = kπ − φ` de `Z_ρ` sur l'axe réel. Les contacts se suivent au rapport `exp(π/T)`
(`contact_ratio`), les rayons au rapport `exp(βπ/T) > 1` (`radius_ratio`, `radius_ratio_gt_one` : descente vers l'origine
quand `k` décroît), la fréquence et la position radiale se reconstruisent depuis deux contacts et depuis un contact
(`height_from_contacts`, `radial_from_contact`). Rien de tout cela ne dit quoi que ce soit sur β : ce sont des identités
pour toute position radiale. La flèche finale du texte, « contribution exacte à chaque écart → reconstruction collective aux
rencontres », est vraie dans le canal lissé seulement (F4, F5), comme dit en §19.24.2.

**19.25.2 Étape F exécutée : `SameGapsAudit.lean`, 24 théorèmes, axiomes standard seuls, aucun `sorry`.** F1 les bornes de la
contribution brute sont celles de `⟨n⟩ : PrimeGapInterval` (`rfl`) ; F2 les bornes de l'écart sont les exponentielles des
bornes de la contribution, la rencontre est `exp b` ; F3 contribution brute `= (p_{n+1}^ρ − p_n^ρ)/ρ = 𝒯_ρ(p_{n+1}) − 𝒯_ρ(p_n)` ;
F4 lissée `= (−m/(ρ+1))` × brute (`rfl`) ; F5 somme lissée sur tous les vrais zéros = incrément du reste lissé jusqu'à la
rencontre ; F6 pour un porteur OFF, paire, liaison et cassure portent les bornes de `⟨C.n⟩` ; F7 aucun contact `C_k` n'est un
changement de signe `x_{k'}` de la densité, pour tous `k, k'` ; F8 aucune famille finie n'accomplit la demande près d'aucune
rencontre. E1 (étape E, identité seule) : la signature hyperbolique de la paire sur trois écarts consécutifs télescope en une
intégrale unique sur `[log p_n, log p_{n+3}]` (`pair_signature_three_gaps`, `gapTerm_add`). Quatre compilations journalisées
(`audits_compilation/SAMEGAPS_20261101.md`) : deux échecs de tactique à la première (le simplificateur de corps laisse un
inverse de `T` ; égalité d'exponentielles non dépliée), un à la deuxième (profondeur de `congr`), succès à la troisième, succès
à la quatrième après ajout de E1. Aucun énoncé ne conclut sur β, aucun n'identifie un contact à un premier.

**19.25.3 Étape G exécutée : E401, registre déterministe des trois Tours sur les 168 écarts depuis 2 (`p_n ≤ 1000`).** Deux
précisions (30 et 50 chiffres) : contacts traversés identiques, toutes les colonnes identiques sur les douze chiffres affichés ;
télescopage de chaque canal exact à 2e−30 ; demande exacte totale sur `[2, 1009]` égale aux deux précisions ; la somme lissée
des trois Tours n'égale la demande sur aucun des 168 écarts (F8) ; le résidu maximal après 3, 30, 100 zéros vaut 0,149, 0,032,
0,013 (contrôle d'implémentation : la queue décroît, conformément à la convergence absolue ; ce n'est pas une mesure de β et
n'est pas lu comme telle). Les onze premières lignes reproduisent E400 et donc le texte collé. Le registre remplace les figures
autour de `li` pour ces trois Tours.

**19.25.4 Étape H.** Les paragraphes E239–E241, E309, E310, E311 du maître portent désormais la mention « journal, non appui ».
Les docstrings où « rencontre » désigne un contact de Tour sont toutes dans la clôture d'importation de
`DemonstrationChain` (202 modules) : `GeneratedFrequency` (`meetingOf`, `ArithmeticMeeting`, `MeetingOnLine`,
`smoothedMeeting`), `DemonstrationChain` (:74–87, :633–646, :792), `OccupiedFrequency` (:46–121), `ConstantAmplitudeNeed`
(:17, :76, :87), `CoupleLock` (:17–186), `GrammarTransportLaw` (:36, :378–415). Par la règle « s'arrêter et demander avant tout
changement à `DemonstrationChain.lean` ou aux fichiers qu'il importe », rien n'y est modifié ; la correction proposée (docstrings
seules, identifiants inchangés : « rencontre » → « contact de Tour ») attend la réponse de l'auteur. `MeetingPoint.lean:125`,
cité en §19.24.5, ne contient pas de mésusage après relecture : la liste de §19.24.5 est corrigée sur ce point.

**19.25.5 Ce qui reste ouvert, inchangé.** Frontière : `ContinuationForced ⟺ RH`, constance par membre ⟺ RH,
`no_carrier_iff_riemannHypothesis`. La question de §19.12 (« la Tour d'une première arrivée OFF et son miroir peuvent-elles
respecter toutes les obligations de rencontre ? ») n'est pas tranchée : E1 en donne la forme sur trois écarts, comme identité.
Règles acquises : « rencontre » est réservé au premier suivant `p_{n+1}` ; « contact » désigne le passage d'une Tour sur
l'axe ; aucun contact n'est un événement premier ; plus aucune démarche statistique, fenêtrée, tronquée ou asymptotique n'est
un appui ; le seul pont compilé des contributions individuelles à la cassure est le canal lissé.

**19.25.6 Suite proposée (rien lancé).** (i) Réponse de l'auteur sur les docstrings de la chaîne (H). (ii) Étape E sur les
identités seules : exprimer, à trois rencontres consécutives, la part imposée du couple (zéro OFF et miroir) par
`imposedShare_eq` et la signature E1, puis dire sous quelle hypothèse NOMMÉE (jamais posée comme prouvée) cette part serait
incompatible avec la constance par membre ; aucune promesse. (iii) Correction du clash racine `windowProjection` (depuis le
2026-10-20). (iv) Renommage `break_compensated_by_other_frequencies → break_complement_identity`.

### 19.26 Décisions de l'auteur sur §19.25 et plan « audit énergétique exact » (proposé, rien lancé) (2026-11-01)

**19.26.1 Ce que l'auteur retient de E401 et du build 00f018c4.** E401 vérifie les formules des trois canaux sur 168 écarts, à
deux précisions, avec télescopage exact ; aucune famille finie de trois Tours ne reconstruit la demande ; la décroissance du
résidu 0,149 → 0,032 → 0,013 vaut pour les troncatures calculées et N'EST PAS une loi générale. E401 ne révèle aucune
contradiction entre contacts et écarts, et ne réalise PAS le contrôle énergétique (énergies individuelles, termes croisés,
énergie collective absents). L'homothétie compilée (`geometricTower_similar_zeroTerm`) impose : l'énergie de la Tour géométrique
vaut K_ρ² fois l'énergie analytique, K_ρ dépend du zéro, donc deux Tours géométriques ne se comparent pas en énergie absolue
sans leurs facteurs ; et toute énergie collective garde ses termes croisés. `pair_signature_three_gaps` est une identité
exacte, conforme au plan, qui ne tranche pas §19.12. Décisions : (A) docstrings de la chaîne : OUI, limitée aux docstrings,
« rencontre » → « contact de Tour » uniquement pour l'intersection géométrique, « rencontre » conservé pour p_{n+1}, aucun
identifiant/type/définition/théorème/import/preuve modifié ; (B) clash `windowProjection` : correction séparée, antérieure au
commit, objectif = racine compilée en conservant les identités nouvelles ; (C) renommage de `break_compensated_by_other_frequencies` :
DIFFÉRÉ jusqu'à la racine compilée. Priorité nouvelle : audit énergétique exact (quatre égalités ou distinctions ; sept modules).

**19.26.2 Reconnaissance préalable (Sonnet × 2, vérifiée par Fable ; `AUDIT_ENERGIE_ET_DOCSTRINGS_20261101.md`).**
(a) Énergie : aucun des sept modules (EnergyIdentity, GeometricEnergyRaccord, RayEnergy, RemainderEnergy, QuadraticVariation,
GrammarWordLoad, GapDemandStability) ne définit l'énergie brute, l'énergie normalisée ni une énergie géométrique ; K_ρ n'existe
nulle part dans le corpus ; la seule énergie collective, `windowEnergy` (QuadraticVariation, hors chaîne), passe à la somme par
`windowEnergy_add`, identité exacte AVEC termes croisés, et `cross_term_unconstrained` dit qu'aucune identité ne les fixe.
Aucun passage individuel → collectif n'omet les termes croisés, pour la raison qu'aucun module ne forme l'énergie d'une
contribution d'écart |Δ_{ρ,n}|² ni sa somme à une rencontre : les anciens théorèmes manipulent des amplitudes ‖zeroTerm‖,
leurs logarithmes (`verticalEnergy`, `horizontalEnergy`, `windowDrift`) ou un incrément au carré par cellule
(`ownCellEnergyDensity`, exposant 2β−1 mais objet ≠ x^{2β−1}/|ρ|²). Réponse par lecture à la question de l'auteur : les
anciennes contraintes énergétiques NE portent PAS sur les grandeurs des contributions aux rencontres ; elles sont à côté, ni
fautives ni correctes à leur égard. À compiler avant d'être tenue pour acquise.
(b) Docstrings : 236 occurrences, 0 au sens réservé p_{n+1}, 215 contacts de Tour, 21 ambiguës (« rencontre collective »
= `CollectiveMeeting x` : reste lissé nul en un x quelconque ; `ConstantNeed` sur toutes les abscisses x ≥ 1) ; aucun identifiant
ne contient le mot ; `meetingOf`, `MeetingOnLine`, `ArithmeticMeeting`, `smoothedMeeting` sont tous des contacts de Tour
(compilé : `contactMinusAt_eq_meetingOf`). Table de 211 remplacements prête et vérifiée ligne à ligne
(`audits_compilation/DOCSTRINGS_RENCONTRE_CONTACT_PROPOSES_20261101.tsv`) ; 5 citations verbatim de l'auteur non touchées.
(c) Clash : reproduit à la racine seule (message exact dans l'audit) ; `SpectralWindowProjection` n'est importé que par
`GapDemandStability` et la racine, hors chaîne.

**19.26.3 Plan (ordre d'exécution ; chaque étape = un commit ; aucune lancée avant feu vert explicite sur ce §).**

*Étape B′ — racine compilée (décision B).* Envelopper `SpectralWindowProjection.lean` dans `namespace RHV6Fresh.Spectral`
(ou préfixer ses noms `spectralWindowProjection…`), qualifier les usages dans `GapDemandStability.lean` ; aucun fichier de la
clôture de `DemonstrationChain` touché ; preuve = `lake build RHV6Fresh` EXIT 0, journal `audits_compilation/ROOT_20261101.md`,
deux tentatives journalisées au plus ; si une troisième est nécessaire, arrêt et rapport. Le renommage C reste différé.

*Étape H′ — docstrings (décision A).* Appliquer les 211 remplacements de la table (script déterministe, vérification que
chaque ancien texte est présent une fois à la ligne indiquée, diff limité aux lignes listées, `grep` prouvant qu'aucun
identifiant n'a changé), puis `lake build RHV6Fresh.Terminal.DemonstrationChain` (la clôture de 202 modules est recompilée par
les docstrings ; attendu : succès sans changement d'axiomes, comparaison des `#print axioms` avant/après). Deux questions à
l'auteur AVANT application, parce que la règle d'arrêt sur la chaîne reste en vigueur pour tout ce qui n'est pas couvert par
la décision A : (i) les 21 lignes ambiguës « rencontre collective » / `ConstantNeed` : conserver « rencontre » (ce n'est pas un
contact d'une Tour), remplacer par « annulation collective », ou laisser à l'auteur ; (ii) la docstring d'`ArithmeticMeeting`
(:150) : « contact de Tour arithmétique » ou autre formule ; les 5 citations verbatim restent telles quelles.

*Étape I — module isolé `Terminal/EnergyAudit.lean` (priorité de l'auteur), non importé par la racine ni la chaîne ;
imports : `SameGapsAudit`, `QuadraticVariation`, `RemainderEnergy`, `OnRadialRing`.* Énoncés visés, tous identités ou
distinctions, aucune hypothèse, aucune conclusion sur β :
I1 énergie brute : ‖zeroTerm z x‖² = x^{2β}/‖ρ‖² (de `zeroTerm_norm`) ;
I2 énergie normalisée : (normalizedRadius z x)² = x^{2β−1}/‖ρ‖² (de `normalizedRadius` = ‖zeroTerm‖/√x) ;
I3 énergie géométrique : ‖geometricTower z s‖² = K_ρ² · ‖zeroTerm z x‖² avec K_ρ := ‖ρ‖²·exp(−2βφ/T) et s = T·log x − 2φ
(de `geometricTower_similar_zeroTerm`) ; I3′ : K_ρ est une fonction explicite du zéro (définition `homothetyFactor`), et
l'énergie géométrique relative r(s₂)²/r(s₁)² = exp(2β(s₂−s₁)/T) ne dépend pas de K_ρ (les rapports d'une même Tour sont
préservés) ;
I4 énergie collective sur un écart : pour toute famille finie J de zéros et tout écart I, |Σ_{j∈J} Δ_j|² = Σ_j |Δ_j|² +
2 Σ_{i<j} Re(Δ_i · conj Δ_j), Δ_j = `smoothedLocalContribution ρ_j I` (version `Finset` de `windowEnergy_add`, à partir de
`Complex.normSq_add` et `Finset.sum_mul_sum`) ; même énoncé pour `primeGapContribution` ;
I5 distinctions : `ownCellEnergyDensity z k` ≠ (normalizedRadius)² en général — compilée comme identité exacte
`ownCellEnergyDensity z k = (C_{k+1}^β + C_k^β)² / (‖ρ‖²·(C_{k+1} − C_k))` et comparaison terme à terme avec I2 au point C_k ;
`verticalEnergy`/`horizontalEnergy` = moitié des logarithmes des énergies brutes (`log E_l − log E_e = 2(H − V)`) ;
I6 lien à la demande : la demande exacte à la rencontre est une somme complexe (`gapDemand_eq_sum`, `tsum_smoothed_eq_remainder_at_meeting`) ;
le passage à |demande|² = énergie collective sur toute la famille infinie n'est PAS compilé ici (série de termes croisés) ;
il est énoncé comme `def CollectiveEnergyAtMeeting : Prop` NOMMÉ, jamais prouvé, pour fixer le vocabulaire.
Deux tentatives journalisées au plus par énoncé ; `#print axioms` sur tous ; aucun `sorry`.

*Étape J — expérience E402 « registre énergétique », jumeau de E401.* Pré-enregistrement écrit avant exécution (les huit
erreurs de débutant revérifiées par écrit), script `python3 -I`, mpmath 30 et 50 chiffres, même 168 écarts, même trois Tours
certifiées, puis K = 30 et 100 ; par écart et par canal (brut, lissé) : énergies individuelles |Δ_j|², somme diagonale,
termes croisés 2Re(Δ_i conj Δ_j) pour les trois paires (1,2), (1,3), (2,3), énergie collective |Σ|², vérification que
collective − diagonale − croisés = 0 à 1e−25 ; en regard, |demande exacte|² du canal lissé et |résidu|² après 3/30/100 zéros ;
facteurs K_ρ des trois Tours et énergie géométrique au contact C_0 pour montrer, par le nombre, que ‖Z‖² ≠ ‖𝒯‖² en général.
Résultats attendus, dits à l'avance : l'identité I4 est vérifiée à la précision (elle est algébrique, l'expérience n'en est
qu'un contrôle d'implémentation) ; les termes croisés changent de signe d'un écart à l'autre (relevé exact par écart, aucun
comptage statistique, aucune moyenne) ; les trois K_ρ sont distincts. Ce que E402 ne peut pas donner : une orientation en β,
une loi de décroissance, une hiérarchie énergétique. Jumeau = les deux précisions ; réel/synthétique séparés (aucun synthétique ici).

*Étape K — confrontation signature de la paire / contribution collective exacte (suite de §19.12, demandée par l'auteur).*
Uniquement sous hypothèse NOMMÉE et sur identités : exprimer, par `pair_signature_three_gaps` et I4, l'énergie collective
d'une famille {ON connus} ∪ {paire OFF, miroir} sur trois écarts consécutifs, en conservant phases et termes croisés ; énoncer
`def PairEnergyIncompatible : Prop` (la part imposée du couple ne peut égaler le complément exigé à chaque rencontre) et
compiler seulement `PairEnergyIncompatible → ¬(existence du porteur)` si la preuve est une identité ; sinon consigner
l'obstacle exact. Aucune promesse ; aucune preuve directe de §19.11.3.

*Étape L — documents à l'issue.* Maître (§19.27 : résultats I, J, K ; registre des cibles fermées), audit
`AUDIT_ENERGIE_ET_DOCSTRINGS_20261101.md` (§4 exécution), `CLAUDE.md` de zeta24-lean (règle : « énergie » ne désigne jamais
une amplitude ni un logarithme d'amplitude ; toute énergie collective s'écrit avec ses termes croisés ; énergies géométriques
comparées seulement à K_ρ près ; E402 = jumeau de E401), mémoire de session, `README` de E402, commit par étape et push.

**19.26.4 Rôles.** Fable : rédaction des énoncés Lean, preuves, pré-enregistrements, décisions de doctrine, relecture de
chaque sortie Sonnet avant usage. Sonnet (agents bornés, lecture seule ou tâches mécaniques vérifiables) : application
scriptée de la table de docstrings et production du diff, extraction des `#print axioms` avant/après, génération des tableaux
du README de E402 à partir des fichiers de sortie, recherche de noms Mathlib. Rien de ce que produit Sonnet n'est un appui
avant vérification par compilation ou relecture Fable ; aucune conclusion mathématique n'est déléguée.

**19.26.5 Ce qui est acquis par lecture seule, et donc à confirmer.** « Les anciennes contraintes énergétiques ne portent
pas sur les contributions aux rencontres » est une lecture ; l'étape I la transforme en identités compilées (I5, I6) ou la
réfute. Frontière inchangée : `ContinuationForced ⟺ RH`, constance par membre ⟺ RH, `no_carrier_iff_riemannHypothesis`.

**19.26.6 Intégration du texte « Pourquoi l'énergie est importante » (auteur, 2026-11-01) : vérification de couverture et ajouts.**

*Vérification dans le corpus (lecture, 2026-11-01).* Le verrou nommé « StrictRaccordHierarchy » par le texte n'existe sous
aucun fichier ni identifiant de ce nom (déjà noté en §19.1) ; l'objet est `RaccordHierarchy` (`Terminal/TowerHierarchy.lean:60`)
= `(towerRaccordOf p).Oriented ∧ towerPitch l < towerPitch e`, où `Oriented` (`TowerRaccord.lean:87`) est exactement
‖zeroTerm l M‖ ≤ ‖zeroTerm e M‖ au premier partagé M, soit la comparaison d'amplitudes A_{n+1}(M) ≤ A_n(M) du texte ; le rapport
A_{n+1}/A_n = M^{β_{n+1}−β_n}·|ρ_n|/|ρ_{n+1}| est la « quantité d'orientation » (`oriented_iff_transport_le_one`). Compilé :
`continuationForced_iff_hierarchy` (`OffCarrier.lean:1353`) : la continuation forcée au raccord sortant ⟺ la hiérarchie à ce
raccord ; `raccordHierarchy_iff_riemannHypothesis` (:133) ; `sameHeight_breaks_hierarchy` : le passage de même hauteur (l'arrivée
OFF) la viole (`outgoing_signature`, OffCarrier:270). Vérification de la flèche demandée par l'auteur : `TowerHierarchy.lean`
ne mentionne ni `gapTerm`, ni `primeGapContribution`, ni `smoothedLocalContribution` ; le seul fichier où `RaccordHierarchy`
et `gapTerm` coexistent est `OffCarrier.lean`, dans des sections distinctes (hiérarchie :262–666 et :1354 ; `gapTerm` :875–900,
signature de la paire) sans théorème ayant l'une en hypothèse et l'autre en conclusion. **Constat : aucun théorème du corpus ne
transporte la hiérarchie des amplitudes au premier partagé jusqu'aux contributions exactes des écarts ni à la cassure.** La
flèche « hiérarchie énergétique au raccord ⟹ contrainte sur les contributions exactes » est ABSENTE, ni prouvée ni réfutée :
c'est, conformément au texte, « exactement celui qu'il faudra tenter de démontrer ». Le plan le prend en charge ci-dessous.

*Couverture du texte par le plan §19.26.3.* Énergie = carré de l'amplitude, phase gouvernée par T, interaction 2Re(A·conj B) :
couvert par I4 et J. « La cassure dépend de la contribution collective, non de la somme des énergies » : couvert par I6
(`CollectiveEnergyAtMeeting` nommé) et J. « Amplitude au raccord ≠ contribution à l'écart » : NON couvert explicitement →
ajout I7, I8. « Identifier le théorème qui transporte le contrôle jusqu'à la cassure, sinon le démontrer » : NON couvert →
ajout I9 et étape K′. « Une énergie nulle exactement en β = 1/2 n'est qu'une caractérisation » : NON couvert → règle de
doctrine R1. « Audit avant toute nouvelle expérience » : l'ordre est corrigé, J passe APRÈS I et K′ et ne sera lancée que si I
laisse une question que seul un registre peut éclairer (contrôle d'implémentation de I4 inclus dans I par `decide`-free
`norm_num` sur un exemple rationnel, pas par mpmath).

*Ajouts à l'étape I (`EnergyAudit.lean`, isolé).*
I7 (rapport d'amplitudes au premier partagé, identité) : pour deux vrais zéros e, l et M > 0, ‖zeroTerm l M‖ / ‖zeroTerm e M‖ =
M^{β_l − β_e} · ‖ρ_e‖/‖ρ_l‖ ; corollaire : `Oriented` ⟺ M^{β_l−β_e} ≤ ‖ρ_l‖/‖ρ_e‖ ; et, pour β_e = β_l, `Oriented` ⟺ ‖ρ_e‖ ≤ ‖ρ_l‖
(l'orientation est aveugle au radial quand les radiaux sont égaux : c'est le contenu de `raccordHierarchy_of_height_advance`
« quelles que soient les positions radiales », relu comme identité).
I8 (la contribution dépend des deux bornes et de la phase, identité) : |Δ_{ρ,n}|² = A(p_{n+1})² + A(p_n)² − 2·A(p_{n+1})·A(p_n)·
cos(T·log(p_{n+1}/p_n)), avec A(x) = x^β/‖ρ‖, pour `primeGapContribution` ; forme lissée avec le facteur 1/‖ρ+1‖². Corollaire
compilé : l'amplitude en un seul point ne détermine pas |Δ| (deux zéros de même amplitude en p_{n+1} et de contributions
distinctes, exhibés par identité, sans synthétique de hauteur existante).
I9 (la flèche, nommée, jamais prouvée) : `def HierarchyTransportsToBreak (C : OffCarrier) : Prop` := « RaccordHierarchy au
raccord sortant ⟹ la part imposée du couple (zéro OFF, miroir) sur l'écart de rencontre satisfait `imposedShare_eq` avec un
complément nul » ; et son renversement utile, le seul qui pourrait fermer : `def BreakRefutesOffArrival : Prop` := « zéro
précédent en ligne ∧ passage authentique ∧ contributions exactes sur les mêmes écarts ∧ reconstruction exacte à la rencontre
⟹ ¬ arrivée OFF ». Compilé seulement : `BreakRefutesOffArrival → ContinuationForced` si c'est une identité (attendu : oui,
par `continuationForced_iff_hierarchy` et le trichotomie de §19.10) ; l'implication inverse n'est pas cherchée.

*Étape K′ (remplace K ; priorité juste après I).* Tenter la flèche à partir des identités seules : exprimer la demande exacte
à la rencontre (`tsum_smoothed_eq_remainder_at_meeting`) comme contribution du zéro précédent (ON, β = 1/2) + contribution du
couple (OFF, miroir ; `pair_gapTerm_signature`, `target_split_of_mirror`) + complément des autres fréquences, PHASES
CONSERVÉES ; chercher si `Oriented` au premier partagé (I7) borne |Δ_{OFF}| + |Δ_{miroir}| par |Δ_{ON}| sur l'écart de rencontre
(I8) ; si oui, dire ce qu'il manque pour que la reconstruction ne puisse pas absorber la différence (ce manque sera nommé) ;
si non, consigner l'obstacle exact (attendu : la hiérarchie compare un point, la contribution intègre deux bornes et une
phase ; l'inégalité ne passe pas sans contrôle de cos(T·log(p_{n+1}/p_n)), qui est une lecture de fréquence, donc §19.15–16).
Deux tentatives journalisées au plus ; aucune hypothèse posée comme prouvée ; aucune promesse.

*Règles de doctrine ajoutées (à porter dans CLAUDE.md à l'étape L).* R1 : toute « énergie » ou « dérive » nulle, constante
ou plate exactement quand β = 1/2 (`ownCellEnergyDensity_flat_iff`, `windowDrift` = (β − 1/2)·budget,
`translated_ratio_one_iff`, `window_stability_law_iff_riemannHypothesis`) est une caractérisation de la ligne, jamais un
levier ; elle ne doit plus être proposée comme contrainte. R2 : « énergie » désigne un carré de module ; une amplitude, un
logarithme d'amplitude ou un rapport d'amplitudes n'est pas une énergie et se nomme comme tel. R3 : toute énergie collective
s'écrit avec ses termes croisés ; une somme d'énergies individuelles sans eux n'est jamais une obligation collective. R4 : une
hiérarchie d'amplitudes en un point n'est pas une hiérarchie de contributions sur un écart tant que la flèche I9 n'est pas
compilée. R5 : montrer que la paire OFF modifie les contributions n'est pas un résultat (déjà calculable) ; le résultat
cherché est que la reconstruction collective ne peut pas absorber la modification.

*Ordre d'exécution corrigé.* B′ (racine) → H′ (docstrings, après réponse aux deux questions) → I (I1–I9) → K′ → J (seulement
si I/K′ laissent une question numérique) → L. Rien n'est lancé avant feu vert sur ce §19.26.

### 19.27 Étape K′ exécutée sur la direction corrigée de l'auteur : le verrou au raccord sortant du zéro authentique (2026-11-01)

*19.27.1 Direction corrigée (auteur, 2026-11-01, consignée telle quelle en substance).* Aucune étude OFF–miroir, aucune
compensation, aucune hypothèse énergétique nouvelle. Point de départ : un zéro authentique (1/2, T_n), sa Tour, ses contacts,
sa contribution exacte aux écarts premiers. Acquis : les contacts déterminent (β, T) ; chaque contribution utilise les mêmes
bornes premières que la rencontre. Verrou unique : démontrer que la lecture obligatoire du précédent au premier partagé M
impose la hiérarchie au raccord sortant. Relation à exploiter : A_{n+1}(M)/A_n(M) = M^{β_{n+1}−β_n}·|ρ_n|/|ρ_{n+1}|. Première
obligation : relier cette comparaison ponctuelle à la contribution exacte de chaque Tour sur l'écart précédent, phases
conservées. Deuxième obligation : démontrer que la progression authentique des contacts et de la fréquence impose cette
relation au raccord, plutôt que la supposer. Contrôle Lean : composer SameGapsAudit, succession, contacts, lecture au premier
partagé ; identifier le premier but non résolu. Critère de clôture : la hiérarchie au raccord à partir de ces seuls acquis,
sans hypothèse équivalente à RH ; « la relation d'amplitudes seule ne suffit pas encore ». Priorité immédiate : cette
composition formelle avant toute expérience, chaîne terminale intacte tant que le lemme n'est pas démontré. Hypothèse de
fermeture de l'auteur (cinq lignes) : la lecture authentique du précédent au premier partagé impose une orientation
géométrique au suivant ; fondement = contacts déterminent (β, T) et mêmes écarts ; mécanisme = succession des fréquences et
lecture du précédent contraignent le rapport ≤ 1 ; justification manquante = les identités ne démontrent pas encore cette
inégalité ; clôture visée = établir l'orientation sans prémisse, puis la hiérarchie et la chaîne terminale excluent la sortie.
Note de correspondance : « StrictRaccordHierarchy » n'existe pas dans le corpus ; l'objet est `RaccordHierarchy` (§19.26.6).

*19.27.2 Ce qui a été compilé.* `Terminal/AuthenticRaccordLock.lean`, module ISOLÉ (non importé par la chaîne, non ajouté à
`RHV6Fresh.lean`), importe `SameGapsAudit`, `AuthenticPassageProfile`, `PairInteraction`. Douze théorèmes, une définition
d'objet (`occurrenceGap e = ⟨idx e⟩`), une Prop nommée jamais prouvée. Deux tentatives journalisées
(`audits_compilation/authenticraccordlock/AUTHENTICRACCORDLOCK_20261101.md`) : tentative 1 échec sur une réécriture
syntaxique (membre du passage contre vrai zéro construit), tentative 2 succès ; axiomes standard 12/12, aucun `sorry`.
(1) `lock_relation_at_sharedPrime` : la relation (point 5) est le champ `transport` du raccord — elle était déjà compilée
(`energyRatio_eq`, `TowerRaccord.transport`) ; `lock_relation_le_one_iff_oriented` : relation ≤ 1 ⟺ `Oriented`.
(2) `occurrenceGap_lower`, `occurrenceGap_meeting`, `sharedPrime_eq_meeting` : le premier partagé de tout raccord sortant de e
est la rencontre de l'écart d'occurrence de e, de bornes Occ(e) = p_idx et p_min(e) = p_{idx+1} (point 3 : mêmes bornes).
(3) `contribution_on_occurrenceGap` : pour TOUTE Tour z, Δ_{z,idx e} = 𝒯_z(M) − 𝒯_z(Occ e) ; `towerInteraction_same_tower` :
Re(𝒯_z(q)·conj 𝒯_z(p)) = A_z(q)·A_z(p)·cos(T_z·(log q − log p)) ; `contribution_energy_on_occurrenceGap` :
|Δ|² = A(M)² + A(Occ)² − 2·A(M)·A(Occ)·cos(T·(log M − log Occ)). C'est l'identité I8 du plan, compilée, phases conservées.
(4) `authentic_departure_hierarchy` : zéro authentique (β_e = 1/2) atteint par un passage vertical ⟹ le passage sortant monte,
la hiérarchie tient au raccord sortant et la relation y est ≤ 1, QUELLE QUE SOIT la position radiale de l'arrivée
(composition de `engaged_regime_kept`, `raccordHierarchy_of_engaged_departure`, `oriented_iff_transport_le_one`) ;
`first_departure_hierarchy` : au premier zéro, avec le fait de l'auteur « premier zéro ON » posé comme hypothèse nommée
`hAnchor` (même convention que `canonical_onLine_of_conservation`) et `bottom_exit_vertical`.
(5) `lock_relation_reads_frequency_only` : dès T_e ≥ 2, la relation ≤ 1 ⟺ T_e < T_l (c'est `towerRaccord_oriented_iff_height_lt`,
déjà compilé) ; `off_arrival_keeps_hierarchy_breaks_next` : une arrivée OFF (β_l < 1/2) sur un passage vertical laisse la
hiérarchie tenir au raccord sortant du zéro authentique ; le passage suivant gèle et son raccord viole la hiérarchie.
(6) `arrival_onLine_iff_next_hierarchy` : depuis un zéro authentique atteint verticalement, l'arrivée est en ligne SI ET
SEULEMENT SI la hiérarchie tient au raccord qui la quitte. `RadialConservationAtAuthenticDeparture` (Prop nommée, jamais
prouvée) = β conservée sur tout passage vertical quittant un membre ON = exactement `hLaw` de
`canonical_onLine_of_conservation` ; `canonical_onLine_of_lock`, `riemannHypothesis_of_lock` : sous ce but et le premier
zéro ON, tous les membres canoniques sont en ligne et RH suit (compositions de théorèmes existants).

*19.27.3 Lecture du résultat (honnête ; rien n'est conclu sur β).* L'hypothèse de fermeture de l'auteur, telle qu'écrite
(orientation du raccord sortant imposée par la lecture authentique du précédent), EST un théorème sur les acquis — et elle
ne ferme pas. Les deux obligations sont remplies comme identités : (1) la comparaison ponctuelle en M ne porte que sur le
terme A(M) de l'énergie de contribution, qui dépend aussi de A(Occ) et de la phase T·(log M − log Occ) ; (2) la succession
authentique impose bien l'orientation au raccord sortant. Mais cette orientation est une lecture de fréquence : dès T_e ≥ 2
elle équivaut à « la fréquence avance », vraie pour toute arrivée β_l ≤ 1/2 (ordre lexicographique, `passage_entry_radial_le_half`),
donc aveugle à β_{n+1}. Le verrou qui fermerait est la hiérarchie au raccord SUIVANT (celui qui quitte ρ_{n+1}), et elle
équivaut à β_{n+1} = 1/2 : c'est le problème terminal « β_n = 1/2 ⟹ β_{n+1} = 1/2 » déplacé d'un raccord, non résolu.
**Premier but non résolu, nommé** : `RadialConservationAtAuthenticDeparture`. Obstacle exact : la seule quantité
radialement sensible au premier partagé est le transport M^{β_l−β_e}·‖ρ_e‖/‖ρ_l‖ (§19.17 déjà), et sur un passage vertical il
est ≤ 1 pour toute arrivée de la bande ; aucune lecture au raccord sortant de ρ_n ne distingue une arrivée ON d'une
arrivée OFF ; la distinction n'apparaît qu'au raccord sortant de ρ_{n+1} (`off_arrival_keeps_hierarchy_breaks_next`), où
elle est l'hypothèse elle-même. Rien n'est promis.

*19.27.4 Ce qui n'a pas été fait, et ce qui suit.* Aucune hypothèse posée comme prouvée ; chaîne intacte ; B′ (racine), H′
(docstrings, en attente des deux réponses), le reste de I (I1–I6, I9), J non lancés : K′ a été pris en priorité sur la
consigne « tenter cette composition formelle avant toute expérience ». Question à l'auteur avant toute suite : le verrou
doit être une quantité au raccord sortant de ρ_{n+1} déterminée par les données authentiques de ρ_n et de l'écart ⟨idx ρ_n⟩ ;
la lecture à un seul raccord ne le fournit pas (compilé). Pistes qui restent dans la direction corrigée, à sa décision :
(a) composer deux raccords consécutifs (ρ_n → ρ_{n+1} → ρ_{n+2}) avec les contributions exactes sur ⟨idx ρ_n⟩ et ⟨idx ρ_{n+1}⟩,
phases conservées, pour chercher ce que les contacts authentiques de ρ_n imposent au raccord de ρ_{n+1} ; (b) continuer I
(I1–I6, I9) comme prévu. Règles R1–R5 (§19.26.6) portées dans CLAUDE.md avec une règle R6 issue de ce §.

### 19.28 Composition de deux raccords consécutifs avec les CAP : exécutée, insuffisante (2026-11-01)

*19.28.1 Décision et critère de l'auteur.* Après 7eda05dd, l'auteur retient la composition de deux raccords consécutifs
(trois membres z_n, z_{n+1}, z_{n+2}, deux écarts d'occurrence, contributions complexes exactes, phases conservées), et non
la poursuite prioritaire de l'audit énergétique. Distinction obligatoire : « deux contributions calculées sur deux écarts »
(déjà accessible) et « une contrainte obligatoire entre ces contributions » (non démontrée) ; la première ne donne pas la
seconde. Critère de succès : une contradiction avec `low_arrival_freezes_cascade` obtenue d'une contrainte indépendante
sur le second raccord ; si la composition ne produit que des identités ou reformule `arrival_onLine_iff_next_hierarchy`,
elle est insuffisante. `RadialConservationAtAuthenticDeparture` n'est pas introduite comme hypothèse. Correction en cours
d'exécution : les CAP (§19.15–19.17 : `lower_cap`, `upper_cap`, `caps_count_off_pairs_twice`, `next_le_double`,
`gap_le_previous`, `next_contacts_bracketed`, `three_raccords_pattern`) avaient été omis ; les réintégrer avec contacts,
deux raccords et contributions exactes ; critère révisé : incompatibilité démontrée entre les deux lectures successives et
une hauteur commune, sans supposer que deux rangs exigent déjà deux hauteurs (différence entre compter deux places et
exiger deux fréquences).

*19.28.2 Ce qui a été compilé* (`Terminal/TwoRaccordReadingTransport.lean`, isolé, 28 théorèmes, axiomes standard, 0 sorry,
trois tentatives journalisées dans `audits_compilation/tworaccordreadingtransport/`). §1 transport d'une lecture de Tour
à travers un écart (`zeroTerm_transport`), décomposition polaire module radial / phase de fréquence
(`transport_factor_polar`), transport de la lecture relative par un facteur purement radial (`relative_reading_transport`).
§2 bornes du second écart = les deux premiers partagés, contribution exacte de toute Tour sur le second écart, télescopage
sur deux écarts, lecture gelée à fréquence égale (phase relative constante, module seul dépendant du point :
`frozen_reading_ratio`), transport composé sur deux raccords = produit des deux transports et du facteur transmis
(`composite_transport`). §3 sur le porteur : profil (arrivée ≤ 1, facteur transmis < 1, sortant > 1,
`off_two_raccord_profile`), le précédent ON domine encore strictement le zéro OFF au second premier partagé
(`previous_dominates_at_second_prime`), rapport composé z_n → z_{n+2} explicite (`composite_ratio_eq`), seul objet
radialement sensible reliant les deux, signe fixé par aucun théorème. §4 orientation, transport ≤ 1, hiérarchie au second
raccord ⟺ `ContinuationForced` chacun. §5 CAP : même phase sur le second écart, contribution gelée du sortant, CAP inférieur
au rang n+1 à la hauteur commune, deux places du comptage, même pas de contacts, membre suivant encadré par la hauteur
commune — toutes instances satisfaites par la paire. Verdict `common_height_excluded_iff_riemannHypothesis` : « sur tout
porteur, les rangs n et n+1 ont des hauteurs distinctes » ⟺ RH.

*19.28.3 Lecture honnête.* Selon le critère fixé par l'auteur, la composition est **insuffisante** : elle produit des
identités (valables pour toute Tour, donc incapables de contredire le gel), un profil de signes compatible, des équivalences
avec le verrou, et des instances des CAP satisfaites par la paire. Les CAP encadrent les hauteurs par le rang et n'exigent
pas une hauteur distincte par rang (§19.17 déjà) ; ils ne transforment pas le second événement premier en obligation d'une
fréquence nouvelle. Cette obligation — « les deux rencontres consécutives imposent deux progressions de fréquence
distinctes » — est, sur le porteur, exactement `ContinuationForced` ⟺ RH ; ce n'est pas un lemme intermédiaire. Rien n'est
conclu sur β ; chaîne intacte.

*19.28.4 Ce qui reste.* L'arrête manquante est la même qu'en §19.20 et §19.27 : ce qui, dans les premiers seuls, fait du
second événement premier (p_{n+2} après la paire) une exigence de fréquence nouvelle plutôt qu'une place de comptage. Aucune
des trois voies compilées (amplitude au raccord, composition de deux raccords avec phases, CAP par le rang) ne la fournit.
B′, H′ (deux réponses de l'auteur attendues), I1–I6/I9, J toujours non lancés. Règle R7 portée dans CLAUDE.md.

### 19.29 Erreur de stratégie consignée : le local à deux ou trois zéros est impossible ; la demande d'un écart est collective ; les contacts sont l'axe réel (auteur, 2026-11-01)

*19.29.1 L'erreur.* §19.27 et §19.28 ont cherché l'obligation de fréquence nouvelle sur un passage (deux zéros) puis sur
deux raccords (trois zéros). L'auteur juge cette stratégie **terriblement erronée**, et le compilateur confirme la raison :
la demande d'un écart n'est jamais portée par deux ou trois zéros, elle est portée collectivement par tous les zéros dont
le pas de contact est au moins la longueur logarithmique de l'écart, qui contribuent à égalité de module (plateau aveugle
à la hauteur) et se distinguent par la phase. Une paire OFF, sur un ou deux écarts, n'est qu'un membre de cette foule : ses
contributions sont noyées dans une somme où rien ne la distingue hors sa phase, son léger excès radial et le décalage de
ses contacts. L'obligation de fréquence nouvelle ne peut donc pas se lire sur un ou deux écarts ; elle ne peut se lire que
là où la demande collective change, sur la succession des écarts, à travers la progression des foules avec les premiers et
l'identité du complément que la foule doit réaliser quand une place est occupée deux fois à une même fréquence. **Règle :
ne plus jamais raisonner sur deux zéros ni sur trois ; il faut des millions de zéros** (R8, CLAUDE.md). Correction de la
phrase de §19.28 et de ma réponse orale : le point « un pas de contact = longueur de l'écart » n'est pas un maximum de
contribution ; le module de la contribution de l'oscillateur unitaire est un plateau `ℓ` pour toutes les Tours sous un pas,
vaut `2ℓ/π` à exactement un pas, décroît ensuite en `2/T` et s'annule quand l'écart vaut un nombre pair de pas.

*19.29.2 Les contacts à la base de tout (consigne de l'auteur).* Les contacts font partie intégrante de l'axe réel où se
trouvent les premiers et leurs écarts ; les formules tangentielles aux contacts (`contactAt_tangent_minus/plus` :
`tan(T·log C_k) = T/β`) sont le point de départ de toute démarche. Module compilé `Terminal/GapContactRegimes.lean`
(isolé, 18 théorèmes, trois tentatives journalisées) : (i) l'écart est lu par `ℓ/pas` cellules de contact ; trois régimes
par contacts — moins d'un pas (au plus un contact dans l'écart), exactement un pas, plusieurs contacts — trichotomie,
« moins d'un pas » ⟺ `T < π/ℓ` ; (ii) contribution de l'oscillateur unitaire : `2|sin(Tℓ/2)|/T`, plateau `≤ ℓ` aveugle à la
hauteur, enveloppe `≤ 2/T`, valeur `2ℓ/π` à un pas, nullité aux périodes entières ; pour toute Tour, plafond aveugle
`e^{βb}·ℓ` et enveloppe `(e^{βb}+e^{βa})/‖ρ‖` ; (iii) **foule d'un écart** = points-zéros dont le pas est au moins `ℓ`
(`crowd I = upperWindow(π/ℓ)`), appartenance ⟺ pas ≥ ℓ, par rang (`crowd_rank_iff`), emboîtement (écart plus court,
foule plus grande), la paire OFF/sortant est dans les foules des mêmes écarts ; (iv) **ce que les contacts lisent de β** :
la formule tangentielle au contact, et le décalage non nul des contacts du zéro OFF et de son miroir (même pas, contacts
différents, décalage `(arctan(T/(1−β)) − arctan(T/β))/T` identique pour toute cellule). Rien n'est conclu sur β.

*19.29.3 Ce qui manque, redéfini globalement.* Ce ne peut pas être lié à un seul passage. Ce qui manque est une
**obligation collective sur la succession des foules** : les transitions de la grammaire sont obligatoires (chaque rang a
son premier d'occurrence, chaque écart sa rencontre, chaque foule sa composition fixée par les pas de contact), et le
levier global est la rigidité de cette grammaire : si une transition est atteinte et qu'une dérive (paire à hauteur
commune) est entreprise, il faut montrer que les transitions obligatoires suivantes ne peuvent plus être respectées par
la foule telle qu'elle est — sur des millions de zéros, pas sur trois. Les objets compilés qui le permettent : les foules
emboîtées et leur taille par rang (RvM porté, CAP), les contributions par régime avec phases, les contacts décalés de la
paire, la lecture tangentielle de β aux contacts.

*19.29.4 Hypothèses proposées (nommées, jamais posées comme prouvées ; chacune à tester pour équivalence avec RH avant tout
usage).* **H-F1 (foule de l'écart, instance)** : pour tout écart, la demande exacte est réalisée par la somme de toutes les
Tours, et la part des Tours hors foule est bornée par l'enveloppe décroissante — identité de la formule explicite plus
`gapTerm_norm_le_cap`, à compiler comme décomposition foule / queue. **H-F2 (progression des foules)** : la suite des
foules, indexée par les écarts, est déterminée par les premiers seuls et chaque transition (entrée d'un nouveau membre
dans la foule) est une lecture du pas de contact contre la longueur de l'écart — vrai par construction, à compiler.
**H-F3 (dérive non soutenable, le levier à tester)** : une paire à hauteur commune, présente dans les foules de tous les
écarts dont la longueur est au plus son pas, impose à chacune de ces foules l'identité du complément (R3, cross terms) ;
l'hypothèse est que la succession des transitions obligatoires de la grammaire est incompatible avec un complément
réalisé par la même foule sur tous ces écarts. Son statut est inconnu ; elle doit être explorée numériquement sur des
millions de zéros avant toute tentative Lean, et jamais posée.

*19.29.5 Expérience pré-enregistrée E402 (non exécutée, en attente du feu vert).* Données réelles : zéros d'Odlyzko
versionnés (2 001 052 zéros, provenance et somme de contrôle dans `experiments/data/`) ; premiers jusqu'à la borne où la
foule reste entièrement dans les données (longueur de l'écart au moins `π/T_max`). Pour chaque écart : la taille de la
foule (nombre de zéros dont le pas ≥ ℓ, lue par contacts), la décomposition de la contribution totale tronquée en trois
régimes (moins d'un pas, un pas, plusieurs contacts), la part de phase (somme vectorielle contre somme des modules), en
regard de la demande exacte de l'écart dans le canal compilé (même formule que E401, aucune autre). Jumeau
déterministe : les identités compilées (télescopage, plateau `≤ ℓ`, enveloppe `≤ 2/T`, nullité aux périodes entières)
vérifiées ligne par ligne à deux précisions. Synthétique, séparé : une paire injectée à une hauteur qui n'est celle
d'aucun zéro réel, pour mesurer sur toutes les foules qui la contiennent le complément exigé, sans jamais lire β.
Résultats dits d'avance : la foule d'un écart ordinaire est immense (bien plus que son rang) ; le plateau est réalisé à
égalité de module ; aucune conclusion sur β ; aucune comparaison à une moyenne ; aucun contact n'est un premier. Les huit
points « erreurs de débutant » et les critères de la main-courante E379 s'appliquent. Exécution bornée (minutes).

### 19.30 Mission R9 : capturer la dérive collective des contacts (2026-11-01) — exécutée

*19.30.1 Ce qui a été fait.* Mission de l'auteur (R9, référence 3dd0f638, R8, §19.29). E402 exécutée après vérification de
son protocole pré-enregistré (§19.29.5), étendue aux mesures demandées : `experiments/E402_CollectiveContacts/` (README,
script, sorties, provenances, bornes). Module isolé `Terminal/CollectiveContactRigidity.lean` (47 théorèmes, 7 définitions,
3 tentatives journalisées dans `audits_compilation/collectivecontactrigidity/`, axiomes standard, chaîne intacte). Sonde hors
build `ProbeCollectiveContactRigidity.lean` affichant le but exact laissé par Lean. Rapport d'audit
`RAPPORT_AUDIT_R9_20261101.md` (correspondance point par point, diagnostic du compilateur).

*19.30.2 Les contacts rendent les deux coordonnées (compilé).* `u_{ρ,k} = (arctan(T/β) + kπ)/T` ; `u_{k+1} − u_k = π/T` ;
`T = π/(u_{k+1} − u_k)` ; `tan(T u_k) = T/β` ; `β = T/tan(T u_k)` ; branche : `T u_k − kπ = arctan(T/β) ∈ ]0, π/2[`
(`contactLog_branch_bounds`). Deux contacts consécutifs rendent `(T, β)` (`coordinates_from_two_contacts`) ; mêmes contacts
⟹ mêmes coordonnées (`coordinates_eq_of_contacts_eq`). Les deux dérives sont séparées : le pas ne lit que `T`
(`contactLog_step_blind_to_radial`) ; à même `T`, `β` déplace tous les contacts de `(arctan(T/β') − arctan(T/β))/T ≠ 0`
(`contactLog_shift_ne_zero_of_radial_ne`) et l'amplitude `x^{β−1}` du zéro OFF est dominée par celle `x^{−β}` du miroir
(`mirror_density_dominates`). Phase de contact dans un écart : `θ_out − θ_in = Tℓ`, `θ(C_k) = kπ`, contacts traversés
`⌊Π(p_{n+1})⌋ − ⌊Π(p_n)⌋` = cardinal des `k` avec `a < u_k ≤ b` ; un membre de la foule traverse au plus un contact.

*19.30.3 La demande de chaque écart, décomposée exactement (compilé, toute position radiale).* Seuil `π/ℓ` ; foule
`= upperWindow(π/ℓ)` ; `localArithmeticTarget I = gapCrowdSum I + gapTailSum I` (C126 + identité du reste) ; la part de foule
est une somme FINIE, phases et signes conservés ; le résidu après la foule est exactement la queue, bornée sans RH par
`budget(π/ℓ)·(p_n + p_{n+1})` (exposant 1 : `collective_residual_bound`) ; le terme du zéro OFF est isolé dans la part de foule
(`crowdSum_split_zero`) et le miroir est dans la même foule. La foule seule n'accomplit jamais la demande (F8). Transitions :
deux foules sont emboîtées ; la différence est faite des points de hauteur entre les deux seuils ; les foules sont des
fenêtres de lecture d'un ensemble fixe (`crowd_eq_filter_of_window`) — une variation de foule n'est pas l'apparition d'un
zéro. Sous `LogGapsVanish` (théorème du port PNT, non importable avec le port Zeta23 dans un même environnement — tentative 1),
tout zéro est dans la foule d'au moins un écart, et **la rigidité radiale de la foule est RH** (`crowdRadialRigidity_iff_riemannHypothesis`).

*19.30.4 E402, résultats (1 229 écarts, `p ≤ 10 000`, 2 001 052 zéros, 108,6 s).* Reconstruction exacte au niveau des
données : résidu max `1,4·10⁻⁷`, médiane `2·10⁻⁹`, tous sous la borne de troncature indépendante (`Σ_{γ>T_max} 1/γ² ≤
1,84·10⁻⁶`, Trudgian 2014, `N(T_max)` exact). La foule porte la demande (part médiane 1,0003 ; queue 0,034) avec forte
compensation de phase (part de phase médiane 0,057). Foules jusqu'à 16 924 membres ; **six écarts courts ont une foule vide**
(seuil sous `T_1`), non dit d'avance, consigné. Contacts traversés par les foules : 1 655 515, aucun n'est une rencontre ;
quarts depuis la rencontre `414 409 / 414 234 / 413 158 / 413 714` (comptage, aucune lecture statistique). Transitions de
`−15 025` à `+15 544`. Jumeaux : E401 reproduit à `4,7·10⁻¹³`, télescopage `4·10⁻¹⁶`, identités `≤ 2·10⁻¹⁵`, mpmath `≤ 2·10⁻¹⁴`.
Synthétique séparé (paire `0,3/0,7` à `T* = 2515,93`, hauteur d'aucun zéro réel) : 468 foules la contiennent ; complément exigé
jusqu'à `4·10⁻⁴`, 2 800 fois le résidu observé, **mais jamais au-dessus des bornes démontrées (0/468, même à l'échelle de la
ligne)**. Lecture : le défaut de reconstruction mesuré contre le résidu observé repose sur la complétude de la liste des
zéros ; c'est un contrôle, pas une preuve ; les bornes compilées ne détectent pas une paire.

*19.30.5 Ce que Lean affiche comme manquant.* Sonde : `C : OffCarrier`, `I`, `hI : zéro OFF dans la foule de I`, toutes les
identités ci-dessus et la borne d'exposant 1 en contexte, `⊢ False`. Toutes les hypothèses sont vraies pour toute position
radiale sauf `β < 1/2`, qui est l'hypothèse à contredire. Hypothèses encore nécessaires : une borne de la queue (ou de la
foule privée de la paire) d'exposant `< 1 − β` à partir des seuls premiers, ou une lecture des contacts de la foule par la
demande qui ne passe pas par `β` ; dépendances à RH connues : borne `√x` de la queue ⟺ suivants en ligne ; rigidité radiale
de la foule ⟺ RH. Blocage mathématique. Réponse à la question terminale : démontré, mesuré, affiché ; pas d'hypothèse posée ;
la rigidité des positions radiales ne découle pas des contraintes disponibles. H-F3 (§19.29.4) reste non testée au sens
fort : E402 montre qu'aucune borne compilée ne fait obstacle au complément exigé par une paire ; une incompatibilité, si elle
existe, doit venir d'une contrainte d'exposant strictement meilleur que 1, non disponible.

### 19.31 Directive R11 : théorèmes acquis, CAP et composition formelle (2026-11-01) — exécutée

*19.31.1 Correction de stratégie (auteur).* Le diagnostic de §19.30.5 est corrigé par l'auteur : le corpus possède déjà une
détermination universelle des zéros depuis les premiers (`rh_gap_criterion` : `primes_determine_nontrivial_zero_multiset`,
`prime_determined_zero_window_eq_canonical_any_length`). Ce qui n'est pas établi est que cette détermination entraîne une
contradiction pour une position OFF. Ordre de travail : premiers → constellation complète déterminée → coordonnées `(β, T)` →
contacts et rencontres → reconstruction des écarts ; puis, séparément, la reconstruction inverse directe par les rencontres.
Principe non négociable : un théorème démontré reste un théorème ; un défaut d'import ne le rétrograde jamais en hypothèse.

*19.31.2 Incident d'import R9 résolu.* Reproduit (`CS.deriv` déclaré deux fois) ; cause : `PNTPort/Sobolev.lean`,
`PNTPort/Fourier.lean`, `PNTPort/Mathlib/…/Log/Basic.lean` sont des copies identiques (corps, `diff` vide) de
`Zeta23Port/FromPNTPlus/…`, déclarant les mêmes objets dans l'espace racine ; nature définitionnelle, non mathématique ;
raccord : les trois fichiers réexportent la copie Zeta23 (aucun théorème modifié) ; `Wiener`, `Consequences`,
`LogGapsTheorem`, `SummitVertical` recompilés ; coexistence vérifiée. Hypothèses de substitution supprimées dans
`CollectiveContactRigidity.lean` : `every_zero_in_some_crowd` et `crowdRadialRigidity_iff_riemannHypothesis` sont désormais
sans hypothèse (`logGapsVanish_holds`). R9 (CLAUDE.md) corrigée en conséquence.

*19.31.3 Détermination universelle portée et raccordée.* `RHV6Fresh/RhGapPort/PrimesDetermineZeros.lean` (22 théorèmes,
mêmes noms, mêmes preuves ; chaînes d'outils différentes, dépendance Lake impossible) : `F = ζ` hors du pôle ; mêmes zéros non
triviaux et mêmes ordres ; source déterminée = source canonique ; toute fenêtre ordonnée déterminée = canonique. Raccords :
`ζ` est admissible et deux `F` admissibles coïncident (la classe d'hypothèse est un singleton) ; prédicat Mathlib ⟺ prédicat
de bande (`isNontrivialZetaZero_iff_strip`, port Kadiri de `rhv3_lean`) ; la vue ordonnée déterminée par les premiers EST la
fenêtre ouverte du corpus. `Terminal/PrimeCapsContactsBridge.lean` (27 théorèmes) §1 : zéros de bande de `F` = vrais zéros ;
`upperWindow`, foule de chaque écart, comptage avec multiplicité (objet des CAP), coordonnées `(β_k, T_k)` de chaque membre
canonique sont lus dans `F` ; « `F` a un zéro bas » ⟺ ¬RH ⟺ un porteur OFF existe ; toute propriété invariante hors du
pôle se transporte (`primeDetermined_property_iff`). Distinction tenue : détermination globale (identité) ≠ reconstruction
constructive par les contacts (`coordinates_from_two_contacts`) ; aucune n'est niée.

*19.31.4 CAP × contacts × foules (compilé, toute `β`).* Pas de contact du rang `k+1` encadré par les deux CAP
(`lower_cap_contact_interval`, `upper_cap_contact_interval`) ; taille de foule capée par la longueur de l'écart
(`crowd_card_cap`) ; rang garanti dans la foule sous le plafond (`crowd_contains_rank_of_upper_cap`) ; contacts traversés par
toute famille de la foule ≤ taille de la foule ≤ cap (`crowd_family_contacts_cap`) ; transitions de foule entre deux écarts
bornées par le comptage local (`crowd_transition_cap`) ; débit de la queue par fenêtre unité borné (`tail_unit_window_cap`) ;
décomposition exacte de la demande avec foule lue dans `F` (`primeDetermined_demand_decomposition`). La paire OFF/sortant
est indiscernable par les CAP et les pas (`pair_blind_to_caps_and_steps`) et entre deux fois dans le comptage
(`pair_counted_twice`) : les CAP ne déterminent pas `β` directement — constaté après composition, non supposé.

*19.31.5 Ce que Lean laisse.* Sonde hors build (`audits_compilation/prime_caps_contacts_bridge/ProbePrimeCapsContactsBridge.lean`,
sortie brute versionnée) : sous `hF`, `C : OffCarrier`, `hI`, et vingt-neuf faits compilés (détermination raccordée, CAP composés,
décomposition, terme OFF isolé, borne de queue exposant 1, miroir, décalage, tangente, amplitude, F8, rigidité ⟺ RH), `⊢ False`
non résolu ; contrôle fermé par `β = 1/2`. Raisons précises (REPORT.md §7) : (1) la détermination est une identité, sa classe
d'hypothèse est `{ζ}`, elle transporte la question radiale sans inégalité ; (2) les CAP comptent ON + 2·OFF, invariants sous
l'échange d'un zéro ON contre une paire à même hauteur ; (3) le pas est `π/T` ; les seuls objets sensibles à `β` (décalage des
contacts, amplitude) entrent par la somme de foule, identité exacte avec une queue bornée à l'exposant 1 seulement ; (4) la
reconstruction inverse directe par les rencontres n'est pas compilée. Aucune hypothèse proposée. Table de dépendances complète
(nom, fichier:ligne, hypothèses, statut, transport, conclusion, dépendance à RH) dans `REPORT.md` §2–§6.

*19.31.6 Incident indépendant.* `lake build` (cible par défaut) échoue avant cette session : `windowProjection` déclaré dans
`SpectralWindowProjection` et `GapTranslationInvariance` (chaîne). Non corrigé ; question à l'auteur. Chaîne vérifiée :
`lake build RHV6Fresh.Terminal.DemonstrationChain` passe.

### 19.32 Projection contre axe réel : contact porteur d'amplitude et somme réelle aux rencontres (2026-11-02) — exécuté

*19.32.1 Question de l'auteur.* Les affirmations « le OFF ne viole aucune contrainte des points de rencontre » sont-elles
faites à partir de π(x) et li(x) ou à partir des vrais écarts et de la somme des contacts sur l'axe réel ?

*19.32.2 Réponse consignée.* À partir de projections ou de définitions sans amplitude : la disparition des écarts
logarithmiques vient du théorème des nombres premiers (projection côté premiers) ; les CAP viennent de Riemann–von
Mangoldt (projection côté zéros) ; le contact compilé ne contenait que la fréquence et la longueur
(`contactLog_step_blind_to_radial` est une conséquence de la définition, pas une découverte) ; la cassure comparait au
fond lissé. La phrase « le OFF ne viole aucune contrainte des rencontres » était trop forte ; elle est retirée. La seule
formulation exacte : « le OFF ne viole aucune des contraintes que le corpus avait formalisées, qui sont des projections ou
des définitions sans amplitude ».

*19.32.3 Module `Terminal/AmplitudeContact.lean` (isolé, 24 déclarations, 2 tentatives journalisées dans
`audits_compilation/amplitude_contact/REPORT.md`).* Le contact reçoit sa troisième coordonnée : l'amplitude du zéro à son
propre contact, module du terme lissé déposé sur l'axe réel (`contactAmplitude_eq` : poids × position^β). Le pas
d'amplitude entre deux contacts consécutifs vaut exp(β·π/T) (`contactAmplitude_ratio`) : à même fréquence, même pas
d'amplitude ⟺ même position radiale (`contactAmplitude_ratio_eq_iff`), et la position radiale se lit sur le pas
(`radial_from_amplitude_step`). Contraste exact avec le pas de position, aveugle. Dépôts aux vrais points de rencontre
(`meetingDeposit`, `meetingDeposit_norm`) ; identité à la rencontre (`meeting_demand_eq_tsum_deposits`) et identité de
l'écart (`gap_demand_eq_deposits`) : la demande des vrais écarts est la différence des deux sommes signées de dépôts ;
la somme des amplitudes de la foule majore la somme signée sans lui être égale (`norm_crowdSum_le_amplitudeSum`).
Paire OFF : le rapport des dépôts miroir/OFF au point de rencontre vaut (w′/w)·p^{1−2β} (`mirror_deposit_ratio`) et
tend vers l'infini avec l'abscisse (`mirror_amplitude_ratio_tendsto`) : la phrase de l'auteur « l'amplitude d'un OFF est
plus grande et croissante » est compilée. Ce que le module ne donne pas : lire β = 1/2 sur les amplitudes des contacts
EST RH (`amplitudeContactRigidity_iff_riemannHypothesis`, but nommé jamais posé) ; aucune identité ne fixe l'amplitude
d'un contact depuis les premiers seuls.

*19.32.4 E403 (pré-enregistrée au commit 03d4346d avant exécution, exécutée en 103 s, `experiments/E403_AmplitudeMeetings/`).*
Vrais écarts (1229, premiers ≤ 10 000, demande exacte par crible), vrais points de rencontre, dépôts de 2 001 052 zéros
avec leurs vraies amplitudes, canal lissé compilé seulement. Résultats contre prédictions : (1) identité réelle tenue au
niveau des données (résidu max 1,4·10⁻⁷, jumeaux mpmath ≤ 2·10⁻¹⁴) ; (2) le contact porteur d'amplitude rend 0,5 sur le
réel (donnée, pas mesure) et 0,3 / 0,7 à 10⁻¹² sur le synthétique : il n'est pas aveugle ; (3) somme des amplitudes à la
rencontre = 103 fois la demande (médiane), part de phase 0,057 : la somme des modules n'est pas la demande ;
(4) synthétique SÉPARÉ, un zéro ON (rang 2000) REMPLACÉ par une paire 0,3/0,7 à une hauteur d'aucun zéro : le complément
exigé dépasse le résidu observé sur 1229/1229 écarts (non dit d'avance : « la plupart »), jusqu'à 3,4·10⁷ fois, croît en
p^{0,400000000000} (= `mirror_deposit_ratio`), et ne dépasse aucune borne compilée (0/1229 contre la borne en ligne,
0/1229 contre l'inconditionnelle) ; (5) rien conclu sur β.

*19.32.5 Ce que cela change.* La comparaison réelle existe désormais, compilée et calculée. Elle montre que la paire
change la somme réelle à chaque rencontre, et que le seul détecteur est le résidu observé, c'est-à-dire la complétude de
la liste des zéros ; aucune contrainte compilée sur l'axe réel n'est violée. Le lieu d'un refus du OFF, s'il existe, est
une identité qui fixe l'amplitude au point de rencontre depuis les premiers seuls ; le corpus n'en contient pas, et
l'énoncé « toute amplitude de contact est celle de la ligne » est RH. Lexique : « contact porteur d'amplitude » = triplet
(position, fréquence, amplitude) ; « dépôt » = terme lissé d'un zéro en un point de rencontre.

*19.32.6 Non fait.* Rien lancé au-delà ; échec préexistant de la cible par défaut (`windowProjection`) toujours non corrigé
sans l'auteur ; H-F1/H-F3, B′, H′, I1–I6/I9, J inchangés.

### 19.33 La somme des contacts le long de l'écart : montée, cassure, redescente, passage à l'écart suivant (2026-11-02) — exécuté

*19.33.1 Demande de l'auteur.* L'amplitude d'un contact isolé ne suffit pas : il faut suivre la somme de tous les
contacts sur l'axe réel le long de chaque écart, pour l'enchaînement des zéros sur la ligne (fréquence qui avance,
amplitude stable) et pour l'enchaînement dégénéré d'une chaîne OFF (fréquence partagée par deux membres, amplitude
scindée en trop faible et trop forte), sans projection ni statistique, écart par écart. Comportement à isoler : la
somme monte, atteint au point de rencontre un sommet très précis qui est l'écart exact (la cassure), puis redescend
pour laisser l'écart suivant recommencer ; lecture de l'auteur, mesurée et non posée : le dernier élan vers la cassure
est porté par une fréquence qui monte fortement. Les deux canaux sont faits à sa demande, le brut d'abord.

*19.33.2 Deux canaux, séparés (R12).* Canal brut : fonction de Tchebychev en escalier contre son fond régulier ; la
somme des zéros y monte avec la pente un entre deux premiers et chute du logarithme du premier rencontré ; ce canal
n'est PAS compilé dans le corpus et reste un jumeau numérique. Canal lissé : demande A(x) contre fond B(x) (E401–E403),
compilé ; la cassure y est un changement de pente. Dans les deux, chaque zéro entre avec sa vraie amplitude et sa vraie
fréquence ; le même facteur de phase sert aux deux, seul le poids change.

*19.33.3 Lean (`Terminal/ContactSumProfile.lean`, isolé, 12 déclarations, 2 tentatives journalisées, axiomes
standard seulement, audit `audits_compilation/contact_sum_profile/REPORT.md`).* Objet compilé : le profil d'un membre
le long de l'écart (`memberProfile`, dépôt en x moins dépôt au début de l'écart, nul au début, amplitude bornée par
le poids fois les deux puissances radiales) et la somme des contacts le long de l'écart (`contactSumProfile`).
Théorèmes : elle vaut zéro au début de l'écart ; elle vaut le reste lissé en x moins le reste au début
(`contactSumProfile_eq`) ; au point de rencontre elle vaut EXACTEMENT la demande de l'écart
(`contactSumProfile_meetingPoint`) : le sommet exact de l'auteur, compilé dans le canal lissé ; l'écart suivant
repart de zéro à la rencontre (`contactSumProfile_next_at_meeting`) ; sans remise à zéro, le profil de l'écart suivant
est le profil continué moins la demande déjà réalisée (`contactSumProfile_continuation`), et deux écarts lus en continu
donnent la somme des deux demandes (`contactSumProfile_two_gaps`). Ce que le module dit en mots : la « redescente » du
canal lissé est un changement d'origine à la rencontre, pas un retour de la somme vers zéro. Ce qu'il ne dit pas : la
forme de la montée et les fréquences qui la portent ; rien sur la position radiale.

*19.33.4 E404 (pré-enregistrée au commit db489888 avant exécution, exécutée en 141 s,
`experiments/E404_ContactSumProfile/`).* Dix écarts lus un par un (dont le plus long, 9551 → 9587, et le dernier de
longueur deux, 9929 → 9931), une fenêtre de six écarts consécutifs suivie sans remise à zéro, grille de cent points par
écart sur les demi-entiers, 2 001 052 zéros, décomposition par fréquence croissante de la montée et de la chute,
jumeau OFF par blocs de 1, 50 et 500 zéros ON remplacés par des paires 0,3 / 0,7 aux hauteurs médianes (jamais la
hauteur d'un zéro), jumeaux mpmath à 10⁻¹².
Canal brut, lecture écart par écart : (a) la somme monte avec la pente un et atteint juste avant la rencontre
l'écart arithmétique exact (n = 614 : 22,970 pour 23 ; n = 1182 : 35,081 pour 35 ; n = 1228 : 32,889 pour 33 ;
l'écart au vrai est le résidu de troncature de la liste, au plus 0,06) ; (b) elle chute d'exactement un moins le
logarithme du premier (n = 614 : −7,393 pour −7,422) : la cassure est un saut d'une hauteur très précise ;
(c) elle ne revient PAS à zéro : après la chute elle reste plus haute de « écart moins log p » et dérive au fil des
écarts (fenêtre continue : 0, 23, 15,6, 16,3, 9,2, 17,5, 12,7, …) ; ce qui revient vers zéro est la dérive x − ψ(x)
sur de longues plages, contenu du théorème des nombres premiers, donc projection ; (d) décomposition par fréquence,
n = 614, seuil de foule 594 : montée cumulée 0,3 avec trois zéros, 2,8 au seuil de foule, 13,9 à mille, 20,1 à dix
mille, 24,5 à trente mille, 22,97 avec tous ; chute cumulée 0,3 au seuil de foule, −1,9 à trois mille, −3,2 à dix
mille, −8,8 à trente mille, −7,39 avec tous. **La montée n'est pas portée par les basses fréquences : elle se
construit entre le seuil de foule et vingt fois ce seuil ; la cassure exige des fréquences de l'ordre de π fois le
premier rencontré, vingt-cinq fois le seuil de foule.** La lecture de l'auteur (la fréquence doit monter fortement pour
réaliser la cassure) est tenue dans ce canal ; la prédiction de l'exécutant (montée déjà portée par les basses
fréquences) est FAUSSE et consignée comme telle. Sur les écarts de longueur deux la liste ne résout pas la grille
(largeur de résolution ≈ 0,03) : ondulation de troncature, montée 0,97 et 0,91 pour 1.
Canal lissé : sommet = demande exacte à 10⁻⁸ sur tous les écarts (théorème lu numériquement) ; profil continu,
courbe, qui plafonne au milieu de l'écart et redescend AVANT la rencontre (n = 614 : 0 → 0,026 au milieu → 0,0199 à
la rencontre) : la montée n'y est ni régulière ni monotone, le sommet exact n'est pas un maximum, la cassure n'est
qu'un changement de pente ; la montée y est presque entière dès les fréquences inférieures à mille : le poids en un
sur T² éteint l'élan de haute fréquence qui fait la cassure brute.
Jumeau OFF, séparé : canal brut, au point de rencontre, différence avec le réel 0,003 à 0,43 pour un zéro remplacé,
jusqu'à 4,2 pour cinquante, 3,9 à 11,9 pour cinq cents, c'est-à-dire de la taille de la cassure (log p ≈ 8 à 9) ; le
long d'un écart la chaîne dégénérée n'ajoute ni pente ni saut mais une ondulation de la taille de la cassure (bloc
500, n = 614 : de −5,7 à +5,1 à l'intérieur d'un seul écart) ; toutes ces différences dépassent le résidu réel de
troncature ; aucune borne compilée n'existe dans ce canal (rien à « violer ») ; canal lissé : différences 10⁻⁷ à
3·10⁻³, au-dessus du résidu réel comme en E403, le bloc 500 dépasserait à n = 1228 la borne en ligne maximale
d'E403, noté sans conclure (cette borne suppose la liste réelle). Rien n'est conclu sur β des vrais zéros.

*19.33.5 Ce que cela change.* Le « up and down » de l'auteur est exact dans le canal brut pour ses deux hauteurs :
montée jusqu'à l'écart exact, chute du logarithme exact du premier ; mais le point de retour n'est pas zéro, et la
chaîne réelle n'y revient que par la dérive de longue plage qui est la projection (R12). L'élan final et la cassure
sont bien l'œuvre des membres de plus haute fréquence, loin au-dessus de la foule de l'écart : c'est la première
mesure directe, sur l'axe réel, de la lecture « la fréquence augmente fortement pour réaliser la cassure ». Le canal
lissé compilé porte le sommet exact comme théorème mais lisse la cassure. La chaîne OFF dégénérée, elle, n'apporte
ni pente ni saut : une ondulation, et son défaut est de la taille de la cassure dès cinq cents zéros remplacés. Lieu
restant d'un refus du OFF : il faudrait qu'une identité fixe, depuis les premiers seuls, la contribution des hautes
fréquences à la cassure ; le corpus prouve que la somme complète la réalise, pas qu'une liste contenant une paire ne le
peut pas (même conclusion qu'E403, maintenant lue sur le profil et non plus au seul point de rencontre). Lexique :
« profil de contacts » = somme des contacts depuis le début de l'écart ; « canal brut » = escalier, non compilé ;
« canal lissé » = demande, compilé.

*19.33.6 Non fait.* Canal brut non compilé ; bornes de queue non recalculées pour le jumeau ; échec préexistant de la
cible par défaut (`windowProjection`) toujours non corrigé sans l'auteur ; H-F1/H-F3, B′, H′, I1–I6/I9, J inchangés.

### 19.34 Plan de tentatives après E404 : sources d'origine, forme unique de la contradiction finale, un verrou, deux tentatives, règle d'arrêt (2026-11-02) — pré-enregistré, non exécuté

*19.34.1 La demande.* L'auteur demande, à partir de sa lecture d'E404 (les hautes fréquences réalisent la cassure ;
deux échelles distinctes, l'échelle de l'écart et l'échelle de résolution de la cassure ; la prochaine analyse doit
suivre la formation progressive de chaque cassure quand les fréquences sont ajoutées, en gardant phases, amplitudes et
contacts de chaque Tour), un plan de **tentatives** et non de constats. Les sources d'origine des constats doivent être
celles que le Lean utilise, et le but est de détecter la contradiction finale, pas d'ajouter des théorèmes. Le plan
ci-dessous obéit à trois règles : chaque tentative vise une contradiction nommée, a un critère d'échec déclaré avant
exécution, et n'entre en Lean que si son jumeau numérique survit.

*19.34.2 Les sources d'origine des constats d'E404.* Trois sources, dont deux seulement sont compilées.
- Source compilée du canal lissé : le reste lissé est défini avec les seuls premiers (somme de von Mangoldt pondérée par
  « un moins le rapport de l'entier au point », moins le fond) ; l'identité compilée l'égale à la somme de tous les
  termes de résidus (`smoothedRemainder_eq_tsum_residueTerm`) ; le profil de contacts et son sommet exact sont compilés
  (`contactSumProfile_meetingPoint`) ; les dépôts à la rencontre sont compilés (`gap_demand_eq_deposits`) ; les bornes
  de queue d'E403 sont compilées. C'est la source de tout ce qui a été lu sur β.
- Source arithmétique compilée : sur un écart ouvert, la somme de von Mangoldt pondérée est une expression élémentaire
  des premiers déjà passés ; au passage du premier suivant, sa pente saute d'une quantité exacte (le logarithme du
  premier rapporté au premier). C'est la « cassure » dans le canal compilé : un saut de pente, pas de valeur.
- Source non compilée du canal brut : la formule explicite tronquée avec son terme d'erreur (origine quantitative du
  constat « la cassure exige des fréquences de l'ordre de π fois le premier »). Un port partiel existe dans un autre
  paquet avec seize `sorry` ; il ne sera pas utilisé ni poursuivi : ce serait exactement « ajouter des théorèmes ».
Règle du plan : tout Lean de §19.34 n'utilise que les deux premières sources.

*19.34.3 La forme unique de la contradiction finale dans la source compilée.* Le corpus contient déjà la forme que doit
prendre toute contradiction avec un zéro OFF : `smoothedRemainder_growth_bounds_zero` dit qu'une borne de croissance
du reste lissé d'exposant θ force tout zéro à avoir une position radiale au plus θ. Donc refuser un zéro OFF de position
β, c'est produire depuis les premiers une croissance du reste d'exposant strictement inférieur à β ; refuser tous les
zéros OFF, c'est l'exposant un demi, et `riemannHypothesis_iff_remainderExponent_eq_half` dit que c'est RH. Le reste à
chaque point de rencontre est la somme télescopée des demandes des écarts précédents (compilé :
`contactSumProfile_continuation`, `contactSumProfile_two_gaps`). La seule flèche ouverte est donc : **une annulation
entre demandes successives, lue sur les seuls premiers, le long de la chaîne des points de rencontre.** Toute
tentative doit finir sur cette flèche ; ce qui n'y mène pas est un constat. Partage R12 : la croissance du reste est une
quantité d'axe réel ; une borne obtenue par le théorème des nombres premiers avec terme d'erreur serait une projection
et ne compte pas.

*19.34.4 Verrou V, à exécuter d'abord (Lean isolé, au plus huit déclarations, deux tentatives journalisées).* Énoncé :
toute partie finie de la somme des contacts est dérivable au premier suivant ; la source arithmétique y a un saut de
pente exact ; donc la queue au-delà de toute troncature porte à elle seule le saut de pente entier, pour toute
troncature. Conséquence : une paire OFF, partie finie, ne participe jamais à la cassure ; aucun détecteur du OFF ne
peut être logé dans la cassure, dans le canal compilé comme dans le canal brut (déjà §19.13 pour le brut, non compilé).
Ce verrou répond directement à la « formation progressive de chaque cassure » demandée dans le texte : elle est un
phénomène de queue, identique pour ON et OFF. Prédiction : compile ; ferme définitivement la famille « la cassure
refuse le OFF » et oriente les tentatives vers la partie régulière entre cassures. Ce n'est pas une contradiction, c'est
le verrou qui empêche d'en chercher une là où le corpus prouve qu'elle n'est pas.

*19.34.5 Tentative A — annulation des demandes successives (axe réel).* Prémisse : une paire OFF de position β
supérieure à un demi et de fréquence donnée. Son dépôt aux points de rencontre croît comme le premier à la puissance β
(compilé : `meetingDeposit_norm`). Cible : une identité, lue sur les seuls premiers, qui donne aux sommes partielles de
demandes un exposant inférieur à β par annulation de signes entre écarts consécutifs ; ce serait la flèche de 19.34.3.
Jumeau numérique pré-enregistré, sur les vrais premiers du fichier d'E404, sans statistique : demande de chaque écart,
son signe, ses sommes partielles aux points de rencontre, comparées au premier à la puissance un demi et aux puissances
six dixièmes et sept dixièmes, et aux dépôts d'une paire synthétique ; décomposition par fréquence héritée d'E404.
Prédiction de l'exécutant : les sommes partielles sont le reste lui-même (tautologie) et aucune loi d'annulation ne
s'écrit avec les premiers seuls sans passer par le terme d'erreur du théorème des nombres premiers. Critère d'échec :
si la seule borne atteignable passe par une projection ou suppose l'exposant, A est morte et déclarée telle ; Lean
seulement si une identité d'annulation en premiers seuls apparaît dans le jumeau.

*19.34.6 Tentative B — la paire dans la tête et dans la queue selon l'échelle de la cassure.* C'est la seule tentative
qui utilise la séparation d'échelles d'E404. Pour les premiers au-dessus de la fréquence de la paire divisée par π, la
paire est dans la tête (fréquences sous l'échelle de la cassure) ; la tête vaut la demande moins la queue, et la queue
est bornée par la sommabilité compilée (bornes d'E403) ; le dépôt de la paire dans la tête est exact, et son pas entre
deux rencontres consécutives lit β (compilé : `contactAmplitude_ratio`, `radial_from_amplitude_step`). Cible : montrer
que les membres ON de la tête ne peuvent pas absorber le pas de la paire à deux rencontres consécutives sans un membre
de fréquence inférieure à l'échelle de la cassure, ce qui contredirait le comptage encadré (`FrequencyCap`). Jumeau
numérique : sur six écarts consécutifs, tête et queue séparées au seuil π fois le premier, dépôt de la paire, résidu
demandé aux ON de la tête. Critère d'échec : si l'absorption par les ON de la tête n'est contrainte que par la constance
par membre (⟺ RH, §19.21), B est morte. Prédiction de l'exécutant : morte pour la même raison qu'E403, mais c'est la
seule lecture d'E404 qui n'a pas encore été tentée.

*19.34.7 Règle d'arrêt.* Ordre : V → jumeau de A → jumeau de B → Lean des seules survivantes. Chaque exécution tient en
minutes ; pré-enregistrement commis avant exécution ; modules isolés, hors `RHV6Fresh.lean` ; aucune modification de
`DemonstrationChain.lean` ni de ses imports ; aucune hypothèse nommée nouvelle sans audit de corpus (R11). Si V compile
et si A et B meurent par leurs critères, le plan consigne que la contradiction finale a, dans la source compilée, la
seule forme de l'exposant de croissance, que la flèche ouverte est l'annulation des demandes successives depuis les
premiers, et demande à l'auteur une **source** nouvelle, pas un théorème nouveau. Aucune de ces tentatives n'est
promise : ce sont des tentatives.

## 19.35 Exécution du plan §19.34 : le canal brut aux points de rencontre (2026-11-02) — pré-enregistré

### 19.35.1 Ce que l'exécution a d'abord trouvé dans le corpus
Le verrou V de §19.34.4 est DÉJÀ compilé dans le canal lissé : `MeetingExactness.lean` prouve que la somme lissée n'est
pas dérivable en un premier (saut de pente égal au poids divisé par le premier), que le fond l'est, donc que le reste ne
l'est pas à la rencontre, et qu'aucune famille finie de parts n'accomplit la demande sur un voisinage d'une rencontre.
Il n'est pas réécrit (règle : aucun code dupliqué).

### 19.35.2 Ce qui manquait dans l'analyse du BRUT, et ce qui est compilé
Le canal brut n'avait aucun objet compilé côté zéros (la série `Σ x^ρ/ρ` n'est pas absolument sommable, `tsum` y vaut
zéro). Mais son côté PREMIERS est élémentaire : le reste brut à l'entier `N` est `ψ(N) − N`, écrit avec `massA` de
`MeetingExactness`. Le module isolé `Terminal/RawMeetingRemainder.lean` (non ajouté à `RHV6Fresh.lean`) compile :
- entre deux rencontres brutes (entiers de poids non nul) le reste brut descend d'exactement une unité par entier, et il
  est pris entre ses valeurs aux deux rencontres : c'est l'« élan de pente un » et la « chute du logarithme » d'E404,
  sans formule explicite ;
- le pont brut → lissé à l'entier : `M · A(M)` est la somme des `ψ(k)` pour `k < M` ;
- la réduction : une borne du reste brut aux deux côtés de chaque rencontre, d'exposant `θ`, se propage à tout entier
  (Bertrand), puis au reste lissé partout, puis à toute position radiale (`smoothedRemainder_growth_bounds_zero`) :
  `β ≤ θ` pour tout membre ; avec `θ = 1/2 + ε` pour tout `ε` : RH (`riemannHypothesis_iff_remainder_growth_all_eps`) ;
- la lecture OFF : un membre à `β` force, pour tout `θ < β` et toute constante, une rencontre brute où le reste brut
  dépasse `C·E^θ` d'un côté ou de l'autre.
Les trois paramètres sont utilisés ensemble : le reste brut à la rencontre est la totalité des termes `x^ρ/ρ`
(amplitude `x^β/|ρ|`, fréquence `γ`, phase `γ log x`) sans qu'aucun ne soit isolé ; la contradiction est localisée au
point de rencontre et nulle part ailleurs ; l'infini est garanti par la répétition des rencontres (Bertrand compilé).

### 19.35.3 Le manque unique, tranché par le compilateur (consigné après compilation)
Module compilé (`lake build`, 22 déclarations, axiomes standard, aucun `sorry` ; trois passages journalisés dans
`experiments/E405_RawMeetingRemainder/COMPILE_JOURNAL.md`). L'objet s'appelle `psiRemainder` (le nom `rawRemainder`
existait déjà dans le corpus pour l'objet réel avec fond, non touché). La tentative 3, ajoutée puis retirée :
```lean
theorem riemannHypothesis_from_raw_meetings : RiemannHypothesis := by
  refine riemannHypothesis_of_psiRemainder_at_events ?_
```
laisse exactement UN but, copié tel quel :
```
⊢ ∀ (ε : ℝ), 0 < ε → ∃ C, 0 ≤ C ∧ ∀ (E : ℕ), IsRawEvent E →
    |psiRemainder E| ≤ C * ↑E ^ (1 / 2 + ε) ∧ |psiRemainder (E - 1)| ≤ C * ↑E ^ (1 / 2 + ε)
```
En mots : aux deux côtés de chaque rencontre brute (premier ou puissance de premier), le reste brut `ψ(E) − E` est
borné par une constante fois `E` à la puissance un demi plus epsilon. C'est le manque, très limité et isolé : une
inégalité sur les seuls premiers, aux seuls points de rencontre, infiniment répétée. Tout le reste (rencontres →
entiers → reste lissé → position radiale → RH) est compilé. Aucune hypothèse nommée n'a été posée.
R12 : ce manque est axe réel (vraies rencontres, vraie fonction de Tchebychev) ; aucune projection n'y entre et
aucune ne peut le remplir (le terme d'erreur du théorème des nombres premiers donne un exposant un, pas un demi).
Ce que le corpus prouve en sens inverse (`off_member_forces_raw_excess_at_event`) : un membre OFF à `β` force, pour
tout exposant au-dessous de `β` et toute constante, une rencontre où le reste brut dépasse la borne d'un côté ou de
l'autre. La contradiction finale est donc localisée aux rencontres, et nulle part ailleurs, dans les deux sens.

### 19.35.5 Résultats des jumeaux et verdicts (E405 exécutée, 4,2 s)
- Volet 1 : identités compilées vérifiées exactement sur crible jusqu'à deux millions (descente d'une unité entre
  rencontres, pont brut → lissé, inégalité rencontres → tout entier). Aucune lecture de θ : le quotient
  |ψ(E) − E|/√E aux rencontres oscille entre 0,19 et 0,71 par tranche dyadique sans tendance lisible.
- Tentative A : morte par son critère ; la somme des demandes aux rencontres EST le reste lissé (identité
  télescopique), aucune loi d'annulation sur les seuls premiers n'apparaît.
- Tentative B : morte par son critère ; à l'échelle de deux rencontres consécutives le facteur radial de la paire
  vaut 1,0003 à 1,0021 alors que son pas est dominé par la phase ; aucun paramètre seul ne lit β, et l'absorption par
  la tête n'est contrainte que par la constance par membre (⟺ RH).
- Verrou V : déjà compilé dans le canal lissé (`MeetingExactness.lean`) ; sa version brute est maintenant compilée
  (descente d'une unité entre rencontres, saut du poids à la rencontre : `psiRemainder_succ`,
  `psiRemainder_of_noEvent`).

### 19.35.6 Règle d'arrêt appliquée
Le plan §19.34 a été exécuté : V compilé (lissé déjà, brut nouveau), A et B mortes par leurs critères déclarés.
La contradiction finale a une seule forme dans la source compilée, et elle est maintenant localisée aux rencontres
brutes : le but exact de 19.35.3. L'exécutant ne pose aucun théorème supplémentaire : il demande à l'auteur une
SOURCE pour ce but unique (une lecture des premiers, aux rencontres, qui donne un demi plus epsilon), et non un
nouveau constat. Toute tentative future doit viser ce but tel qu'affiché, ou le réduire à un but plus petit compilé.

### 19.35.4 Jumeaux (E405, pré-enregistrés dans `experiments/E405_RawMeetingRemainder/README.md`)
Volet 1 : identités compilées vérifiées sur crible jusqu'à deux millions, maxima de `|r|/N^θ` aux rencontres contre tout
entier, tranches dyadiques. Volet 2 : tentative A (§19.34.5). Volet 3 : tentative B minimale (§19.34.6). R12 : tout est
axe réel (crible, rencontres vraies) ; aucune projection.

## 19.36 Suite logique après E404, E405 et `RawMeetingRemainder.lean` : E406–E411 (2026-11-02) — pré-enregistré

### 19.36.1 Demande de l'auteur (reprise en mots)
Relier le mécanisme révélé par E404 (la cassure brute en un premier est construite par les hautes fréquences) à la condition
terminale d'E405 (borne du reste brut aux deux côtés de chaque rencontre, exposant un demi plus epsilon). Sens de
reconstruction conservé : axe réel → premiers → écarts → cassures → hautes fréquences → contacts et amplitudes → (β, T).
Six livrables : E406 canal brut côté zéros avec convergence explicite ; E407 décomposition par seuil fréquentiel ; E408
raccord cassure / fréquences ; E409 amplitudes et coordonnées ; E410 composition de toutes les rigidités ; E411 recherche
de la borne. Rien n'est supprimé ni transformé en hypothèse ; aucune fermeture déclarée sans la borne.

### 19.36.2 Rectification de §19.35.2 (audit du corpus avant écriture)
Le canal brut côté zéros EXISTAIT déjà compilé : `Terminal/InverseReading.lean` (`spectralRemainder N`, pas de cellule de
la primitive absolument convergente, `arithmetic_eq_spectral`). La convention de convergence demandée par E406 est donc
celle-là : intégrale sur la cellule unité, où l'escalier est constant ; aucune convention au point de saut n'est
nécessaire. Ce qui manquait : le lien borné avec `psiRemainder` (E405), l'instance par seuil de fréquence, et une borne de
ce que les basses fréquences peuvent réaliser à une cassure. Pré-enregistrement complet :
`experiments/E406_E411_RawSpectralChannel/README.md`. Module isolé annoncé : `Terminal/RawSpectralChannel.lean`.

### 19.36.3 Ce qui est compilé (module isolé `Terminal/RawSpectralChannel.lean`, 37 déclarations, aucun `sorry`)
- **E406** : `psiRemainder_eq_spectral_add_correction` : à tout entier `N ≥ 2`, `ψ(N) − N` est le canal de cellule des
  zéros (`spectralRemainder N`, `InverseReading`) plus une correction `c(N)` bornée par une constante explicite
  (`norm_cellCorrection_le`, `cellBackgroundConstant` = un demi + dérivée logarithmique en zéro + deux fois la queue
  triviale). Convention de convergence : le pas de cellule de la primitive absolument convergente ; aucune convergence
  ponctuelle de la série brute n'est posée. Le lien `massA = ψ` est compilé (`massA_eq_psi`).
- **E407** : `lowFrequencies H` (indices de hauteur absolue au plus `H`, deux branches), finitude par
  `explicitIndex_locallyFinite` ; instances du découpage compilé sur le reste et sur l'incrément
  (`exactRemainder_split_frequency`, `remainderIncrement_split_frequency`).
- **E408** : `norm_packetIncrement_finset_le` : la seconde différence de cellule d'une famille FINIE d'indices est bornée
  par la somme des multiplicités (deux inégalités des accroissements finis sur `x^ρ/ρ` puis `x^{ρ−1}`, avec
  `x^{β−1} ≤ 1` car `β ≤ 1`, `explicitIndex_re_le_one`). Conséquences : `break_realized_by_high_frequencies` (la part de
  la cassure `Λ(N+1)` qui dépasse `1 + 4τ + K(H)` est portée par le complément), `prime_break_above_threshold`
  (cassure `log p`), `frequency_floor_of_low_realization` (si les fréquences au plus `H` réalisent seules la cassure,
  `K(H) ≥ log p − 1 − 4τ`). Fond : `norm_backgroundBreak_sub_one_le` (seconde différence du fond = un à `4τ` près).
- **E409** : aucun théorème nouveau. Récupérable avec le compilé : par membre, `(β, T)` depuis SES contacts
  (`inversion_radial`, `radial_from_amplitude_step`, `two_contacts_height_quantized`) ; globalement, la fonction totale
  sur tout `x > 1` détermine chaque poids (`spectral_weights_unique`). NON compilé : la récupération des composantes à
  partir des seules valeurs aux rencontres (entiers). C'est le raccord ouvert de l'étape 5.
- **E410** : `off_member_forces_break_and_excess` : un membre à `β > θ` force (E405) une rencontre brute `E` avec
  dépassement du reste brut, ET à cette rencontre, pour tout seuil, la cassure est portée au-dessus du seuil à hauteur
  d'au moins `Λ(E) − 1 − 4τ − K(H)` (E408). Chaîne nommée : premiers → `psiRemainder_succ` (saut du poids) →
  `psiRemainder_eq_spectral_add_correction` (canal de cellule) → `exactRemainder_split_frequency` (seuil) →
  `norm_packetIncrement_finset_le` (le bas ne casse pas) → `break_realized_by_high_frequencies` (le haut casse) ;
  en sens inverse `off_member_forces_raw_excess_at_event` → `riemannHypothesis_of_psiRemainder_at_events`.
  Rigidités NON raccordées dans ce module : CAP (`upper_cap`, `lower_cap` : le lien `K(H)` ↔ Riemann–von Mangoldt
  est PROJECTION, R12, non compilé ici) ; contacts et inversions (par membre, pas sur la somme) ; miroir (OffCarrier) ;
  unicité de la constellation (sur tout `x > 1`, pas aux rencontres).
- **E411** : `abs_psiRemainder_le_of_packets` (réduction vraie : bornes des deux paquets ⟹ borne du reste brut).
  Tentative 1 compilée puis retirée ; but affiché par le compilateur (copié dans `COMPILE_JOURNAL.md`) :
  « il existe un seuil et deux constantes telles que, à tout entier, le paquet bas ET le complément soient bornés par
  la constante fois `N^{1/2+ε}` ». MORTE par le critère déclaré : le paquet bas exige `β ≤ 1/2 + ε` pour les zéros bas
  (circulaire), le complément est la borne de queue elle-même. Tentative 2 morte par inspection : E408 MINORE le
  complément, il ne majore pas son niveau. Aucune hypothèse nommée posée.

### 19.36.4 Jumeaux (E406–E411, 4,5 s, `experiments/E406_E411_RawSpectralChannel/e406_e411_results.txt`)
- E406 : identité de cellule tenue au résidu de troncature (2·10⁻² à 10⁴, 0,3 à 10⁵, 4 à 10⁶ où la liste ne résout plus
  la cellule) ; correction constante 1,338 sous la borne 5,628 ; seconde différence du fond = un à 10⁻¹¹.
- E407/E408 : l'incrément du paquet bas est sous `K(H)` de trois à six ordres de grandeur ; le plancher compilé est
  trivial (H ≥ 14 ou 21) contre π·p observé en E404 (10⁴ à 3·10⁵). Part de la cassure portée au-dessus de H : 100 %
  jusqu'au seuil de foule et au-delà, décroissant seulement vers π·p ; dépassements de 100 % à certains seuils.
- E411 : niveau du complément sur √p entre 2·10⁻⁴ et 8·10⁻² ; aucune lecture d'exposant.

### 19.36.5 Verdict et causalité (en mots)
Le théorème E408 est vrai et faible : il lit le NOMBRE des basses fréquences, pas l'organisation de leurs phases ; or
la cassure est réalisée par annulation de phase (les secondes différences des basses fréquences se compensent de
trois à six ordres de grandeur sous leur borne de comptage) et par l'élan des fréquences de l'ordre de π·p. Le raccord
terminal demandé par l'auteur (organisation des hautes fréquences ⟹ contrôle du reste aux rencontres) n'est donc pas
un raccord de comptage : tout théorème qui ne lit que le nombre de fréquences par fenêtre (CAP, `K(H)`) est aveugle à
ce mécanisme, exactement comme les caps de §19.15 étaient radialement aveugles. Ce qui est compilé localise où le
mécanisme doit agir (la seconde différence à la rencontre, portée par le complément) ; ce qui manque est une lecture
de l'organisation des phases à la rencontre qui majore le NIVEAU du complément, et non ses variations. Le but unique
d'E405 reste tel quel (§19.35.3). R12 : tout ce module est axe réel ; la seule projection nommée (K(H) ↔ RvM) n'y est
pas compilée.

### 19.36.6 Règle d'arrêt
Deux tentatives journalisées, mortes par leurs critères. Aucun théorème supplémentaire. Pas de fermeture déclarée.
Demande à l'auteur : une SOURCE pour la majoration du niveau du complément (ou du reste brut) aux rencontres qui lise
les phases et non le comptage ; le compilateur a affiché le but (journal E411-1) et la réduction qui l'attend
(`abs_psiRemainder_le_of_packets`).

## §19.37 — Mission « accumulation spectrale exacte des Tours » exécutée (2026-11-03)

**19.37.1 Demande.** Reconstruire les écarts premiers depuis les zéros par accumulation des VALEURS complexes des Tours sur
leurs intervalles de contacts successifs (pas de comptage, pas de longueurs), jusqu'à la somme collective ; auditer, formaliser,
compiler, exécuter E414–E419, tester un quartet OFF, dire si une rigidité nouvelle apparaît. Rapport :
`experiments/CONTACT_ACCUMULATION_MASTER_REPORT.md` ; audit : `experiments/CONTACT_ACCUMULATION_CIRCULARITY_AUDIT.md`.

**19.37.2 Compilé (six modules isolés, non ajoutés à `RHV6Fresh.lean`, 102 déclarations, aucun sorry).**
`ContactValueGeometry` (contact = passage sur l'axe, `contact_is_axis_passage` ; télescopage exact pour toute F ;
indépendance du découpage) ; `CollectiveContactAccumulation` (famille finie, conjugaison avec multiplicité, réalité) ;
`ContactSpectralLimit` (limite du canal intégré par hauteur ; prémisse brute isolée `RawExplicitFormulaAt`, conditionnels aux
demi-entiers ; `psi_half_difference`) ; `RawEventReconstruction` (`spectralPrimitive` côté spectral ; `reconstructedPsi_eq_psi`,
`reconstructedVonMangoldt_eq` ; opérateur `Λ(N) = log N ⟺ N premier`) ; `PrimeGapReconstruction`
(`reconstructedPrimeGap_eq_actualGap`, succession) ; `ContactAccumulationChain` (reste brut d'E405 = limite des accumulations
moins N ; `riemannHypothesis_of_contact_accumulation_bound`, prémisse ⟺ RH, jamais posée ; `off_member_forces_contact_excess`).

**19.37.3 Mesuré (2 001 052 zéros, jumeaux déterministes).** E414 : identité à l'arrondi (12/12, 32 M de contacts). E415 :
Λ̂ depuis les zéros, erreur rms 323/T_max (canal intégré), 2,9e−4 sur [3, 300]. E416 : **écarts premiers reconstruits sans le
premier suivant, 60/60 exacts dès 1 000 zéros sur [3, 300]**, 3/3 à 10⁴ dès 10⁵ zéros, 1/1 à 10⁵ dès 10⁶ ; règle sans seuil ;
dépend de la troncature (T_max ≳ πx). E417 : largeur πx/T_max vérifiée, Gibbs 9 % constant. E418 : quartet OFF synthétique :
défaut ≤ borne démontrée, aucune erreur de lecture, compensable par amplitudes réelles. E419 : découpage indifférent (4e−16) ;
aucune contrainte nouvelle au raccord.

**19.37.4 Verdict.** Niveaux 1–5 de la mission atteints (5 à troncature finie sur les fenêtres testées, et en limite par
théorème). **Niveaux 6 et 7 non atteints** : l'accumulation par contacts est un télescopage ; elle reproduit la formule
explicite et ne lit pas la position radiale (contacts déplacés de (½−β)/T², amplitude seule sensible, compensable). Le manque
unique est inchangé depuis §19.35.3 : la majoration du niveau du reste brut aux rencontres (exposant ½+ε), lue par les phases.
Aucune hypothèse nouvelle posée ; RH non démontrée.

**19.37.5 Cible par défaut rétablie (2026-11-03, ordre de l'auteur).** `lake build RHV6Fresh` échouait depuis le commit
c9eea2e5 du 2026-10-20 (§19.23.3, §19.31.6) : `windowProjection` déclaré à la fois dans `GapTranslationInvariance` (2026-10-19,
importé par `DemonstrationChain`) et dans `SpectralWindowProjection` (E350). Correction minimale : renommage
`windowProjection → logWindowProjection` (et ses théorèmes `logWindowProjection_*`) dans `SpectralWindowProjection.lean` et
son seul dépendant `GapDemandStability.lean` ; aucun énoncé, aucune preuve, aucun import modifié ; `DemonstrationChain` et ses
imports intacts. Résultat : `lake build RHV6Fresh` réussit (9 064 tâches, aucune erreur) ; les six modules de §19.37 restent
verts (9 045 tâches). Règle consignée : la cible par défaut doit rester verte après chaque tentative ; aucun doublon de nom
n'est admis, le balayage `grep` des identifiants précède tout nouveau module.

## §19.38 — Géométrie des contacts sur l'axe réel : valeurs réelles, inversion tangentielle, entrelacement (2026-11-03)

**19.38.1 Demande (auteur).** Exploiter ce que le télescopage de §19.37 ne mesurait pas : la valeur réelle à chaque contact
(signe, amplitude), l'alternance, la récupération de T et β par inversion tangentielle, l'évolution des amplitudes à
l'enroulement, l'entrelacement des contacts de Tours différentes, la somme collective des valeurs réelles aux contacts (les
autres Tours évaluées aux mêmes positions), la comparaison ON/OFF aux contacts déplacés. Objectif Lean : identités exactes,
inversion, contraintes éventuelles de l'entrelacement. Objectif expérimental : sans premiers, écarts, cellules ni li. Sans
présumer que cette géométrie exclut les zéros OFF. Rapport : `experiments/CONTACT_REAL_VALUE_REPORT.md`.

**19.38.2 Compilé (`Terminal/ContactRealValue.lean`, isolé, 32 déclarations, aucun sorry, axiomes standards ; cible par
défaut verte, 9 064 tâches).** `towerValue_at_contact` : au contact k, la Tour vaut (−1)^k C_k^β/‖ρ‖ (réelle) ;
`contactRealValue_succ` / `_alternates` : v_{k+1} = −e^{βπ/T} v_k ; `contactRealValue_mul_pos` : même signe à même indice pour
toutes les Tours ; `height_of_contact_log_step`, `radial_of_contact_tangent` (β = T/tan(T log C_k − kπ)),
`radial_of_contact_value_ratio` ; `log_abs_contactRealValue` (affine en k, pente βπ/T) ; `interleaving_offset`, `cycleIndex`,
`interleavingCount_bounds` (⌊T₂/T₁⌋ ou ⌈T₂/T₁⌉ entre deux contacts consécutifs, quel que soit β) ;
`contact_displacement_lt_half_step` ; `mirror_contacts_coincide_iff` (coïncidence des contacts d'une paire miroir ⟺ β = ½) ;
`collectiveAxisSum_at_contact` (valeur propre réelle + autres Tours à la même position).

**19.38.3 Mesuré (E420–E423, pré-enregistrées b89b57b5).** E420 : identités à l'arrondi sur 5,2 M de contacts ; T et β
récupérés à 7e−10 et 3e−10 par les amplitudes ; la tangente se dégrade en T²·ε (critère pré-enregistré non tenu au-delà du
rang 10⁴, limite numérique). E421 : bornes d'entrelacement tenues sur dix paires jusqu'à 2 001 052 ; phases équiréparties ;
prédiction « au plus un cran » RÉFUTÉE (jusqu'à 72 crans pour β = 0,3) ; miroir : écart minimal exact (1−2β)/(πT) pas.
E422 : part propre de la somme collective de 0,8 (Tour 1) à 0,01 (rang 1 000) ; reste de phases plates, rms 3–4, stabilisé à
2 001 052 ; les contacts ne sont pas des points remarquables de la somme. E423 : ON/OFF à même hauteur : déplacement
(½−β)/T² constant en k et inférieur au demi-pas, même signe, rapport des modules x^{β−½}|ρ_½|/|ρ_β| exact ; paire miroir :
passages distincts, membre 1−β dominant ; invisible dans la somme collective (≤ 7,5e−4).

**19.38.4 Verdict.** Les sept points ont une réponse compilée et mesurée. **Aucune contrainte nouvelle** : l'entrelacement est
aveugle au radial à l'échelle du comptage, la somme collective aux contacts n'est pas gouvernée par l'hôte, et ON/OFF ne
diffèrent que par l'amplitude et un décalage de phase sous le demi-pas. Rien n'oblige β = ½ ; aucune hypothèse posée ; RH non
démontrée. Règle pour la suite : lire β par les amplitudes ou par des phases relatives entre Tours, jamais par la phase
absolue à grande hauteur (conditionnement T²·ε).

## §19.39 — Directive « stratégie des contacts réels » : contraintes entre Tours successives lues aux contacts (2026-11-03)

**19.39.1 Directive (auteur, reprise en mots).** Abandon confirmé comme stratégie active : projection spectrale sur les
entiers, reconstruction des poids arithmétiques par approximation, détection des événements premiers par seuils,
primitives intégrées comme substituts aux Tours, cellules unitaires comme support de reconstruction, intégrale
logarithmique, fermeture par les restes de troncature ; les théorèmes, données et expériences antérieurs sont conservés et
les dépendances de compilation ne sont pas détruites. Base formelle de référence : `TowerWinding`, `ContactValueGeometry`,
`ContactRealValue`, E420–E423, `CONTACT_REAL_VALUE_REPORT.md`, §19.38. Priorité absolue : l'inversion tangentielle
(hauteur, partie réelle, rapports d'amplitudes, phases relatives, contacts miroirs, contraintes entre Tours successives,
raccordement aux écarts premiers), sans remplacer les valeurs réelles par un comptage. Corrections issues de E420–E423 :
plus de domination de l'hôte supposée dans la somme collective ; plus de phase absolue à grande hauteur comme méthode ;
rapports d'amplitudes et phases relatives privilégiés. Objectif de recherche : les contraintes qu'imposent simultanément
positions de contact, valeurs signées, amplitudes, hauteurs, positions radiales, entrelacement, succession et raccordement
aux premiers, spécifiquement pour une première arrivée OFF après une Tour ON, avec les théorèmes de lecture de la fréquence
précédente et de raccordement. Objectif terminal : une incompatibilité démontrée entre première arrivée OFF et contraintes
exactes de raccordement, sans prémisse équivalente à RH, sans annoncer de contradiction avant sa démonstration. Stratégie
active unique : Tours → contacts sur l'axe réel → valeurs réelles → inversion tangentielle → contraintes entre Tours →
raccordement aux écarts premiers → exclusion OFF. Motif donné par l'auteur : la méthode spectrale reconstruisait un résultat
connu sans contrainte sur la position radiale de chaque zéro ; les contacts rendent hauteur et position radiale lisibles
individuellement, et la question devient la liberté du successeur de changer de position radiale sous les contraintes
établies avec son prédécesseur.

**19.39.2 Compilé (`Terminal/SuccessiveContactConstraints.lean`, isolé, 24 déclarations, aucun sorry, axiomes standards ;
cible par défaut verte, 9 064 tâches ; cinq passes de compilation journalisées, règle des deux tentatives non tenue sur ce
module, consigné).** `towerValue_step_at_contacts` : entre deux contacts consécutifs de la grille (β, T), toute Tour ρ est
multipliée par exp(ρ·π/T). `crossAmplitudeRatio_eq` : rapport croisé = exp(Re ρ·π/T). `radial_of_crossAmplitudeRatio`,
`radial_difference_of_crossRatios`, `crossRatios_eq_iff_same_radial`, `crossRatio_onLine_iff` : la position radiale de toute
Tour, et la différence des positions radiales de deux Tours, sont lues aux contacts d'une seule grille ; rapports égaux ⟺
même position radiale. `mirrorRelativePhase` (nulle ⟺ β = ½, positive ⟺ β < ½, de module < π/2), `towerValue_polar`,
`mirror_at_contact`, `mirror_im_at_contact`, `pair_axis_at_contact_iff` : la somme de la paire miroir est réelle au contact
d'un membre si et seulement si ce membre est sur la ligne. Porteur OFF : `arrival_crossRatio_ne` (aux contacts du zéro
OFF, le rapport croisé du dernier membre ON diffère de celui du zéro OFF), `radialShift_read_at_contacts` (le décalage
radial est lu exactement dans le quotient de ces rapports), `pair_not_on_axis_at_zero_contact`.

**19.39.3 Mesuré (E424–E425, pré-enregistrées 501ce5d4, 2 001 052 zéros, jumeaux mpmath, synthétique aux hauteurs milieu).**
E424 : sur 2 001 051 paires consécutives, différence radiale lue ≤ 3,4·10⁻¹⁰, position du prédécesseur ≤ 2,7·10⁻¹⁰ de ½,
hauteur du prédécesseur lue dans le pas de phase relative à 3,7·10⁻¹¹ de T_l (croissance T·ε par décade, critères tenus) ;
synthétique : ½ − β_l et 1 − 2β_l retrouvés à 10⁻¹¹. E425(a) : aux contacts d'un membre OFF, la somme de la paire n'est
jamais réelle ; écart à (−1)^k·sin(phase relative) ≤ 3,4·10⁻¹⁰, critère 10⁻¹⁰ non tenu à la hauteur 75 000 (bruit T·ε,
jumeau 10⁻²⁶) ; contrôle ON nul à l'arrondi. E425(b) : le premier de même rang tombe dans la cellule de contact de son zéro à
une fraction indiscernable de l'uniforme au pour-cent près (2 M), sans préférence de signe ni de phase ; cran OFF/ON nul sur
tous les zéros (prédiction compilée {−1, 0} tenue).

**19.39.4 Verdict.** La position radiale d'un zéro et celle de son prédécesseur sont lisibles aux seuls contacts du zéro ; un
zéro OFF est visible à ses propres contacts (amplitudes croisées, paire non réelle). Aucune de ces lectures n'est une
interdiction : la seule proposition qui transformerait la visibilité en contrainte équivaut à la position sur la ligne par
construction. **Aucune contrainte nouvelle n'oblige β = ½ ; RH n'est pas démontrée ; rien ici n'est lu comme excluant les
zéros OFF.** Le raccordement brut au premier de même rang est écarté par la mesure. Candidats non présumés pour la suite :
premiers suivants relativement aux contacts du zéro ; coïncidences exactes de contacts entre prédécesseur et successeur.
Rapport : `experiments/SUCCESSIVE_CONTACT_REPORT.md` ; résultats : `experiments/E424_E425_SuccessiveContacts/RESULTS.md`.

## §19.40 — Correction de démarche : les rencontres entre Tours avant toute contrainte (2026-11-03)

**19.40.1 Correction (auteur).** E420–E425 ont étudié les Tours séparément puis leurs valeurs croisées, jamais les
rencontres entre leurs trajectoires sur l'axe réel. E425(b) (premier de même rang contre contacts) et les instanciations
sur le porteur OFF de §19.39 sont déclarées **hors route** : elles sautent les étapes « points de rencontre » et
« succession des rencontres ». Trois objets à distinguer : (A) coïncidence de contacts, (B) rencontre de valeurs (mêmes
parties réelles à la même abscisse), (C) rencontre collective. Chaîne corrigée : Tours → contacts réels → valeurs réelles →
points de rencontre → succession des rencontres (cassures : fin d'un écart, début d'un autre) → raccordement aux premiers et
aux écarts. L'inversion tangentielle reste un outil, plus l'objectif immédiat. Aucune projection spectrale, aucune
hypothèse OFF, aucune recherche prématurée de contradiction. Lexique : « point de rencontre » (`meetingPoint`) reste la fin
d'un écart premier ; les objets ci-dessous sont des « rencontres entre Tours ».

**19.40.2 Compilé (`Terminal/TowerMeetings.lean`, isolé, 27 déclarations, aucun sorry, axiomes standards, deux tentatives
journalisées ; cible par défaut verte, 9 064 tâches).** `towerRe`, `towerRe_eq_re`, `towerRe_at_contact` (trajectoire
réelle, valeur signée aux contacts) ; `contactsCoincide_iff`, `contactsCoincide_not_meeting` (une coïncidence de contacts
n'est jamais une rencontre de valeurs) ; `unit_difference`, `unitMeeting_iff` (rencontres unitaires = réseau lent de pas
2π/(T₁−T₂) ∪ réseau rapide de pas 2π/(T₁+T₂)) ; `gap_of_slowMeetings` (**l'écart des hauteurs est relu exactement dans deux
rencontres lentes consécutives**), `sum_of_fastMeetings` ; `slowMeetingLog_zero_pos/_lt` (indice 0 collé à l'abscisse 1) ;
`towerMeeting_iff_same_radial`, `towerMeeting_of_unitMeeting_iff` (rencontre brute déplacée du réseau unitaire sauf aux
passages par zéro) ; `slowMeetings_coincide_iff` (cassure : coïncidence des rencontres lentes de paires voisines ⟺ relation
exacte entre écarts consécutifs et phases) ; `gap_of_slowMeetings_at_primeGap` (conditionnel : rencontres lentes aux bouts
d'un écart premier ⟹ écart des zéros = 2π sur la longueur logarithmique de l'écart premier ; hypothèse explicite).

**19.40.3 Mesuré (E426, pré-enregistrée a2420c40, 2 001 051 paires + 300 paires en racines exactes, jumeaux mpmath et
pseudo-premiers de densité).** Identités à l'arrondi (10⁻¹⁶). Première rencontre lente à x₁ ≈ T/2π en médiane (rapport
1,03–1,04, stable en hauteur), position dans la grille de contacts équirépartie. Rencontres brutes : loin des rencontres
lentes, collées au réseau rapide à grande hauteur (rms 0,025 → 1,4·10⁻⁴ pas rapides) ; près de chaque rencontre lente,
géométrie invariante en hauteur (deux racines disparaissent, racine voisine déplacée d'environ 0,6 pas rapide, valeur non
nulle) : **la rencontre lente, où l'écart est lu, n'est jamais une rencontre brute.** Cassure : la rencontre lente suivante
se place sur le réseau précédent selon le rapport des écarts consécutifs, 0 coïncidence exacte. Raccordement : position de
x₁ dans son écart premier équirépartie, produit écart × longueur logarithmique indiscernable du jumeau de densité.
Corrections de lecture consignées : g·log x₁ = 2π + Δφ est une identité (retirée des mesures) ; égalité des fractions de
cellule à la rencontre lente est une identité.

**19.40.4 Verdict.** Géométrie des rencontres entre Tours consécutives entièrement décrite et compilée ; raccordement aux
écarts premiers **négatif** (densité seule) ; aucune contrainte radiale lue ni cherchée ; RH non démontrée ; rien n'exclut
un zéro OFF. Rapport : `experiments/TOWER_MEETINGS_REPORT.md` (avec l'index de toutes les analyses par contacts) ;
résultats : `experiments/E426_TowerMeetings/RESULTS.md`.

### 19.41 Directive E427 : la grammaire des écarts premiers reconstruite depuis les Tours, puis ce que son équilibre transporte aux contacts (2026-11-04)

**19.41.1 Directive consignée (deux messages de l'auteur).** Premier message : chercher le transport de l'équilibre exact de
la grammaire modulo 6 (transitions orientées, bilan borné, retour après croisements inverses) vers la géométrie des
contacts ; interdictions (projection spectrale posée, comptage approché, modèles statistiques, familles artificielles,
rencontres par cosinus normalisés, indices indépendants des Tours, stabilité posée, prémisse ⟺ RH, relation posée contact
⟷ événement). Second message, **priorité absolue corrigée** : reconstruire d'abord la grammaire **depuis les Tours des zéros
authentiques** (états, transitions, ordre, alternance, bilan borné, retour), les premiers ne servant qu'à valider ; ensuite
seulement la conservation géométrique ; enfin seulement les contraintes sur les Tours. Trois niveaux de verdict exigés.

**19.41.2 Compilé (`Terminal/GrammarContactStability.lean`, isolé, 64 déclarations, aucun sorry, axiomes standards ;
trois tentatives journalisées, la troisième corrigeant un seul `congr 1` manquant ; cible par défaut verte).**
Orientation signée des transitions (`orientation_eq_ind` : différence d'indicatrices) ; bilan orienté d'un mot valide :
télescopage exact, confinement dans [−1, 1], retour exact après deux croisements inverses quel que soit le nombre de
séjours, neutralité des maintiens, et `confinement_not_dwell_equality` (le confinement ne dit rien des nombres de séjours) ;
`validWordEquivPath` et `card_validWords_twelve` (8 192 mots valides de douze transitions, aucune autre propriété) ;
grammaire des événements premiers (`eventOrientation_of_gap` : orientation ⟺ écart ≡ 4, 2, 0 mod 6). **Niveau 1** : états,
transitions et bilan **définis sur la suite reconstruite** (prédicat spectral `ReconstructedPrimeAbove`, aucun premier
injecté) ; deux états dès le rang 1, classe = écart reconstruit mod 6, raccord, télescopage, confinement, retour ;
validation `reconstructedTransition_eq_actual`. **Niveau 2** : borne d'Abel du bilan pondéré par les valeurs réelles aux
contacts, pour tout (β, T) (`contact_weighted_balance_abs_le`) ; la transition ne détermine ni le rapport des premiers ni
celui des amplitudes (`29 → 31` et `113 → 127`, même `t51`) ; sur un segment de bilan nul, dérive d'amplitude relative
neutre ⟺ β = ½ (`return_drift_eq_one_iff`, caractérisation, jamais posée).

**19.41.3 Mesuré (E427, pré-enregistrée d2e86049 (6331004d avant rebasage sur deux suppressions distantes sans rapport)).** (a) Grammaire exacte sur 5 761 453 premiers ≤ 10⁸ : 0 violation
(conformité, télescopage, alternance, retour), 8 192 mots valides tous réalisés, N11 − N55 jusqu'à −1 019 (mesure, aucune
loi), jumeau en entiers purs exact. (b) **Niveau 1 réussi** : depuis les 2 001 052 zéros, canaux brut et intégré, les
premiers reconstruits de W1 = [3, 300], W2, W3 (61 + 4 + 2) portent états, transitions et bilans **sans aucun désaccord**
avec la grammaire des vrais premiers (dès 1 000 zéros sur W1, 10⁵ sur W2, 10⁶ sur W3) ; route par contacts authentiques
(1,2 million de contacts, accumulation de chaque Tour sur ses propres contacts) identique aux bords à 5,6·10⁻¹⁴ ; contrôles
de séparation en échec (mêmes hauteurs à β = 0,3 : 32 premiers sur 61 ; hauteurs pseudo-aléatoires de même densité, jamais
aux hauteurs réelles : états faux dès 4, 6, 10, …) ; jumeau mpmath 2,3·10⁻¹³. (c) **Niveau 2 négatif** : borne d'Abel
jamais violée (identité) ; aucun candidat géométrique (décalage d'indice de contact, log-amplitude, valeur au contact de
rencontre) n'est une fonction de l'orientation ; l'information mutuelle orientation ⟷ décalage de contact croît avec la
hauteur parce que la fréquence résout l'écart (identique à β = 0,3 ; 0,5 ; 0,7) ; dérive d'amplitude neutre sur 100 % des
segments à β = ½ et 0 % à β ≠ ½, que le bilan soit revenu ou non.

**19.41.4 Verdict.** Niveau 1 (reproduction) : **oui** — les Tours des zéros authentiques reproduisent la grammaire des
écarts premiers, compilé en limite et mesuré sans désaccord ; les familles synthétiques ne la reproduisent pas.
Honnêtement : c'est la formule explicite lissée compilée relue en grammaire ; les contacts sont le découpage de
l'accumulation (identité), pas une information supplémentaire ; raccord, alternance, confinement et retour sont des
identités sur toute suite d'entiers, seule la position des premiers est de l'information, et elle vient des hauteurs
authentiques. Niveau 2 (conservation) : **non** — rien ne se transporte aux contacts hors une somme d'Abel valable pour
tout (β, T) ; la seule conservation exacte (dérive neutre) caractérise la ligne et ignore la grammaire. Niveau 3 :
**aucune** contrainte, aucune cherchée. Information arithmétique manquante, nommée : une grandeur des contacts d'une Tour
dont la variation à travers un écart lise le résidu de l'écart modulo 6 et non sa seule longueur logarithmique (les
contacts ne dépendent que de (β, T) ; l'écart n'y entre que par T·log(p'/p) et β·log(p'/p)). Rapport :
`experiments/GRAMMAR_CONTACT_STABILITY_REPORT.md` ; résultats : `experiments/E427_GrammarContactStability/RESULTS.md`.
RH non démontrée ; rien n'exclut un zéro OFF.

### 19.42 Plan proposé (non exécuté) : exploiter la rigidité prouvée contre la dérive OFF, et E428 — lecture des transitions par la progression complète des contacts sur une série d'écarts (2026-11-04)

Statut : **plan soumis à l'auteur, en attente du feu vert ; rien n'est compilé ni mesuré pour §19.42.** Textes de l'auteur du
2026-11-04 (après §19.41) : (i) « la question n'est pas la reproduction de la grammaire mais les contraintes géométriques
obligatoires que sa stabilité impose aux contacts, fréquences et succession des Tours » ; cible « équilibre grammatical
exact ⟹ loi de conservation géométrique aux contacts ⟹ contraintes sur la succession des Tours » ; (ii) « exploiter la
rigidité et la stabilité prouvées ; les OFF créent des dérives, c'est diamétralement opposé » ; (iii) E428 : « examiner si la
progression complète des contacts, avec la localisation arithmétique déjà démontrée, détermine exactement la transition ;
la progression renseigne un rapport, la transition dépend d'une différence entière ; démontrer la conversion sans
réinjecter la réponse ; test décisif : information issue des Tours, ou simple recalcul depuis deux premiers connus » ;
(iv) « ne pas travailler sur un seul écart mais sur une série d'écarts ».

#### 19.42.1 Inventaire : l'opposition rigidité / dérive est déjà compilée (rien à redémontrer)

| Côté | Énoncé compilé | Fichier |
|---|---|---|
| rigidité (grammaire) | bilan orienté confiné, retour exact indépendant des séjours, raccord ; 8 192 mots | `GrammarContactStability`, `TransitionRigidity` |
| rigidité (ligne) | dérive d'amplitude aux rencontres neutre ⟺ β = ½ (`meeting_drift_eq_one_iff`) ; sur un segment de bilan nul idem (`return_drift_eq_one_iff`) ; invariance par translation d'un écart ⟺ ligne (`zeroMode_translation_invariant_iff`) ; **symbole de l'opérateur grammatical nul en ligne sur toute série de m écarts** (`classWeightedCurvature_onLine`) | `GrammarDrift`, `GapTranslationInvariance`, `GrammarOperator` |
| dérive (OFF) | paire miroir = enveloppe 2cosh (`pairMode_eq_cosh`) ; dérives opposées de produit 1 (`mirror_pair_gap_ratios_product`) ; courbure de paire > 0 hors ligne, **minorée par le plancher grammatical de la classe** (`zero_pair_curvature_gap_floor`, `curvatureSymbol_ge_classFloor`) ; **non bornée le long des translations sur une série de m écarts** (`off_classWeightedCurvature_unbounded`) | `CollectiveCurvature`, `GrammarOperator` |
| réduction | `grammar_operator_two_lemma_closes` : [observable grammaticale du collectif bornée sur la série] ∧ [complément borné] ⟹ ⊥ pour tout zéro bas | `GrammarOperator` (chaîne VII quater) |

Lecture : le « diamétralement opposé » est un théorème : sur une série de m écarts pondérée par les classes, l'opérateur
grammatical annule exactement tout mode en ligne et fait exploser toute paire OFF, avec un plancher qui lit le résidu de
chaque écart (classe 0/4/2 ⟹ longueur minimale 6/4/2). La contradiction est **réduite à deux lemmes arithmétiques** non
démontrés : (L1) la borne, depuis les premiers seuls, de l'observable grammaticale du collectif ; (L2) la borne du
complément infini. §19.19 (aucune conservation dans le corpus), E427 (aucun transport aux contacts d'un écart isolé) et
§19.41 n'ont fourni ni L1 ni L2. Aucune des deux ne sera posée.

#### 19.42.2 Pourquoi E427 ne pouvait rien lire sur un écart, et ce que la série change

Sur un écart isolé, la Tour ne fournit que T·log(p'/p) (phase) et β·log(p'/p) (amplitude), aveugles au résidu
(`logRatio_not_determined_by_transition`). Sur une **série** d'écarts depuis un rang d'ancrage r, l'indice de cellule des
contacts (`cellIndexAt β T q = ⌈(T log q − arctan(T/β))/π⌉ − 1`) télescope : la progression complète des indices aux points
de rencontre k_{r+j} − k_r encadre T·log(p_{r+j}/p_r)/π à moins d'une unité près, la phase arctan(T/β) étant **commune et
éliminée par la différence**. Connaissant un seul premier d'ancrage p_r (localisation déjà démontrée, niveau 1), la
conversion rapport → différence entière est exacte dès que la résolution de la Tour suffit : p_{r+j}·(e^{π/T} − 1) < ½.
C'est la conversion demandée par l'auteur ; elle ne réinjecte pas p_{r+j} ; elle n'utilise de la Tour que sa **fréquence**
(« fréquence avant hauteur », §19.15 : la fréquence est plafonnée par le rang, donc le rang fixe jusqu'où une Tour lit).

#### 19.42.3 E428 — protocole proposé (à pré-enregistrer avant exécution)

**Étape A — module isolé `ContactSeriesReading.lean`** (grep préalable, non ajouté à `RHV6Fresh.lean`, deux tentatives
journalisées) :
* A1 `cellIndex_series_telescopes` : l'indice cumulé sur la série est la somme des décalages par écart (identité) ;
* A2 `cellIndex_difference_bounds` : pour tout (β, T) et tous q < q', |(k(q') − k(q)) − T·log(q'/q)/π| < 1 ;
* A3 `gap_series_determined` : sous l'hypothèse de résolution p_{r+m}·(e^{π/T} − 1) < ½, chaque p_{r+j} (j ≤ m) est
  l'arrondi de p_r·exp(π(k_{r+j} − k_r)/T) ; donc la **loi de lecture** : le mot des m transitions (classes, orientations,
  bilan) est une fonction de (p_r, T, indices cumulés) — composition avec `transitionOf_cls` et `eventOrientation_of_gap` ;
* A4 `reading_law_radially_blind` : pour β, β' > 0 et même T, sous la même hypothèse, la loi lit le même mot (la phase
  s'élimine dans les différences ; A2 vaut pour tout β) — **prédiction compilée avant mesure** ;
* A5 `reading_law_fails_below_resolution` (séparation) : deux transitions de classes distinctes et mêmes décalages
  d'indices pour une fréquence sous le seuil (candidat : 101 → 103 et 103 → 107 à la fréquence du premier zéro) ; si le calcul
  numérique de logarithmes résiste à Lean en deux tentatives, l'énoncé est remplacé par sa version mesurée et consigné.

**Étape B — mesure** (réutilise `e427c` ; Tours authentiques des rangs 1, 10, 100, 1 000, 10 000, 100 000, 10⁶, 2 001 052 ;
Tours de séparation β ∈ {0,3 ; 0,7} aux mêmes hauteurs) : ancrages r ∈ {2, 100, 1 000}, séries de m ∈ {12, 120, 1 200}
écarts ; pour chaque Tour, indices cumulés aux points de rencontre, loi de lecture appliquée avec **le seul ancrage p_r**,
comparaison aux vraies transitions **après** ; taux d'exactitude par Tour et par série contre le seuil de résolution
compilé ; lectures identiques à β = 0,3 / 0,5 / 0,7 (A4) ; jumeau mpmath 30 chiffres sur une série.

**Test décisif (celui de l'auteur), réponse attendue consignée avant exécution** : la loi existe et est exacte au-dessus du
seuil ; l'information issue de la Tour est sa fréquence et rien d'autre ; au-dessous du seuil aucune lecture ; la position
radiale n'entre pas (A4). Critère de réfutation : une lecture exacte sous le seuil, ou une lecture différente entre β = ½
et β ≠ ½ à même T, contredirait un énoncé compilé et serait traitée comme une erreur à localiser, jamais comme un
résultat.

**Étape C — conséquence pour le plan de contradiction (19.42.1)** : si A4 tient (attendu), la lecture par série ne fournit
pas L1 ; la réduction `grammar_operator_two_lemma_closes` reste la frontière, inchangée. Ce que E428 établira de positif :
toute Tour au-dessus du seuil porte, dans la progression complète de ses contacts, le mot grammatical exact de la série
(niveau 2 au sens « nécessité » de l'auteur : la succession des contacts d'une Tour est obligée d'être compatible avec le
mot, pour toute fréquence résolvante) — contrainte sur T, satisfaite par toute Tour, sans contenu radial. Niveau 3 : rien.

#### 19.42.4 Ce qui n'est pas dans ce plan

Aucune hypothèse OFF ; aucune contradiction anticipée ; aucune borne posée sur l'observable grammaticale ; aucune famille
de Tours artificielle hors les deux contrôles de séparation ; aucune lecture de β. La question ouverte, à ne pas poser :
une grandeur des contacts, **sur une série**, dont la variation lise le résidu et non la longueur — le plancher grammatical
(`curvatureSymbol_ge_classFloor`) est pour l'instant la seule liaison résidu → longueur compilée, et elle va dans le sens
inverse de la lecture.

#### 19.42.5 Mise en correspondance avec les quatre obligations A–D de l'auteur (2026-11-04, amendement du plan, non exécuté)

Chaîne de l'auteur : zéros authentiques → Tours et contacts réels → lecture exacte de T, β, phases, amplitudes ;
**lecture individuelle** (contacts → identité complète de chaque zéro) et **lecture collective** (tous les zéros → écarts
premiers → grammaire) ; **obligation de compatibilité au point de rencontre** : quelle relation exacte la grammaire
impose-t-elle aux contacts et aux paramètres des Tours ? → contrainte sur β et sur la succession des zéros.

Audit honnête du plan 19.42.1–19.42.4 contre les quatre obligations :

| Obligation | État dans le plan 19.42 | Correction apportée ici |
|---|---|---|
| **A. Raccord individuel–collectif** | à moitié : la lecture par série utilise une Tour isolée (fréquence + ancrage) sans dire comment sa contribution entre dans la réalisation collective de l'écart | ajout de l'étape A0 ci-dessous |
| **B. Conservation grammaticale aux rencontres** | intégrée (loi de lecture des transitions par la progression complète des contacts ; recherche d'une égalité/inégalité sur une série) | inchangée, reformulée comme égalité/inégalité sur contacts, valeurs **et** amplitudes |
| **C. Sensibilité radiale** | **non intégrée, et contredite** : l'énoncé A4 « cécité radiale » et l'exclusion « aucune lecture de β » (19.42.4) réduisaient l'étude à la seule fréquence, ce que l'auteur interdit | A4 retiré comme conclusion ; remplacé par l'étape C ci-dessous, qui lit β par l'inversion compilée et teste la Tour hors ligne avec son miroir |
| **D. Fermeture terminale** | intégrée (réduction compilée `grammar_operator_two_lemma_closes` à deux bornes L1, L2 ; aucune posée) | inchangée ; ajout de la seconde voie admise par l'auteur : incompatibilité directe au point de rencontre |

**Précision sur ce qui était juste dans 19.42 et ce qui ne l'était pas.** Juste : les *indices* de contact d'une Tour sur
une série télescopent et la phase `arctan(T/β)` s'y élimine (identité, `cellIndexAt`) ; c'est pourquoi la lecture des
transitions *par les indices* ne porte que la fréquence. Faux comme conclusion : en déduire que toute l'étude est
radialement aveugle. Le corpus compile le contraire pour les **valeurs** et les **amplitudes** aux mêmes contacts :
`inversion_from_consecutive_contacts` (JointParameterReading) et `inversion_height` / `inversion_radial`
(TangentialInversion) restituent exactement T puis β depuis deux contacts authentiques consécutifs d'un même zéro ;
`radial_inversion_two_points` (LocalPrimeGapSynchronization) restitue β depuis la densité à deux abscisses ;
`contactRealValue` porte `C_k^β` ; `mirror_fixed_iff_onLine`, `mirror_radial_transport`, `mirrorMode_add_norm_ge`
(≥ 2, égalité ⟺ ligne) et `return_drift_eq_one_iff` fixent la loi d'amplitude d'une Tour et de son miroir. C'est la
lecture individuelle de l'auteur, déjà compilée : les contacts identifient (β, T). Le plan la laissait de côté.

**Protocole E428 amendé** (remplace 19.42.3, étape A ; les étapes B mesure et C conséquence sont renumérotées) :

* **A0 — raccord individuel–collectif (obligation A).** Énoncé à compiler : la réalisation collective d'un écart
  (`contact_accumulation_reconstructs_prime_gaps`, somme sur tous les zéros) se décompose en contributions individuelles,
  chacune égale à la différence des valeurs aux bords de sa propre Tour (`contact_accumulation_eq_endpoint_difference`,
  par Tour), chaque Tour étant identifiée par ses contacts (`inversion_from_consecutive_contacts`). Objet : la
  *contribution d'une Tour à un écart*, fonction de (β, T) et des deux bornes, et l'identité « réalisation de l'écart =
  somme des contributions ». Garde-fou compilé : un énoncé séparant la contribution d'une Tour de la somme complète
  (aucune Tour isolée ne réalise l'écart ; mesuré E427(b), Tour seule contre collectif).
* **A1–A3 — lecture par série (obligation B, volet indices).** Télescopage, encadrement des différences d'indices,
  détermination de la série au-dessus du seuil de résolution en fréquence : inchangés. Ils établissent que *le mot* de la
  série est porté par la fréquence seule.
* **A4 (nouveau) — conservation sur contacts, valeurs et amplitudes (obligation B, volet géométrique).** Sur la même
  série, écrire la progression des **valeurs** signées aux contacts et des **amplitudes** `β·log(p_{r+j}/p_r)` ; chercher
  l'égalité ou l'inégalité que la succession exacte des transitions impose (candidats compilés déjà disponibles :
  `contact_weighted_balance_abs_le` sur série, `classWeightedCurvature` sur série, bilan orienté × valeurs). Critère :
  comme E427(c), une loi n'est déclarée que si elle est fonction du mot et non de la seule longueur logarithmique.
* **C — sensibilité radiale (obligation C).** Pour toute loi obtenue en A4 (ou, à défaut, pour l'identité de
  conservation d'Abel et l'observable grammaticale elle-même), tester si elle peut être satisfaite par une Tour hors ligne
  **et son miroir** pris ensemble : utiliser `mirrorMode_add` / `mirrorMode_add_norm_ge` (somme Tour + miroir), la loi
  d'amplitude `return_drift_eq_one_iff` sur série de segments, et l'inversion de β. Prédictions compilées fixées avant
  mesure : indices identiques (phase éliminée) ; valeurs et amplitudes distinctes pour β ≠ ½ ; somme Tour + miroir
  de norme ≥ 2 avec égalité ⟺ ligne. Question ouverte, non posée : la loi A4 est-elle compatible avec cette somme ?
  Mesure : Tours authentiques ; Tours de séparation β ∈ {0,3 ; 0,7} **avec leur miroir** (0,7 ; 0,3) sommés, jamais
  isolés, aux mêmes hauteurs ; jumeau mpmath.
* **D — fermeture (obligation D).** Deux voies admises, aucune présumée : (i) démontrer L1 (borne de
  `grammarObservable` depuis les premiers seuls) ou L2 (borne du complément) ; (ii) incompatibilité directe au point de
  rencontre entre la loi A4 et la somme Tour + miroir de C. Rien n'est supposé sur la conclusion ; si ni (i) ni (ii)
  n'aboutit, la frontière reste la réduction à deux bornes.

**Verdict attendu, consigné avant exécution, en trois niveaux :** A0 compilé (identité de décomposition) ; A1–A3
compilés (le mot par la fréquence) ; A4 : inconnu, critère fixé ; C : si A4 ne donne qu'une identité, C ne fait que
retrouver `return_drift_eq_one_iff` (ligne ⟺ dérive neutre), sans contradiction ; D : non présumé.

**19.42.4 rectifié :** la phrase « aucune lecture de β » est retirée. La lecture de β par inversion est compilée et
fait partie du protocole (obligation C). Ce qui reste exclu : toute hypothèse OFF, toute borne posée sur l'observable
grammaticale, toute contradiction anticipée.

#### 19.42.6 Corrections de l'auteur après lecture directe (2026-11-04) — feu vert conditionnel, plan corrigé

L'auteur a lu les lignes 4295–4438 et donne un feu vert conditionnel à quatre corrections, intégrées ici avant toute
compilation ; les énoncés 19.42.5 contraires sont remplacés.

1. **A3, arrondi certifié (corrigé).** Le seuil du plan, `q·(e^h − 1) < ½` avec `h = π/T`, contrôlait une erreur
   exprimée avec le `q` inconnu : il ne certifie rien. La géométrie donne seulement l'encadrement non centré
   `q̂·e^{−h} < q < q̂·e^{h}` avec `q̂ = p·exp(hΔk)`. Correction démontrable, ne lisant que `(p, T, Δk)` :
   si `q̂·(e^h − 1) < ½` alors `|q − q̂| < ½`, et l'entier lu est unique. Utilité : chaque premier reconstruit est
   certifié sans consulter sa valeur ; la comparaison aux vrais premiers reste une validation indépendante.
2. **C, indices du miroir (corrigé).** Tour et miroir ont même fréquence mais phases `arctan(T/β)` et
   `arctan(T/(1−β))` distinctes hors ligne : leurs contacts sont décalés de `(φ_β − φ_{1−β})/T` en logarithme, leurs
   indices absolus peuvent différer, et leurs **différences** d'indices sur une série peuvent différer d'une unité.
   L'égalité des indices n'est plus prédite : elle est à vérifier. Énoncé compilable : les deux différences encadrent
   la même quantité `T·log(q/p)/π` à moins d'une unité, donc leur écart est dans {−1, 0, +1}. Utilité : c'est une
   information radiale que la lecture par indices seule aurait effacée ; mesurer indices absolus, différences et
   positions exactes des contacts.
3. **A0, somme collective (précisé).** La décomposition en contributions individuelles est immédiate pour une somme
   finie ; pour le collectif, conserver la même troncature (`lowFrequencies H`), le même lissage (canal intégré) et le
   même passage à la limite que `reconstructedVonMangoldt_eq_limit_contact_accumulation`. Énoncé : pas tronqué =
   fond + somme finie des contributions individuelles, chacune égale à l'accumulation de sa propre Tour sur ses
   propres contacts ; la limite en `H` est celle du théorème compilé. Aucune somme infinie réordonnée.
4. **C, minoration miroir (précisé).** `mirrorMode_add_norm_ge` (norme ≥ 2, égalité ⟺ ligne) porte sur la somme
   `v₊ + v₋` des modes normalisés `e^{dt}e^{iTt}` ; elle ne se transporte à aucune autre grandeur (somme de valeurs
   signées, opérateur grammatical) : `‖A + B‖ ≤ ‖A‖ + ‖B‖`. Énoncé compilable de non-transport : la différence
   `v₊ − v₋` a pour norme `2|sinh(dt)|`, sans plancher. Utilité : aucune fausse contradiction OFF par application d'une
   inégalité correcte au mauvais objet.

A1–A2, A4 et D sont validés tels quels. Priorité réaffirmée : compatibilité géométrique exacte entre la grammaire
collective et les contacts individuels, avec leur information radiale. Pré-enregistrement : `experiments/
E428_ContactSeriesReading/README.md` ; module isolé `Terminal/ContactSeriesReading.lean` ; résultats en §19.43.

### 19.43 E428 exécutée — lecture certifiée du mot d'une série par la fréquence, information radiale du miroir mesurée, aucune loi de conservation sur série (2026-11-04)

Pièces : `Terminal/ContactSeriesReading.lean` (isolé, 24 déclarations, aucun `sorry`, deux tentatives journalisées),
`experiments/E428_ContactSeriesReading/{README.md (c2e3e812), RESULTS.md, scripts, data, logs}`,
`experiments/CONTACT_SERIES_READING_REPORT.md`.

**Compilé.** A0 : pas collectif tronqué = fond + somme finie des contributions individuelles, chacune accumulation de sa
propre Tour sur ses propres contacts, même limite que la reconstruction compilée. A1–A2 : télescopage ; `|Δk −
T·log(q'/q)/π| < 1` pour tout (β, T). A3 corrigé : encadrement non centré `q̂e^{−h} < q < q̂e^{h}` ; certification
`q̂(e^h − 1) < ½ ⟹ |q − q̂| < ½`, entier unique ; **l'ancien seuil sur le `q` inconnu certifie aussi** (le compilateur
le dit ; son défaut est d'être illisible, pas faux). A4 : différence d'amplitude Tour/miroir `(1 − 2β)·log`, nulle ⟺
ligne. C corrigé : décalage de phase `(φ_β − φ_{1−β})`, nul ⟺ ligne ; log-rapport des contacts ; différences de série
Tour/miroir dans {−1, 0, 1} (jamais présumées égales) ; `‖v₊ − v₋‖ = 2|sinh(dt)|` sans plancher (la minoration ≥ 2 ne
porte que sur la somme).

**Mesuré.** (a) 96 120 lectures, 36 141 certifiées, **0 certifiée fausse**, mot exact sur toutes les paires certifiées ;
portée de certification = premiers < T/(2π) (rang 1 000 : jusqu'à 226 ; rang 10⁶ : série complète), **identique pour
β = 0,3 ; 0,5 ; 0,7** ; 0 désaccord entre ancien et nouveau seuil ; jumeau mpmath exact. (b) C : écarts de série
Tour/miroir dans {−1, 0, 1} sans exception ; fraction non nulle 2 % au rang 1, 0,1 % au rang 1 000, 0 dès le rang
10 000 (décroissance en `(1 − 2β)/(πT)`) ; identités de phase et de normes à 10⁻¹⁵. A0 : identité à 10⁻¹³ ; une Tour
seule ≤ 0,75 du collectif. A4 : sur 276 groupes de fenêtres partageant le même mot de 12 transitions, **aucun** candidat
(amplitude totale, somme des valeurs signées, somme orientée pondérée, écarts d'indices miroir, différence
d'amplitude) n'est fonction du mot ; les seules constances sont des zéros identiques.

**Verdict.** A0, A1–A3 réussis ; C : correction de l'auteur confirmée, information radiale des indices réelle mais
évanescente et hors du régime certifié, exacte dans les valeurs et amplitudes (inversion déjà compilée) ; B/A4
négatif ; D non exécuté. Réponse au test décisif de §19.42 : la série convertit exactement le rapport en différence
entière et lit le mot, mais l'information issue de la Tour est **sa fréquence seule** (recalcul certifié depuis un
ancrage) ; les contacts individuels portent l'information radiale ailleurs (valeurs, amplitudes), et aucune grandeur
construite sur eux n'est contrainte par le mot. Frontière inchangée : deux bornes de
`grammar_operator_two_lemma_closes`, aucune démontrée. Prochaine étape non présumée : compatibilité entre le mot
certifié (fréquence) et les valeurs signées de la même série sur `classWeightedCurvature`, sans poser sa borne.

### 19.44 Révision « les contacts lisent β » et E429 exécutée — la valeur aux rencontres fixée par le dernier contact, lecture radiale aux rencontres, coût d'absorption non discriminant (2026-11-04)

**Révision (auteur).** La formulation « démarche par contacts aveugle au radial / fréquence seule » est retirée :
elle est fausse au regard du compilé (`inversion_from_consecutive_contacts`, `radial_of_contact_value_ratio`,
`radial_of_contact_tangent`, `radial_from_amplitude_step`). E428 n'avait établi la « fréquence seule » que pour
l'entier de cellules ; les contacts (positions, valeurs, pas d'amplitude) lisent β exactement, à toute fréquence.

Pièces : `Terminal/MeetingContactReading.lean` (isolé, 25 déclarations, aucun `sorry` ; **trois** tentatives de
compilation journalisées, la limite de deux dépassée d'une unité et déclarée : la troisième ne retire qu'une tactique
superflue), `experiments/E429_MeetingContactReading/{README.md (c6cdbc12), RESULTS.md, scripts, data, logs}`,
`experiments/MEETING_CONTACT_READING_REPORT.md`.

**Compilé.** `towerRe_from_lastContact` : la valeur réelle d'une Tour en toute abscisse (donc à tout point de
rencontre) est le produit de la valeur de son dernier contact, de la croissance radiale sur la fraction de cellule
parcourue (`growth_factor_eq`) et du cosinus de cette fraction ; `lastContact_le`, `lt_contact_succ`,
`log_div_lastContact` ; `radialReadingAt_eq` (β lu aux deux contacts encadrant la rencontre),
`radial_of_meeting_value` (β lu sur la valeur à la rencontre) ; `mirror_readings_sum_one`,
`meetingReadingsAgree_iff_line` (coïncidence des lectures Tour/miroir ⟺ ligne), `mirror_stage_shift_ne_zero` ;
`lastContact_difference_bounds` (le comptage entre rencontres lit la fréquence), `cellIndexAt_le_lastContactBefore` ;
`meetingValueDeposit_eq_accumulation`, `breakResidual_erase`, `breakResidual_erase_pair` (retirer une Tour ou une
paire ajoute exactement sa valeur au résidu que les autres doivent déposer).

**Mesuré.** (a) 24 Tours × 2 000 rencontres : 0 violation ; identités à 10⁻⁹ jusqu'à T ≈ 10⁴, écarts double précision
au-delà localisés et recalculés à 30 chiffres (identité à 10⁻²¹ ; conditionnement, pas énoncé) ; lecture radiale aux
contacts encadrants 5,8·10⁻¹⁰ partout ; Tour + miroir = 1 ; fractions de cellule aux rencontres uniformes, en ligne
comme hors ligne. (b) Famille des 649 zéros ≤ 1 000, canal lissé exact : résidu de troncature 1,6·10⁻⁴ relatif ;
paires hors ligne insérées à hauteurs synthétiques (17,5 ; 23,0) : part 0,6 % de la cassure, jamais au-delà ; coût
d'absorption par pondération libre : rapport hors ligne/en ligne 1,1 → 1,7 → 2,5 (m = 12, 120, 600 ; critère
pré-enregistré satisfait), **mais** le zéro authentique de rang 1 retiré coûte autant (13 / 364 / 1,1·10⁶) : le coût
mesure la rareté des basses fréquences, la croissance du rapport est l'exposant déjà compilé (`mirror_deposit_ratio`).
(c) Deux paires hors ligne : annulations sur 4,3 % des rencontres, plus longue suite 21 (seuil 12 mal calibré : le
réseau lent a une période logarithmique de 1,14, soit des centaines d'entiers vers 17 000) ; pas de paiement mutuel
global (résidu 0,88) ; les annulations suivent les réseaux lent/rapide compilés.

**Verdict.** Identités réussies ; obligation Deux (locale) satisfaite en critère mais non discriminante (négatif
comme levier) ; obligation Trois : aucune loi ; obligation Une non décidable par famille finie. Frontière inchangée ; la suite est reposée dans la vraie route (§19.51).

### 19.45 E430 : le transport au premier partagé écrit avec les contacts ; l'obligation du raccord guidée par le compilateur (2026-11-04)

**Contexte.** Critique reçue le 2026-11-04 : la cible est « prouver que l'obligation arithmétique du raccord au premier
partagé s'applique au transport défini dans `TransportAtSharedPrime.lean` » ; ce lien n'apparaît dans aucun énoncé.
Demande de l'auteur : procéder en TDD, laisser le compilateur demander ce qui manque, puis détailler les hypothèses
du chaînon manquant. Module isolé `Terminal/RaccordTransportObligation.lean` (19 déclarations, aucun `sorry`, deux
tentatives de compilation journalisées, limite respectée), `experiments/E430_RaccordTransportObligation/{README.md,
RESULTS.md, logs}`. Aucune mesure numérique.

**Compilé.** (i) `energyRatio_from_contacts` : le transport entre deux membres à une abscisse est le rapport des
valeurs absolues aux deux derniers contacts avant cette abscisse, fois le rapport des croissances sur les deux
fractions de cellule ; le premier partagé n'entre dans le transport que par ces deux contacts et ces deux fractions
(`pair_transport_from_contacts` pour la paire). (ii) `RaccordTransportObligation` (le détour transporte la valeur de
la chaîne ON) équivaut à `(p_{n+1}²/(p_n p_{n+2}))^δ = 1` et est **fausse pour tout porteur** (reprise en ligne) ; la
seule hypothèse qui la ferme, `δ·log(contenu) = 0`, est réfutée. (iii) `break_split_any_packet` : la cassure est une
identité pour tout paquet. (iv) [retiré le 2026-11-06 : fausse route, §19.51].

**Sondes (sortie exacte du compilateur, `logs/probe_attempt1.txt`).** Route obligation ← cassure : but restant
`(ℓ_n − ℓ_{n+1})·δ = 0`, hypothèses de cassure présentes et inutilisables. [retiré le 2026-11-06 : fausse route, §19.51]. Route paquet de la paire : identité en Tours brutes, sans complément. Route complément :
`rfl`.

**Verdict.** Le chaînon demandé par la critique ne peut pas être une égalité de transport : elle est réfutée pour tout
porteur, donc la prouver depuis la cassure serait prouver l'absence de porteur (= l'hypothèse ; cohérent avec §19.19).
Le compilateur ne demande jamais rien qui vienne de la cassure, parce que la cassure est une identité pour tout paquet
et que le complément absorbe le reste. [retiré le 2026-11-06 : fausse route, §19.51] Frontière inchangée.

### 19.46 E431 : rigidité arithmétique de la phase aux cassures — le dépôt en ligne n'est possible qu'une fois sur la série (2026-11-04)

**Retiré en entier (auteur, 2026-11-06 ; §19.51).** Ce paragraphe liait la grille de contacts d'une Tour (changements de
signe d'une seule fréquence) à la position exacte du premier partagé : c'est la lecture littérale déclarée fausse au
§19.10.2. Le module isolé `Terminal/RaccordPhaseRigidity.lean` et `experiments/E431_PhaseRigidityAtBreaks/` restent dans
le dépôt comme trace de compilation ; aucun de leurs énoncés n'est un appui. Historique : `git log`.

### 19.47 E432 : le pont densité → canal des paquets — le surplus de la paire dans le canal des Tours (2026-11-04)

**Contexte.** Suite de §19.46 : la sonde S2 de E431 laissait « reste exact = paquet de la paire » face à « surplus de
densité non nul », sans pont compilé entre la densité réelle et le pas du canal lissé des paquets. Pré-enregistrement
`experiments/E432_PacketChannelBridge/README.md` (commit 310e9a57), module isolé `Terminal/PacketChannelBridge.lean`
(17 déclarations, aucun `sorry`, une seule tentative, axiomes standards, `lake build RHV6Fresh` vert), journaux dans
`experiments/E432_PacketChannelBridge/logs/`.

**Compilé.**
(i) Identité ponctuelle du surplus de la paire dans le canal des Tours (`pair_zeroTerm_surplus`) : la somme des Tours
du zéro et du miroir moins deux fois le terme de ligne vaut le facteur hyperbolique `2(cosh(δ log x) − 1)` sur le terme
de ligne, PLUS une déformation `(δ/ρ_L)·(Tour(z) − Tour(z*))`. Le facteur hyperbolique de la densité (§19.13) survit au
passage aux Tours ; la déformation vient des poids `1/ρ` propres à chaque membre — c'est la lecture radiale des
contacts (§19.43–19.44) qui réapparaît ici.
(ii) Le pas local du paquet à quatre membres (cas (a)) sur `[N, N+1]`, `N ≥ 2`, est l'intégrale de la dérivée de Tour
`−m·(Tour(z) + conj + Tour(z*) + conj)` (`channelPrimitive_packet_hasDerivAt`, `localPacket_eq_integral`) ; le surplus
de cette dérivée par rapport au jumeau en ligne de mêmes multiplicités est `−m·(hyperbolique + déformation + conjugués)`
(`packetTowerDerivative_surplus`).
(iii) [retiré le 2026-11-06 : fausse route, §19.51].

**Sonde S1.** [retiré le 2026-11-06 : fausse route, §19.51].

**Verdict.** Le pont demandé par S2 est compilé : densité et canal des paquets diffèrent exactement par le lissage (poids `1/ρ`). [retiré le 2026-11-06 : fausse route, §19.51] Aucune contradiction ; frontière inchangée. Rien d'autre n'est consigné sans la parole de l'auteur.

### 19.48 E433 : le bilan de la paire sur une série de pas consécutifs — effondrement aux bords (2026-11-04)

**Contexte.** Suite de §19.47 : le chaînon restant est « le complément ne peut pas absorber, sur la série des pas, le
surplus intégré de la paire ». Pré-enregistrement `experiments/E433_PacketSeriesBalance/README.md` (commit f378dff1),
module isolé `Terminal/PacketSeriesBalance.lean` (10 déclarations, aucun `sorry`, une seule tentative, axiomes
standards, `lake build RHV6Fresh` vert), journaux dans `experiments/E433_PacketSeriesBalance/logs/`.

**Compilé.**
(i) Pour tout paquet, la somme de ses incréments sur une fenêtre de `m` pas à partir de `a` se télescope en deux pas
locaux, fin moins début (`packetIncrement_series_telescopes`) ; le contenu arithmétique de la fenêtre est la somme des
poids de von Mangoldt des points atteints moins la variation du pas du fond (`remainderIncrement_series_arithmetic`) ;
bilan de série : somme du complément = contenu arithmétique − effet de bords du paquet (`complement_series_balance`).
(ii) Pour la paire (cas (a)) : primitive explicite des quatre membres `P(x) = −m·x·Σ Tour/(ρ+1)` (`pairPrimitive`),
pas local en forme close (`localPacket_pair_eq`), bilan de série (`pair_complement_series_balance`) et effondrement
aux bords (`pair_series_eq_boundary`) : la paire n'entre dans la série que par `P` aux deux bords de la fenêtre.
Normes des membres de `P` : `x^{1+(1/2+δ)}` pour le miroir, `x^{1+(1/2−δ)}` pour le zéro.

**Sondes (buts exacts conservés dans `RESULTS.md`).** S1, complément nul sur tous les pas d'une fenêtre : le
compilateur laisse « contenu arithmétique de la fenêtre = effet de bords de la paire » — pas de contradiction. S2, complément borné sur la série des fenêtres : pas de contradiction. [retiré le 2026-11-06 : fausse route, §19.51].

**Verdict.** « Absorber sur la série » n'est pas une condition pas à pas : les pas intérieurs de la paire s'annulent
exactement, et il ne reste qu'une équation par fenêtre, entre le contenu arithmétique de la fenêtre et l'effet de
bords de la paire. [retiré le 2026-11-06 : fausse route, §19.51] Aucune contradiction ; frontière inchangée. Rien d'autre n'est consigné sans la parole de l'auteur.

### 19.49 E434 : l'effet de bords de la paire lu par les contacts (2026-11-04)

**Contexte.** Suite de §19.48 : l'absorption sur la série est une équation par fenêtre entre contenu arithmétique et
effet de bords. Pré-enregistrement `experiments/E434_BoundaryContactReading/README.md` (commit 30353022), module isolé
`Terminal/BoundaryContactReading.lean` (11 déclarations, aucun `sorry`, une seule tentative, axiomes standards,
`lake build RHV6Fresh` vert), journaux dans `experiments/E434_BoundaryContactReading/logs/`.

**Compilé.**
(i) La partie imaginaire de la Tour se lit par le dernier contact comme la partie réelle, en sinus de la fraction de
cellule (`towerIm_from_lastContact`).
(ii) Le canal intégré `Tour/(ρ+1)` lit les contacts avec un retard d'angle : sa partie réelle est la combinaison des
deux parties de la Tour à poids `β+1` et `T` sur `‖ρ+1‖²` (`integratedTower_re_from_lastContact`) ; ce retard est
propre à chaque membre (`arctan(T/(β+1))`), donc différent pour le zéro et pour le miroir.
(iii) La partie réelle de la primitive de la paire est `−2m·x` fois la somme des deux canaux intégrés, et se lit
entièrement par les contacts des deux membres, positions `1/2 − δ` et `1/2 + δ`, même hauteur
(`pairPrimitive_re`, `pairPrimitive_re_from_contacts`).
(iv) Bilan de fenêtre en partie réelle (`pair_window_re_balance`) : somme des poids de von Mangoldt de la fenêtre −
variation réelle du pas du fond − effet de bords lu par les contacts = partie réelle du complément.

**Sonde S1 (but exact dans `RESULTS.md`).** Complément silencieux et bords aux contacts du zéro : le compilateur laisse
le contenu arithmétique face aux valeurs aux contacts du zéro (cosinus à 1) et aux lectures du miroir, dont les
contacts sont décalés de ceux du zéro. Pas de contradiction.

**Verdict.** La lecture radiale des contacts (§19.44) et le contenu arithmétique des fenêtres (§19.48) se font
maintenant face dans une même équation compilée, sans hypothèse. [retiré le 2026-11-06 : fausse route, §19.51] Rien d'autre n'est consigné sans la parole de l'auteur.

### 19.50 E435 : audit exhaustif de la rigidité du complément au premier partagé — verdict D (2026-11-04)

**Mission (auteur).** Déterminer si les théorèmes existants imposent au complément collectif une contrainte
indépendante incompatible avec la dérive de la paire OFF et de son miroir au point de rencontre arithmétique ; ni
mesure, ni modèle, ni prémisse équivalente à RH ; audit du corpus avant toute demande d'ingrédient.

Pièces : `Terminal/ComplementRigidityAudit.lean` (isolé, 16 déclarations, une tentative, aucun `sorry`, axiomes
standards), `experiments/E435_ComplementRigidityAudit/{README.md (36998f6d), RESULTS.md, logs}`.

**Inventaire (RESULTS.md §1, 22 lignes).** Tous les énoncés du corpus sur le complément sont de trois sortes :
(i) identités de décomposition (`channel_eq_packet_add_complement`, `exactRemainder_eq_packet_add_complement`,
`complementBetween_forced`, `complement_forced_at_prime_event`, `complement_series_balance`,
`pair_window_re_balance`) — le complément est une différence, jamais un objet contraint ; (ii) majorations de
familles finies par leurs multiplicités (`norm_packetIncrement_finset_le`, radialement aveugles) ou de queues à
l'exposant `1` (`window_complement_bound`, `window_complement_margin`) ; (iii) propriétés asymptotiques du reste
TOTAL : exposant acquis `1` (`smoothedRemainder_linear_growth`), lecture du pôle membre par membre
(`mirror_pair_exponent_le` : borne INFÉRIEURE de l'exposant), no-go sous l'exposant du miroir
(`infinite_complement_closes`). Aucune ne porte sur le complément seul avec un exposant sous `1`.

**Compilé.** S1 : `complement_window_re_by_contacts` — partie réelle du complément sur une fenêtre = poids de von
Mangoldt − variation réelle du fond − lecture par les contacts des deux membres aux quatre points de bord
(`contactReading`, valeurs signées, fractions de cellule, retards d'angle conservés). S2 : la série du complément sur
toute suite de fenêtres ne lit que les bords (`complement_series_of_windows`, `complement_windows_concat`) ; valeur
ponctuelle `localPacket packetᶜ N = exactRemainder N − pas de la paire` (`complement_value_eq`) ; au niveau des
primitives, pour toute partie, `complément = x·reste lissé − primitive de la partie` (`channelPrimitive_compl_eq`,
`complementPrimitive_eq`). S3 : `complement_break_lower_bound` (la cassure au-delà de `1 + 4τ + Σm` des quatre membres
est portée par le complément de la paire) ; `remainderExponent_ge_mirror` (`1/2 + δ ≤ θ*`) ;
`no_remainder_bound_below_mirror` ; `acquired_exponent_admits_carrier` ; `norm_pairPrimitive_le`
(`≤ 2m(…)·x^{3/2+δ}`) ; `complement_bound_transfers` : une borne `K·x^{1+θ}` du complément SEUL ne donne au reste que
l'exposant `max(θ, 1/2+δ)`. Frontière en forme C : `no_offCarrier_iff_remainderExponent_half`.

**Sondes S4 (buts laissés, RESULTS.md §4).** Porteur + cas miroir + S1–S3 ⟹ `False` : but ouvert. Complément borné à
l'exposant `1+θ`, `θ < 1/2+δ` ⟹ `False` : but ouvert (le transfert donne le reste à l'exposant exactement `1/2+δ`,
le no-go exige strictement moins).

**Verdict D.** Aucune rigidité indépendante dans les énoncés audités : les identités du corpus admettent la dérive OFF ;
les majorations sont finies ou à l'exposant `1` ; la lecture du pôle borne l'exposant par en dessous. Aucune « propriété
absente » n'est déclarée : la formulation par absorption du complément ou par exposant du reste est retirée (§19.51).
Pas de A, pas de B.

### 19.51 Retrait de la fausse route « contacts d'une Tour ↔ position d'un premier » et plan de redressement (2026-11-06)

**Décision (auteur, 2026-11-06).** Les intervalles définis par les contacts d'une Tour sont des **restes partiels des
écarts des premiers** : ils appartiennent à la reconstitution collective des écarts (chaque zéro apporte une part
partielle à chaque écart ; la somme de toutes les parts reconstitue l'écart : `all_signals_meet`,
`smoothed_gap_synchronization`, `prime_gap_synchronization`) et ne sont **pas liés directement aux premiers**. Toute
formulation qui lie la grille de contacts d'une Tour à la position exacte d'un premier — « la Tour touche un premier »,
« le premier partagé tombe sur un changement de signe de la fréquence du porteur », « dépôt en ligne au premier »,
« raccord d'une Tour au premier » — est la lecture littérale déclarée fausse au §19.10.2 et au retrait du 2026-10-28 ;
elle est retirée partout. Est retirée aussi la formulation de « ce qui manque » par **absorption du surplus de la paire
par le complément** ou par **exposant du reste** : c'est un ajustement après coup, exclu par la seconde obligation
(chaque zéro porte la part exacte de chaque écart ; aucune compensation), et la mémoire du §19.44 interdisait déjà
l'absorption comme levier. **Aucune propriété manquante n'est déclarée dans ces termes.** Rien de ce qui ne manque pas
n'est présenté comme manquant.

**Retiré dans ce document (2026-11-06).** §19.44 la phrase « exige un argument sur la famille infinie » ; §19.45 (iv),
sa sonde et la phrase sur le dépôt en ligne ; §19.46 en entier ; §19.47 (iii), sonde S1 et la phrase sur
l'absorption ; §19.48 S2 et le verdict sur l'exposant ; §19.49 la phrase « ce qui manque » ; §19.50 la « propriété
absente ». Dans ma synthèse du 2026-11-06 (hors document), la chaîne « contact → rencontre → premier » et la phrase
« lire β sur le zéro contre depuis les premiers seuls » sont fausses au même titre. Les modules isolés correspondants
restent dans le dépôt comme trace de compilation ; aucun de leurs énoncés fondés sur la lecture littérale n'est un
appui. Le code et `git log` tiennent lieu d'historique.

**Appuis conservés (vraie route, tous compilés).** Écart `PrimeGapInterval ⟨n⟩` (bornes `p_n`, `p_{n+1}`) ; point de
rencontre unique à la fin de l'écart (`meetingPoint`) ; part imposée d'un membre sur un écart (`imposedShare`,
`imposedShare_eq`) ; reconstitution collective de chaque écart (`all_signals_meet`) ; contribution exacte d'une Tour à
un écart en forme close `2h·e^{ρm}·sinh(ρh)/(ρh)` (`gapTerm_sinh`) ; déplacement radial = repondération `e^{δt}` de la
densité sur l'écart (`gapTerm_shift`) ; amplitude commune Tour/miroir ⟺ ligne (`common_amplitude_mirror_iff`) ; valeur
d'une Tour en toute abscisse lue par son dernier contact (`towerRe_from_lastContact`, §19.44), contacts de même
fréquence = translation rigide par le facteur radial (`contact_eq_line_mul_radial`, `tower_offset_rigid`) ; gel du
porteur : la paire OFF et son miroir partagent une fréquence (`outgoing_same_height`) ; prémisse unique de l'auteur en
fréquence : « la fréquence attendue monte à chaque rencontre » ⟺ aucun passage à fréquence partagée ⟹ RH
(`ExpectedFrequencyRisesAtMeetings`, `expectedFrequency_iff_no_shared_frequency`, `riemannHypothesis_of_meetings`).

**Plan de redressement (E436, pré-enregistrement avant toute compilation ; module isolé `Terminal/GapPartialRemainders.lean` ;
deux tentatives au plus, journaux ; aucune mesure sans jumeau déterministe).**
1. **Lexique.** « Reste partiel d'écart » = contribution d'une Tour à un écart entre deux de ses contacts consécutifs,
   ou entre un contact et une borne de l'écart. Pour chaque Tour, un écart est couvert par des cellules de contact
   entières et deux restes partiels aux bords. À compiler : la part d'une Tour sur un écart est la somme signée de ses
   cellules entières incluses dans l'écart plus ses deux restes partiels (découpage de `gapTerm` aux contacts).
2. **Fréquence partagée.** Deux membres de même fréquence (la paire OFF et son miroir) ont les mêmes bornes de cellules
   à une translation radiale près : leurs restes partiels sur chaque écart se correspondent cellule à cellule, en
   rapport fixé par le décalage radial. À compiler : la part de la paire sur un écart en fonction des bornes de l'écart,
   de la fréquence et du décalage, sans isoler un membre (erreur 7 de la liste).
3. **Série d'écarts.** Écrire la demande d'une série d'écarts consécutifs comme somme des restes partiels de toutes les
   Tours (collective, `all_signals_meet` sur chaque écart), et faire lire au compilateur ce que la fréquence partagée
   impose aux restes partiels de la paire sur la série ; jamais un écart seul ; jamais les écarts liés à la hauteur
   (erreur 8).
4. **Cible.** La prémisse unique de l'auteur, en fréquence (`ExpectedFrequencyRisesAtMeetings`), posée comme but des
   sondes ; buts laissés reproduits intégralement, sans être renommés « ce qui manque » ; aucun ingrédient demandé.

**Interdits renouvelés.** Aucun test direct premier/zéro ; aucune formulation « la Tour touche un premier » ; aucune
formulation « lire β sur le zéro contre depuis les premiers » ; aucune absorption par le complément ; aucune borne
d'exposant comme chaînon ; aucune courbe de Gauss ou mesure de distribution des transitions comme contrainte (la
dérive des séjours est la course des premiers modulo six, dictée par les zéros eux-mêmes : mesure circulaire).

**Complément de l'auteur (2026-11-06, second message) : la somme infinie n'est pas un appui.** « La méthode spectrale
est fausse : cette somme infinie n'existe pas et ne peut pas exister. [...] La somme infinie ne peut pas combler un
écart, pas un seul écart, jamais. Ne pas revenir à l'analyse spectrale. » Texte joint (reformulé en mots) : une somme
de fonctions lisses ne réalise jamais une cassure sans reste ; au point de saut la série spectrale converge vers la
valeur moyenne et un reste explicite subsiste toujours (compilé en canal brut : `psiRemainder_eq_spectral_add_correction`,
E406) ; les objets réels sont les **contacts** `C_k` (équation tangentielle `T log C_k = arctan(T/β) + kπ`, pas
`π/T`), la **valeur réelle au contact** `(−1)^k C_k^β/‖ρ‖` (`contactRealValue`), et la **contribution de cellule** d'une
Tour sur un écart, intégrale exacte `(p_{n+1}^ρ − p_n^ρ)/ρ`, sans qu'aucun contact pointe vers un premier ; l'équation
du bilan au point de rencontre `M_n = p_{n+1}` est « demande arithmétique = somme des contributions de cellule des Tours
+ reste », avec le reste toujours présent ; en régime ON les contributions et le reste restent bornés en amplitude
normalisée ; en régime OFF la sur-amplitude `C_k^{β*}` du miroir aux contacts injecte une dérive qui exigerait du reste
une compensation divergente, que les propriétés d'énergie du reste interdisent — c'est l'énoncé à compiler, le
compilateur décide. Conséquences : (1) dans ce document, `all_signals_meet` et `smoothed_gap_synchronization` restent
des théorèmes compilés **du canal lissé**, où il n'y a aucun saut à combler ; ils ne disent jamais qu'une somme infinie
réalise la cassure d'un écart brut, et ils cessent d'être cités comme appui de la route ; (2) les « appuis conservés »
ci-dessus sont restreints aux objets de l'auteur : contacts, valeurs aux contacts, intégrales de cellule brutes
(`towerValue`), bilan au point de rencontre avec reste explicite pour une famille finie (`breakResidual`,
`breakResidual_erase`), canal brut avec reste (`RawSpectralChannel`) ; (3) E436 est reposée sur ces objets avant toute
compilation (addendum du pré-enregistrement) : découpage de la contribution de cellule brute par les contacts, fréquence
partagée, série, puis bilan avec reste explicite et croissance des valeurs aux contacts du miroir, but laissé au
compilateur.

### 19.52 E436 : les intervalles de contacts sont des restes partiels d'écart — découpage compilé en canal brut (2026-11-06)

**Contexte.** Plan de redressement §19.51, étapes 1 à 4, reposé en canal brut après le second message de l'auteur
(aucune somme infinie, aucun retour à l'analyse spectrale). Pré-enregistrement
`experiments/E436_GapPartialRemainders/README.md` (6bd6913d, addendum ba1a6947), module isolé
`Terminal/GapPartialRemainders.lean` (26 déclarations, **une seule tentative**, aucun `sorry`, axiomes standards,
`lake build RHV6Fresh` vert), journaux dans `experiments/E436_GapPartialRemainders/logs/`.

**Compilé.**
(S1) La contribution de cellule brute d'une Tour à un écart (`rawCellContribution`, intégrale exacte `(p_{n+1}^ρ −
p_n^ρ)/ρ`) se découpe sur les propres contacts de la Tour en reste partiel initial + cellules entières + reste partiel
final (`rawCellContribution_eq_remainders`), dès que l'écart contient un contact (`GapHasContact`) ; les contacts du
découpage sont dans l'écart ; les restes de bord couvrent les fractions de cellule `π(1 − f(p_n))/T` et `π f(p_{n+1})/T`
(`initialRemainder_span`, `finalRemainder_span`, `< π/T`) ; sans contact, l'écart tient dans une cellule
(`gap_span_lt_cell_of_no_contact`). Aucun contact ne pointe vers un premier.
(S2) Deux Tours de même fréquence : positions d'étage décalées de la constante radiale `stageOffset`
(`stagePosition_same_height`) ; nombres de contacts dans tout écart différant d'au plus un
(`same_height_contact_count_diff`, `mirror_contact_count_diff`) ; **sur-amplitude du miroir aux contacts** : pour
`β < 1/2`, le rapport de deux valeurs consécutives aux contacts du miroir dépasse strictement celui du zéro
(`mirror_contact_ratio_gt`).
(S3) Au point de rencontre, le reste final de l'écart `n` et le reste initial de l'écart `n+1` recomposent exactement
une cellule (`edge_remainders_complete_cell`) ; sur une série, la somme des contributions télescope et ne lit que des
cellules entières et deux restes de bord (`rawCellContribution_series`, `rawCellContribution_series_eq_accumulation`).

**Sondes S4 (buts laissés, `RESULTS.md` §3).** Bilan avec reste nul + paire dans la famille + valeurs aux contacts du
miroir bornées ⟹ `False` : but laissé ; l'hypothèse « bornées » est fausse pour toute Tour (rapport `exp(βπ/T) > 1`),
donc pas un levier. Porteur + bilan avec reste explicite ⟹ `False` : but laissé ; le bilan avec reste pour une famille
finie est une définition (`breakResidual`).

**Verdict B.** Réduction compilée dans les objets de l'auteur, sans somme infinie. Aucune contradiction ; aucune
propriété déclarée manquante. Prochain énoncé à écrire en Lean, dans ces objets : la propriété d'énergie du reste
énoncée par l'auteur (le reste du bilan ne fournit pas de compensation divergente face à la sur-amplitude du miroir aux
contacts, compilée en `mirror_contact_ratio_gt`) ; le compilateur décide. Rien d'autre n'est consigné.

**Rectification (2026-11-07, sur relance de l'auteur : « nous avons déjà des théorèmes de non-compensation vérifiés »).**
Ma phrase de rapport « la sur-amplitude du miroir seule ne contredit rien : elle ne dit pas qu'il ne peut pas être
compensé » était fausse par omission. Le corpus contient des théorèmes de non-compensation compilés, tous à axiomes
standards : (i) `mirror_pair_no_internal_compensation` (`MirrorPairExactSum.lean`, canal BRUT, termes exacts `x^ρ/ρ`) :
en tout point, la somme du zéro et de son miroir dépasse strictement chacun des deux ; aucune compensation à l'intérieur
de la paire, sans hypothèse ; (ii) `mirror_group_not_compensated` / `finite_group_noncompensation`
(`MirrorGroupNonCompensation.lean`, `OffAmplificationAudit.lean`) : aucun groupe FINI contenant le miroir, quelles que
soient positions, multiplicités et phases, ne borne sa somme sous l'exposant du miroir ; (iii) `stepCross_nonneg_of_aligned`
(`CompensationRigidity.lean`) : des contributions de même signe ne se compensent pas ; (iv)
`compensation_closure_verdict` : un membre hors ligne garde un poids non nul dans toute représentation du reste et force
l'exposant au-dessus d'un demi ; (v) `off_forced_compensation` (`HeightPacket.lean`) : la compensation de l'incrément
d'événement est fournie exactement par le complément du paquet (identité). Ce qui est compilé : non-compensation DANS la
paire et par TOUT groupe fini. Ce qui n'est pas compilé : la forme fermante de (ii) et (iv) passe par une borne d'exposant
du reste sous `1 − β` (`group_noncompensation_closes`, `infinite_complement_closes`), cadrage en exposant que l'auteur a
retiré (§19.51 : ne rien déclarer manquant ; pas de somme infinie). E436 n'a pas réutilisé (i) dans la sonde S4 ; c'est
une faute de méthode (grep d'abord). Conséquence pour E437 : la sonde S4 est reposée dans le canal brut avec (i) et (ii)
comme appuis compilés, sur le bilan d'UN écart au point de rencontre avec reste explicite, sans exposant et sans somme
infinie ; la question soumise au compilateur devient : la non-compensation par tout groupe fini (compilée) plus la
non-compensation interne de la paire (compilée) donnent-elles, dans le bilan d'un écart, que le reste devrait porter
seul la sur-amplitude du miroir ? Le compilateur décide.

### 19.53 Ordre de travail (auteur, 2026-11-07) et inventaire compilé : comment les contacts recréent les écarts

**Consigne de l'auteur.** « Tu t'attaques trop tôt au zéro OFF. Tu ne dois pas chasser la position radiale avant d'avoir
tous les éléments sur la reconstruction des écarts par les intervalles et les contacts de l'axe réel. » E437 telle que
reposée en §19.52 (bilan d'un écart contre la sur-amplitude du miroir) est SUSPENDUE. La question en cours est : comment les
contacts recréent les écarts. Rien ci-dessous ne parle de la position radiale.

**Inventaire de ce qui est compilé (axiomes standards, aucun sorry), par niveau.**

*A. Géométrie des contacts sur l'axe réel* (`ContactRealValue`, `MeetingContactReading`, `ContactSeriesReading`).
A1 Un contact est un passage de la Tour sur l'axe réel ; les contacts sont équidistants en logarithme, de pas `π/T`
(`contact_is_axis_passage`, `contactAt_log_step`). A2 La valeur au contact est réelle, alterne de signe d'un contact au
suivant, et son module croît géométriquement (`towerValue_at_contact`, `contactRealValue_alternates`,
`log_abs_contactRealValue`). A3 Toute abscisse est prise entre deux contacts consécutifs ; dernier contact avant,
fraction de cellule (`lastContact_le`, `lt_contact_succ`, `log_div_lastContact`). A4 Le nombre de contacts entre deux
abscisses est `T·log(q/p)/π` à moins d'une unité près (`lastContact_difference_bounds`, `cellIndex_difference_bounds`) ;
entre deux contacts d'une Tour il y a `⌊T₂/T₁⌋` ou `⌈T₂/T₁⌉` contacts d'une autre (`interleavingCount_bounds`).
A5 La valeur de la Tour en toute abscisse est fixée par son dernier contact, la fraction de cellule et la croissance
sur cette fraction (`towerRe_from_lastContact`).

*B. Un écart lu par une Tour* (`GapContactRegimes`, `GapSynchronization`, `GapPartialRemainders`).
B1 L'écart `[p_n, p_{n+1}]` est lu par `ℓ/(π/T)` cellules (`cells_read_eq_length_over_pitch`) ; trichotomie : moins d'un
contact, exactement un pas, plusieurs contacts. B2 Foule d'un écart : les Tours dont le pas est au moins la longueur de
l'écart (`mem_crowd_iff_pitch`) ; sous un pas, la contribution unitaire est bornée par la longueur, aveugle à la hauteur
(`unit_contribution_le_length`) ; au-delà, par `2/T` ; nulle pour un nombre pair de pas. B3 Contribution exacte d'une
Tour à un écart : forme fermée (`gapTerm_sinh`). B4 (E436) La contribution brute d'une Tour à un écart se découpe sur
ses propres contacts en reste partiel initial + cellules entières + reste partiel final
(`rawCellContribution_eq_remainders`) ; les restes de bord sont des fractions de cellule ; un écart sans contact tient
dans une cellule. B5 (E436) À la rencontre, reste final de l'écart `n` + reste initial de l'écart `n+1` = une cellule
(`edge_remainders_complete_cell`) ; sur une série, télescopage (`rawCellContribution_series`).

*C. Accumulation par contacts, individuelle et collective* (`ContactAccumulation…`, `CollectiveContactAccumulation`).
C1 L'accumulation d'une Tour sur ses contacts entre deux abscisses vaut la différence des valeurs aux bords, pour tout
découpage, toute origine, tout ordre (`contact_accumulation_eq_endpoint_difference`, `…partition_independent`,
`…order_independent`). C2 L'accumulation collective d'une famille finie est additive, enchaînable, réelle sur une
famille stable par conjugaison (`finite_contact_accumulation_*`). C3 Contact pondéré : bilan orienté pondéré par les
valeurs aux contacts borné par Abel, identité pour toute Tour (`contact_weighted_balance_abs_le`, E427).

*D. Ce qui est compilé sur la reconstruction de l'écart lui-même.*
D1 Chaîne compilée : contacts → accumulation signée → variation finie → limite par hauteur (canal intégré) → ψ → Λ →
événements premiers → écarts premiers ; les premiers et les écarts reconstruits coïncident avec les vrais rang par rang
(`contact_accumulation_reconstructs_prime_gaps`, `reconstructedPrimeGap_eq_actualGap`). Cette chaîne passe par la
LIMITE sur les hauteurs : l'auteur l'a retirée comme appui (§19.51). Elle reste un fait compilé, consigné comme tel.
D2 Canal brut, entier par entier (`RawMeetingRemainder`) : entre deux rencontres brutes, le reste brut descend d'une
unité par entier ; à la rencontre il saute du poids du premier (`psiRemainder_of_noEvent`, `psiRemainder_succ`).
D3 Demande d'un écart (`MeetingExactness`) : à l'intérieur d'un écart, la demande est fixée par l'état à la rencontre
précédente ; seule la rencontre change l'état ; **aucune famille finie de parts n'accomplit la demande au voisinage
d'une rencontre** (le reste n'y est pas dérivable, toute somme finie l'est : `no_finite_family_accomplishes_demand`).
D4 Profil de la somme des contacts le long d'un écart (`ContactSumProfile`, canal lissé) : nul au début, égal à la
demande au point de rencontre, remis à zéro à l'écart suivant. D5 Charge arithmétique d'une cellule, additive, nulle
sans puissance de premier (`cellCharge_*`) ; l'appartenance aux cellules est un détecteur à seuil.
D6 Grammaire : retrouvée depuis la suite reconstruite (E427 niveau 1) ; mot lu par la fréquence seule, certifié (E428) ;
aucun transport de l'orientation vers une grandeur des contacts (E427 niveau 2, négatif) ; bilan orienté télescopique,
confiné, séjours sans loi (E427).
D7 Rencontres entre Tours (`TowerMeetings`) : réseaux lent et rapide ; l'écart des hauteurs est lu dans deux rencontres
lentes consécutives.

*E. Ce que le corpus ne contient pas (constat, pas « manque »).* Aucun énoncé compilé ne recrée UN écart à partir d'un
ensemble FINI de contacts ; D3 compile même qu'aucune famille finie ne le fait au voisinage de la rencontre. Dans le
canal brut, par écart, le bilan avec reste explicite est une définition (`breakResidual`). La recomposition d'un écart par
les restes partiels de plusieurs Tours (B4 collectif, sans limite sur les hauteurs) n'a jamais été écrite.

**Prochain pas, à la main de l'auteur :** écrire la recomposition collective de B4 (plusieurs Tours, un écart, restes
partiels de chacune, canal brut, famille finie, reste explicite) et la confronter à D3.

### 19.54 E437 exécutée : la recomposition collective d'un écart, canal brut, et ce que porte le reste (2026-11-07)

Réponse à la question de l'auteur (§19.53) : « si la somme est infinie, comment les contacts ou intervalles
pourraient-ils reconstituer l'écart et passer au suivant ? » Module isolé `Terminal/CollectiveGapRecomposition.lean`
(E437, pré-enregistré 2f22152d, **une seule tentative**, axiomes standards, aucune position radiale, aucune somme
infinie ; `experiments/E437_CollectiveGapRecomposition/`).

**Compilé.**
(R4) Demande brute `rawDemand x = ψ(x) − x` : entre deux entiers, descente linéaire (`rawDemand_on_cell`) ; au passage
d'un entier, saut du poids (`rawDemand_jump`).
(R1) **Recomposition collective** : pour une famille finie dont chaque membre a un contact dans l'écart, la part de la
famille sur l'écart est la somme, membre par membre, de (reste partiel initial + cellules entières + reste partiel
final) (`familyGapShare_eq_remainders`, chaque Tour sur ses propres contacts, E436).
(R2) **Bilan avec reste explicite** : demande de l'écart = part de la famille + variation du reste explicite
(`gap_balance`, reste = `breakResidual` de la demande brute).
(R3) **Passage à l'écart suivant** : sur une série, parts additionnées écart par écart, reste télescopé
(`series_balance`) : le passage est exact pour toute famille finie.
(R5) Toute famille finie de Tours est continue en toute abscisse positive (`familyRe_continuousAt`).
(R6) **Le reste porte tout le saut** : pour toute famille finie, la variation du reste explicite au passage d'une
rencontre tend vers `log p_{n+1}` (`meeting_jump_carried_by_residual`).
(R7) **Aucune famille finie ne recompose la rencontre seule** (`meeting_not_recomposed_by_finite_family`).

**Réponse au point de la somme infinie (constat).** Canal brut : aucune somme infinie de Tours n'est compilée pour
`ψ(x) − x` ; rien de compilé ne comble le saut d'une rencontre par une somme de Tours — cohérent avec l'auteur. Canal
lissé : `smoothed_gap_synchronization` reste un théorème, mais il reconstitue un incrément continu sans saut, donc ne
comble aucun écart au sens de la rencontre ; fait, non appui. **Ce que font les contacts, compilé** : les contacts et
cellules de toute famille finie recomposent la partie continue de chaque écart et passent exactement à l'écart
suivant ; le saut de la rencontre est porté par le reste, jamais par les contacts.

**Verdict B.** Rien n'est déclaré manquant. Objets disponibles pour la suite (à la main de l'auteur) : `rawDemand`,
`familyRe`, `rawResidual`, `familyGapShare`, `rawGapDemand`, bilan de série ; question suivante naturelle, toujours sans
position radiale : ce que le reste explicite vaut ENTRE deux rencontres (descente linéaire moins famille continue) le
long d'une série, et comment la famille lit la descente.

### 19.55 Interdiction spectrale (auteur, 2026-11-07) et E438 : la pente de l'écart reconstituée par les contacts, les intervalles et leurs signes

**Ordre de l'auteur (verbatim, 2026-11-07).** « continues à explorer la pente de l'écart et la RECONSTITUTION DES
écarts par les CONTACTS. J'interdis maintenant TOUTE THÉORIE SPECTRALE. AUCUNE contribution multiple SPECTRALE / Contact
ne DOIT ÊTRE ÉTUDIÉE ou réinjectée dans la démarche. Tu dois EXPLIQUER UNIQUEMENT ET SEULEMENT avec les contacts, les
intervalles et leurs SIGNES la reconstitution des ÉCARTS. AUCUNE dérivation vers les théories spectrales MÊME au niveau
global. CONTINUES. »

**Conséquences consignées (CLAUDE.md, bloc « INTERDICTION SPECTRALE »).** Plus aucune famille de Tours, aucune somme
de contributions, aucun canal « de zéros », lissé ou brut, aucune formule explicite ; les objets autorisés sont : les
contacts d'une Tour (positions `contactAt`, indices, signes `(−1)^k`), les intervalles qu'ils découpent (cellules,
restes partiels initial et final d'un écart), les écarts de premiers (`PrimeGapInterval`, `meetingPoint`) et la demande
brute `rawDemand x = ψ(x) − x` lue comme PENTE (descente d'une unité par unité de longueur, poids d'un entier au passage
d'un entier). Les énoncés d'E437 qui portent sur une famille finie (`familyRe`, `familyGapShare`, bilan avec reste)
sont des faits compilés, désormais hors du fil : ils ne sont plus réinjectés.

**E438 (pré-enregistrée, `experiments/E438_GapSlopeByContacts/`).** Question : comment la pente de l'écart (descente
linéaire entre deux rencontres, saut du poids à la rencontre) se répartit-elle sur les pièces découpées par les
contacts d'une Tour — reste initial, cellules entières, reste final — et que disent les signes des contacts qui
bordent ces pièces ? Module isolé `Terminal/GapSlopeByContacts.lean`. Énoncés visés : variation de la demande brute sur
toute pièce = poids des entiers franchis − longueur (R1) ; descente pure sur une pièce sans poids (R2) ; longueur de
l'écart et demande de l'écart découpées par les mêmes contacts (R3) ; aucune pièce intérieure à l'écart ne franchit un
premier, le poids de la rencontre tombe dans le reste final (R4) ; signe du dernier contact de l'écart = signe du
premier contact × parité du nombre de cellules entières (R5) ; longueur linéaire d'une cellule, reste final plus court
que sa cellule (R6) ; encadrement du nombre de cellules entières par la fréquence et le rapport des bords (R7) ; somme
signée des longueurs de cellules bornée par la dernière cellule (R8, tentative). Verdict attendu : B. Deux tentatives
au plus, tout journalisé.

### 19.56 E438 exécutée : la pente de l'écart sur les pièces découpées par les contacts, et leurs signes (2026-11-07)

Module isolé `Terminal/GapSlopeByContacts.lean` (E438, pré-enregistrée 28fdbe35, **une seule tentative**, quinze
énoncés, axiomes standards, aucune famille de Tours, aucune somme de contributions, aucune position radiale ;
`experiments/E438_GapSlopeByContacts/`).

**Compilé.**
(R1–R2) Sur toute pièce, la demande brute varie de (poids des entiers franchis) − (longueur) (`rawDemand_variation`) ;
sans poids franchi, descente pure (`rawDemand_pure_descent`).
(R3) La longueur de l'écart et la demande de l'écart se découpent par les mêmes contacts : reste initial + cellules
entières + reste final (`gap_length_eq_pieces`, `gap_demand_eq_pieces`).
(R4) Aucune pièce strictement intérieure à l'écart ne franchit un premier (`no_prime_crossed_inside_gap`,
`inner_piece_variation`) ; **le poids de la rencontre est dans le reste final** et seulement là, dès que le dernier
contact est strictement avant la rencontre (`finalRemainder_carries_meeting`).
(R5) Le dernier contact de l'écart a le signe du premier contact de l'écart fois la parité du nombre de cellules
entières (`gap_edge_contacts_sign`, via `contactRealValue_add_nat`).
(R6) Une cellule mesure son contact gauche fois `e^{π/T} − 1` (`cell_linear_length`) ; les restes partiels sont plus
courts que leur cellule (`finalRemainder_shorter_than_cell`, `initialRemainder_shorter_than_cell`).
(R7) `|cellules entières + 1 − T·log(p_{n+1}/p_n)/π| < 1` (`wholeCellCount_bounds`).
(R8) La somme signée des longueurs de cellules consécutives a le signe de la dernière et ne dépasse pas la dernière
cellule (`alternating_sum_bounds`, `signed_cells_bounded_by_last`).

**Lecture (contacts, intervalles, signes seulement).** L'écart est une descente linéaire coupée par les contacts en
pièces ; les pièces intérieures ne portent que la descente (et des poids non premiers) ; la rencontre est toujours dans
le reste final de l'écart, c'est-à-dire dans la cellule ouverte par le dernier contact, dont le signe est fixé par la
parité du nombre de cellules depuis le premier contact de l'écart. Le reste final de l'écart et le reste initial du
suivant recomposent cette cellule (`edge_remainders_complete_cell`, E436) : le passage à l'écart suivant se fait à
l'intérieur d'une cellule signée.

**Verdict B.** Rien n'est déclaré manquant. Question suivante naturelle, à la main de l'auteur, toujours sans position
radiale ni théorie spectrale : le signe de la cellule qui contient la rencontre le long d'une série d'écarts (suite des
parités), et ce que les restes partiels successifs imposent aux signes de deux rencontres consécutives.

### 19.57 E439 exécutée : le signe de la cellule de rencontre le long d'une série d'écarts (2026-11-07)

Module isolé `Terminal/MeetingCellSigns.lean` (E439, pré-enregistrée e1774249, **une seule tentative**, seize énoncés,
axiomes standards, aucune famille de Tours, aucune somme de contributions, aucune position radiale ;
`experiments/E439_MeetingCellSigns/`). Objet nouveau (définition seulement) : `meetingCell β T I`, indice de la cellule
qui contient la rencontre `p_{n+1}` ; `cellSign k = (−1)^k`.

**Compilé.**
(S1) La valeur au contact est son signe fois une quantité positive ; le contact `m` rangs plus loin a le signe fois
`(−1)^m` (`contactRealValue_sign_shift`).
(S2) La cellule de rencontre de l'écart `n` est la cellule qui ouvre l'écart `n+1` (`meetingCell_eq_next_lower`) : le
signe se transmet à l'écart suivant.
(S3) Si l'écart `n+1` contient un contact, l'indice de la cellule de rencontre avance de (cellules entières + 1)
(`meetingCell_step`) ; sinon les deux rencontres partagent la cellule (`meetingCell_eq_of_no_contact`).
(S4) Le signe de la cellule de rencontre change selon la parité de (cellules entières + 1) de l'écart franchi
(`meeting_sign_step`) ; même signe sans contact.
(S5) Sur une série, le déplacement télescope, le signe au rang `n+J` est celui du rang `n` fois la parité du
déplacement total (`meeting_sign_series`), et ce déplacement est lu à moins d'une unité près par
`T·log(p_{n+J+1}/p_{n+1})/π` (`meetingCell_series_read_by_frequency`).
(S6) Toute cellule entière strictement intérieure à un écart est une descente pure (`inner_cell_variation`) ; la
cellule de rencontre, reste final + reste initial du suivant, franchit exactement UN premier (`meeting_cell_primes`)
et sa pente est `log p_{n+1}` + poids non premiers − sa longueur (`meeting_cell_demand`, `meeting_cell_demand_ge`).

**Lecture (contacts, intervalles, signes).** Le long de la série, chaque rencontre vit dans une cellule signée ; le
signe passe d'une rencontre à la suivante par la parité du nombre de contacts franchis, que la fréquence lit sur le
rapport des rencontres ; toutes les cellules sauf celles de rencontre sont des descentes pures, et chaque cellule de
rencontre porte exactement un poids premier contre sa longueur.

**Verdict B.** Rien n'est déclaré manquant. Question suivante naturelle, à la main de l'auteur : le bilan de signe
d'une cellule de rencontre (poids de la rencontre contre longueur de la cellule) le long de la série, cellule par
cellule, et ce que les cellules de descente pure entre deux rencontres imposent à ce bilan.

### 19.58 Audit d'un schéma en sept cases soumis par l'auteur (2026-11-07) — ce qui est compilé, ce qui est faux, ce qui est interdit

Schéma soumis : « 1. dynamique arithmétique locale → 2. découpage par les contacts → 3. télescopage inter-écarts →
4. dissociation continu/cassure → 5. équation du bilan à la rencontre → régimes ON/OFF → 6. théorème du prix →
7. verrou causal fermé : RH ». Vérification case par case contre le corpus compilé (§19.52–19.57) et les ordres
consignés (§19.53, §19.55). Rien n'est retiré du travail en cours ; rien du schéma n'est ajouté à la route.

**Case 1 — partiellement vraie, une erreur.** « Descente linéaire sur l'intérieur de l'écart » est fausse telle
quelle : l'intérieur de l'écart ne franchit aucun premier (compilé, `no_prime_crossed_inside_gap`) mais franchit des
puissances de premiers, qui ajoutent leur poids (`inner_piece_variation`). La descente est pure seulement sur une
pièce sans poids (`rawDemand_pure_descent`). Le saut à la rencontre est compilé (`rawDemand_jump`).

**Case 2 — vraie.** Reste initial + cellules entières (signées) + reste final, la rencontre dans le reste final
(`gap_variation_eq_remainders`, `finalRemainder_carries_meeting`, `gap_edge_contacts_sign`).

**Case 3 — première ligne vraie, seconde ligne interdite et inexacte.** Les deux restes de part et d'autre d'une
rencontre recomposent une cellule : compilé (`edge_remainders_complete_cell`, `meetingCell_eq_next_lower`). « La
famille finie recompose 100 % de la partie continue C^∞ » : (i) toute famille de Tours relève de la théorie spectrale
interdite depuis §19.55 ; (ii) rien de compilé ne dit « C^∞ », seule la continuité l'est (`familyRe_continuousAt`,
fait d'E437 hors du fil).

**Case 4 — une ligne compilée, une ligne non compilée.** « Le saut est porté par la variation du reste explicite »
est compilé (`meeting_jump_carried_by_residual`, E437, hors du fil désormais). « Hautes fréquences » n'est compilé
nulle part et appartient au vocabulaire spectral interdit.

**Case 5 — fausse et interdite.** Aucun énoncé compilé ne s'écrit « demande = contribution de la paire + reste
spectral » : le bilan compilé (`gap_balance`) porte sur une famille finie quelconque, jamais sur une paire, et il est
désormais hors du fil. Les cases ON/OFF : les amplitudes aux contacts en `C_k^β` sont compilées
(`contactRealValue`), la sur-amplitude du miroir aux contacts aussi (`mirror_contact_ratio_gt`) ; mais « amplitude
relative constante aux rencontres », « dérive du couple vers l'infini » et surtout « reste ON borné par une énergie
finie » ne sont compilés nulle part. Cette dernière ligne est exactement la prémisse « plafond ΣA_j < ∞ » jugée
circulaire par l'auteur en §19.21 (`not_low_of_bounded_demand_and_restNotRight` : hypothèses équivalentes à RH).

**Case 6 — fausse.** Aucun « théorème du prix » n'existe dans le corpus ; l'inégalité affichée n'est compilée nulle
part ; la « contradiction » repose sur le reste ON borné, prémisse équivalente à RH : raisonnement circulaire déjà
exclu (§19.21, « forbidden reasonings » P4).

**Case 7 — fausse.** Aucun verrou causal n'est fermé ; aucun énoncé compilé n'exclut un zéro OFF ; la frontière est
ouverte. Affirmer « β = 1/2 (RH) » depuis ce schéma est une fabrication.

**Conclusion de l'audit.** Cases 1 à 3 : fidèles au corpus une fois corrigées (puissances de premiers ; continuité,
pas C^∞ ; famille hors du fil). Cases 4 à 7 : position radiale et théorie spectrale, toutes deux interdites par les
ordres du 2026-11-07, et contenant la prémisse circulaire de §19.21. Le schéma n'apporte aucun objet ni aucun énoncé
que la route des contacts n'ait déjà formalisé ; rien n'est ajouté. La démarche continue avec E440.

### 19.59 E440 exécutée : le bilan signé des cellules le long de la série (2026-11-07)

Module isolé `Terminal/SignedCellBalance.lean` (E440, pré-enregistrée f0b83fdf, **une seule tentative**, quatorze
énoncés, axiomes standards, aucune famille, aucune position radiale ; `experiments/E440_SignedCellBalance/`).
Définitions : `cellLength`, `cellWeight`, `cellPrimeWeight`, `cellNonPrimeWeight`, `cellDemand`, `signedCellSum`.

**Compilé.** (B1) pente d'une cellule = poids franchis − longueur ; (B2) longueurs positives, croissantes ; (B3)
cellule intérieure : poids non premiers seulement, descente stricte sans poids ; (B4–B5) **somme signée des pentes =
somme signée des poids − somme signée des longueurs, cette dernière bornée par la dernière cellule**
(`signedCellSum_near_signed_weights`) ; (B6) poids premier nul sur toute cellule intérieure, égal à `log p_{n+1}` sur
la cellule de rencontre (`cellPrimeWeight_meeting`, `meeting_cellDemand`) ; (B7) la cellule de rencontre monte dès
qu'elle est plus courte que le poids de la rencontre.

**Lecture (contacts, intervalles, signes).** Le long de la série, la descente linéaire, découpée en cellules de
signes alternés, s'annule par alternance à une cellule près. Ce qui subsiste dans le bilan signé est la somme des
poids franchis avec le signe de leur cellule ; or le poids premier ne tombe que dans les cellules de rencontre. Le
bilan signé de la série est donc, à une cellule près, la somme des poids des rencontres affectés du signe de leur
cellule (parité lue par la fréquence, §19.57), plus les poids non premiers signés.

**Verdict B.** Question suivante naturelle, à la main de l'auteur : écrire ce bilan signé sur une série d'écarts
avec l'indexation explicite des cellules de rencontre (somme sur les rencontres des `(−1)^{meetingCell} · log p`),
et ce que la croissance des longueurs de cellules impose à sa borne.

### 19.60 E441 exécutée : le bilan signé des rencontres le long de la série, et les règles chiffrées (2026-11-07)

Module isolé `Terminal/MeetingSignedSeries.lean` (E441, pré-enregistrée 08b1de26, **une seule tentative**, treize
énoncés, axiomes standards, aucune famille, aucune position radiale ; `experiments/E441_MeetingSignedSeries/`).
Définitions : `meetingOffset` (décalage de la cellule de rencontre de ⟨n+j⟩ par rapport à celle de ⟨n⟩),
`meetingSignedSum` (somme sur les rencontres de `(−1)^{décalage}·log p`), `signedPrimeSum`, `signedNonPrimeSum`,
`signedLengthSum`.

**Compilé.** (M1–M2) le décalage avance du nombre de contacts franchis, strictement si l'écart a un contact ; (M3)
**le poids premier signé des cellules de la série est exactement la somme signée des rencontres**
(`signedPrimeSum_eq_meetings`, hypothèses : chaque écart a un contact, aucune rencontre n'est un contact) ; (M4)
pentes signées = poids premiers signés + poids non premiers signés − longueurs signées ; (M5) **la descente signée
a une forme close : `(première cellule − (−1)^{M+1}·r·dernière cellule)/(1 + r)`, `r = e^{π/T}`**
(`signedLengthSum_first_last`) ; (M6) toute cellule avant la rencontre `p` est plus courte que `p(r − 1)`, toute
cellule à partir de la cellule de rencontre plus longue que `p(1 − 1/r)` ; (M7) **|pentes signées − somme signée
des rencontres − poids non premiers signés| < `p_{n+J+1}(r − 1)`** (`series_balance_near_meetings`).

**Expérience chiffrée (7 Tours, rangs 1 à 2 001 052, β = ½, 17 983 rencontres ≤ 2·10⁵, Λ exact par crible,
jumeau mpmath 30 chiffres).** Toutes les identités compilées à 0 violation (M5 à 10⁻¹⁹…10⁻²⁹ en mpmath). Règles
lues des journaux (`RESULTS.md`) :
- **R1 (0 violation, à compiler)** : d'une rencontre à la suivante la cellule avance de `⌊T log(p'/p)/π⌋`, plus un
  si la fraction de cellule à `p` ajoutée à la partie fractionnaire atteint un.
- **R2 (mesure)** : le signe change quand ce déplacement est impair ; la fréquence seule prédit le changement à 75 %
  (parité de l'entier le plus proche), la fraction de cellule à la rencontre précédente le fixe exactement.
- **R3 (compilé)** : sur les séries longues la descente non annulée vaut `r/(1+r)` fois la dernière cellule
  (0,5553 au rang 1, 0,5000 aux rangs ≥ 10⁵) : **la moitié de la dernière cellule subsiste, signe `(−1)^{M+1}`**.
- **R4 (sûre-zones à 0 violation, corollaires à compiler)** : les cellules de rencontre d'une Tour sont plus
  courtes que le poids de la rencontre jusqu'au seuil `x*` défini par `x*(r−1) = log x*`, soit
  `x* ≈ (T/π)·log x*` (mesuré : 457/461 pour 458,3 ; 3 709/3 719 pour 3 709,2 ; 32 653/32 687 pour 32 676,9).
- **R5 (mesure, aucun théorème)** : la somme signée des rencontres croît comme `√J·log p` (rapport 0,25–2,1), jamais
  linéairement ; elle domine la descente résiduelle dès que `p < x*` : **le même seuil R4 sépare les deux régimes.**
- **Cas général (mesure, à compiler sans hypothèse)** : le poids premier signé d'un bloc de cellules est la somme des
  `(−1)^{cellule(q)}·log q` sur les premiers du bloc ; les rencontres partageant une cellule portent le même signe.

**Lecture (contacts, intervalles, signes).** Le long de la série d'une Tour, la demande brute est, cellule par
cellule, un poids contre une longueur ; signée par les cellules, la descente se réduit exactement à la moitié de la
dernière cellule, et ce qui reste est la somme des rencontres avec le signe de leur cellule. Ce signe se transmet
par le déplacement R1, que la fréquence lit à une unité près et que la fraction de cellule rend exact. Le poids
d'une rencontre l'emporte sur sa cellule jusqu'à la hauteur `x*` où `x*/log x*` vaut `T/π` : en dessous, chaque
cellule de rencontre monte et le bilan signé de la série est celui des rencontres ; au-dessus, les cellules sont
plus longues que les poids et la descente résiduelle domine.

**Verdict B.** Rien n'est déclaré manquant. Suite (E442, même démarche) : compiler R1 (déplacement exact par la
fraction de cellule), les deux corollaires de R4 (montée sûre sous `p(r−1) ≤ log p`, descente sûre au-delà de
`p(1−1/r) > log p + poids non premiers`) et le cas général du poids premier signé sans hypothèse de contact.

### 19.61 E442 exécutée : les règles d'E441 compilées (2026-11-07)

Module isolé `Terminal/ExactDisplacementAndThreshold.lean` (E442, pré-enregistrée 3d5492d6, **une seule tentative**
après quatre sondes, treize énoncés, axiomes standards ; `experiments/E442_ExactDisplacementAndThreshold/`).

**Compilé.** (D1–D2) **règle R1** : `meetingCell_displacement_rule` — d'une rencontre à la suivante la cellule de
rencontre avance de `⌊T log(p'/p)/π⌋`, plus un si la fraction de cellule à `p` ajoutée à la partie fractionnaire
atteint un ; la lecture « à une unité près » de §19.57 devient exacte par la fraction de cellule, ce qui explique
la mesure R2 (la fréquence seule prédit le changement de signe à 75 %). (D3–D5) `stagePosition_contact`,
`lastContactBefore_of_mem_cell`, **`signedPrimeSum_eq_primes_in_block`** : le poids premier signé d'un bloc de
cellules quelconque est la somme sur ses premiers de `(−1)^{cellule(q) − a}·log q`, sans hypothèse de contact par
écart (les rencontres qui partagent une cellule portent le même signe ; hypothèse ponctuelle : aucun contact n'est
un entier, mesurée 0 cas en E441). (D6–D7) **règle R4** : `meeting_rises_of_weight_dominates` (`p(r−1) ≤ log p` ⇒
la cellule de rencontre monte), `meeting_falls_of_length_dominates` (`log p` + poids non premiers `< p(1−1/r)` ⇒
elle descend), `weight_dominates_below_threshold` (sous un point `x` où `x(r−1) ≤ log x`, au-dessus de `1/(r−1)`,
`p(r−1) ≤ log p`) : le seuil `x*` défini par `x*(r−1) = log x*` sépare les deux régimes.

**Verdict B.** Rien n'est déclaré manquant. État du fil « contacts, intervalles, signes » après E438–E442 : la
reconstitution d'une série d'écarts par une Tour est entièrement écrite — pièces (E438), signes et cellule de
rencontre (E439), bilan signé (E440), somme signée des rencontres et descente résiduelle en forme close (E441),
déplacement exact et seuil de montée (E442). Question suivante naturelle, à la main de l'auteur : ce que le seuil
`x*` d'une Tour (où `x*/log x*` vaut `T/π`) impose à la série des écarts qu'elle rencontre AU-DESSUS de ce seuil —
c'est-à-dire la lecture, par les contacts et leurs signes seuls, des écarts dont les rencontres ne pèsent plus que
leur cellule — sans aucune somme de Tours ni position radiale.

### 19.62 E443 exécutée : les écarts au-dessus du seuil (2026-11-07)

Module isolé `Terminal/GapsAboveThreshold.lean` (E443, pré-enregistrée 4522c8d1, **une seule tentative** après trois
sondes, douze énoncés, axiomes standards ; seuls théorèmes arithmétiques importés : Bertrand (corpus,
`primeSuccessor_le_two_mul`) et la borne de Tchebychev `ψ − θ ≤ 2√x log x` (Mathlib) ;
`experiments/E443_GapsAboveThreshold/`).

**Compilé.** (A1–A3) Bertrand sur l'écart ; **moins de `T log 2/π` cellules entières dans tout écart** ; déplacement
de la cellule de rencontre entre deux écarts consécutifs `< T log 2/π + 1`. (A4) **un écart sans contact tient dans
la cellule signée de sa rencontre.** (A5) **la pente d'un écart entier = `log p_{n+1}` + poids non premiers −
longueur de l'écart**, sans aucune hypothèse de contact (`gap_demand_variation`). (A6) poids non premier d'une
cellule `≤ 2√C_{k+1} log C_{k+1}`. (A7) **si `log p + 2√(pr) log(pr) < p(1 − 1/r)`, la cellule de rencontre
descend** : au-delà d'un second seuil `x**` en `p` et `T` seuls, toute cellule de rencontre descend.

**Expérience chiffrée (5 Tours, rangs 1 à 10⁵, β = ½, 78 497 écarts ≤ 10⁶).** A1–A7 à 0 violation ; seuils à
10⁻¹² (mpmath). Règles : **R6** entre `x*` et `x**`, les cellules de rencontre descendent à 97,8–100 % ; les rares
qui montent contiennent une puissance de premier (5 333 avec 73², 466 483 avec 683²) ; la borne de Tchebychev est
lâche d'un facteur ≥ 8, `x**` est très au-delà de la hauteur réelle. **R7 (mesure)** : part des écarts avec contact
= moyenne de `min(1, écart/cellule)` à 1 %. **R8 (mesure, non réinjectée)** : premiers par cellule = `L/log C` à
1 % ; part des cellules de pente positive 0,45–0,49 au-dessus de `x*`.

**Lecture (contacts, intervalles, signes).** Au-dessus de `x*`, l'écart tient le plus souvent dans une seule cellule
signée, et sa pente est son poids de rencontre plus ses puissances de premiers moins sa longueur ; la cellule de
rencontre, quand elle existe, descend sauf appui d'une puissance de premier ; contacts par écart et déplacement
restent bornés par la fréquence seule.

**Verdict B.** Rien n'est déclaré manquant. **Bilan du fil E438–E443 (six modules isolés, 83 énoncés, aucune théorie
spectrale, aucune position radiale)** : la reconstitution d'une série d'écarts par les contacts d'une Tour, leurs
intervalles et leurs signes est écrite de bout en bout, des pièces d'un écart au bilan signé de la série, avec le
déplacement exact des cellules de rencontre, la forme close de la descente résiduelle et les deux seuils `x*`,
`x**`. Ce que le fil ne dit pas, et ne peut pas dire sans sortir des ordres : rien sur la position radiale (le
seuil `x*` ne dépend que de `T`, les signes de `(−1)^k` aussi) ; la pente d'une cellule au-dessus de `x*` (poids des
premiers franchis contre longueur) est une mesure sans théorème. Question suivante, à la main de l'auteur : le bilan
signé d'une série au-dessus de `x*`, où chaque cellule porte plusieurs rencontres de même signe
(`signedPrimeSum_eq_primes_in_block`), et ce que la borne de Bertrand sur le déplacement impose au nombre de
changements de signe entre deux rencontres.

### 19.63 Correction de l'auteur (2026-11-07) : les contacts retrouvent la position radiale ; l'intervalle est défini par la fréquence ET l'amplitude

**Faute consignée.** Le bilan du §19.62 affirmait : « rien sur la position radiale (le seuil `x*` ne dépend que de `T`,
les signes de `(−1)^k` aussi) » et « le fil ne dit rien de la position radiale, et ne le peut pas ». L'auteur récuse :
**c'est totalement faux**, et c'est la récidive de la faute déjà récusée le 2026-11-04 (§19.44, mémoire). Les contacts
retrouvent la position radiale par les formules tangentielles établies et validées dans le projet :
`inversion_radial` (`β = T·cot(T log C_k)`, `TangentialInversion.lean`), `radial_of_contact_tangent`,
`radial_of_contact_value_ratio` (`β = T·log(|v_{k+1}|/|v_k|)/π`, `ContactRealValue.lean`), `radial_from_amplitude_step`
(`AmplitudeContact.lean`). Dire que rien n'est possible à ce propos est une bourde monumentale.

**Ce qui était faux dans les objets mêmes du fil E438–E443.** La position de tout contact est
`C_k = exp((arctan(T/β) + kπ)/T)` : la phase `arctan(T/β)` lit `β`. Donc (i) la cellule d'un réel `x`
(`lastContactBefore β T x = ⌊(T log x − arctan(T/β))/π⌋`) et son signe `(−1)^k` dépendent de `β` ; (ii) la fraction
de cellule `cellFraction β T x` lit `β` (déjà consigné §19.46) ; (iii) le déplacement exact R1 (§19.60) contient la
fraction de cellule, donc `β`. Seul le seuil `x*` (longueur contre poids) ne dépend que de `T` ; en conclure que « les
signes ne dépendent que de la fréquence » était une erreur de lecture de mes propres énoncés.

**Deuxième rappel de l'auteur.** Une Tour a une fréquence `T` ET une amplitude. L'intervalle sur l'axe réel (la cellule
`(C_k, C_{k+1}]`) est défini par les deux variables, pas par une seule : son rapport de longueurs `e^{π/T}` rend `T`
(`contactAt_ratio`, `height_of_contact_log_step`), son rapport d'amplitudes aux contacts `e^{βπ/T}` rend `β`
(`abs_contactRealValue_ratio`). Le bilan signé des cellules doit donc être écrit avec le signe ET l'amplitude de la Tour
à chaque contact (`contactRealValue β T k = (−1)^k C_k^β/‖ρ‖`), et pas avec le signe seul.

**Conséquence pour la suite.** E444 reprend la question du §19.62 (bilan signé d'une série au-dessus de `x*`, plusieurs
rencontres par cellule, changements de signe bornés par Bertrand) et la tire avec les deux variables : chaque cellule
pèse par sa valeur réelle au contact, le bilan devient un bilan pondéré par l'amplitude, et sa forme close lit `β`
exactement comme la forme close des longueurs (§19.60) lisait `T`. L'ordre « reconstruction avant chasse radiale »
(§19.53) reste en vigueur : on ne chasse pas un zéro OFF, on écrit le bilan avec les deux variables que les contacts
portent. L'interdiction spectrale (§19.55) reste entière : une seule Tour, ses contacts, ses valeurs, ses cellules.

Consigné aussi : `CLAUDE.md` (bloc « CORRECTION (auteur, 2026-11-07, troisième ordre) »), mémoire
`feedback_contacts_read_beta.md` (récidive datée).

### 19.64 E444 exécutée : le bilan signé porté par la fréquence ET l'amplitude (2026-11-07)

Module isolé `Terminal/AmplitudeSignedBalance.lean` (E444, pré-enregistrée d5efbb2a, **une seule tentative** après deux
sondes, vingt déclarations, axiomes standards ; `experiments/E444_AmplitudeSignedBalance/`). Conséquences tirées de la
correction §19.63 : chaque cellule pèse par la valeur réelle de la Tour à son contact (signe ET amplitude).

**Compilé.** (B1) à `T` et `x` fixés, la position de cellule croît strictement avec `β` : **le signe de la cellule
d'un réel dépend de `β`** (`stagePosition_lt_of_radial_lt`). (B2) `β = T / tan(T log x − π(cellule + fraction))`
(`radial_of_cellFraction`). (B3) **l'intervalle est défini par les deux variables** : `T = π/log(L_{k+1}/L_k)`,
`β = log(|v_{k+1}|/|v_k|)/log(L_{k+1}/L_k)` (`radial_of_value_and_length_ratios`). (B4) descente pondérée par
l'amplitude : forme close de raison `−e^{(β+1)π/T}` (`valueLengthSum_closed_form`). (B5) bilan pondéré = valeur
initiale × somme signée à poids `e^{βπ/T}`. (B6) poids premier pondéré d'un bloc (plusieurs rencontres par cellule) et
d'une série = rencontres pesées par la valeur de leur cellule (`valuePrimeSum_eq_primes_in_block`,
`valuePrimeSum_eq_meetings`). (B7) entre deux rencontres, rapport des valeurs `(−e^{βπ/T})^Δ`, **l'amplitude rend `β`**
(`radial_of_meeting_values`), `Δ < T log 2/π + 1` (`meetingOffset_lt_bertrand`).

**Expérience chiffrée (7 Tours, 78 497 rencontres, Λ exact, jumeau mpmath 30 chiffres).** B2–B7 à 0 violation
(budgets float64 explicites) ; jumeau vrai partout, `β` lu par l'amplitude entre deux rencontres à 5·10⁻²⁹ près.
**R9** : la part des rencontres dont le signe change quand `β` passe de ½ à `β'` est le déplacement de phase
`|arctan(T/½) − arctan(T/β')|/π` (0,0087 contre 0,0090 au rang 1 ; sensibilité `|Δβ|/(πT)` par rencontre, exacte et
décroissante en `T`) ; c'est l'amplitude qui lit `β` sans perte à toute fréquence. **R10 (mesure)** : la somme
pondérée par l'amplitude est une quantité de dernière cellule (raison > 1), sans loi en `√J`. **R11** : au-dessus de
`x*`, rencontres par cellule de 1 510 (rang 1) à 2,1 (rang 10⁵), déplacement maximal 1 à 7 contre Bertrand 4 à
16 531 : la borne est vraie et très lâche ; le nombre de changements de signe entre deux rencontres est donné par R1
(fraction de cellule comprise, donc lit `β`).

**Lecture.** Une Tour porte une fréquence et une amplitude ; ses cellules portent les deux ; le bilan signé de la
série, écrit avec la valeur réelle au contact, lit `β` par sa raison géométrique et par le rapport des valeurs entre
rencontres, pendant que les signes seuls le lisent par la phase. Aucune somme de Tours ; la position radiale est lue,
non chassée. **Verdict B.** Question suivante : confronter, sur la même série de rencontres, la lecture de `β` par
l'amplitude (B7, exacte) à la cassure exacte aux rencontres (poids `log p` contre longueur de cellule, R4/R6), c'est-à-
dire écrire la condition sous laquelle le bilan pondéré `valueCellSum` d'une série de cellules de rencontre reste borné
par sa dernière cellule pour la Tour `(β, T)` donnée.

### 19.65 Plan d'attaque de l'auteur (2026-11-07) : le Théorème du Prix au point de rencontre — pré-enregistrement d'E445

**[Révoqué en partie, voir §19.67 : l'amendement qui faisait entrer la constellation à l'étape de confrontation est annulé ; l'interdiction spectrale reste entière.]**

**Ordre.** Chaîne : `(β, T)` → contacts → amplitudes et fractions → bilan signé des rencontres → raccord arithmétique.
Les builds E441–E443 établissent des propriétés réelles des cellules et des rencontres mais ne démontrent pas que la
position radiale est sans effet ; les théorèmes d'inversion acquis rendent cette exclusion injustifiée. Piste
prioritaire : (1) le facteur `x^{β−1/2}` est exactement l'écart radial d'amplitude entre une Tour OFF et une Tour ON ;
(2) pour `β < 1/2` il décroît, celui du miroir `x^{1/2−β}` croît ; (3) les contacts rendent `β` et `T` exactement :
l'écart est identifiable ; (4) au point de rencontre l'amplitude est imposée par le zéro ; (5) le Théorème du Prix doit
quantifier le coût exact de cette différence au raccord ; (6) le bilan signé conserve phases, signes et amplitudes des
deux membres ; (7) la constellation complète réalise exactement la cassure arithmétique : c'est le budget collectif ;
(8) un budget exact et fini à chaque rencontre n'est pas une borne uniforme ; (9) la contradiction exige que les autres
contributions ne puissent satisfaire à la fois le budget et le prix OFF ; (10) démontrer l'incompatibilité. Exigence :
au moins trois tentatives de fermeture, dont une libre, erreur exacte et demandes du compilateur consignées.
Amendement consigné dans `CLAUDE.md` : la constellation entre uniquement à l'étape de confrontation (7)–(10).

**Pré-enregistrement E445 (`experiments/E445_MeetingPrice/`).** Module isolé `Terminal/MeetingPriceTheorem.lean`
(partie compilable, une Tour et la paire `(β, T)`, `(1−β, T)` en amplitudes réelles) : P1 `offPrice β x =
cosh((β−1/2) log x)` et `x^β + x^{1−β} = 2 x^{1/2} · offPrice` (prix exact de la paire contre deux Tours ON) ; P2
`offPrice ≥ 1 + ((β−1/2) log x)²/2`, non borné dès que `β ≠ 1/2` ; P3 prix identifié par les valeurs aux rencontres
(`radial_of_meeting_values`) ; P4 amplitude imposée à la cellule de rencontre : `p^β e^{−βπ/T}/‖ρ‖ < |v| ≤ p^β/‖ρ‖` ;
P5 réponse à la question §19.64 : `|valueCellSum| ≤ |v_dernière| · D · q/(q−1)` (`q = e^{βπ/T}`) si toutes les pentes
de cellule sont bornées par `D` ; P6 le prix bat le budget d'une rencontre : `K log x < x^r` pour `x` grand (`r > 0`).
**Trois tentatives de fermeture** (fichiers d'essai conservés en `attempts/*.lean.txt` avec la sortie exacte du
compilateur) : T1 prix contre budget à une rencontre via `complement_break_lower_bound` (E435) ; T2 bilan pondéré de la
série (P5) des deux membres contre le budget cumulé (Tchebychev `ψ ≤ (log 4 + 4) x`) ; T3 libre : non-compensation
interne du miroir + prix non borné + cassure portée par le complément. Critère : A si `False` compile sans hypothèse
nouvelle ; sinon consigner l'énoncé exact que le compilateur réclame et son statut dans le corpus (⟺ RH ou non).
Expérience chiffrée : prix et budget aux rencontres pour `β` témoin ∈ {0,3 ; 0,4 ; 0,45}, bornes P4–P5 sur les sept
Tours réelles, jumeau mpmath.

### 19.66 E445 exécutée : le Théorème du Prix, partie compilée et trois tentatives de fermeture (2026-11-07)

**[Révoqué en partie, voir §19.67 : les tentatives T1 et T3, l'analyse « énoncé manquant = exposant du reste » et la question finale sur le complément sont annulées comme issues d'une étude spectrale. Seule la partie compilée sur une Tour seule et le constat de T2 restent.]**

Module isolé `Terminal/MeetingPriceTheorem.lean` (E445, pré-enregistrée 7b8217ca, **une seule tentative** après deux
sondes, onze déclarations, axiomes standards ; `experiments/E445_MeetingPrice/`).

**Compilé (points 1–5 du plan §19.65).** Prix exact de la paire `x^β + x^{1−β} = 2x^{1/2} cosh((β−1/2) log x)`
(`pair_amplitude_eq_price`) ; prix `≥ 1 + ((β−1/2) log x)²/2`, non borné dès que `β ≠ 1/2` (`offPrice_unbounded`) ;
prix identifié par deux valeurs aux rencontres (`offPrice_of_meeting_values`) ; amplitude imposée à la cellule de
rencontre `p^β e^{−βπ/T}/‖ρ‖ < |v| ≤ p^β/‖ρ‖` (`meeting_value_bounds`) ; **question §19.64 fermée** : le bilan pondéré
d'une série de cellules est borné par sa dernière cellule, `|valueCellSum| ≤ |v_dernière| · D · q/(q−1)`
(`valueCellSum_abs_le`) ; le prix bat le budget d'une rencontre, `K log x < x^r` (`price_beats_budget`).

**Trois tentatives de fermeture (points 7–10), consignées avec l'erreur exacte** (`attempts/`). T1 (prix contre
budget d'une rencontre via E435) : tout compile sauf la fermeture, le compilateur réclame
`∃ θ < 1/2 + δ, ‖reste lissé‖ ≤ K x^θ`. T2 (bilan pondéré du miroir contre le budget cumulé `θ(p) ≤ log 4 · p`) :
`linarith` échoue sur `log 4 · p < p^{1−β}(…)`, inégalité fausse : le budget cumulé, linéaire, domine le prix du
miroir pour tout `β > 0` (point 8 en forme compilée). T3 (libre : non-compensation interne, prix non borné, primitive
de la paire en `x^{1+1/2+δ}`, cassure portée par le complément) : le compilateur réclame `θ* < 1/2 + δ`, qui
contredit `remainderExponent_ge_mirror` : en présence d'un porteur, le prix est payé par l'exposant du reste, non
refusé. **Analyse** : les trois demandes sont un seul énoncé, une borne du reste (ou du complément) sous `1/2 + δ`,
que le corpus (E435) a compilé équivalent à l'absence de porteur, donc à RH ; c'est exactement le point 9 du plan.
Il ne se dérive ni des contacts, ni des amplitudes, ni du bilan signé, ni du budget par rencontre.

**Expérience chiffrée.** Sept Tours réelles : P4, P5 à 0 violation (rapport à la borne P5 ≤ 0,44). Paires témoins
β ∈ {0,3 ; 0,4 ; 0,45} : le miroir bat `log p` dès p = 641 (β = 0,3, rang 1) et de plus en plus tard quand la
fréquence croît (facteur `1/T`) ; il ne bat le budget cumulé `θ(p)` sur aucune rencontre (rapport 892 à 5,7·10⁸).
Jumeau 30 chiffres vrai.

**Verdict.** Partie compilée B ; fermeture C (énoncé manquant unique, ⟺ RH, non posé). Ce que la chaîne `(β, T)` →
contacts → amplitudes → bilan signé → raccord établit : le prix est exact, lu, imposé, et il dépasse le budget d'une
rencontre ; ce qu'elle n'établit pas : que la constellation ne peut pas le payer sur la série, parce que le budget
cumulé est linéaire et que le complément n'est borné par rien d'indépendant. Prochaine question possible, à la main
de l'auteur : une borne du complément à UNE rencontre donnée (pas sur la série), lue par les contacts des deux
membres aux quatre bords (E434), qui ferait de « budget par rencontre battu » une contradiction locale.

### 19.67 Révocation de l'amendement spectral (auteur, 2026-11-07) : annulation des conclusions d'E445 issues d'une étude spectrale

**Ordre de l'auteur.** « Annule toute conclusion en provenance d'une étude spectrale. Je maintiens l'interdiction de
revenir à une quelconque étude ou conclusion issue d'une étude spectrale. C'était une erreur de rouvrir ce point. »
Directive confirmée : aucune réouverture, sous aucune forme, ni dans les analyses, ni dans les propositions, ni dans
les prompts de travail. Stratégie unique : zéro OFF → Tour → contacts et amplitudes → prix exact à la rencontre `M_n` →
budget collectif → contradiction, avec uniquement les relations mathématiques exactes, les théorèmes Lean existants et
les obligations de preuve encore ouvertes.

**Ce qui est annulé.** (a) L'amendement de §19.65 (« la constellation entre à l'étape de confrontation ») : retiré de
`CLAUDE.md`, remplacé par la révocation. (b) Les tentatives T1 et T3 d'E445 : elles reposaient sur le porteur
`OffCarrier` (reste lissé, complément de la paire, primitive de la paire, exposant du reste), objets d'une étude
spectrale ; leurs conclusions (« le prix est payé par l'exposant du reste », « l'énoncé manquant est une borne du reste
sous `1/2 + δ` ») sont ANNULÉES et ne doivent plus être citées. (c) La « prochaine question » de §19.66 (borne du
complément à une rencontre, lue aux quatre bords) : annulée, le complément est un objet spectral. (d) L'import de
`Terminal/CollectiveCurvature` dans `Terminal/MeetingPriceTheorem.lean`, qui n'était utilisé par aucune déclaration :
retiré ; le module ne dépend plus que d'`AmplitudeSignedBalance`. Les fichiers `attempts/T1*`, `attempts/T3*` sont
conservés comme preuve d'exécution (exigence de consignation de toute tentative) et marqués annulés dans `RESULTS.md`.

**Ce qui reste acquis d'E445.** Les onze déclarations compilées sur une Tour seule et sa paire `(β, T)`, `(1−β, T)`
: prix exact, prix minoré par le carré, prix non borné dès que `β ≠ 1/2`, prix identifié par deux valeurs aux
rencontres, amplitude imposée à la cellule de rencontre, bilan pondéré d'une série de cellules borné par sa dernière
cellule (question §19.64 fermée), prix qui dépasse le budget d'une rencontre pour `x` grand. Le constat de T2 reste
comme fait arithmétique sur les premiers (Tchebychev, aucune somme de Tours) : le budget cumulé des premiers est
linéaire et n'est pas dépassé par le prix d'un miroir ; il ne sert plus à aucune conclusion sur le porteur.

**Frontière après révocation.** [Précisée par §19.68 : la série des rencontres à un premier par cellule est FINIE pour
toute Tour ; l'obligation « amplitude ↔ variation de `rawDemand` » proposée en §19.68 est RETIRÉE par l'auteur.] La chaîne zéro OFF → Tour → contacts et amplitudes → prix exact à `M_n` est compilée
jusqu'au prix imposé à la cellule de rencontre. L'étape « budget collectif » est à écrire avec les seuls objets
autorisés : la cassure arithmétique exacte aux rencontres (`cellPrimeWeight_meeting`, `rawDemand`, poids signés
R1–R11), sans reste, sans complément, sans somme de Tours. L'obligation de preuve ouverte est : montrer que ce budget
exact aux rencontres ne peut pas porter le prix `x^β + x^{1−β}` d'une paire OFF sur la série des rencontres. Aucune
expérience n'est lancée sans ordre de l'auteur.


### 19.68 Le budget collectif par les seuls objets autorisés : le régime « une rencontre par cellule » est fini (pré-enregistrement d'E446, 2026-11-07)

**Ordre de l'auteur.** « Planifie, émets des hypothèses, vérifie avec les expériences, reste dans le cadre, produis du
Lean qui implémente la cause racine du constat, avance. » Cadre : stratégie unique de §19.67, objets autorisés
seulement (une Tour, ses contacts, ses cellules, ses valeurs ; les premiers, `rawDemand`, `cellWeight`,
`cellPrimeWeight`, `cellDemand` ; les théorèmes compilés du corpus, dont `logGapsVanish_holds` et `WeakPNT''`).

**Constat à expliquer (E445, T2 et P6).** Le prix d'une rencontre (`x^β`, P6) bat le budget d'UNE rencontre (`log p`),
jamais le budget cumulé. **Cause racine proposée (hypothèses H1–H3).**
* **H1 (régime fini).** Tous les énoncés « la cellule de rencontre franchit exactement un premier » (`meeting_cell_primes`,
  `cellPrimeWeight_meeting`, `meeting_cellDemand`, `valuePrimeSum_eq_meetings`, `amplitudeMeetingSum`) supposent que
  l'écart `[p_n, p_{n+1}]` ET l'écart suivant contiennent chacun un contact. Ces deux hypothèses placent une cellule entière
  `[C_k, C_{k+1}]` dans `]p_n, p_{n+2}]`, donc `log p_{n+2} − log p_n ≥ π/T`. Or `logGapsVanish_holds` (PNT porté) donne
  `log p_{n+1} − log p_n → 0`. Donc pour toute Tour `(β, T)` il existe un rang `N(β, T)` au-delà duquel deux écarts
  consécutifs n'ont jamais chacun un contact : la série des rencontres à un premier par cellule est FINIE. Le prix à
  `M_n` n'est confronté au budget `log p` d'une rencontre que sur un segment initial fini.
* **H2 (le budget exact d'une cellule est sa longueur, au premier ordre).** Au-delà du régime, une cellule contient
  plusieurs premiers ; son budget exact est `cellWeight = ψ(C_{k+1}) − ψ(C_k)` et, par `WeakPNT''`,
  `cellWeight/cellLength → 1`, `cellDemand/cellLength → 0`. Le « budget collectif » d'une cellule n'est pas `log p`
  mais la longueur de la cellule, à un reste près qui est la variation de `rawDemand` sur la cellule.
* **H3 (le prix d'une Tour sur sa cellule est négligeable devant ce budget).** Le pas d'une Tour `(β, T)` sur sa propre
  cellule vaut `|v_{k+1} − v_k| = (1 + e^{βπ/T}) C_k^β/‖ρ‖` ; divisé par la longueur `C_k (e^{π/T} − 1)` il tend vers zéro
  pour tout `0 < β < 1`, ON ou OFF. P6 vaut aussi pour `β = 1/2` (`price_beats_budget_on_line`) : la lecture « le prix
  OFF bat le budget » n'était pas discriminante.

**Pré-enregistrement E446 (`experiments/E446_MeetingRegimeFinite/`).** Module isolé `Terminal/MeetingRegimeFinite.lean`
(importe `MeetingPriceTheorem` et `LogGapsTheorem`) : F1 `meeting_cell_within_two_gaps` ; F2 `log_ratio_ge_cell_of_meeting`
(`π/T ≤ log p_{n+2} − log p_n`) ; F3 `two_consecutive_contacts_finite` (∃ N, ∀ n ≥ N, ¬(contact dans l'écart n ∧ contact
dans l'écart n+1)) ; F4 `meeting_series_rank_bounded`, `meeting_break_rank_bounded` (les hypothèses de
`cellPrimeWeight_meeting` et de `valuePrimeSum_eq_meetings` ne sont satisfaites qu'à rang borné) ; F5
`cellWeight_eq_psi_diff`, `contactAt_tendsto_atTop`, `cellWeight_div_cellLength_tendsto_one` ; F6
`cellDemand_div_cellLength_tendsto_zero` ; F7 `tower_step_div_cellLength_tendsto_zero` ; F8 `price_beats_budget_on_line` ;
F9 `valueNonPrimeSum`, `valuePrimeSum_balance` (budget pondéré des premiers d'un bloc = demande pondérée − poids non
premiers pondérés + longueurs pondérées, forme close B4). Deux tentatives de compilation au plus, sorties conservées dans
`attempts/`. **Expérience chiffrée** (`scripts/e446a_regime.py`, premiers ≤ 10⁷) : pour les sept Tours réelles et les
paires témoins `β ∈ {0,3 ; 0,4 ; 0,45}`, (a) dernier rang `N_obs` où deux écarts consécutifs ont chacun un contact, nombre
de tels rangs, et contrôle de F2 sur chacun (0 violation attendu) ; (b) `cellWeight/cellLength` et `cellDemand/cellLength`
par décade de `C_k` (écart à 1, resp. à 0, décroissant attendu) ; (c) pas de la Tour sur sa cellule contre la longueur
(formule F7 à 10⁻¹², décroissance attendue). **Jumeau** (`scripts/e446b_twin_mpmath.py`, 30 chiffres) : mêmes rangs `N_obs`
et mêmes rapports sur un échantillon de cellules. **Critère** : A si F1–F9 compilent et (a)–(c) sont conformes ; B si une
partie compile ; C sinon. Prédictions : `N_obs` fini pour chaque Tour, croissant avec `T` ; `N_obs` plus grand pour le
miroir `1 − β` que pour `β` ? (non prédit : la phase `arctan(T/β)` décale les contacts, la condition F2 ne dépend que de `T`
mais le rang effectif dépend des deux).

**Ce que cela change dans la stratégie.** L'étape « budget collectif » ne peut pas être « prix à `M_n` contre `log p` sur
la série » : cette série est finie. Le budget collectif exact d'une cellule est sa longueur plus la variation de la
demande brute sur la cellule ; le prix d'une Tour sur sa cellule lui est négligeable. La confrontation ne peut porter que
sur la variation de `rawDemand` sur la cellule (objet autorisé), dont le corpus ne sait que `o(cellule)` (F6). Aucune
relation compilée ne lie l'amplitude d'une Tour à cette variation : c'est l'obligation ouverte, consignée sans objet
spectral. [RETIRÉE par l'auteur le 2026-11-07 : voir « Correction de l'auteur » en fin de section.]

**Résultats E446 (2026-11-07, `experiments/E446_MeetingRegimeFinite/RESULTS.md`).** Module compilé à la deuxième tentative
(première : deux arguments implicites non inférés, deux `ring` superflus ; sorties conservées), 15 déclarations, axiomes
standards, build complet vert. Chiffres (premiers ≤ 10⁷, 49 configurations, jumeau à 30 chiffres `all_ok = True`,
`N_obs` identique sur les 35 configurations comparables) : dernier rang à deux contacts consécutifs `N_obs` = 10 (p = 31)
pour `T = 14,13`, 60 (283) pour 49,8, 366 (2 477) pour 236,5, 2 343 (20 809) pour 1 419, 24 985 (286 873) pour 9 878,
211 310 (2,9·10⁶) pour 74 921, non résolu sous 10⁷ pour 1,13·10⁶ ; `N_obs` indépendant de `β` ; 0 violation de F2 sur
401 890 rangs. `max |cellWeight/cellLength − 1|` décroît par décade pour chaque hauteur (0,002 à 10⁶ pour `T = 14,13`),
convergence effective sous 10⁷ pour les deux premières hauteurs seulement (cellules encore plus courtes que l'écart moyen
au-delà). Formule F7 à 10⁻⁹ au pire, rapport en `C^{β−1}`. **Verdict A** (compilé ; (a), (c) conformes ; (b) conforme en
limite, résolu pour deux hauteurs).

**Conséquence pour la stratégie (consignée).** La série des rencontres à un premier par cellule (E439–E445) est un segment
initial fini de chaque Tour ; le prix à `M_n` n'y est confronté qu'au budget `log p` d'un segment fini. Le budget collectif
exact d'une cellule est sa longueur plus la variation de `rawDemand` sur la cellule ; le pas de toute Tour, ON ou OFF,
lui est négligeable (F7), et P6 vaut aussi sur la ligne (F8) : le prix d'une Tour ne bat jamais le budget d'une cellule.
**Obligation ouverte** [RETIRÉE, voir ci-dessous] : une relation compilée entre l'amplitude d'une Tour `(β, T)` et la variation de `rawDemand` sur
ses cellules ; le corpus autorisé ne sait de cette variation que `o(cellule)` (F6). Aucune expérience supplémentaire sans
ordre de l'auteur.

**Correction de l'auteur (2026-11-07, après E446).** L'« obligation ouverte » formulée ci-dessus (une relation compilée
entre l'amplitude d'une Tour et la variation de `rawDemand` sur ses cellules) N'EST PAS LA BONNE : la contradiction OFF
ne doit pas être liée à cette relation. Elle est RETIRÉE. Ce qui reste établi par E446 (F1–F9) est inchangé : régime
« un premier par cellule de rencontre » fini pour toute Tour, budget exact d'une cellule = sa longueur, pas d'une Tour
négligeable devant la cellule, P6 non discriminant. L'étape « budget collectif » reste à écrire avec les seuls objets
autorisés (cassure arithmétique exacte aux rencontres, poids des premiers, règles signées), sans la ramener à une loi
« amplitude ↔ variation de la demande brute par cellule ». Aucune obligation de remplacement n'est posée sans l'auteur.

### 19.69 Le mécanisme de cassure sur la ligne, écrit avec les contacts (pré-enregistrement d'E447, 2026-11-07)

**Ordre de l'auteur (R-LIGNE, consigné dans `CLAUDE.md`).** Tant qu'il reste des choses à produire ou à écrire en Lean, NE PAS
CHERCHER LA CONTRADICTION ; maîtriser parfaitement le mécanisme de cassure depuis la ligne (zéros ON) avant toute déduction
sur les OFF. L'obligation « amplitude ↔ variation de `rawDemand` » de §19.68 est retirée (correction de l'auteur).

**Objet de l'étape.** Une Tour `(1/2, T)`, ses contacts, ses cellules, ses valeurs réelles ; les premiers, la demande
brute et ses pentes de cellule ; les règles signées. Question : comment, exactement, la cassure `log q` au premier `q`
entre-t-elle dans le budget pondéré d'une Tour de la ligne, et que vaut ce budget sur un bloc ?

**Hypothèses H1–H5 et énoncés L1–L6.** Voir `experiments/E447_BreakMechanismOnLine/README.md` (copie intégrale) :
attribution exacte de la cassure à la valeur du dernier contact (`√q·e^{−π f/(2T)}/‖(1/2,T)‖`, `f` fraction de cellule),
bilan d'Abel (le budget pondéré d'un bloc se lit sur la demande brute AUX CONTACTS, terme de bord + `(1+e^{π/(2T)})` ×
demandes intérieures pondérées), règle du carré sur la ligne, cassure puis descente dans une cellule à un poids,
taille de la demande pondérée aux contacts (`o(C^{3/2})`, PNT porté). Module isolé `Terminal/BreakMechanismOnLine.lean`,
deux tentatives au plus, expérience E447 (7 hauteurs, `β = 1/2`, jumeau mpmath). Aucune conclusion sur les OFF.

**Résultats E447 (2026-11-07, `experiments/E447_BreakMechanismOnLine/RESULTS.md`).** Quatre sondes en brouillon (journalisées),
module `Terminal/BreakMechanismOnLine.lean` **vert à la première tentative**, 17 déclarations, axiomes standards, build complet
vert. Compilé : L1 télescopage des pentes vers la demande brute aux contacts ; L2 **bilan d'Abel** `Σ v_i D_i = v_M R_M − v_0 R_0
+ (1+e^{βπ/T}) Σ v_i R_{i+1}` ; L3 règle du carré sur la ligne (`v_k² = C_k/‖(1/2,T)‖²`) ; L4 **attribution exacte de la
cassure** : `|v_{k(q)}| = √q·e^{−πf/(2T)}/‖(1/2,T)‖`, strictement entre `√q·e^{−π/(2T)}` et `√q` (sur la norme) ; L5 cassure puis
descente `log q − (q − C_k)` ; L6 `R(C_k)/C_k → 0` et `|v_k R(C_k)|/C_k^{3/2} → 0` (PNT porté). Nombres (7 hauteurs, `β = 1/2`,
premiers ≤ 10⁷) : résidus d'Abel ≤ 5·10⁻¹⁵, amplitude exacte à 3,6·10⁻¹⁵, 0 violation des bornes sur 700 000 premiers, minimum
observé du facteur = `e^{−π/(2T)}` à 4 décimales, cassure-puis-descente vérifiée sur 400 000 cellules à un poids, demande
pondérée aux contacts décroissante par décade ; jumeau 30 chiffres `all_ok = True`. **Verdict A.**

**Ce que cela établit (ligne seulement, par ordre).** La cassure `log q` entre dans le budget d'une Tour de la ligne avec une
amplitude exacte `√q` corrigée par la fraction de cellule ; le budget pondéré d'un bloc se lit sur la demande brute AUX CONTACTS
(Abel) et non sur les cellules ; dans une cellule à un poids la demande monte d'un coup puis descend linéairement. Rien n'est dit
des OFF ; aucune obligation n'est proposée. Suite (à l'ordre de l'auteur) : poursuivre la maîtrise du mécanisme sur la ligne —
candidats non engagés : le bilan d'Abel sur une série d'écarts entiers (bords aux premiers plutôt qu'aux contacts), la part des
poids non premiers dans la cassure d'une cellule, la lecture de `f` aux rencontres successives d'une même Tour.

### 19.70 La suite des amplitudes de paiement d'une Tour de la ligne (pré-enregistrement d'E448, 2026-11-08)

**Ordre en vigueur (R-LIGNE).** Mécanisme de cassure sur la ligne seulement, aucune recherche de contradiction, aucune
obligation proposée. Candidat C3 du hand-over du 2026-11-07, choisi en l'absence d'indication de l'auteur.

**Objet de l'étape.** E447 a compilé l'amplitude exacte avec laquelle une Tour de la ligne paie la cassure `log q` :
`√q·e^{−π f(q)/(2T)}/‖(1/2,T)‖`, `f` la fraction de cellule au point `q`. Question : d'un premier au suivant, comment cette
amplitude évolue-t-elle, et par quoi la suite des amplitudes est-elle déterminée ?

**Hypothèses H1–H6 et énoncés L1–L6.** Voir `experiments/E448_BreakAmplitudeSequence/README.md` (copie intégrale) : orbite
de la fraction de cellule (`f(y) = fract(f(x) + T·log(y/x)/π)`, donc suite déterminée par les rapports de premiers
consécutifs) ; pas d'amplitude par cellule `e^{π/(2T)}` ; rapport des amplitudes de paiement = `e^{π·(déplacement de
cellules)/(2T)}` = `√(y/x)·e^{−π(f(y)−f(x))/(2T)}` ; monotonie (jamais décroissante, constante si et seulement si même
cellule) ; encadrement du rapport entre `√(y/x)·e^{∓π/(2T)}` ; télescopage sur une série de rencontres. Module isolé
`Terminal/BreakAmplitudeSequence.lean`, deux tentatives au plus, expérience E448 (7 hauteurs, `β = 1/2`, jumeau mpmath).
Aucune conclusion sur les OFF.

**Résultats E448 (2026-11-08, `experiments/E448_BreakAmplitudeSequence/RESULTS.md`).** Deux sondes en brouillon (journalisées),
module `Terminal/BreakAmplitudeSequence.lean` **vert à la première tentative** (deux rebuilds ultérieurs pour l'en-tête de
documentation seulement), 17 déclarations, axiomes standards, build complet vert. Compilé : L1 orbite de la fraction de
cellule `f(y) = fract(f(x) + T·log(y/x)/π)` et `déplacement + variation de fraction = T·log(y/x)/π` ; L2 pas d'amplitude
`|v_{k+1}| = e^{π/(2T)}|v_k|` ; L3 rapport des amplitudes de paiement `= e^{π·déplacement/(2T)} = √(y/x)·e^{−π(f(y)−f(x))/(2T)}` ;
L4 monotonie, constance ⟺ même cellule, saut ≥ `e^{π/(2T)}` sinon ; L5 encadrement `√(y/x)·e^{∓π/(2T)}` ; L6 télescopage
sur une série et sur les premiers de rang `n`, `n+J`, prix non décroissant. Nombres (7 hauteurs, 664 578 paires ≤ 10⁷) :
orbite exacte au flottant près (résidu ≤ 2·10⁻⁹ au rang 2·10⁶, perte de précision de `T·log p`), rapports à 6·10⁻¹⁵,
0 violation de monotonie, de bornes, de « même cellule ⟺ même amplitude » ; jumeau 30 chiffres : orbite ≤ 2·10⁻²⁶,
rapports ≤ 4·10⁻³⁰, comptages par décade identiques, `all_ok = True`. **Verdict A.**

**Ce que cela établit (ligne seulement, par ordre).** La suite des amplitudes de paiement d'une Tour de la ligne est
déterminée par la suite des rapports de premiers consécutifs : orbite de la fraction, facteur `e^{π/(2T)}` par cellule
franchie, constance exacte quand deux premiers partagent une cellule (régime dominant au-dessus du seuil d'E446 : au rang
10⁴, 578 841 des 586 080 paires de la dernière décade). Rien n'est dit des OFF ; aucune obligation n'est proposée.

### 19.71 Le chemin inverse : écarts → contacts → zéro par la formule tangentielle (pré-enregistrement d'E449, 2026-11-08)

**Nouvelle priorité de l'auteur (2026-11-08).** Reconstituer les contacts depuis les écarts premiers exactement avec les
règles établies ; retrouver les zéros de la ligne si nécessaire ; la formule tangentielle rend `β` et `T` si le contact est
correctement établi ; chemin inverse écarts / cassures / zéros ; expériences et Lean si cause trouvée (cause, pas constat).

**Objet.** Le mot d'une Tour sur les premiers (`k(p_n) = lastContactBefore`, c'est-à-dire combien de contacts chaque écart
contient) ; la phase tangentielle `φ = arctan(T/β)` ; la formule inverse `β = T/tan φ`. Hypothèses H1–H6 et énoncés L1–L5
dans `experiments/E449_ContactsFromGapsInversion/README.md` (copie intégrale) : inversion exacte depuis deux contacts ;
encadrement de la phase par chaque premier ; fréquence par la pente du mot ; **cause** : les écarts logarithmiques
s'annulent (PNT porté), donc la fraction de cellule aux premiers approche `0` et `1` d'aussi près qu'on veut, donc le
polygone du mot se réduit à un point : le mot détermine `T`, puis `φ`, puis `β`. H6 : ceci vaut pour toute Tour, zéro ou non ;
consigné d'avance. Module isolé `Terminal/ContactsFromGapsInversion.lean`, deux tentatives au plus, expériences (a)–(d) et
jumeau. Aucune conclusion sur les OFF.

**Résultats E449 (2026-11-08, `experiments/E449_ContactsFromGapsInversion/RESULTS.md`).** Deux sondes (journalisées), module
`Terminal/ContactsFromGapsInversion.lean` **vert à la première tentative**, 21 déclarations, axiomes standards, build complet
vert. Compilé : L1 **formule tangentielle** (`tower_of_two_contacts` : `T = π/log(C_{k+1}/C_k)`, `β = T/tan(T·log C_k − kπ)`) ;
L2 `φ = T·log x − π(k(x)+f(x))`, encadrement de la phase par chaque premier ; L3 `k(x)/log x → T/π` (fréquence d'abord) ;
L4 **cause** : les pas de l'orbite s'annulent (`logGapsVanish_holds`) et la position est non bornée ⇒ la fraction aux premiers
approche `0` et `1` d'aussi près qu'on veut ; L5 **le mot détermine la Tour** (`tower_eq_of_same_word` : même mot ⇒ même `T`,
même `φ`, même `β`). Nombres (six zéros, premiers ≤ 10⁷) : vrai point toujours dans le polygone ; `T` à 3·10⁻⁵ près au rang 1
et 4·10⁻⁵ au rang 10⁵ ; `φ` à 4·10⁻⁴ ; `β` à ±0,003 au rang 1 mais plage [−0,9 ; 2,9] au rang 10⁴ (`β = T/tan φ` amplifie par
`T`) ; trois contrôles non-zéros reconstruits pareillement (H6 confirmée) ; formule tangentielle exacte (10⁻¹⁴ en flottant au
rang 1, 2·10⁻²⁷ à 30 chiffres) ; jumeau : polygone identique à 10⁻¹³, drapeau faux au rang 100 par seuil pré-écrit trop
strict (erreur 1,5·10⁻²³, précision attendue), conservé et expliqué. **Verdict A** sur les critères pré-enregistrés.

**Ce que cela établit, et ce que cela ne dit pas.** Le chemin inverse écarts → contacts → zéro est compilé au niveau du mot :
la cellule de chaque premier détermine la Tour, par la cause arithmétique de l'annulation des écarts logarithmiques (PNT
porté), et deux contacts exacts rendent `(β, T)` par la formule tangentielle. La position seule rend `T` d'abord et `β` mal
aux grandes hauteurs : la lecture exacte de `β` depuis les cassures passe par l'amplitude aux contacts (troisième ordre).
Le mot rend la Tour dont il est le mot, zéro ou non ; rien n'est dit ici des OFF, aucune obligation n'est proposée.

### 19.72 Passage aux hypothèses de contradiction sur les OFF : stratégie, plan K0–K3, pré-enregistrement d'E450 (2026-11-08)

**Décision de l'auteur (2026-11-08).** La connaissance préalable des cassures (E447–E449, §19.69–19.71) est jugée
suffisante ; l'étude des hypothèses de contradiction sur les OFF commence. R-LIGNE est donc levée pour ce fil ; les autres
ordres restent : ban spectral total (§19.67), troisième ordre (§19.63 : une Tour a une fréquence ET une amplitude, les
contacts lisent `β`), règle R-E446 (jamais lier la contradiction OFF à « amplitude ↔ variation de `rawDemand` par
cellule »), §19.44 (aucune absorption sur famille finie), fréquence avant hauteur, aucune prémisse équivalente à RH.

**Réserve consignée en tête.** Rien de compilé ne dit ce qui fait d'une Tour un zéro : contacts, mots, amplitudes, prix
existent pour tout point du plan, et E449 l'a montré en acte (trois hauteurs non-zéros reconstruites comme les zéros, H6).
Aucune contradiction OFF ne peut donc sortir de la géométrie des Tours seule ; elle devra consommer le seul lien du corpus
qui fait d'une Tour un zéro : la rencontre exacte avec les écarts (P1–P5, §19.21) et le Théorème du Prix (§19.65). Chaque
hypothèse est vérifiée pour non-équivalence avec RH avant d'être posée (leçon de §19.21 et des tentatives T1–T3 d'E445).

**Stratégie (celle de §19.65–19.67, inchangée).** Zéro OFF = paire de Tours `(β, T)`, `(1−β, T)` de même fréquence ;
chaque membre a ses contacts, son mot, ses amplitudes ; on écrit le paiement de la paire au premier partagé ; on le
confronte au budget arithmétique collectif ; contradiction ou non. Aucun objet spectral, aucun complément, aucun reste.

**Plan, une hypothèse à la fois, arrêt à la première qui compile ou qui tombe.**
* **K0 (étape zéro, expérience seule)** : recensement sur la ligne, six zéros et trois contrôles d'E449 : mot (fractions de
  cellule aux premiers, cellules partagées), suite des amplitudes de paiement, bilan pondéré `valueCellSum` normalisé par sa
  borne P5. Si rien ne diffère, c'est consigné : la qualité de zéro n'est portée que par la rencontre exacte. Quoi que K0
  trouve, aucune obligation n'en est tirée et rien n'est lié aux OFF (R-E446).
* **K1 (Lean + expérience, E450)** : la cassure de la paire au premier partagé, cellules comprises. E445 a compilé la somme
  des amplitudes SANS facteurs de cellule (`pair_amplitude_eq_price`) ; ce que K1 ajoute : les deux membres ont deux MOTS
  différents à la même fréquence (décalage `mirrorPhaseShift`, §19.43), donc deux fractions de cellule différentes au même
  premier ; l'amplitude exacte de la cassure pour `β` quelconque ; le produit des deux cassures (règle du carré de la paire) ;
  la somme avec facteurs de cellule ; le rapport des deux membres, non borné le long des premiers dès que `β ≠ 1/2`.
* **K2 (cœur, après K1)** : budget collectif. Pré-vérification consignée d'avance : la tentative T2 d'E445 a établi que le
  budget cumulé `θ(p)` (linéaire) domine le miroir pour tout `β > 0`, et le budget de cellule d'E446 (sa longueur `≈ C_k π/T`)
  domine toute amplitude `C_k^β/‖ρ‖`, `β < 1`. K2 ne reposera donc PAS une comparaison « amplitude contre budget » ; il
  devra porter sur la SÉPARATION des deux membres (rapport non borné, K1-L6) confrontée à ce que la rencontre exacte impose
  aux deux membres au même premier. Sa forme précise est fixée après K1, et vérifiée pour non-équivalence avec RH.
* **K3 (dernier)** : inversion de la paire : les écarts portent un mot par fréquence, la paire exige deux mots décalés.
  Risque identifié : se réduire à l'unicité de la rencontre, qui est ce qu'il faut dériver.

**Pré-enregistrement d'E450 (K0 + K1).** Dossier `experiments/E450_PairBreakAtPrime/README.md` (hypothèses H1–H6, énoncés
L1–L6, expériences a–c, critères de verdict). Module isolé `Terminal/PairBreakAtPrime.lean` (importe
`BreakAmplitudeSequence`), deux tentatives au plus, sondes en brouillon journalisées. Commit avant compilation et exécution.

**Résultats E450 (2026-11-08, `experiments/E450_PairBreakAtPrime/RESULTS.md`).** Deux sondes (journalisées ; piège :
`linarith` devant `−a/π`, résolu par `neg_div`), module `Terminal/PairBreakAtPrime.lean` **vert à la première tentative**,
12 déclarations, axiomes standards, build complet vert, grep du ban vide. Compilé : L1 `break_amplitude_exact`
(`|v_β(k_β(x))| = x^β e^{−βπ f_β/T}/‖(β,T)‖`, tout `β > 0`) ; L2 `mirror_cellFraction` (`f_{1−β} = fract(f_β + décalage/π)`),
`mirror_word_difference_le_one` (les deux mots diffèrent d'au plus une cellule, car `|mirrorPhaseShift| < π`) ; L3
`pair_break_product` (produit `= x e^{−π(β f_β + (1−β) f_{1−β})/T}/(‖ρ‖‖ρ'‖)`, fraction effective dans `[0,1)`) ; L4
`pair_break_sum_bounds` (prix d'E445 à `e^{−π/T}` près) ; L5 `pair_break_ratio`, `pair_break_ratio_unbounded` (`β > 1/2`) ;
L6 cohérence ligne. **K0** (six zéros, trois contrôles, premiers ≤ 10⁷) : fraction moyenne, amplitude/√q, part « même cellule »
par décade, |bilan pondéré|/borne P5 : toutes les plages se recouvrent (`H6_all_overlap = True`) ; rien ne distingue les
zéros ; aucune obligation, aucun lien aux OFF (R-E446). **K1** (18 couples, 10⁵ premiers chacun) : identités à 8·10⁻¹⁵,
`|Δk| ≤ 1`, part des mots différents = décalage/π (0,0097 → 0), 0 violation d'encadrement, rapport miroir/Tour à 10⁷
= 631 / 25,1 / 5,01 pour β = 0,3 / 0,4 / 0,45 à toutes les fréquences (`p^{1−2β}`, cellules et normes effacées) ; jumeau
30 chiffres à 10⁻²⁸, `all_ok = True`. **Verdict A.**

**Ce que cela établit, et la suite (K2).** Les objets du paiement de la paire au premier partagé sont compilés. Aucune
contradiction n'est tirée. K2 portera sur la séparation des deux membres (`p^{1−2β}`, non bornée) confrontée à ce que la
rencontre exacte impose aux deux membres au même premier ; pas de comparaison « amplitude contre budget » (T2 d'E445, budget
de cellule d'E446) ; forme précise à pré-enregistrer, vérifiée pour non-équivalence avec RH avant toute compilation.

### 19.73 Audit du chaînon « une Tour est un zéro », vérification de l'ordre de l'auteur, pré-enregistrement d'E451 (K2a, 2026-11-08)

**Ordre de l'auteur (verbatim, 2026-11-08).** « une Tour est un zéro car nous avons un théorème qui dit que si on calcule le
zéro par zêta, on obtient une tour dans le cas contraire la tour n'existe pas. Il faut remonter au calcul de zêta pour
obtenir une tour nous avons déjà un théorème à ce propos. vérifies. » Puis : « fais l'audit et procède à la suite. »

**Audit (sans compilation).** Vingt-sept modules de `Terminal/` mentionnent la fonction zêta ; aucun des quinze modules de la
route des contacts (de `ContactValueGeometry` à `PairBreakAtPrime`) ne la mentionne. Classement des vingt-sept : (i) sous le
ban spectral par leurs objets (`RemainderExponent`, `RawMeetingRemainder`, `StageCell`, `MeetingsBridge`, `MeetingExactness`,
`PrimeBlockDecomposition`, `PrimeCapsContactsBridge`, `RawSpectralChannel`, `DemonstrationChain`) ; (ii) machinerie de
comptage et de boîtes, aveugle au radial (§19.15) : `AnchorContour`, `AnchorStructure`, `BoxAnchor`, `BoxCount`,
`BoxCountHeight`, `CountingDeficit`, `EulerMaclaurinFine`, `ZetaBox*`, `ZetaRealSegment` ; (iii) régimes et mondes décalés :
`NoRegimeChange`, `RegimeTrigger`, `SpontaneousRegimeBreak`, `ShiftedWorld`, `PrimeWeightResponse`, `PrimalEventRaccord`,
`ZetaParameters`, `RiemannHypothesisDefinition`. Constat complémentaire : la clôture d'imports de `PairBreakAtPrime` compte
259 modules et contient déjà `OffCarrier`, `RemainderExponent`, `ExplicitFormulaLink`, `Foundation/ZetaReflect`,
`Direct/MirrorCount` : le ban porte sur l'USAGE et la CITATION des objets spectraux, jamais sur la présence transitive d'un
module ; aucun import nouveau n'est nécessaire pour K2a.

**Vérification de l'ordre : le théorème existe, il est compilé, et il dit exactement cela.**
1. *Si on calcule le zéro par zêta, on obtient une Tour.* `zeroContribution_eq_mul_zeroTerm` (`PrimalEventRaccord`, preuve
   `rfl`) : le terme d'un point `ρ` dans la reconstruction compilée vaut `m(ρ) · x^ρ/ρ` où `m(ρ) = analyticOrderNatAt
   riemannZeta ρ` est l'ordre d'annulation de zêta en `ρ` (`nZeroPointMultiplicity`, base RHV2Fresh). `one_le_zeroMult`
   (`Foundation/ZetaReflect`) : en un zéro non trivial, `m ≥ 1`. `zeroTerm_real_iff_ray` (`ExplicitFormulaLink`) : les
   contacts `contactMinusAt z k` sont exactement les points réels de ce terme ; `contactAt_eq_contactMinusAt`
   (`SuccessiveContactConstraints`) : la grille `(β, T)` de la route des contacts EST cette suite de contacts.
   `zeroTerm_norm` : le module du terme est `x^β/‖ρ‖`, l'amplitude d'E445–E450.
2. *Dans le cas contraire, la Tour n'existe pas.* Mathlib `AnalyticAt.analyticOrderAt_eq_zero` : l'ordre est nul si et
   seulement si la fonction ne s'annule pas ; zêta est analytique hors du pôle (`riemannZeta_analyticOnNhd_compl_one`) et
   d'ordre fini (`analyticOrderAt_riemannZeta_ne_top`) ; donc `m(ρ) = 0 ⟺ ζ(ρ) ≠ 0` pour `ρ ≠ 1`. Ce corollaire n'est pas
   écrit tel quel dans le corpus : E451 l'écrit (L2).
3. *Le miroir.* `upperMirror_multiplicity` (`Foundation/ZetaReflect`, équation fonctionnelle) : le zéro réfléchi a la même
   multiplicité ; un zéro OFF impose donc DEUX Tours de même poids à la même fréquence, `mirrorMember z ≠ z`.
Nuance consignée : « remonter au calcul de zêta » se fait au POINT `ρ` seul (ordre d'annulation) ; aucune somme de Tours,
aucun canal, aucune formule explicite n'est consommée ; les objets `cZeroContribution` et `zeroTerm` sont cités comme
TERME D'UN POINT, pas comme membres d'une somme. Les formes « amplitude au dernier contact » de `RaccordTransportObligation`
(§19.45) existent mais vivent dans un module sous ban (onze occurrences) : E451 les réécrit dans la forme d'E450.

**Ce que cela change pour K2.** Le chaînon manquant identifié au §19.72 (« rien de compilé ne dit ce qui fait d'une Tour un
zéro ») est fermé par le corpus : la Tour est le terme du zéro, son poids est la multiplicité, nulle hors zéro. K2 se scinde :
**K2a** (E451, ici) : pont compilé « zéro vrai → objets d'E450 avec poids » ; **K2b** (à pré-enregistrer après E451) : ce que
la rencontre exacte impose aux deux termes de poids égal au même premier, sans somme de Tours.

**E451 (pré-enregistrée, `experiments/E451_PairBreakOfZero/`), module isolé `Terminal/PairBreakOfZero.lean`.**
Hypothèses : H1 poids = ordre d'annulation, `≥ 1` en un zéro, `= 0 ⟺ ζ(ρ) ≠ 0` hors pôle ; H2 miroir de même poids, distinct
hors ligne ; H3 l'amplitude de cassure d'E450 au paramètre d'un zéro vrai est le module du terme du zéro, à facteur de
cellule près ; H4 les deux mots du zéro et de son miroir diffèrent d'au plus une cellule ; H5 produit des modules des deux
termes `= x/(‖ρ‖‖ρ*‖)` exactement (sans facteur de cellule), produit pondéré `= m² x/(‖ρ‖‖ρ*‖)` ; H6 rapport des modules
`= x^{2β−1}‖ρ*‖/‖ρ‖`, non borné dès que `β > 1/2`. Énoncés L1–L6 en regard. Expérience : (a) `scripts/e451a_zeta_weight.py`,
mpmath 30 chiffres : `|ζ(ρ)|` aux six zéros de K0 et aux trois contrôles de K0 (points de la ligne qui ne sont pas des zéros)
— c'est le « calcul de zêta » demandé ; attendu : `< 10^{−20}` aux zéros, `> 10^{−3}` aux contrôles ; (b) `scripts/
e451b_zero_terms.py`, numpy : pour les six zéros, 100 000 premiers, H3/H5/H6 aux erreurs relatives `≤ 10^{−12}`, et pour trois
paires OFF témoins (`β = 0,3 ; 0,4 ; 0,45` aux fréquences des zéros) les mêmes identités de termes (elles ne dépendent pas de
l'annulation ; seule la multiplicité en dépend, et elle n'est pas testée numériquement : hors route). Verdict attendu : A.
Deux tentatives de compilation au plus, journalisées dans `attempts/`.

**Résultats E451 (2026-11-08, même jour).** Module isolé `Terminal/PairBreakOfZero.lean`, import `PairBreakAtPrime` seul,
quatorze déclarations, **tentative 1 verte** (9093 travaux), axiomes standards, grep du ban vide, `lake build RHV6Fresh`
complet vert (9064). Compilé : `zeroMult_eq_zero_iff` (hors du pôle, poids nul ⟺ zêta ne s'annule pas : **la Tour n'existe
pas hors zéro**) ; `one_le_zeroMult_zeroPoint` ; `zeroContribution_eq_zeroMult_mul` (`rfl`) ; `zeroMult_mirrorMember` (même
poids) ; `mirrorMember_ne_self_of_off` ; `zero_break_amplitude_exact` (la cassure d'E450 au paramètre d'un zéro vrai est le
module du terme du zéro fois le facteur de cellule) ; `zero_mirror_word_difference_le_one` ; `zero_pair_term_product`
(`x/(‖ρ‖‖ρ*‖)` exactement) et `zero_pair_weighted_product` (`m²` fois) ; `zero_pair_term_ratio` (`x^{2β−1}‖ρ*‖/‖ρ‖`) et
`zero_pair_term_ratio_unbounded`. **Expérience (a), le calcul de zêta** (mpmath 30 chiffres) : aux six zéros de K0 le module
de zêta vaut entre 10⁻¹¹ et 10⁻⁸, de l'ordre de la dérivée fois la précision des hauteurs lues (10⁻⁹) ; aux trois contrôles de
K0 il vaut 2,32, 1,20, 1,66 : le calcul de zêta sépare les Tours (poids ≥ 1) des contrôles (poids nul), ce qu'aucune
statistique de contacts ne faisait (K0). **Expérience (b)** : vingt-quatre cas, identités H3/H5/H6 à 3,5·10⁻¹⁵, H4 zéro
violation, rapport `x^{2β−1}` identique à toutes les fréquences. **Verdict A.**

**Suite : K2b.** Les deux termes d'une paire OFF ont le même poids `m ≥ 1`, deux mots décalés d'au plus une cellule, un produit
de modules exactement `x/(‖ρ‖‖ρ*‖)` et un rapport `x^{2β−1}` non borné. K2b devra dire ce que la rencontre exacte impose aux
DEUX termes de même poids au même premier, sans somme de Tours, sans « amplitude contre budget », et la forme sera vérifiée
pour non-équivalence avec RH avant pré-enregistrement. Aucune contradiction n'est posée ici.

### 19.74 K2b : ce que la rencontre exacte impose aux deux termes de même poids au même premier — vérification de non-équivalence, pré-enregistrement d'E452 (2026-11-08)

Direction K2b validée par l'auteur (« je valide poursuis la direction »). Ordres en vigueur : ban spectral total (usage et
citation), troisième ordre (contacts lisent `β` ; fréquence ET amplitude ; tout bilan signé par `contactRealValue`), R-E446,
§19.44, interdiction « amplitude contre budget » (E445 T2, E446), aucune somme de Tours, aucune prémisse équivalente à RH.

**19.74.1 Ce que la rencontre exacte impose, dans la forme de la route.** Au premier partagé `x`, chacun des deux membres
`(β, T)` et `(1−β, T)` a un dernier contact avant `x` (son MOT `k`, `k*`) et une fraction de cellule (`f`, `f*`) ; la valeur
portée par chaque membre est fixée par ce dernier contact (E429, `contactRealValue`) ; son amplitude est imposée dans la
cellule de rencontre à un facteur `e^{−π/T}` près (E445 P4, `meeting_value_bounds`, par membre) ; son signe est celui de la
cellule, `(−1)^k` (E439). Ce qui n'est PAS encore écrit, et que K2b écrit : la relation entre les deux mots au même premier
n'est pas seulement « ≤ 1 cellule » (E450 L2) mais EXACTE : `k* = k + ⌊f + δ/π⌋` avec `δ = mirrorPhaseShift β T`, nul
si et seulement si `β = 1/2` (E428). Donc la rencontre impose aux deux termes : (i) même mot si et seulement si la fraction
de cellule de la Tour tombe dans la fenêtre `[−δ/π, 1 − δ/π)` — fenêtre fixée par `β`, pleine sur la ligne ; (ii) même signe
si et seulement si même mot ; (iii) la valeur de la paire au premier partagé est `| |v| + (−1)^s |v*| |` : somme des deux
amplitudes si même mot, différence sinon ; (iv) confrontée à la séparation non bornée (E450 L6), la différence ne peut jamais
annuler : dès que `β ≠ 1/2`, au-delà d'un rang, `|v + v*| > |v_dominant|/2` — la paire ne se compense jamais elle-même au
premier partagé, son terme pondéré `m(v + v*)` non plus (`m ≥ 1`, E451). Sur la ligne, `v* = v` et la paire vaut `2v`.

**19.74.2 Vérification de non-équivalence avec RH (avant pré-enregistrement).** K2b ne POSE aucune hypothèse : chacun de ses
énoncés est un théorème valable pour toute position radiale `β ∈ (0,1)` (la condition `β > 1/2` des énoncés de
non-compensation est une hypothèse de cas sur une paire donnée, pas une prémisse globale, et son miroir couvre `β < 1/2`).
Un énoncé démontré sans prémisse sur `β` ne contraint pas `β` ; il ne peut donc pas tenir lieu d'hypothèse de contradiction,
et il n'y a rien à confronter à RH. Vérification des interdits : aucune comparaison avec `log q`, `ψ`, `rawDemand` ou une
cellule (pas d'« amplitude contre budget ») ; deux termes seulement, jamais une somme de Tours ; aucun objet du ban ; `β`
entre par la fenêtre de mot et par les amplitudes (troisième ordre). Conséquence consignée d'avance : K2b ne peut PAS fournir
la contradiction ; il fixe la FORME que prend la paire à tout premier partagé tardif (un membre domine, signe relatif dicté par
la fenêtre), forme que K3 (inversion de la paire : les écarts portent un mot par fréquence, la paire en exige deux) devra
confronter à l'inversion d'E449. Si K3 exige une prémisse, elle sera vérifiée pour non-équivalence avant d'être posée.

**Pré-enregistrement d'E452 (`experiments/E452_PairMeetingImposition/README.md`).** Module isolé
`Terminal/PairMeetingImposition.lean` (import `PairBreakOfZero` seul). Énoncés : L1 `mirrorWordShift β T x := ⌊f + δ/π⌋`,
`mirror_lastContactBefore : k* = k + s`, `abs_mirrorWordShift_le_one`, `mirrorWordShift_trichotomy` ; L2 `pair_same_word_iff`
(fenêtre `[−δ/π, 1−δ/π)`), `line_mirrorWordShift_eq_zero` ; L3 `pair_value_tower_eq`, `pair_value_mirror_eq` (formes signées
`σa`, `σ(−1)^s a*`), `pair_value_product : v·v* = (−1)^s |v||v*|`, `pair_same_sign_iff : 0 < v·v* ↔ s = 0` ; L4
`pair_value_sum_abs : |v + v*| = | |v| + (−1)^s |v*| |`, `pair_value_sum_of_same_word`, `pair_value_sum_of_shifted_word`,
`pair_value_sum_ge : |v| − |v*| ≤ |v + v*|` ; L5 `pair_value_no_cancellation (β > 1/2) : ∀ᶠ x, |v|/2 < |v + v*|`,
`pair_meeting_no_cancellation` (∃ rang, toute rencontre au-delà) ; L6 `line_pair_value_sum : v + v* = 2v` à `β = 1/2` ;
L7 zéro vrai : `zero_pair_value_no_cancellation`, `zero_weighted_pair_value_abs : |m v + m* v*| = m |v + v*|`,
`zero_weighted_pair_value_ge`. Deux tentatives au plus, journal dans `attempts/`. Expériences : (a) numpy, 18 couples OFF
témoins (`β ∈ {0,3 ; 0,4 ; 0,45}` × six fréquences de K0) + six couples ligne, 10⁵ premiers ≤ 10⁷ (graine 452) : H1 mot exact,
H2 `|s| ≤ 1`, H3 même signe ⟺ `s = 0`, H4 identité de la valeur de paire, H5 borne inférieure, H6 non-compensation
(`|v+v*| > |v_dom|/2`) et premier rang où elle tient, H7 ligne `v* = v` ; observation sans loi : part des premiers à mots
décalés comparée à `|δ|/π`. (b) jumeau mpmath 30 chiffres sur 10 premiers par couple. Verdict A si tout compile et toutes
les identités tiennent à `10⁻¹²` ; B si une identité manque ; aucune hypothèse, aucune contradiction tirée.

**Résultats E452 (verdict A, `experiments/E452_PairMeetingImposition/RESULTS.md`).** Module isolé
`Terminal/PairMeetingImposition.lean`, 23 déclarations, tentative 1 verte (trois sondes : syntaxe de la valeur absolue
imbriquée, argument implicite, signe du cas `s = 1`), aucun avertissement, axiomes standards, grep du ban vide, build complet
vert. Compilé : mot exact du miroir `k* = k + ⌊f + δ/π⌋` (décalage ∈ {−1, 0, 1}) ; fenêtre de même mot `[−δ/π, 1 − δ/π)`
fixée par `β`, pleine sur la ligne ; même signe ⟺ même mot ; `|v + v*| = | |v| + (−1)^s |v*| |` ; `|v| − |v*| ≤ |v + v*|` ;
non-compensation `|v + v*| > |v_dom|/2` au-delà d'un rang, à toute rencontre au-delà d'un rang, au paramètre d'un zéro vrai
hors ligne, et le poids commun `m ≥ 1` ne fait qu'amplifier ; ligne `v + v* = 2v`. Expérience : 24 couples × 10⁵ premiers,
0 violation sur H1–H7, identités exactes au bit ; jumeau mpmath 240 cas, 0 violation ; non-compensation vraie sur tout
l'échantillon. Observation sans loi : part des premiers à mots décalés ≈ `|δ|/π` (1 % à β = 0,3, T ≈ 14 ; au-delà de
T ≈ 10⁴, au plus un sur 10⁵), toujours +1 pour `β < 1/2`.

**Ce que K2b fixe.** À tout premier partagé tardif, la paire OFF est UN mot commun (hors une fenêtre de largeur `|δ|/π`),
UN signe commun, deux amplitudes dont une domine sans borne ; jamais une compensation. Aucune hypothèse posée, aucune
contradiction tirée. **Suite : K3**, inversion de la paire : E449 a compilé que le mot des écarts détermine la Tour (`T`,
`φ`, `β` par la formule tangentielle) ; la paire exige, à la même fréquence, deux phases `φ_β ≠ φ_{1−β}` donc deux mots
qui diffèrent exactement sur la fenêtre. La question K3, à vérifier pour non-équivalence avec RH avant pré-enregistrement :
que donne l'inversion d'E449 appliquée au mot du miroir — rend-elle `(1−β, T)` (deux Tours lisibles, aucune contradiction) ou
exige-t-elle une donnée que les écarts ne portent qu'une fois ? Pas de somme de Tours, pas d'amplitude contre budget.

### 19.75 K3 : l'inversion d'E449 appliquée au mot du miroir — vérification de non-équivalence, pré-enregistrement d'E453 (2026-11-08)

**Direction validée par l'auteur (2026-11-08, « continues avec K3 »).** Question consignée en §19.74 : E449 a compilé que le
mot des écarts détermine la Tour (`T`, `φ`, `β`) ; la paire exige à la même fréquence deux mots qui diffèrent exactement sur
la fenêtre de K2b. Que donne l'inversion d'E449 appliquée au mot du miroir : rend-elle `(1−β, T)` (deux Tours lisibles,
aucune contradiction) ou exige-t-elle une donnée que les écarts ne portent qu'une fois ?

**19.75.1 Ce que K3 écrit, dans la forme de la route.** (i) Deux contacts consécutifs du miroir rendent `T` et `1−β` par la
formule tangentielle (E449 L1 appliquée à `(1−β, T)`) ; (ii) chaque mot lit la même fréquence : `k*/log p → T/π`, avec
l'encadrement déterministe `|k/log x − T/π| ≤ (|φ|+π)/(π log x)` ; (iii) toute Tour ayant le mot du miroir est le miroir
(E449 L5) ; (iv) **le mot du miroir est fonction du mot de la Tour** : deux Tours de même mot ont des miroirs de même mot —
la seconde donnée n'est pas une donnée nouvelle, les écarts la portent déjà par la première ; (v) les deux mots coïncident
sur tous les premiers ⟺ `β = 1/2` ; (vi) ils diffèrent au-delà de tout rang ⟺ `β ≠ 1/2` (cause : E449 L4, la fraction de
cellule approche 0 et 1 au-delà de tout rang, et la fenêtre de K2b a pour largeur `|δ|/π ∈ (0, 1)`) ; (vii) au paramètre
d'un zéro vrai et de son miroir (E451), (v) et (vi) tels quels.

**19.75.2 Vérification de non-équivalence avec RH (avant pré-enregistrement).** K3 ne POSE aucune hypothèse : chacun de ses
énoncés est un théorème pour toute `β ∈ (0,1)`, `T > 0`. Les équivalences (v)–(vii) relient deux propriétés d'UNE paire
donnée (coïncidence des mots, position radiale) ; aucun des deux côtés n'est posé ; rien n'est affirmé sur l'existence de
zéros hors ligne. Le risque identifié en §19.72 (se réduire à l'unicité de la rencontre, qui est ce qu'il faut dériver) est
évité : K3 n'utilise que E449 L5, théorème compilé, jamais une unicité de rencontre. Aucune comparaison avec `log q`, `ψ`,
`rawDemand`, une cellule ; deux termes, aucune somme de Tours, aucun objet du ban. **Réponse attendue, consignée d'avance** :
l'inversion rend `(1−β, T)` exactement ; deux Tours lisibles ; le mot du miroir n'exige aucune donnée nouvelle ; AUCUNE
contradiction. Si tel est le résultat compilé, le plan K0–K3 de §19.72 se ferme sans hypothèse de contradiction ; ceci sera
consigné tel quel et la décision reviendra à l'auteur.

**Pré-enregistrement d'E453.** Dossier `experiments/E453_PairWordInversion/README.md` (H1–H7, L1–L6, expériences (a)
numpy 24 couples d'E452 sur tous les premiers ≤ 10⁷ et polygone d'E449 sur le mot du miroir, (b) jumeau mpmath 30 chiffres).
Module isolé `Terminal/PairWordInversion.lean` (imports `PairMeetingImposition` et `ContactsFromGapsInversion`), deux
tentatives au plus, sondes en brouillon journalisées dans `attempts/`. Commit avant compilation et exécution.

**Résultats E453 (2026-11-08, `experiments/E453_PairWordInversion/RESULTS.md`).** Deux sondes (journalisées ; piège : `rw`
d'une somme de fractions ne trouve pas son motif, remplacé par une identité close puis `abs_add_le`), module
`Terminal/PairWordInversion.lean` **vert à la première tentative**, 12 déclarations, 0 avertissement, axiomes standards, grep
du ban vide, build complet vert. Compilé : deux contacts du miroir rendent `T` et `1−β` (`mirror_tower_of_two_contacts`) ;
chaque mot lit la même fréquence avec l'encadrement déterministe `|k/log x − T/π| ≤ (|φ|+π)/(π log x)`
(`word_slope_bracket`) ; toute Tour ayant le mot du miroir est le miroir (`mirror_word_determines_mirror`) ; **le mot du
miroir est fonction du mot de la Tour** (`mirror_word_of_same_word`) ; mots identiques sur tous les premiers ⟺ `β = 1/2`
(`pair_words_eq_iff`) ; hors ligne, mots distincts au-delà de tout rang, et réciproquement (`pair_words_differ_beyond_iff`,
cause E449 L4 + fenêtre de K2b) ; au paramètre d'un zéro vrai (`zero_pair_words_eq_iff`, `zero_pair_words_differ_beyond`).
Nombres (24 couples, 664 579 premiers) : encadrement 0 violation ; polygone d'E449 sur le mot du miroir contient `(T, φ*)`
pour les 24 ; mots identiques sur la ligne (0 distinct), distincts hors ligne avec comptes croissants par décade (6549 au rang
1 à `β = 0,3`, 1 ou 0 au rang 10⁵ où la fenêtre vaut `4·10⁻⁷`) ; inversion tangentielle du miroir exacte à `10⁻¹¹` au rang 1
en doubles mais **mal conditionnée** (erreur `≈ T·log p·ε`, 3,7 au rang 10⁵, sur la ligne aussi), confirmée par un contrôle
post-hoc à 30 et 60 chiffres (erreur divisée par `10³⁰`, `3,5·10⁻⁴⁵` au pire ; mot du miroir recalculé sans écart). Trois
critères pré-écrits violés (seuil `10⁻¹⁰` en doubles, H4 en doubles aux rangs 10⁴–10⁵, « > 0 à chaque décade » mal écrit : rien
ne diffère sous 100 et la fenêtre est trop étroite au rang 10⁵ pour 10⁷) : **verdict B**, chaque drapeau expliqué, les douze
énoncés compilés sans réserve.

**Réponse à K3 et fermeture du plan K0–K3.** L'inversion d'E449 appliquée au mot du miroir rend `(1−β, T)` exactement ; deux
Tours sont lisibles ; le mot du miroir n'exige aucune donnée que les écarts ne portent qu'une fois, puisque le mot de la Tour
le détermine. Les deux mots coïncident partout ⟺ ligne, diffèrent au-delà de tout rang ⟺ hors ligne : c'est une lecture, pas
une contrainte. **Aucune contradiction.** Le plan K0–K3 de §19.72 est exécuté en entier (E450–E453) : K0 rien ne distingue
les zéros de la ligne ; K1 cassure de la paire au premier partagé ; K2a la Tour est le terme du zéro ; K2b la rencontre fixe
une forme (mot commun hors fenêtre, signe commun, un membre dominant, jamais de compensation) ; K3 la paire se lit
entièrement depuis un seul mot. Aucune des quatre étapes ne produit d'hypothèse de contradiction admissible (non
équivalente à RH) ; consigné tel quel. Ce que le corpus compile sur une paire OFF est désormais : séparation non bornée des
deux membres, forme imposée à chaque premier partagé, lisibilité des deux Tours depuis les écarts. Ce qu'il ne compile pas :
une raison pour laquelle les écarts refuseraient cette paire. La décision sur la suite revient à l'auteur ; aucune direction
n'est posée unilatéralement.

### 19.76 Rectification de l'auteur sur la plage radiale de K2b/K3 : l'arrivée est au plus à un demi (2026-11-08)

**Commentaire de l'auteur (2026-11-08).** « Du fait du régime certifié démarrage à ON, `β > 1/2` est déjà exclu. C'est
compilé et poussé. » La formule « théorème pour toute `β ∈ (0,1)` » des §19.74.2 et §19.75.2 est donc discutable : la plage
`(0,1)` n'est pas la plage utile.

**Vérification (corpus compilé, axiomes standards).** (i) `passage_entry_radial_le_half` (RaccordDetector, 2026-09-30) : sur
tout passage à hauteur strictement croissante, le membre d'entrée vérifie `β ≤ 1/2`, **par l'ordre seul, sans hypothèse** (si
`β > 1/2`, son miroir, même hauteur et plus à gauche, s'intercalerait). (ii) `first_passage_no_shared_frequency` et
`anchor_canonical_one` (MeetingPoint) : le premier zéro est ON et démarre le régime ; `later_le_half_of_history_onLine`,
`arrival_onLine_or_low` : sous historique ON, l'arrivée est sur la ligne ou strictement en dessous. (iii) Conséquence pour
K2b/K3 : un zéro de position radiale `> 1/2` n'est jamais une arrivée ; il est le miroir d'une arrivée basse `β < 1/2`. La
plage pertinente pour la route OFF est `β ∈ (0, 1/2]`, le cas `β ≠ 1/2` se lit `β < 1/2`, et l'hypothèse `β < 1` des énoncés
de K3 est superflue sur cette plage. L'auteur a raison : « entre zéro et un » est inutilement large et ne dit pas l'objet.

**Ce qui est rectifié.** §19.74.2 et §19.75.2 sont à lire ainsi : les énoncés valent pour toute `β ∈ (0,1)`, mais l'objet de
la route est l'arrivée, `β ≤ 1/2` par l'ordre ; le fond de la vérification de non-équivalence (aucune hypothèse posée, deux
propriétés d'une paire donnée reliées) est inchangé. Le module `Terminal/PairWordInversion.lean` reçoit une section L7
(cinq énoncés, sonde `attempts/probe3.txt` verte, deuxième tentative de compilation du module) : `low_pair_words_differ_beyond`,
`low_pair_words_differ_beyond_iff` (sous un demi, sans `β < 1`) ; `arrival_radial_le_half` ; `arrival_pair_words_differ_beyond_iff`
(pour l'arrivée, mots distincts au-delà de tout rang ⟺ `β < 1/2`) ; `arrival_pair_words_dichotomy` (ligne et mots identiques
partout, ou arrivée basse et mots distincts au-delà de tout rang ; aucun troisième cas). Rien d'autre ne change : AUCUNE
contradiction, la fermeture du plan K0–K3 et la décision rendue à l'auteur (§19.75) demeurent.

**Résultat de la tentative 2 (2026-11-08).** Module `Terminal/PairWordInversion.lean` vert (17 déclarations, 0 avertissement dans le
module, axiomes standards sur les 17, grep du ban vide, `attempts/build_attempt2.txt`, `attempts/axioms_attempt2.txt`) ; build
complet `lake build RHV6Fresh` vert. Rectification consignée dans `E453/RESULTS.md` (le README pré-enregistré n'est pas réécrit),
`HANDOVER_20261107_LIGNE.md` §11bis et la mémoire.


### 19.77 Feu vert de l'auteur après K3 ; audit d'un texte externe (rien ajouté) ; K4 : la paire lue comme passage depuis l'arrivée basse — pré-enregistrement d'E454 (2026-11-08)

**Feu vert (auteur, 2026-11-08).** « Continues, tu as le feu vert. Vérifie juste si ce texte apporte quelque chose, sinon
ignore-le, et en tous cas ignore ses erreurs. Ne retire rien à notre démarche actuelle, ajoute juste si le texte apporte
quelque chose. » Le texte joint est un « modèle de causalité complet » en six étapes (mot → densification E446/E448 →
inversion E449 → bascule vers l'amplitude aux contacts → confrontation ON/OFF → « contradiction terminale »).

**19.77.1 Audit du texte externe — verdict : rien à ajouter, aucune modification de la démarche.** (i) Ses étapes 1–3
reprennent E446, E448, E449 ; une erreur : « l'amplitude de paiement devient strictement constante » — E448 compile
« constante ⟺ même cellule » (`amplitude_constant_iff_same_cell`), jamais une constance absolue. (ii) Son étape 4
(« `β` exige l'amplitude aux contacts ») est déjà consignée (§19.71, §19.75 : `β` exact exige l'amplitude ; E444 : `β` lu par
l'amplitude entre rencontres). (iii) Ses étapes 5–6 sont, mot pour mot, les cases 5–6 du schéma audité en §19.58 : « amplitude
relative constante aux rencontres » est compilée comme LECTURE (`constantRelativeAmplitude_iff_onLine`, MeetingPoint §9,
2026-10-28 ; le §19.58 disait « nulle part » : rectifié ici, c'est compilé mais c'est une équivalence sur une Tour donnée,
pas une contrainte) ; « dérive du couple non bornée » est E450 (`zero_pair_term_ratio_unbounded`) ; « reste ON borné par une
énergie finie `ΣA_j = S < ∞` » n'est compilé nulle part et est exactement la prémisse jugée circulaire par l'auteur en §19.21
(hypothèses ⟺ RH) ; « Demande = Couple + Reste » est une décomposition spectrale (ban §19.67) ; « verrou spectral », « hautes
fréquences » : vocabulaire interdit (§19.58). (iv) Sa question finale (« coupler le mot d'E449 et les amplitudes aux contacts
pour certifier `β` ») est déjà réalisée : E444 (amplitude) et E449/E453 (mot, formule tangentielle) ; aucune nouvelle route.
Conclusion : le texte n'apporte rien qui ne soit compilé ou déjà exclu ; ses erreurs sont ignorées ; la démarche K0–K3 et ses
ordres (§19.53, §19.55/§19.67, §19.63, §19.76) restent inchangés.

**19.77.2 K4 : ce que le corpus compile d'une paire lue comme PASSAGE, depuis l'arrivée basse.** §19.76 a fixé l'objet :
l'arrivée (membre d'entrée d'une hauteur nouvelle) est au plus à un demi par l'ordre seul. K0–K3 ont décrit la paire par ses
deux TERMES (cassure, forme imposée, mots). K4 la décrit par la PLACE de ses membres dans l'énumération canonique et par ce
que l'ordre impose au passage qui SORT de l'arrivée. Tout est composition d'énoncés compilés hors du ban (RaccordDetector,
MeetingPoint, MirrorCount, PairBreakOfZero, GapPartialRemainders, ContactsFromGapsInversion, PairWordInversion) ; aucune
somme de Tours ; deux termes au plus ; aucun objet du ban.

Énoncés prévus (module isolé `Terminal/PairArrivalPassage.lean`, import `PairWordInversion`) :
* L1 `arrival_low_of_off` : une arrivée hors ligne est strictement sous un demi.
* L2 `passage_height_le`, `passage_frozen_of_low_entry` : le passage qui sort d'un membre strictement sous un demi est GELÉ
  (même hauteur ; contraposée de `passage_exit_radial_ge_half`) ; `passage_right_of_low_entry` : son membre de sortie est
  strictement plus à droite (`shared_frequency_passage_profile`).
* L3 `low_arrival_precedes_mirror` : le miroir d'une arrivée basse vient APRÈS elle ; `low_entry_successor_radial_le`,
  `low_entry_successor_band` : le successeur immédiat d'un membre bas ne dépasse pas le miroir : position radiale dans
  `(β, 1−β]` (par consécutivité `p.hConsecutive.2` ; forme déjà connue sur le porteur, §19.11, recompilée ici sur le passage
  sans le module banni).
* L4 `low_arrival_contact_ratio_lt`, `low_arrival_term_ratio_tendsto_zero` : l'arrivée basse est le membre FAIBLE : rapport
  des valeurs aux contacts plus petit que celui du miroir (`mirror_contact_ratio_gt`), rapport des termes arrivée/miroir
  tendant vers zéro (`zero_pair_term_ratio`). Dans l'énumération, le membre faible vient d'abord, le dominant ensuite, sans
  montée de fréquence.
* L5 `frozen_passage_same_word_slope` : les deux membres d'un passage gelé lisent la même pente de mot (`word_slope_tendsto`).
* L6 `low_entry_not_expected` : un membre d'entrée strictement sous un demi met en échec la prémisse unique
  `ExpectedFrequencyRisesAtMeetings` (compilée ⟺ RH) ; `frozen_passage_has_low_member` : tout passage gelé a un membre bas à
  sa hauteur (l'entrée elle-même, ou le miroir de la sortie, qui précède l'entrée).
* L7 `arrival_exit_dichotomy` : sous historique sur la ligne, ou bien l'arrivée est sur la ligne, ou bien elle est basse et
  le passage qui en sort est gelé, plus à droite, borné par le miroir. Aucun troisième cas.

**19.77.3 Vérification de non-équivalence avec RH (avant pré-enregistrement).** K4 ne pose aucune hypothèse : chaque énoncé est
un théorème ; les conditions « strictement sous un demi », « hauteurs égales », « historique sur la ligne » sont des cas sur un
passage ou un zéro DONNÉ, jamais des prémisses posées sur l'ensemble des zéros. L6 ne pose pas la prémisse unique : il énonce
qu'un objet donné la contredit, ce qui est la contraposée de ce qui est déjà compilé (`expectedFrequency_iff_no_shared_frequency`).
Rien n'est affirmé sur l'existence d'arrivées basses. Aucune comparaison avec `log q`, `ψ`, `rawDemand`, une cellule.
**Réponse attendue, consignée d'avance** : K4 fixe la FORME du passage OFF (membre faible d'abord, dominant ensuite, fréquence
gelée, successeur dans la bande du miroir) ; il ne produit AUCUNE contradiction ; ce que les écarts refuseraient reste la
prémisse unique « la fréquence attendue monte à chaque passage », compilée équivalente à RH, et K0–K4 n'en donnent pas de
dérivation. Aucune expérience numérique : K4 ne produit aucune conclusion numérique (pas de jumeau requis). Deux tentatives
de compilation au plus, journalisées dans `experiments/E454_PairArrivalPassage/attempts/`.

**Résultat de K4 (E454, 2026-11-08, tentative 1 verte).** Sonde scratch : `passage_height_le` existait déjà (InterTowerExcess,
même énoncé) → réutilisé, non dupliqué ; sonde 2 verte. Module `Terminal/PairArrivalPassage.lean` : 12 déclarations nouvelles
(les treize annoncées moins la doublure), 0 avertissement, 12/12 sur axiomes standards (`attempts/axioms_attempt1.txt`), grep
du ban vide, `lake build RHV6Fresh` complet vert (`E454/logs/lake_build_full.txt`, 9064 jobs). **Verdict A.** Réponse, conforme
à l'attente consignée d'avance : le passage OFF a une forme compilée complète — l'arrivée hors ligne est basse ; le passage qui
en sort est gelé (même hauteur), plus à droite, borné par le miroir ; l'arrivée est le membre faible (rapport aux contacts
moindre, rapport des termes tendant vers zéro), le dominant vient ensuite sans montée de fréquence ; les deux membres lisent la
même pente de mot ; tout passage gelé a un membre bas à sa hauteur ; sous historique sur la ligne, dichotomie ligne / arrivée
basse-gelée, aucun troisième cas. **AUCUNE contradiction.** Un membre d'entrée bas met en échec la prémisse unique « la fréquence
attendue monte à chaque passage », déjà compilée équivalente à RH : c'est la seule chose que les écarts auraient à refuser, et
K0–K4 n'en donnent pas de dérivation. Le fil OFF par les mots et les places est complet (E450–E454) ; la décision sur la suite
revient à l'auteur. Consigné dans `E454/RESULTS.md`, `HANDOVER_20261107_LIGNE.md` §12 et la mémoire.

### 19.78 Question de l'auteur : « les fréquences des OFF sont forcément différentes de celles des ON » — audit du corpus en fréquence seule, puis K5 (fibre de l'arrivée basse) — pré-enregistrement d'E455 (2026-11-08)

**19.78.1 La question.** L'auteur rappelle qu'il n'y a que deux cas (tous les zéros sur la ligne, ou une arrivée hors ligne
strictement basse, §19.76), qu'il ne penche pour aucun, et demande de vérifier et d'élaborer, EN FRÉQUENCE et non en amplitude,
trois affirmations : (a) un OFF ne peut pas prendre la hauteur d'un ON occupée ; (b) un OFF ne peut pas atteindre le prochain ON ;
(c) sa fréquence en est donc forcément affectée. Remarque jointe : les rapports récents (K4) parlent trop d'amplitudes.

**19.78.2 Audit du corpus compilé (modules autorisés uniquement ; aucune citation sous le ban §19.67).**
* (a) **Compilé pour le ON que l'arrivée suit et pour tout ON de son historique** : `no_shared_frequency_of_history_onLine` et
  `frequency_rises_of_history_onLine` (MeetingPoint §7) — si le membre antérieur est sur la ligne et tout membre précédant
  l'arrivée est sur la ligne, la hauteur de l'arrivée est strictement supérieure. Mécanisme : l'ordre est lexicographique
  (hauteur, position radiale) ; à hauteur égale l'arrivée serait à droite du ON, donc au-dessus d'un demi, donc son miroir (bas,
  même hauteur) précéderait le ON et serait dans l'historique, contradiction. **NON compilé pour un ON qui viendrait APRÈS
  l'arrivée à la même hauteur** : « aucune fibre mixte » est l'hypothèse nommée `NoMixedHeight` (FixedGapRaccords), impliquée par
  RH (`noMixedHeight_of_riemannHypothesis`) et jamais dérivée. L'ordre l'autorise : (β, T) puis (1/2, T) puis (1 − β, T).
  `fibre_onLine_unique` (RegimeTrigger) dit seulement qu'il y a AU PLUS UN membre sur la ligne par hauteur ;
  `fibre_multiple_iff_off` dit qu'une fibre est multiple si et seulement si elle contient un membre hors ligne.
* (b) **Compilé sous la forme de l'ordre** : `consecutive_no_height_between` (OnCrossReadings) — aucun membre n'a une hauteur
  strictement entre deux membres consécutifs ; `frequency_never_decreases` (FrequencyCascadeStability) — la fréquence ne recule
  jamais le long de l'énumération. Donc tout ON postérieur à l'arrivée basse a une hauteur AU MOINS égale à la sienne ;
  STRICTEMENT supérieure seulement si la fibre de l'arrivée ne contient pas de ON, ce qui est (a) second point.
* (c) **Ce qui est compilé n'est pas que la hauteur prise par l'OFF diffère de celle qu'un ON aurait prise** : les bornes de la
  hauteur par le rang (FrequencyCap §19.15) sont aveugles au radial. **Ce qui est compilé, c'est que la SUITE des fréquences est
  affectée par une répétition** : la fibre à la hauteur d'une arrivée basse porte au moins deux unités (`low_arrival_count_jump`,
  `low_member_deficit_ge_two`, LowNextZeroSignatures ; `two_le_fiberCount_of_low`, ArrivalFiberHypotheses) ; un seul membre hors
  ligne force deux rangs consécutifs à la même fréquence (`mirror_breaks_frequency_cascade`) ; depuis une entrée basse le passage
  qui sort est gelé (`passage_frozen_of_low_entry`, K4). Formulation exacte de (c) : la fréquence de l'OFF n'est pas « une autre
  valeur », c'est « une valeur prise deux fois au moins », et la montée reprend seulement après la fibre.
* **Sur la remarque « trop d'amplitudes »** : fondée. Dans K4, deux énoncés sur sept (rapport aux contacts, rapport des termes)
  sont des énoncés d'amplitude ; les cinq autres sont d'ordre et de fréquence. Les faits de fréquence sont les plus forts du
  corpus : aucun passage à la limite, aucune asymptotique, de l'ordre pur. K5 ne contient aucune amplitude.
* **Sur la logique des deux cas** : la dichotomie est compilée (`arrival_onLine_or_low` sous historique sur la ligne). L'absence
  d'une contradiction dérivée ne tranche AUCUN des deux cas : le corpus est muet, il ne dit pas que Riemann a tort.

**19.78.3 K5 : la fibre de l'arrivée basse, en fréquence seule.** Module isolé `Terminal/LowArrivalFrequencyFibre.lean`
(import `PairArrivalPassage`, `LowNextZeroSignatures`, `FixedGapRaccords`, `FrequencyCascadeStability`, `OnCrossReadings`), non
ajouté à `RHV6Fresh.lean`. Six énoncés :
* M1 `low_arrival_above_on_history` : sous historique sur la ligne, une arrivée basse a une hauteur strictement supérieure à celle
  du membre qu'elle suit, et aucun membre n'a de hauteur strictement entre les deux.
* M2 `low_entry_successor_le_half_of_on_fibre` : si la fibre d'une entrée basse contient un membre sur la ligne, le successeur de
  l'entrée est au plus à un demi (l'ordre place le ON entre l'entrée et son miroir).
* M3 `no_on_in_fibre_of_successor_right` : si le successeur d'une entrée basse est strictement au-dessus d'un demi, aucun membre
  sur la ligne n'a la hauteur de l'entrée (contraposée de M2).
* M4 `low_entry_successor_trichotomy` : le successeur d'une entrée basse est strictement bas (second membre bas, fibre d'au moins
  quatre), ou exactement sur la ligne (fibre mixte), ou strictement au-dessus d'un demi, borné par le miroir, avec fibre sans ON.
  C'est le côté du successeur qui décide si l'OFF « prend la hauteur d'un ON ».
* M5 `low_arrival_on_fibre_refutes_noMixedHeight` : une entrée basse et un ON de même hauteur mettent en échec `NoMixedHeight`
  (contraposée ; aucune hypothèse posée).
* M6 `on_members_split_by_low_arrival` : pour une entrée basse donnée, tout membre sur la ligne a une hauteur strictement
  inférieure, ou une hauteur au moins égale et vient après elle dans l'ordre.

**19.78.4 Vérification de non-équivalence avec RH.** Aucune hypothèse posée : chaque énoncé porte sur un passage, un zéro ou un
membre DONNÉ ; M5 nomme `NoMixedHeight` uniquement pour dire qu'une configuration donnée la réfute. Aucune amplitude, aucune
cellule, aucune somme. **Réponse attendue, consignée d'avance** : K5 ne produit AUCUNE contradiction ; il fixe en fréquence seule
ce que (a)–(c) veulent dire : l'arrivée basse prend une hauteur neuve au-dessus de tout son historique ; elle ne peut pas être
dépassée sans que la fibre soit épuisée ; le seul point ouvert est la fibre mixte (un ON à SA hauteur, après elle), décidé par le
côté du successeur et exclu seulement par `NoMixedHeight` (⟸ RH) ; la frontière reste la prémisse unique. Aucune expérience
numérique. Deux tentatives de compilation au plus, journalisées dans `experiments/E455_LowArrivalFrequencyFibre/attempts/`.

**Résultat de K5 (E455, 2026-11-08, tentative 1 verte).** Sonde scratch verte avec un avertissement : l'hypothèse « arrivée
basse » de M1 n'est pas utilisée — retirée ; M1 vaut pour TOUTE arrivée sous historique sur la ligne : l'OFF prend sa hauteur
neuve exactement comme un ON l'aurait prise, rien entre les deux. Module `Terminal/LowArrivalFrequencyFibre.lean` : 6
déclarations, 0 avertissement, 6/6 sur axiomes standards, grep du ban vide, `lake build RHV6Fresh` complet vert (9064 jobs).
**Verdict A**, conforme à l'attente. Réponse à l'auteur, en fréquence seule : (a) l'OFF ne reprend aucune hauteur de son
historique (compilé, M1) ; qu'un ON vienne ensuite à SA hauteur est la seule chose ouverte, c'est exactement `NoMixedHeight`
(⟸ RH), réfutée par toute fibre mixte (M5), et le côté du successeur de l'entrée basse décide (M2–M4 : successeur bas ⇒ second
membre bas ; successeur sur la ligne ⇒ fibre mixte ; successeur au-dessus d'un demi ⇒ fibre sans ON, borné par le miroir) ;
(b) le prochain ON n'est jamais dépassé par l'OFF (M1, M6), il est atteint seulement dans la fibre mixte ; (c) la fréquence de
l'OFF n'est pas « une autre valeur », c'est « une valeur prise au moins deux fois » puis la montée reprend : `low_arrival_count_jump`,
`mirror_breaks_frequency_cascade`, `passage_frozen_of_low_entry`. **AUCUNE contradiction** ; frontière inchangée. Consigné dans
`E455/RESULTS.md`, `HANDOVER_20261107_LIGNE.md` §13 et la mémoire.

### 19.79 Deux questions de l'auteur — « affecter β change la fréquence atteignable à même hauteur » et « les OFF deviennent peut-être nécessaires aux grandes hauteurs pour réaliser la cassure » ; audit du texte collé sur les transitions modulo 6 ; K6 et étude de causalité ON/OFF — pré-enregistrement d'E456 (2026-11-08)

#### 19.79.1 Les questions (texte de l'auteur, résumé fidèle)
(Q1) Les conclusions de §19.78 sont incomplètes sur un cas : la différence FORCÉE de fréquence entre un zéro calculé sur la ligne et
un zéro calculé hors ligne qui viseraient la même hauteur ; selon l'auteur, affecter une valeur à β change la fréquence potentielle
atteignable, « si on affecte quelque chose à β, T en souffre » ; la question aurait déjà été étudiée. (Q2) Les OFF sont peut-être
nécessaires : la montée vers les très hautes fréquences est nécessaire à la cassure ; à partir de très grandes hauteurs la fonction
devrait peut-être passer à des OFF. (Q3) Texte collé sur les quatre transitions modulo 6, les fenêtres de douze transitions, les
« archétypes » et les comptes sur cinq mille écarts : corriger les erreurs, conduire les expériences avec des études de causalité sur
les ON et les OFF. (Q4) La distribution des transitions est-elle une courbe de Gauss ?

#### 19.79.2 Audit du corpus (avant toute compilation)
**Q1 — déjà étudiée et en grande partie compilée.** (i) `gap_reading_height_only`, `gap_readings_agree_iff_height` (DoubleRigidity) :
la lecture d'un écart par une Tour ne dépend que de la hauteur ; deux Tours lisent tout écart de la même façon ⟺ même hauteur. La
position radiale n'y entre pas : à hauteur égale, le PAS est identique. (ii) Ce qui dépend de β à hauteur fixée est la PHASE
`arctan(T/β)` (`towerPhase`), donc la position absolue des contacts : `windingContact_lt_of_radial_lt` (TowerTwoSidedRoom) — à hauteur
égale, position radiale plus grande ⟹ tout contact strictement plus bas ; `windingContact_sameHeight` (TowerWinding) — rapport unique,
le même pour tout indice. (iii) `contact_eq_iff_phase`, `contact_radial_formula` (TangentialInversion) : un premier égal au contact
d'indice k fixe β = T·cot(T·log q) ; `two_contacts_height_quantized`. (iv) `tower_eq_of_same_word` (ContactsFromGapsInversion, §19.71) :
même mot sur tous les premiers ⟹ même hauteur ET même β. Donc « un OFF ne peut pas prendre les rencontres d'un ON » est compilé à
même hauteur (contacts tous décalés) comme à toute hauteur (le mot fixe β). **Non compilé, et compilable sans hypothèse** : (a) deux
Tours de même hauteur et de positions radiales différentes ne partagent AUCUN contact, à aucun couple d'indices ; (b) si un même
premier est contact des deux, les hauteurs diffèrent — forme littérale de « si on affecte β, T en souffre » ; (c) le décalage à même
hauteur est strictement inférieur à une demi-cellule de chaque côté (lecture certifiée des indices dans {−1, 0, 1}, E428) ; (d) le
rapport de cellule `e^{π/T}` est aveugle à β. Aucune de ces quatre n'existe (grep `shared_contact|no_common_contact|contact_ne_of`
vide). C'est K6. Ce que cela NE dit PAS : que l'OFF à hauteur T ait une hauteur différente de T — la hauteur est la sienne ; ce qui
change, c'est la grille des rencontres (décalée, jamais confondue) et, si l'on impose une rencontre commune, la hauteur.
**Q2 — la phrase « la montée vers les hautes fréquences réalise la cassure » vient d'E404 (§19.33, canal de sommation, mesure) et
d'E408 (§19.36), c'est-à-dire du canal interdit depuis §19.55/§19.67 ; elle n'est pas citée plus loin.** Dans la route autorisée, le
même fait est compilé par les contacts, pour TOUTE Tour : `log_ratio_ge_cell_of_meeting` (MeetingRegimeFinite) — une Tour qui touche
deux écarts consécutifs a une cellule plus courte que la réunion des deux écarts, `π/T ≤ log(J.upper/I.lower)` ; et
`two_consecutive_contacts_finite` — pour toute Tour (β quelconque), ce régime est fini : au-delà d'un rang, aucune Tour fixée ne
touche deux écarts consécutifs. La hauteur nécessaire pour résoudre les cassures autour de x est donc de l'ordre de x divisé par le
logarithme de x, quelle que soit la position radiale. L'existence de zéros à toute hauteur est inconditionnelle (`FrequencyCap`, §19.15,
aveugle au radial). Rien dans le corpus ne fait dépendre de β le pouvoir de résolution d'une Tour : il dépend de T seul (point (d)
de K6). La thèse « la fonction doit passer à des OFF aux grandes hauteurs » est la négation de RH au-delà d'une hauteur ; aucun
énoncé compilé ne la soutient ni ne la réfute ; le mécanisme de cassure sur la ligne (E447, §19.69) est écrit pour toute hauteur T > 0
et tout x > 0 sans obstruction de hauteur. Verdict attendu : la thèse n'est pas soutenue par les objets de fréquence ; elle n'est pas
non plus réfutée (frontière).
**Q3 — le texte collé décrit E427 (§19.41) sous une forme altérée.** Compilé dans le corpus : `prime_goodMod6`, `gapClass6_alternates`,
`eventOrientation_of_gap` (orientation ⟺ écart ≡ 4, 2, 0 mod 6), `orientedBalance_telescopes`, `orientedBalance_abs_le_one`,
`card_validWords_twelve` (8 192 = 2¹³ mots valides de douze transitions). Erreurs du texte, à vérifier par le jumeau : (e1) les
effectifs sont incohérents — 1 490 + 1 490 + 994 + 1 026 = 5 000 transitions, mais « 9 590 premiers » et « 799 fenêtres de 12 »
font 9 588 transitions ; (e2) « conformité 100 %, 0 violation » est une tautologie : toute suite de premiers > 3 satisfait la grammaire
par construction (états ±1 mod 6, raccord), 8 192 est le nombre de suites d'états, rien ne peut la violer ; (e3) l'égalité
τ15 = τ51 ne « démontre » pas le télescopage : le télescopage est compilé et dit seulement |τ15 − τ51| ≤ 1, l'égalité valant ⟺
premier et dernier premiers de l'échantillon ont le même reste ; (e4) les « archétypes » B, C, D forment une partition par comparaison
des séjours, donc leurs parts doivent sommer à 100 % — 10,5 + 43,8 + 43,8 = 98,1 et 10,6 + 40,4 + 42,4 = 93,4 : incohérent ; A n'est
pas défini ; (e5) la seule information non triviale est le DÉFICIT des maintiens (994 + 1 026 contre 2 980 croisements), biais connu
des résidus consécutifs, déjà mesuré en E427 (N11 − N55 jusqu'à −1 019 sur 10⁸, « mesure, aucune loi »). Liaison avec les ON/OFF :
E427 niveau 2 a compilé que la transition ne détermine ni le rapport des premiers ni celui des amplitudes ; E429 A4 : aucun candidat
de Tour n'est fonction du mot de douze transitions. Aucun lien compilé entre résidu mod 6 et position radiale ; une liaison par les
fonctions L de caractères serait spectrale, interdite, et n'est pas ouverte.
**Q4 — une distribution sur douze transitions a un support fini de treize valeurs : elle ne peut pas ÊTRE gaussienne.** Attendu :
sous l'uniforme sur les 8 192 mots, le nombre de croisements par fenêtre suit la binomiale de paramètres 12 et 1/2 ; sur les vrais
premiers il suit approximativement une binomiale de paramètre décalé (biais e5), et seules de longues fenêtres approchent la
normale (asymétrie et aplatissement à mesurer). La réponse sera chiffrée, pas affirmée.

#### 19.79.3 Plan d'E456 (deux volets, un commit de pré-enregistrement avant toute exécution)
**Volet Lean, K6 — module isolé `Terminal/SameHeightContactShift.lean`** (NON ajouté à `RHV6Fresh.lean` ; imports
TowerTwoSidedRoom, TangentialInversion, ContactsFromGapsInversion, MeetingRegimeFinite ; aucune hypothèse, aucune amplitude) :
* M1 `same_height_distinct_radial_no_shared_contact` : β ≠ β' (positifs), T > 0 ⟹ ∀ k j, contact k de (β,T) ≠ contact j de (β',T).
* M2 `off_shares_no_contact_with_line_same_height` : β ≠ 1/2 ⟹ aucun contact de (β,T) n'est un contact de ligne à hauteur T.
* M3 `shared_contact_forces_height_change` : même premier contact des deux Tours et β ≠ β' ⟹ T ≠ T'.
* M4 `same_height_shift_within_half_cell` : à même hauteur, chaque contact de (β,T) est strictement entre le contact de même indice de
  (β',T) multiplié par `e^{−π/(2T)}` et par `e^{π/(2T)}`.
* M5 `cell_ratio_radially_blind` : contact k+1 = `e^{π/T}` × contact k, pour tout β (si absent du corpus ; grep avant).
Deux tentatives au plus ; sonde scratch non versionnée ; grep du ban avant build ; `lake build RHV6Fresh` complet après.
**Volet déterministe — `experiments/E456_SameHeightContactShift/e456_causal_mod6_contact_shift.py`** (entiers et flottants
double, aucune liste de zéros autre que `data/odlyzko_zeros1_first5000.txt`, aucun paramètre libre) :
* P1 jumeau de K6 : sur les 5 000 hauteurs réelles et β ∈ {0,3 ; 0,4 ; 0,5}, rapport de cellule identique, facteur de décalage
  dans ]e^{−π/(2T)}, e^{π/(2T)}[, distance minimale entre grilles de contacts > 0.
* P2 audit du texte collé : recompte des quatre transitions sur les 5 000 premiers écarts (p > 3) et sur 799 fenêtres de douze ;
  bilan orienté ; énumération exacte des 8 192 mots (nombre de croisements, N11 − N55) ; parts des classes « égalité », « famille 1 »,
  « famille 5 » (doivent sommer à 1) ; recherche de la définition de « A » qui rend 51,9 % sur 8 192 (candidats pré-écrits :
  croisements ≥ 7 ; croisements > maintiens ; croisements ≥ 6).
* P3 Gauss : distribution du nombre de croisements par fenêtre de 12 (réel contre binomiale 12, 1/2 et binomiale 12, p̂ ; distance du
  khi-deux) ; fenêtres de 120 et 1 200 transitions : asymétrie, aplatissement, écart maximal à la normale ajustée.
* P4 causalité ON/OFF, intervention sur β à T fixée (hauteurs réelles, premiers ≤ 10⁶) : ensemble des écarts touchés (`GapHasContact`)
  pour β = 0,5 et β = 0,3 — recouvrement ; composition modulo 6 des écarts touchés (parts des quatre transitions) ON contre OFF ;
  table de contingence « type de transition × quartile de fraction de cellule au premier » pour ON et pour OFF (khi-deux) ;
  intervention sur T à β fixée en contrôle (tout change : pas, phase, contacts — `height_advance_concurs`).
**Réponses attendues, consignées d'avance** : P1 exact ; P2 : effectifs réels différents de ceux du texte ou cohérents avec 5 000
seulement ; |τ15 − τ51| ≤ 1 ; parts B + C + D = 1 ; P3 : binomiale décalée, pas gaussienne à douze ; normale approchée aux longues
fenêtres ; P4 : recouvrement des écarts touchés élevé mais non total (décalage < demi-cellule), composition mod 6 identique au bruit
près pour ON et OFF, contingence nulle (le contact ne lit pas le résidu), T change tout. **Aucune contradiction OFF attendue** ; si un
écart apparaît, il est consigné sans conclusion. Vérification de non-équivalence : aucune hypothèse n'est posée ; M1–M5 sont des
identités de paramètres (β, T), sans zéro, à la manière de `parameter_model_twin_escapes`.

**Résultat d'E456 (2026-11-08 ; pré-enregistrement 33c36e43 ; Lean tentative 1 verte ; volet déterministe exécuté une fois).**
*K6 (`Terminal/SameHeightContactShift.lean`, isolé, six énoncés M0–M5, 0 avertissement, 6/6 sur `[propext, Classical.choice,
Quot.sound]`, grep du ban 0, `lake build RHV6Fresh` complet vert, 9 064 tâches).* M1 : à même hauteur, deux positions radiales
différentes ne partagent aucun contact, à aucun couple d'indices ; M2 : un OFF de hauteur T ne prend aucune rencontre de la Tour de
ligne de hauteur T ; M3 : une rencontre commune à deux positions radiales différentes impose des hauteurs différentes (forme exacte
de « si on affecte β, T en souffre » : à rencontre imposée) ; M4 : le décalage est strictement inférieur à une demi-cellule ; M5 : le
pas `e^{π/T}` est aveugle à β. Réponse à Q1 : la phrase de l'auteur est vraie et maintenant compilée dans sa forme littérale ; elle ne
dit pas que l'OFF de hauteur T ait une autre hauteur, elle dit que sa grille de rencontres est décalée, jamais confondue, et que
reprendre une rencontre du ON exige de changer de hauteur. Réponse à Q2 : le pouvoir de résolution d'une Tour ne dépend que de T
(M5 et `log_ratio_ge_cell_of_meeting`, `two_consecutive_contacts_finite`, valables pour toute Tour) ; la montée vers les hautes
fréquences est un fait inconditionnel et aveugle au radial ; rien ne soutient ni ne réfute « la fonction doit passer à des OFF aux
grandes hauteurs » ; la thèse est la négation de RH au-delà d'une hauteur ; frontière inchangée.
*Volet déterministe (`e456_causal_mod6_contact_shift.py`, premiers ≤ 10⁶ par crible, 5 000 hauteurs d'Odlyzko, sortie
`logs/e456_output.txt`).* **P2, correction de l'audit préalable** : les quatre effectifs du texte collé sur 5 000 écarts (p > 3) sont
EXACTS (994, 1 490, 1 490, 1 026) ; ce qui est faux est l'habillage : « 9 590 premiers » et « 799 fenêtres de douze » (9 588
transitions : 1 915, 2 868, 2 868, 1 937) ne correspondent pas à 5 000 écarts ; l'erreur e1 est donc rectifiée en « effectifs justes,
cadre faux ». Bilan orienté sur tout préfixe dans {−1, 0}, nul ⟺ même état aux deux bouts (télescopage compilé, pas une découverte) ;
l'égalité 1 490 = 1 490 tient parce que le cinquième premier et le cinq-mille-cinquième ont le même reste. Énumération exacte des
8 192 mots : égalité des séjours 11,28 %, famille 1 44,36 %, famille 5 44,36 % (somme 1) ; le texte (10,5 ; 43,8 ; 43,8, somme 98,1)
est faux ; aucun des cinq candidats pré-écrits ne rend 51,9 % pour « A » (croisements ≥ 7 : 38,72 % ; ≥ 6 : 61,28 %) — « A » n'est
pas défini par le texte et n'est reproduit par aucune définition pré-écrite. Sous l'uniforme, le nombre de croisements suit la
binomiale de paramètres douze et un demi, chaque profil étant porté par deux suites d'états (facteur 2 exact). Fenêtres réelles :
799 premières — égalité 13,27 %, famille 1 42,55 %, famille 5 44,18 % (texte : 10,6 ; 40,4 ; 42,4, somme 93,4, faux) ; 6 541
fenêtres ≤ 10⁶ — 15,29 / 41,81 / 42,90 ; croisements moyens 7,18 puis 6,98 pour 6 attendus sous l'uniforme : c'est le biais des
résidus consécutifs (maintiens 41,8 % au lieu de 50 %), déjà mesuré en E427, « mesure, aucune loi ».
**P3 (Q4, gaussienne) : NON.** À douze transitions le support est discret (treize valeurs) ; contre la binomiale douze, un demi :
khi-deux 2 267 sur 10 degrés (rejet) ; contre la binomiale douze, p̂ = 0,582 : khi-deux 28,9 sur 10 degrés (p ≈ 7·10⁻⁴, rejet),
dispersion 0,92 (sous-dispersée : alternance des résidus), asymétrie −0,05, aplatissement excédentaire −0,23. Aux fenêtres de 120
(654 fenêtres) : asymétrie 0,02, aplatissement −0,14, dispersion 0,97, Shapiro p 0,055 — approximation normale acceptable, pas une
loi ; 1 200 (65 fenêtres) : Shapiro p 0,25 ; 12 000 (6 fenêtres) : dispersion 4,4 — la proportion dérive avec la hauteur des premiers,
la suite n'est pas une binomiale stationnaire. Réponse : binomiale biaisée et sous-dispersée à douze, approchée par la normale aux
fenêtres moyennes comme toute somme de variables bornées, dérivante aux grandes fenêtres ; aucune loi gaussienne n'est affirmée.
**P1 (jumeau de K6) exact** : écart maximal des rapports de cellule ON/OFF 4·10⁻¹⁶ ; décalage sur demi-cellule au plus 0,009, 0
violation ; distance minimale entre grilles 5,8·10⁻⁶ cellule (> 0), décroissante en 1/T.
**P4 (causalité ON/OFF).** Intervention sur β à T fixée (200 hauteurs, 78 495 écarts) : part des écarts touchés 6,53 % pour ON et
pour OFF ; recouvrement de Jaccard des ensembles touchés 0,992 en moyenne (minimum 0,34 aux plus basses hauteurs, cellules larges,
peu d'écarts touchés) ; composition modulo 6 des écarts touchés identique à 10⁻⁴ près (maintiens 0,446, τ15 0,299, τ51 0,255 pour ON
comme pour OFF) ; la différence avec l'ensemble de tous les écarts (0,418 / 0,291 / 0,291) est un effet de LONGUEUR d'écart (un
contact tombe plus souvent dans un écart long, et les écarts longs sont plus souvent de classe 0), identique pour ON et OFF ;
table de contingence « type de transition × quartile de fraction de cellule » : p-valeurs médianes 0,81 (ON) et 0,81 (OFF), part
< 0,05 : 0,5 % — le contact ne lit pas le résidu, sur la ligne comme hors ligne. Contrôle, intervention sur T à β fixée : Jaccard 0,24
(tout change : pas 0,2223 → 0,1494, phase, contacts — `height_advance_concurs`). Intervention sur β à T = 14,13 : pas identique,
phase 1,5354 → 1,5496, contact d'indice un 1,3922 → 1,3936, facteur 1,0010 dans la fenêtre d'une demi-cellule. **Lecture causale** :
β n'agit que sur la phase (décalage de grille inférieur à une demi-cellule, M4) et sur l'amplitude (hors de ce volet) ; T agit sur
tout ce qui est fréquence ; le résidu modulo 6 n'est lu ni par l'un ni par l'autre. **Aucune contradiction ; aucune liaison compilée
ni mesurée entre la grammaire modulo 6 et la position radiale ; rien n'est ajouté du texte collé au corpus, qui le contenait déjà
(E427) sous forme exacte.** Verdict A pour K6 et P1 ; verdict B pour l'audit préalable (e1 rectifiée). Décision à l'auteur.

### 19.80 L'arête manquante : la sélection des porteurs — proposition de plan Φ (nommer, isoler, dichotomiser, hypothéquer), en attente de l'accord de l'auteur (2026-11-08)

**Point de départ validé par l'auteur (soir du 2026-11-08).** « L'hypothèse de Riemann devient : parmi tous les mots que les premiers
engendrent, ceux qui portent un zéro sont exactement les mots égaux à leur miroir. Le seul nœud non lu par le canal des contacts est
le poids du zéro. Rien dans la fréquence, l'amplitude ou la grammaire ne distingue les mots porteurs des autres. Les premiers ne
sélectionnent pas un mot unique, ils engendrent un mot par Tour. La causalité est complète en aval de la Tour et muette sur la
sélection des porteurs. » Le graphe causal compilé : premiers → grammaire modulo 6 (tautologie) ; premiers + (β, T) → mot ; mot → (β, T)
(inversion, cause = PNT porté, `tower_eq_of_same_word`) ; mot → mot du miroir (`mirror_word_of_same_word`) ; mots égaux ⟺ ligne
(`pair_words_eq_iff`) ; grammaire → Tours : par la longueur des écarts seulement, via T, jamais via β (E456 P4) ; aucune arête
grammaire ↔ radial (E427 niveau 2, E429 A4). Nœud non lu : « porteur » = `zeroMult (zeroPoint z) ≥ 1` (PairBreakOfZero), dont on ne
sait que : nul hors zéro, ≥ 1 en un zéro, égal pour le miroir.

**Doctrine du plan.** « Poser des hypothèses » ne veut pas dire en admettre : chaque hypothèse de ce plan est une proposition NOMMÉE en
Lean, puis (a) classée contre RH (compiler ⟸ RH ; tenter ⟹ RH ; si les deux passent, c'est une REFORMULATION de la cible, jamais une
prémisse), (b) ses exigences compilées (ce qu'elle impose aux premiers, aux contacts, au poids), (c) son jumeau mesuré sur les 5 000
hauteurs d'Odlyzko avec contrôles (β perturbé à hauteur de zéro ; ligne à hauteur hors zéro). Interdits inchangés : aucune théorie
spectrale (§19.67), aucune lecture littérale contact ↔ position d'un premier (§19.10, §19.51), aucun axiome, aucun `sorry`,
modules isolés, deux tentatives, pré-enregistrement avant compilation.

**Φ0 — Nommer l'arête (module `CarrierSelection.lean`, E457).** Définir le mot d'un zéro vrai (déjà implicite dans
`zero_pair_words_eq_iff`), l'ensemble des mots porteurs, et compiler TROIS reformulations exactes (les deux sens) :
(R1) RH ⟺ tout mot porteur est égal à son miroir ; (R2) RH ⟺ la hauteur est injective sur les zéros vrais du demi-plan supérieur
(deux porteurs de même hauteur sont le même) — le miroir supérieur `mirrorMember` a la même hauteur, donc injectivité ⟹ β = 1 − β ;
(R3) RH ⟺ le prix (E445) est radialement aveugle sur les porteurs : deux porteurs de même fréquence et de même poids paient le
même prix au même premier — le rapport des termes `x^{2β−1}·‖ρ*‖/‖ρ‖` (`zero_pair_term_ratio`) ne vaut 1 en deux premiers distincts
que si β = 1/2. Attendu : trois équivalences compilées ; aucune n'est une prémisse ; elles disent en Lean « ce que l'arête doit
livrer » : injectivité de la hauteur, OU cécité radiale du prix, OU vacuité de la bande (Φ2). Jumeau : aucun (énoncés exacts) ;
contrôle de non-trivialité : vérifier que `NoMixedHeight` (FixedGapRaccords) reste strictement plus faible que R2 (R2 ⟹ NoMixedHeight
compilé ; la réciproque ne doit PAS compiler sans RH — une hauteur à porteurs tous hors ligne la satisfait).

**Φ1 — Théorème d'isolement : la sélection n'est dans aucun préfixe fini (même module ou `CarrierNotFinite.lean`, E457).** Énoncé
visé : pour tout zéro vrai z et tout ensemble FINI de premiers, il existe une Tour NON porteuse (poids nul) de même mot que z sur
ces premiers. Ingrédients, tous compilés ou Mathlib : les zéros de zêta sont isolés (zêta analytique sur ℂ∖{1}, non identiquement
nulle : `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`) ; la position d'étage `stagePosition β T q` est croissante en T
(dérivée `log q − β/(β²+T²) > 0` pour q ≥ 2, T ≥ 1) ; donc en augmentant T d'assez peu, aucune partie entière ne descend et
celles qui sont entières restent (le mot est conservé sur l'ensemble fini) tandis que le poids tombe à zéro (`zeroMult_eq_zero_iff`).
Conséquence compilée : aucun prédicat sur un nombre fini d'écarts ne sépare porteurs et non-porteurs — K0 (E450) et A4 (E429)
deviennent des théorèmes, la route des fenêtres finies (grammaire modulo 6 incluse) est fermée définitivement, et l'arête manquante
est une propriété de QUEUE du mot, comme l'inversion elle-même [RECTIFIÉ §19.85, 2026-11-09 : « propriété de queue » n'est PAS démontré ; seul l'est : aucune sélection fondée exclusivement sur une fenêtre finie du mot]. Jumeau : sur 200 zéros, exhiber numériquement la Tour voisine de même
mot sur les premiers ≤ 10⁶ (écart de hauteur nécessaire, à comparer au demi-écart entre zéros consécutifs).

**Φ2 — Dichotomie de la bande (module `MirrorStrip.lean`, E458).** Bande d'un zéro = ensemble des premiers où son mot et celui du
miroir diffèrent (`zero_mirror_word_difference_le_one` : la différence vaut alors exactement 1). Compiler : (B1) bande vide ⟺ ligne ;
(B2) bande infinie ⟺ hors ligne (reformulation de `pair_words_differ_beyond_iff` en termes de premiers) ; (B3) bande non vide et
finie IMPOSSIBLE ; (B4) un premier de bande est encadré par le dernier contact du zéro et le dernier contact du miroir, deux contacts
jamais confondus (`same_height_distinct_radial_no_shared_contact`, K6), décalés de moins d'une demi-cellule. Lecture : un porteur hors
ligne exige une infinité de premiers dans une bande de largeur logarithmique fixée par β et T ; mais toute Tour hors ligne, porteuse ou
non, a cette bande — la géométrie de la bande ne porte PAS l'arête, qui ne peut être que dans ce que le porteur FAIT aux premiers de
bande. INTERDIT : affirmer une densité de la bande (équirépartition de `T log p` modulo π = énoncé spectral) ; seule l'infinitude est
compilée. Jumeau : sur les contrôles β perturbés, effectif de la bande jusqu'à 10⁶, encadrement B4 vérifié à 0 violation ;
« mesure, aucune loi ».

**Φ3 — Hypothèses locales NON équivalentes à RH, à classer puis à mesurer (module `CarrierLocalReading.lean`, E459).**
(H-a) *Même lecture au premier partagé* : le premier de la première cassure de la paire (E450, `PairBreakAtPrime`) n'est pas un
premier de bande. ⟸ RH trivial ; ⟹ RH attendu FAUX (un seul premier contraint, bande infinie ailleurs possible) ⇒ hypothèse strictement
plus faible. Exigence à compiler : fenêtre de β autour de 1/2 fixée par T et la fraction de cellule au premier partagé
(PairMeetingImposition, « fenêtre de même mot fixée par β »). Jumeau : sur les contrôles, part des β perturbés qui satisfont H-a.
(H-b) *Même lecture sur toutes les cellules de rencontre* (une cellule de rencontre franchit exactement un premier, E439) : classement
contre RH à établir (attendu : plus faible, car les premiers de rencontre forment une sous-suite et la bande peut vivre ailleurs) ;
exigence : la bande évite tous les premiers de rencontre ; jumeau : sur contrôles, premier rang de rencontre où H-b casse, en fonction
de |β − 1/2|.
(H-c) *Poids et bande* : effectif de bande jusqu'à x borné par une fonction du poids. ⟹ RH par B3 (bande finie ⟹ vide) ; ⟸ RH trivial
⇒ ÉQUIVALENTE : consignée comme reformulation (le poids devrait borner la bande), jamais posée.
Toute hypothèse classée équivalente passe en Φ0 comme reformulation ; seules H-a et H-b (si plus faibles) sont mesurées.

**Φ4 — Où le poids peut entrer sans théorie spectrale (audit avant tout module, E460 si module).** Inventaire exhaustif de ce que le
corpus et Mathlib donnent au POINT ρ seul : ordre d'annulation (`zeroMult`), équation fonctionnelle (`ZetaReflect`), conjugaison,
analyticité ; et rien d'autre (produit d'Euler divergent à β ≤ 1/2, série de Dirichlet idem). Question à trancher par audit, pas par
compilation : existe-t-il un énoncé reliant l'ordre d'annulation à une quantité lue aux contacts d'UNE Tour (sa propre amplitude, son
propre prix) sans somme sur les premiers ni sur les zéros ? Si l'audit répond non, c'est consigné : l'arête manquante exige un canal
arithmétique ponctuel qui n'existe pas dans le corpus, et la décision de route revient à l'auteur.

**Ordre et budget.** Φ0 et Φ1 d'abord (théorèmes, aucune hypothèse, un module, deux tentatives, E457) ; puis Φ2 (E458) ; puis Φ3 après
classement de H-a et H-b contre RH (E459) ; Φ4 en audit parallèle. Chaque étape : pré-enregistrement, `attempts/`, `#print axioms`,
grep d'interdiction à zéro, `lake build RHV6Fresh` vert, rapport en mots. Critère d'arrêt : une hypothèse plus faible que RH, vraie sur
les contrôles ET dont l'exigence compilée fait intervenir le poids — c'est alors le premier candidat sérieux d'arête ; sinon, Φ4
dit en Lean ce que l'arête exige et ce qui manque.

### 19.81 Synthèse de l'état de la route au soir du 2026-11-08 et mise en cohérence de `CLAUDE.md` (2026-11-08)

**Ce qui est compilé depuis l'ouverture de la phase OFF (§19.72, E450–E456, modules isolés, axiomes standard, aucune hypothèse).**
K0 : rien ne distingue les zéros parmi les Tours dans le canal des contacts (mesure). K1 (E450) : cassure de la paire au premier
partagé, deux mots décalés d'au plus une cellule, rapport des termes `p^{1−2β}` non borné. K2 (E451) : la Tour est le terme du zéro,
le poids est l'ordre d'annulation, nul hors zéro, égal pour le miroir. K2b (E452) : mot exact du miroir, fenêtre de même mot fixée par
β, non-compensation au premier partagé. K3 (E453) : l'inversion rend `(1−β, T)` depuis le mot du miroir ; le mot du miroir est
fonction du mot de la Tour ; mots identiques ⟺ ligne ; la seconde Tour n'apporte aucune donnée indépendante. K4 (E454) : la paire
lue comme passage, arrivée basse = membre faible. K5 (E455) : en fréquence seule, compilé vers le bas, ouvert vers le haut
(`NoMixedHeight`, ⟸ RH). K6 (E456) : à même hauteur, aucun contact partagé entre deux positions radiales, rencontre commune ⟹
hauteurs différentes, décalage < une demi-cellule, pas aveugle à β ; β agit sur la phase (et l'amplitude), T sur toute la fréquence,
la grammaire modulo 6 sur aucune des deux. **Aucune contradiction** à aucune étape ; frontière inchangée.

**Lecture causale validée par l'auteur (§19.80, point de départ).** Premiers → grammaire (tautologie) et premiers → mot par Tour ;
mot → Tour ; mot → mot du miroir ; mots égaux ⟺ ligne ; grammaire → Tours par la longueur des écarts, via T seulement. RH ⟺ tout mot
porteur est égal à son miroir. Nœud non lu : le poids. Arête manquante : la sélection des porteurs. Plan Φ (§19.80) : nommer (R1–R3,
trois reformulations exactes de RH), isoler (la sélection n'est dans aucun préfixe fini du mot : théorème visé), dichotomiser (bande
vide ou infinie, jamais finie non vide), hypothèses locales H-a/H-b classées contre RH puis mesurées, audit de ce que le poids peut
livrer sans théorie spectrale. En attente de l'accord de l'auteur.

**Mise en cohérence de `CLAUDE.md` (dépôt `zeta24-lean`, même jour).** Le fichier d'entrée contenait des couches contradictoires avec
la démarche en cours : route « régime ON engagé / verrou unique / `ContinuationForced` » (§5 i–iii de `CLAUDE.md`), « main peut être
rouge, un seul build, livraison = `status.sh` », « aucune hypothèse de hors-ligne dans les énoncés », « la seule proposition nommée est
`PNoRegimeChange` », R7 (« arête manquante = fréquence nouvelle au second événement premier »), R8 (« ne jamais raisonner sur deux
zéros »), R12 (« un contact sans amplitude est aveugle au radial »), ORDRE DE TRAVAIL et R-LIGNE (levés pour le fil OFF par §19.72),
inventaires des sections 4, 5 (iv), 5 (v), 6 citant des objets spectraux. Traitement : rien n'est effacé ; une section `1bis`
« Préséance et état de la route » est insérée en tête (règle : le plus récent l'emporte, le compilé l'emporte sur tout ; route en
vigueur ; ordres en vigueur datés ; ordres levés ou dépassés) ; chaque passage dépassé porte un marqueur `[DÉPASSÉ …]`, `[LEVÉ …]`,
`[REFORMULÉ …]` ou `[PARTIELLEMENT DÉPASSÉ …]` renvoyant au paragraphe du présent maître qui le remplace ; les sections d'inventaire
portent une bannière « INVENTAIRE HISTORIQUE » ; une règle R-Φ résume l'état causal et l'arête manquante. R12 est reformulée selon le
troisième ordre : seul le pas entre contacts est aveugle au radial, la position des contacts lit β. Les maîtres mathématique et Lean
(figés au 2026-10-25, §§7–14) décrivent la route antérieure (formule explicite, reste, prémisse unique) : ils ne sont pas modifiés
ici, et le présent maître sémantique fait foi pour la route depuis §19 (règle de §2 de `CLAUDE.md`, maîtres corrigés après coup).

### 19.82 Validation du plan Φ par l'auteur et exécution — E457 (Φ0 + Φ1), pré-enregistrement (2026-11-08)

**Ordre de l'auteur (2026-11-08, soir) :** « je valide le plan, consigne-le et exécute chaque proposition ». Le plan Φ de §19.80 passe de
proposition à route en vigueur ; ses quatre étapes sont exécutées dans l'ordre Φ0+Φ1 (E457) → Φ2 (E458) → Φ3 (E459) → Φ4 (E460), chacune
pré-enregistrée avant compilation, deux tentatives au plus, module isolé, aucune hypothèse admise.

**E457 pré-enregistré** (`experiments/E457_CarrierSelection/README.md`) : module `Terminal/CarrierSelection.lean` ; objets `towerWord`,
`zeroWord`, `IsCarrier` ; trois reformulations exactes R1 (porteurs égaux à leur miroir), R2 (hauteur injective sur les porteurs), R3 (prix
d'E445 égal à celui de la ligne en tout premier ; variante R3' : même module des termes du zéro et du miroir, et deux premiers distincts
suffisent) — chacune ⟺ RH ; R2 ⟹ `NoMixedHeight` ; sonde consignée : `NoMixedHeight ⟹ RH` ne doit pas se compiler. Φ1 : stabilité du mot
vers la droite en `β` (position d'étage croissante et continue en `β`), puis théorème d'isolement : tout zéro vrai a, à MÊME hauteur et
aussi près qu'on veut à sa droite, une Tour non porteuse de même mot sur tout ensemble fini de rangs ; corollaire : aucun prédicat à
fenêtre finie ne sépare les porteurs. Écart au plan consigné : variation en `β` à `T` fixé au lieu de `T' > T` (plus simple, et plus fort :
même fréquence). Jumeau : marges radiale et en hauteur conservant le mot sur les premiers ≤ 10⁶, 200 zéros + 600 contrôles, attendus
écrits d'avance.

**E457 exécuté (2026-11-08, soir) — verdict A.** Module `CarrierSelection.lean` vert à la première tentative (22 déclarations, 9 imprimées
sur les trois axiomes standard, ban 0, build complet vert). Compilé : R1, R2, R3 (prix d'E445), R3' (modules des termes du zéro et du
miroir ; deux premiers distincts suffisent) — chacune ⟺ RH, aucune posée ; R2 ⟹ `NoMixedHeight`, réciproque non obtenue par sonde ;
Φ1 : tout zéro vrai a, à MÊME hauteur et aussi près qu'on veut à droite, une Tour non porteuse de même mot sur tout ensemble fini de
rangs ; la partie entière étant continue à droite, un premier posé exactement sur un contact reste dans sa cellule (convention de bord
réglée par le choix de la direction) ; corollaire : aucun prédicat à fenêtre finie ne sépare les porteurs. **K0 (E450) et A4 (E429) sont
désormais des théorèmes ; la route des fenêtres finies, grammaire modulo 6 comprise, est fermée par théorème ; l'arête manquante est une
propriété de QUEUE du mot [RECTIFIÉ §19.85, 2026-11-09 : « propriété de queue » n'est PAS démontré ; seul l'est : aucune sélection fondée exclusivement sur une fenêtre finie du mot].** Jumeau : sur 800 Tours (200 hauteurs × ligne + trois contrôles), marge en hauteur conservant tout le mot sur
les premiers ≤ 10⁶ de l'ordre du millionième, des milliers de fois plus petite que le demi-écart entre zéros ; marges des contrôles du
même ordre que celles de la ligne (rapport des médianes 0,98–1,11, rangs décorrélés) ; vérification directe aux bords 800/800 après
recontrôle en précision étendue de 9 cas sous le bruit double. Mesure, aucune loi. Détail : `experiments/E457_CarrierSelection/RESULTS.md`.

### 19.83 Remarques externes sur le plan Φ (relecture transmise par l'auteur le 2026-11-08) : ce qui est retenu, ce qui est déjà réglé

L'auteur a transmis une relecture externe du plan (accord sur l'architecture, trois corrections demandées, priorité à Φ4). Traitement :
1. **Φ1, « un premier exactement sur un contact »** — objection fondée contre le plan écrit (direction T' > T sans convention de bord) ;
   RÉGLÉE dans E457 par le choix de la direction : position d'étage continue et strictement croissante en β, partie entière continue à
   droite, donc toutes les lectures du préfixe sont préservées, bord compris (`floor_stable_right_of_continuous_mono`, compilé).
2. **R3, définition du prix** — RETENUE : R3 est écrite sur `offPrice` exactement tel que défini en E445, avec son identité de normalisation
   `x^β + x^{1−β} = 2√x · offPrice β x` (`pair_amplitude_eq_price`) ; la variante R3' porte le rapport des termes avec son facteur
   `‖ρ*‖/‖ρ‖`, et c'est précisément ce facteur qui impose DEUX premiers distincts (`radial_half_of_term_modulus_eq_two_primes`).
3. **Φ3, « plus faible que RH »** — RETENUE et précisée : un échec de sonde Lean ne prouve pas une non-implication (il est consigné comme
   constat, cf. `NoMixedHeight`). Pour E459, le classement d'une hypothèse locale H devra distinguer trois rubriques : (i) implications
   compilées (RH ⟹ H) ; (ii) CONTRE-MODÈLE COMPILÉ au niveau des Tours : exhiber en Lean un couple `(β, T)` avec `β ≠ 1/2` qui satisfait
   la forme paramétrique de H (alors H, lue sur les Tours, ne force pas la ligne : c'est une non-équivalence effective, sans rien supposer
   sur les zéros) ; (iii) réciproques ouvertes (H ⟹ RH non obtenue), énoncées comme telles. Seule la rubrique (ii) autorise à écrire
   « strictement plus faible », et seulement « sur les Tours ».
4. **Priorité à Φ4** — RETENUE : l'audit du poids (E460) est conduit immédiatement après E457, avant E458 et E459, et ses conclusions
   encadrent les deux expériences suivantes. Les reformulations R1–R3 délimitent la cible et ne sont pas le résultat principal.
5. Reformulation de l'arête proposée par la relecture — « données arithmétiques → condition caractérisant les Tours porteuses » — est
   la même que §19.80 (le poids caractérise le porteur par définition ; il faut une condition indépendante, lisible aux contacts et aux
   premiers). E457 ajoute : cette condition ne peut être qu'une propriété de queue du mot [RECTIFIÉ §19.85, 2026-11-09 : « propriété de queue » n'est PAS démontré ; seul l'est : aucune sélection fondée exclusivement sur une fenêtre finie du mot], et la relecture ne la fournit pas non plus.

### 19.84 Audit Φ4 du poids — inventaire collecté le 2026-11-08 au soir (EN COURS, conclusions à tirer demain, E460)

Inventaire exhaustif par grep (hors `Zeta23Port` et hors canaux de sommation, interdits) de ce que le corpus et Mathlib donnent AU POINT
`ρ` seul sur le poids d'une Tour :
* **Définition** : `zeroMult ρ = (analyticOrderAt riemannZeta ρ).toNat` (Foundation/ZetaReflect) ; finitude hors du pôle
  (`analyticOrderAt_riemannZeta_ne_top`) ; `≥ 1` en un zéro de bande (`one_le_zeroMult`) ; nul ⟺ zêta non nulle (`zeroMult_eq_zero_iff`, E451).
* **Symétries ponctuelles** : conjugaison (`analyticOrderAt_zeta_conj`, Mathlib `riemannZeta_conj`), réflexion `ρ ↦ 1 − ρ̄` et `ρ ↦ 1 − ρ`
  (`analyticOrderAt_zeta_reflect`, `zeta_mult_functionalReflect`, Mathlib `riemannZeta_one_sub` : facteur gamma–cosinus non nul dans la bande) :
  le poids est le même aux quatre points de l'orbite ; aucun de ces énoncés ne distingue `β` de `1 − β`.
* **Topologie des zéros** : isolés et localement finis (`riemannZeta_zeros_locallyFinite`, `zeta_window_finite`, Mathlib `isDiscrete_riemannZetaZeros`) ;
  c'est l'ingrédient d'E457, il dit où les porteurs ne sont PAS (voisinage), jamais où ils sont.
* **Factorisation locale** : `f = (z − ρ)^m · g`, `g` entière non nulle en `ρ` (`ArgumentPrinciple.exists_entire_div_pow`) ; le poids est l'exposant ;
  son usage dans le corpus est le comptage par intégrale de bord (`argument_principle_rect`), canal de comptage aveugle au radial.
* **Détermination universelle par les premiers** (port RhGap, `primes_determine_nontrivial_zero_multiset`, `primeDetermined_zero_iff`) : le
  multiensemble des zéros AVEC poids est déterminé par le produit d'Euler sur `Re s > 1` et la continuation analytique ; c'est une
  détermination GLOBALE (principe d'identité), pas une lecture ponctuelle : elle ne fournit aucune formule du poids en fonction de
  grandeurs lues en `ρ`.
* **Mathlib, expressions arithmétiques de zêta** : série de Dirichlet (`zeta_eq_tsum_one_div_nat_cpow`) et produit d'Euler
  (`riemannZeta_eulerProduct`) seulement pour `Re s > 1` ; non-annulation pour `Re s ≥ 1` (`riemannZeta_ne_zero_of_one_le_re`) ; rien dans la bande.
* **Objets de la route des contacts** : `windingContact`, `towerPhase`, `contactRealValue`, `offPrice`, `towerWord` sont définis pour TOUT couple
  `(β, T)` sans référence à zêta ; `contactAmplitude z k` est défini sur un zéro vrai mais ne dépend que de `(β, T)` du zéro (E444, E445) ;
  aucun théorème du dossier `Terminal` ne conclut `riemannZeta ρ = 0` ou `IsCarrier β T` à partir de ces objets (grep : seules
  `primeDetermined_zero_iff` et `primeDetermined_strip_iff`, tautologiques par identité `F = ζ`).
Constat provisoire (à confirmer demain par la relecture des modules `PrimeWeightResponse`, `BoxAnchor`, `ZetaRealSegment` et des deux
certificats de boîte) : il n'existe dans le corpus aucun énoncé reliant l'ordre d'annulation à une quantité lue aux contacts d'UNE Tour sans
somme sur les premiers ni sur les zéros ; E457 ajoute que toute telle quantité devrait être une propriété de queue du mot [RECTIFIÉ §19.85, 2026-11-09 : « propriété de queue » n'est PAS démontré ; seul l'est : aucune sélection fondée exclusivement sur une fenêtre finie du mot]. Si la relecture
confirme, c'est consigné comme résultat d'audit (E460) et la décision de route revient à l'auteur.

### 19.85 Rectification de portée d'E457 : « impossibilité d'une sélection par fenêtre finie », et non « propriété de queue » (réserve transmise par l'auteur, 2026-11-09)

**Réserve reçue (relecture externe transmise par l'auteur à la reprise du 2026-11-09), retenue en entier.** La phrase « l'arête manquante
est une propriété de queue du mot » (§19.80 Φ1, §19.82, §19.83 point 5, §19.84, hand-over §16, `RESULTS.md` d'E457, en-tête de
`CarrierSelection.lean`) dit PLUS que ce qui est compilé. Le théorème `finite_window_predicate_not_carrier_selective` établit : aucun
prédicat sur les mots qui ne dépend que d'un nombre fini de rangs ne sépare les porteurs des non-porteurs. Il n'établit pas que la
propriété cherchée ne dépend QUE de la queue : une propriété peut exiger le mot infini entier tout en dépendant de ses premiers termes.
**Formulation démontrée, seule à citer désormais :** *la sélection des porteurs ne peut pas être caractérisée par un prédicat portant
exclusivement sur une fenêtre finie du mot.* **Portée exacte :** le théorème exclut les critères fondés uniquement sur les valeurs du
mot à un nombre fini de rangs ; il n'exclut PAS une condition arithmétique locale enrichie d'une information indépendante du mot.
**Traitement :** les sept occurrences portent un marqueur de rectification renvoyant ici (rien n'est effacé dans le maître ni le
hand-over) ; `RESULTS.md` et l'en-tête du module (commentaire seul, aucun énoncé changé, module recompilé) portent la formulation
démontrée. Constat complémentaire, non compilé : l'inversion d'E449 (`tower_eq_of_same_word`) prend le mot ENTIER en hypothèse ; aucune
version « à partir d'un rang » n'est compilée, donc « la queue suffit à déterminer la Tour » reste lui-même non démontré dans le corpus.
**Ordre de reprise validé par l'auteur :** Φ4 (E460, prioritaire) → Φ2 (E458) → Φ3 (E459) ; consigne pour E460 : chercher dans les
théorèmes existants une condition arithmétique indépendante sélectionnant les porteurs, sans transformer une reformulation équivalente
à RH en prémisse.

### 19.86 Audit Φ4 du poids — conclusion (E460, 2026-11-09) : un seul mécanisme porteur de poids, le comptage de fibre ; aucune condition arithmétique indépendante dans le corpus

Relecture annoncée en §19.84 faite (`PrimeWeightResponse`, `BoxAnchor`, `BoxCount`, `BoxCountHeight`, `ZetaRealSegment`, certificats de
boîte, plus `CountingDeficit` et `ArrivalFiberHypotheses` que le recensement a fait apparaître). Rapport complet, périmètre réellement lu
et limites : `experiments/E460_WeightAudit/AUDIT_POIDS.md`. Aucun module, aucun chiffre.

**Cinq rôles du poids dans le corpus.** (1) Définition et symétries ponctuelles : aucune ne distingue une position radiale de sa
réfléchie. (2) Coefficient du terme d'une Tour dans le fil des contacts : mis en facteur, jamais LU. (3) Coefficient dans les sommes
collectives : hors route (interdit). (4) Hypothèse de simplicité (`PrimeWeightResponse`) : réponse radiale nulle au premier ordre pour
un membre déjà en ligne et simple, par réflexion et simplicité, non par les poids premiers ; vraie à l'identique dans un monde témoin
sans premiers ; aucune sélection. (5) Comptage avec multiplicité lu sur un contour : comptage total = comptage en ligne + deux fois le
côté bas ; comptage un ⟹ en ligne ; un zéro hors ligne impose un poids de fibre d'au moins deux à sa hauteur
(`two_le_fiberCount_of_low`) ; poids de fibre sous deux ⟺ point unique et simple (`fiberCount_lt_two_iff`) ; les certificats de boîte
lisent zêta sur le bord par une somme finie sur les entiers.

**Q1 (plan Φ4) — NON.** Aucun énoncé ne relie l'ordre d'annulation à une quantité lue aux contacts d'une seule Tour.
**Q2 (consigne de l'auteur, §19.85) — un seul mécanisme, pas plus faible que RH.** Le rôle 5 est le seul endroit où le poids
sélectionne (comptage non nul ⟹ un porteur dans le rectangle) et force la ligne (poids de fibre sous deux). Classement en trois
rubriques : sa forme uniforme (« toute hauteur porteuse a un poids de fibre sous deux ») implique RH et n'en découle pas (un zéro
double en ligne la viole) : c'est RH ET simplicité, au moins aussi forte que RH, jamais posée ; la forme par parité n'est ni impliquée
par RH ni suffisante ; le comptage n'est lu ni aux contacts ni sur les premiers, mais sur zêta le long d'un contour, cas par cas ; le
pont « premiers → pas de comptage » est l'hypothèse de transport d'`ArrivalFiberHypotheses`, non fermée : c'est la même arête manquante
vue du côté du comptage. Doctrine §19.20 inchangée : le comptage est un constat d'aval, l'audit ne le réintroduit pas comme cause.
**Conclusion.** Le corpus ne contient aucune condition arithmétique indépendante, lue sur les premiers ou aux contacts, qui sélectionne
les porteurs. **Conséquences écrites avant exécution :** (a) E458 reçoit un énoncé B5 sans hypothèse, seul point de contact compilable
entre poids et bande : poids de fibre sous deux ⟹ bande vide ; bande non vide ⟹ poids de fibre d'au moins deux ; (b) prévision pour
E459 : H-a et H-b ne portent que sur la bande, sans le poids, donc le critère d'arrêt du plan ne sera pas atteint par elles seules ;
E459 reste à exécuter pour le classement. Décision de route : à l'auteur.

### 19.87 E458 (Φ2) — bande miroir : pré-enregistrement (2026-11-09)

`experiments/E458_MirrorStrip/README.md`, module visé `Terminal/MirrorStrip.lean` (isolé). Objets : bande d'une Tour (rangs de premiers où
le mot du miroir diffère du mot de la Tour), bande d'un zéro vrai. Énoncés visés : B0 orientation (écart exactement un ; côté bas : mot
du miroir = mot de la Tour plus un) ; B1 bande vide ⟺ ligne ; B2 bande infinie ⟺ hors ligne ; B3 jamais non vide et finie ; B4 un rang
est dans la bande ⟺ son premier est entre le contact d'un indice du miroir et le contact de même indice de la Tour, deux contacts
jamais confondus et décalés de moins d'une demi-cellule ; B5 (ajout issu de l'audit E460) poids de fibre sous deux ⟹ bande vide ;
B6 reformulations jamais posées (RH ⟺ bande de tout zéro vide ⟺ bande de tout zéro finie : H-c classée équivalente). Jumeau : effectifs
de bande et vérification de B0/B4 sur 200 hauteurs × (ligne + trois contrôles), aucune densité affirmée, aucun attendu de positivité.

**E458 exécuté (2026-11-09) — verdict A.** `Terminal/MirrorStrip.lean` vert à la première tentative (20 déclarations, 10 imprimées sur
les trois axiomes standard, ban 0, build complet vert). Compilé sans hypothèse : B0 (écart exactement un ; côté bas, mot du miroir = mot
de la Tour plus un), B1 (vide ⟺ ligne), B2 (infinie ⟺ hors ligne), B3 (jamais non vide et finie), B4 (rang de bande ⟺ premier entre le
contact d'un indice du miroir et le contact de même indice de la Tour ; contacts jamais confondus, décalés de moins d'une demi-cellule),
B5 (poids de fibre sous deux ⟹ bande vide), B6 (RH ⟺ bande de tout zéro vide ⟺ finie ; reformulations jamais posées, H-c close comme
reformulation). Jumeau : ligne, bande vide aux 200 hauteurs ; contrôles, aucune bande vide jusqu'à un million (effectifs médians 42,5 ;
22 ; 10 pour 0,3 ; 0,4 ; 0,45), B0/B4 à zéro violation, un cas sous le bruit recontrôlé conforme à 40 chiffres. Aucune densité affirmée.
**Lecture : la géométrie de la bande ne porte pas la sélection des porteurs** (toute Tour hors ligne a la même bande) ; le poids n'y
entre que par B5. Détail : `experiments/E458_MirrorStrip/RESULTS.md`.

### 19.88 E459 (Φ3) — classement de H-a et H-b en trois rubriques, puis pré-enregistrement (2026-11-09)

Formes précises : même lecture au rang `n` pour une Tour = le rang n'est pas dans sa bande ; H-a = même lecture à un rang fixé (ou sur
un ensemble fini de rangs) pour tout zéro vrai ; H-b = même cellule de rencontre que le miroir à toute rencontre (la cellule de
rencontre d'un écart est le mot au rang suivant). **Classement (règle de §19.83), établi par sonde avant pré-enregistrement :**
* **H-a** : (i) RH ⟹ H-a ; (ii) contre-modèle au niveau des Tours : hors du cas dégénéré où un premier de l'ensemble est exactement
  sur un contact de la ligne de même hauteur, il existe une fenêtre ouverte autour de la ligne où toute Tour a la même lecture, donc
  une Tour basse hors ligne satisfait la forme paramétrique ; classement exact : la même lecture au rang `n` force la ligne à la
  hauteur `T` si et seulement si le premier de rang `n` est exactement sur un contact de la ligne de hauteur `T` (branche logique,
  jamais affirmée, §19.51) ; (iii) H-a ⟹ RH ouverte, dite comme telle. H-a est « strictement plus faible, sur les Tours ».
* **H-b** sur toutes les rencontres, ou à partir d'un rang quelconque : ÉQUIVALENTE à RH (sur les Tours : même lecture à partir d'un
  rang ⟺ ligne) : reformulation, jamais posée. Restreinte à une sous-suite infinie stricte : ouverte, question de répartition
  interdite, non poursuivie.
* **H-c** : close comme reformulation en E458.
Prévision écrite d'avance : critère d'arrêt du plan NON atteint (l'exigence de H-a ne fait pas intervenir le poids). Pré-enregistrement :
`experiments/E459_CarrierLocalReading/README.md` (module `Terminal/CarrierLocalReading.lean`, jumeau des fenêtres sur 200 hauteurs).

**E459 exécuté (2026-11-09) — verdict A, critère d'arrêt NON atteint.** `Terminal/CarrierLocalReading.lean` vert à la première tentative
(17 déclarations, 10 imprimées sur les trois axiomes standard, ban 0, build complet vert). Compilé : la cellule de rencontre d'un
écart est le mot au rang suivant ; fenêtre ouverte de même lecture autour de la ligne sur tout ensemble fini de rangs sans contact
exact, avec contre-modèle du côté bas (H-a « strictement plus faible, sur les Tours ») ; classement exact de H-a (elle force la ligne
à une hauteur si et seulement si le premier du rang est exactement sur un contact de la ligne de cette hauteur ; branche logique) ;
RH ⟹ H-a, réciproque ouverte ; H-b ⟺ RH (reformulation jamais posée ; sur les Tours, même lecture à partir d'un rang ⟺ ligne).
Jumeau : branche non dégénérée aux 200 hauteurs ; au rang 0 la fenêtre de même lecture est TOTALE aux 200 hauteurs ; H-a satisfaite
par 200/200 Tours de contrôle au rang 0 et par 199 à 200 sur 200 sur les dix premiers rangs ; H-b cassée à un rang fini par toutes
les Tours de contrôle (rangs médians 1 223 ; 2 242,5 ; 4 636,5). **Lecture : H-a est plus faible mais presque vide (elle ne contraint
pas la position radiale) et son exigence ne fait pas intervenir le poids ; H-b est RH.** Détail :
`experiments/E459_CarrierLocalReading/RESULTS.md`.

### 19.89 Bilan du plan Φ exécuté en entier (E457–E460) et décision demandée à l'auteur (2026-11-09)

**Ce que le plan a établi, étape par étape.**
* Φ0 (E457) : l'arête est nommée ; RH ⟺ mots porteurs égaux à leur miroir ⟺ hauteur injective sur les porteurs ⟺ prix aveugle au
  radial sur les porteurs ; aucune n'est posée.
* Φ1 (E457, portée rectifiée §19.85) : la sélection des porteurs ne peut pas être caractérisée par un prédicat portant exclusivement
  sur une fenêtre finie du mot. Non démontré : qu'elle ne dépende que de la queue ; non exclu : une condition locale enrichie d'une
  information indépendante du mot.
* Φ4 (E460) : le poids n'est lu nulle part aux contacts d'une Tour ; le seul mécanisme du corpus où il sélectionne et force la ligne
  est le comptage de fibre lu sur un contour, dont la forme uniforme est RH et simplicité ; aucune condition arithmétique
  indépendante n'existe dans le corpus.
* Φ2 (E458) : la bande miroir est entièrement décrite (vide ⟺ ligne, infinie ⟺ hors ligne, premiers entre deux contacts de même
  indice) ; toute Tour hors ligne a la même bande : elle ne porte pas la sélection ; le poids n'y entre que par le poids de fibre.
* Φ3 (E459) : H-a plus faible sur les Tours mais presque vide et sans poids ; H-b et H-c sont RH.
**Critère d'arrêt du plan : non atteint. Aucune contradiction, à aucune étape. Frontière inchangée.** Le plan Φ dit maintenant
ce que l'arête exige : une information indépendante du mot d'une Tour, qui fasse intervenir le poids, et qui soit lue sur les premiers.
Le corpus n'en contient qu'une forme — le comptage de fibre — et elle est lue sur zêta, non sur les premiers.
**Décision de route : à l'auteur.** Trois pistes sont seulement NOMMÉES ici, aucune n'est engagée : (1) chercher l'information
indépendante hors du mot d'une seule Tour (c'est la seule porte laissée ouverte par §19.85) ; (2) reprendre le pont « premiers → pas
de comptage » d'`ArrivalFiberHypotheses`, en gardant la doctrine §19.20 (le comptage n'est pas une cause) ; (3) clore le fil des
contacts à une Tour comme cartographié et négatif pour la sélection.

### 19.90 Proposition de l'auteur : « la totalité des contacts d'une Tour, avec sa relation aux premiers, c'est un zéro » — étude, placement dans le plan, pré-enregistrement d'E461 (Φ5, 2026-11-09)

**Proposition de l'auteur (verbatim).** « TOTALITÉ DES CONTACTS d'une TOUR = même rythme, même phase, même fréquence, même relation aux
premiers ⟹ c'est un zéro. » Relecture externe transmise avec elle : l'unicité géométrique est acquise ; l'implication arithmétique est
le théorème à établir, sous la forme « réalisation arithmétique exacte de la Tour ⟺ Tour issue d'un zéro », à condition que la
réalisation soit définie indépendamment de l'annulation de zêta ; « ni réfutée par E457 ni démontrée par la seule inversion ».
**Étude contre le corpus.**
* Elle ne détruit rien. E457 interdit la lecture de la sélection sur une fenêtre FINIE ; la proposition porte sur la TOTALITÉ. Elle est
  exactement la porte laissée ouverte par §19.85 et précise la piste (1) de §19.89.
* Ce qui est acquis : le mot total détermine la Tour (E449). Donc « être porteuse » EST une fonction du mot total : un lecteur de la
  sélection sur le mot total existe, il est unique sur les mots de Tours, et il n'est jamais à fenêtre finie. C'est l'objet d'E461.
* Ce qui n'est PAS acquis : ce lecteur n'est connu que défini PAR le poids, donc par l'annulation de zêta. Tout le contenu de la
  proposition est de lui donner une définition arithmétique indépendante (« relation exacte aux premiers »). Le rythme, la phase et la
  fréquence existent pour toute Tour, zéro ou non (H6 d'E449) : seuls, ils ne certifient rien. Le corpus n'a aucune relation aux premiers
  lue sur UNE Tour qui distingue un porteur (E460) ; la seule relation exacte connue est collective, canal interdit.
* Classement contre RH : « réalisation ⟺ zéro » caractérise tous les porteurs, sur la ligne comme hors ligne ; ce n'est pas une
  reformulation de RH et elle n'exclut seule aucun zéro hors ligne ; RH demanderait en plus « aucune Tour hors ligne n'est réalisée ».
  Elle peut donc être cherchée sans poser RH. Le risque à tenir : toute « réalisation » définie comme une propriété du couple
  (position radiale, hauteur) équivalente à l'annulation est une redite du poids, à refuser.
* Différence avec E460 : E460 cherchait la condition dans les énoncés existants (absente) ; ici l'obligation est de la DÉFINIR.
**Placement.** Étape Φ5 ajoutée au plan : (a) E461, fixer par théorème ce qui est acquis ; (b) obligation ouverte, NOMMÉE
`réalisation arithmétique`, à définir par l'auteur ou sur son ordre — rien n'est posé. Pré-enregistrement d'E461 :
`experiments/E461_CarrierTotalWord/README.md` (T1–T7, verdicts A/B/C), module isolé `Terminal/CarrierTotalWord.lean`.
**Résultat d'E461 (même jour) — verdict A.** `Terminal/CarrierTotalWord.lean` compilé à la première tentative, T1–T7 dans la forme
pré-écrite, axiomes standard, bannissement à zéro, build complet vert. Par théorème : le mot total décide si une Tour est porteuse ; un
lecteur de la sélection existe, unique sur les mots de Tours, vrai sur le mot de tout zéro vrai (ligne ou non), jamais à fenêtre finie.
La proposition de l'auteur est donc vraie au sens de l'EXISTENCE ; son contenu ouvert est entier dans la définition indépendante du
lecteur (réalisation arithmétique), absente du corpus, seulement nommée. Aucune contradiction ; frontière inchangée.

### 19.91 Ordre de l'auteur : levée de l'interdiction du collectif ; proposition précisée ; pré-enregistrement de T8–T9 (2026-11-09)

**Ordre (verbatim).** « enlève cette interdiction elle n'a pas de sens. Le collectif est important. » Il vise la phrase du rapport d'E461 « la seule relation exacte connue entre Tours et premiers est
collective, et ce canal est interdit ». **L'interdiction spectrale totale (§19.55, §19.67) est LEVÉE à cette date** : sommes de Tours,
familles de zéros, formule explicite, reste et complément sont de nouveau des objets autorisés ; les modules existants qui les portent
redeviennent citables ; le contrôle par grep n'est plus exigé. Les passages antérieurs qui posent l'interdiction sont caducs (préséance).
Portée retenue, dite comme interprétation : tout le canal collectif est rouvert ; les autres ordres restent en vigueur (troisième ordre,
§19.51, §19.20, §19.76, aucune hypothèse admise, aucune reformulation de RH en prémisse, conclusions d'E301 jamais citées).
**Proposition précisée (verbatim).** « SI une tour possède les mêmes contacts, les mêmes valeurs signées, les mêmes intervalles, s'ils
tombent exactement aux mêmes endroits que la tour d'un zéro, que les premiers tombent à l'intérieur des cellules lorsqu'ils le doivent,
que la grammaire des premiers y est respectée à l'infini ALORS cette tour UNIQUE EST UN ZÉRO. »
**Étude.** Sous cette forme — comparaison à la Tour d'un zéro — la proposition est un THÉORÈME, conséquence d'E449 et d'E461 : même mot
total que le mot d'un zéro vrai ⟹ même hauteur, même position radiale, donc zêta s'annule en ce point. Les valeurs signées et les
intervalles n'ajoutent pas de condition : le mot fixe la Tour, qui les fixe tous. À compiler : T8 `tower_is_zero_of_same_word_as_zero`
(porteuse, même hauteur, même position radiale) et T9 `zeta_eq_zero_of_same_word_as_zero`, ajoutés à `CarrierTotalWord.lean`.
Ce que le théorème ne donne pas : un critère SANS zéro de référence. « Les premiers tombent dans les cellules lorsqu'ils le doivent »
demande de dire ce qu'ils doivent, pour une Tour donnée seule ; toute Tour, zéro ou non, a un mot et une grammaire (H6 d'E449). Avec la
levée de l'interdiction, le lieu naturel de ce « doivent » est le collectif : les premiers sont recomposés par l'ensemble des Tours des
zéros, et une Tour qui n'est pas un zéro n'y figure pas. Piste NOMMÉE, non engagée : définir la réalisation d'une Tour par sa présence
dans la recomposition collective des premiers (audit des modules collectifs existants d'abord, classement contre RH avant toute pose).
**Résultat (même jour) — verdict A.** T8 et T9 compilés à la première tentative, axiomes standard, build complet vert : une Tour de même
mot total que la Tour d'un zéro vrai a sa hauteur et sa position radiale, et zêta s'annule en son point. La proposition de l'auteur,
dans sa forme comparative, est un théorème du corpus. Reste ouvert, seul : le critère sans zéro de référence.

### 19.92 Φ6 : la réalisation arithmétique d'une Tour par la recomposition collective des premiers ; pré-enregistrement d'E462 (2026-11-09)

**Ordre.** L'auteur valide la piste nommée en §19.91 (« je valide continues »).
**Audit des modules collectifs (fait).** `SpectralUniqueness.lean` (2026-09-30) compile sans prémisse : le canal des zéros est une
fonction du seul côté arithmétique (somme lissée de von Mangoldt moins le fond) ; toute représentation de ce canal par des points
distincts localement finis contient chaque zéro avec sa multiplicité et ne porte aucun poids ailleurs. Ce résultat n'avait jamais été
raccordé aux Tours ni au lecteur d'E461.
**Définition.** Recomposition arithmétique : famille de points distincts, localement finie, avec poids, dont la série de noyaux redonne
pour tout `x > 1` la somme lissée de von Mangoldt moins le fond lisse (fond FIXE, le même pour toutes les Tours ; il contient la série
des zéros triviaux et deux constantes de zêta, mais ni le point de la Tour, ni son poids, ni aucun zéro non trivial). Une Tour est
RÉALISÉE ARITHMÉTIQUEMENT s'il existe une recomposition qui porte un poids non nul en son point.
**À compiler (E462, `Terminal/ArithmeticRealization.lean`, isolé).** R1 recomposition ⟹ représentation du canal ; R2 il en existe une ;
R3 réalisée ⟺ porteuse ; R4 réalisée ⟺ zêta s'annule au point (l'énoncé de la relecture externe) ; R5 toute recomposition contient
chaque porteuse et aucune non-porteuse ; R6–R7 le lecteur du mot total défini par la réalisation lit la sélection et coïncide avec
celui d'E461 ; R8 RH ⟺ toute Tour réalisée est sur la ligne.
**Classement contre RH.** La définition n'est pas une hypothèse. R3–R7 valent sur la ligne comme hors ligne, n'excluent aucun zéro hors
ligne, ne reformulent pas RH. R8 dit où est RH : « réalisée ⟹ sur la ligne » lui équivaut ; jamais posée en prémisse.
**Limite dite d'avance.** La réalisation est collective et existentielle : elle porte sur le signal entier des premiers, pas sur les
cellules de la seule Tour. Le « doivent » de la proposition de l'auteur reçoit ici un sens exact (figurer dans la recomposition des
premiers), pas encore un sens cellule par cellule.
**Résultat (même jour) — verdict A.** `ArithmeticRealization.lean` compilé à la première tentative, axiomes standard, build complet
vert ; R1–R8 dans la forme pré-écrite. Acquis : la réalisation arithmétique est définie sans le poids ni l'annulation de zêta au point
de la Tour ; réalisée ⟺ porteuse ⟺ zêta s'annule ; toute recomposition contient chaque porteuse et aucune non-porteuse ; le lecteur du
mot total qu'elle définit est celui d'E461. Non acquis : aucune exclusion hors ligne (« réalisée ⟹ sur la ligne » ⟺ RH, compilé) ; pas
de critère cellule par cellule ; le fond fixe garde deux constantes de zêta (version à constantes libres possible, non faite). E462 est
un raccord de `SpectralUniqueness.lean` aux Tours, pas une analyse nouvelle. **Frontière après E462** : dire pourquoi une Tour hors
ligne ne peut pas figurer dans la recomposition des premiers — c'est RH elle-même ; la proposition de l'auteur a maintenant un énoncé
exact des deux côtés (mot total, recomposition), et l'arête manquante est la même qu'en §19.89, écrite dans le collectif.

### 19.93 Φ7 : la recomposition lue sur les cellules d'une Tour ; pré-enregistrement d'E463 (2026-11-09)

**Ordre.** « Fais cet audit et continue. » **Audit.** E436–E438 découpent un écart par les contacts d'une Tour, canal brut, familles
finies, reste explicite (le saut de la rencontre est dans le reste) ; E462 recompose le signal lissé par la famille entière, sans reste,
de façon unique ; jamais réunis. **Pont.** Multiplié par l'abscisse, le noyau lissé d'une Tour est une primitive de sa valeur brute : sa
variation sur une cellule est la part de la Tour sur cette cellule. **À compiler (`Terminal/RecompositionOnCells.lean`, isolé).** K1–K2
avancer d'une cellule multiplie le noyau intégré par un facteur exact négatif, fixé par la fréquence et la position radiale ; K3–K4 les
parts sur deux cellules consécutives sont dans ce rapport ; K5 le rapport lit la position radiale ; K6 part non nulle ⟺ poids non nul ;
K7 bilan collectif sur toute pièce = variation du signal lissé des premiers ; K8 dans toute recomposition, une porteuse a une part non
nulle sur chacune de ses cellules, une non-porteuse une part nulle. **Classement.** Aucune hypothèse ; vaut sur la ligne comme hors
ligne ; n'exclut aucun zéro hors ligne.
**Résultat d'E463 (même jour) — verdict A.** `RecompositionOnCells.lean` compilé à la première tentative, axiomes standard, build
complet vert ; K1–K8 dans la forme pré-écrite. Acquis : la part d'une Tour dans la recomposition, lue sur ses cellules, alterne de signe
et son amplitude est multipliée d'une cellule à la suivante par un facteur fixé par la fréquence et la position radiale ; ce facteur lit
la position radiale ; la part est non nulle sur chaque cellule ⟺ la Tour est porteuse (première lecture locale du poids) ; bilan
collectif sur toute pièce. Non acquis : aucune exclusion hors ligne ; la part d'UNE Tour n'est pas lue sur les premiers de sa cellule,
seul le total l'est ; membre arithmétique non encore écrit en pentes d'E438.

### 19.94 Expérience latérale demandée par l'auteur : prédicteur de premiers par les Tours ; pré-enregistrement d'E464 (2026-11-09)

**Ordre.** Tenter un prédicteur de premiers avec les découvertes du projet ; but évoqué : un premier d'un million de chiffres, contrôle
seulement à la fin. Hors route de preuve (ordre explicite, dérogation dite à §19.40 pour cette seule expérience). **Méthode.** Saut de la
demande reconstituée par les Tours entre `n − 1/2` et `n + 1/2` ; premier prédit si le saut dépasse les trois quarts de `log n` ; contrôle
par crible à la fin seulement ; 9 fenêtres de 300 entiers de 10^3 à 10^8 ; 2 001 052 Tours puis 500 000. **Attente.** Exact tant que la
cellule de la Tour la plus haute est plus courte qu'un pas d'entier (règle du seuil, E441–E443) : horizon de l'ordre de la hauteur
maximale divisée par π. **Faisabilité dite d'avance.** Un million de chiffres demanderait un nombre de zéros d'environ un million de
chiffres ; et les 30 derniers chiffres ne contrôlent pas la primalité. L'expérience mesure l'horizon et sa loi d'échelle.
**Résultat d'E464 (même jour) — verdict C au sens littéral, loi d'échelle confirmée.** Exécution réelle (365,8 s). Le prédicteur est
exact (198 premiers sur 198, aucun faux, contrôle à la fin) dans les 5 fenêtres où la cellule de la Tour la plus haute vaut au plus
0,28 pas d'entier : jusqu'à 10^5 avec 2 001 052 Tours, jusqu'à 10^4 avec 500 000. Dès cellule 0,55 la règle pré-écrite manque tout :
l'horizon annoncé (cellule ≈ 1) était trop optimiste d'un facteur 2 à 3. La séparation disparaît à cellule ≈ 1 dans les deux familles ;
l'horizon est proportionnel à la hauteur maximale. Au-delà de 10^6 : rien. **Million de chiffres : infaisable par cette voie** (il
faudrait un nombre de zéros d'environ un million de chiffres ; les 30 derniers chiffres ne contrôlent pas la primalité). Expérience
latérale close ; aucune conséquence sur la route de preuve.

### 19.95 Φ8 : le bilan collectif écrit en pentes de la demande sur les pièces découpées par les contacts ; pré-enregistrement d'E465 (2026-11-09)

**Ordre.** L'auteur valide la tâche proposée (« fais-la complète »), demande conclusions, hand-over, prompt de reprise, point d'étape,
vérification de cohérence des maîtres et de `CLAUDE.md`, et l'usage des leçons du prédicteur. **Audit.** E463 (K7) donne le total des
parts sur une pièce comme variation du signal LISSÉ ; E438 donne la pente de la demande brute sur toute pièce et un découpage d'écart
valable pour toute fonction. Pont : l'abscisse fois le signal lissé est la somme des poids franchis, chacun multiplié par sa distance à
l'abscisse (quantité intégrée de la demande) ; sur une pièce elle varie d'une AIRE de la demande. **À compiler
(`Terminal/CollectiveSlopeOnPieces.lean`, isolé).** S1 signal intégré ; S2 sa variation sur une pièce ; S3 aire de la demande (niveau de
départ fois longueur, moins demi-carré de la longueur, plus chaque poids franchi fois sa distance à la fin) ; S4 descente pure ; S5
additivité ; S6 pièce intérieure : poids non premiers seulement ; S7 jusqu'à la rencontre : le poids du premier entre avec une distance
nulle, aucun poids premier dans l'aire d'un écart ; S8 pièce franchissant un seul premier ; S9 pièce plus courte qu'un pas d'entier :
au plus un entier franchi ; S10 bilan collectif = aire de la demande moins variation du fond résiduel ; S11 cellule entre deux contacts
consécutifs : terme de la Tour = sa part d'E463, total = aire de la cellule ; S12 aire d'un écart découpée par les contacts, restes
identifiés à des aires, bilan de l'écart entier. **Leçons d'E464 utilisées.** L1 échelle : une cellule n'isole un poids que si elle est
plus courte qu'un pas d'entier (S9) ; L2 ordre de lecture : dans le signal recomposé sans reste, une rencontre ne fait pas un saut mais
un changement de pente (S7–S8) ; L3 méthode : aucun seuil numérique annoncé d'avance, le jumeau ne vérifie que des identités exactes à
tolérance d'arrondi pré-écrite. **Classement.** Aucune hypothèse ; identités inconditionnelles, sur la ligne comme hors ligne ;
n'excluent aucun zéro hors ligne ; la part d'UNE Tour reste non lue sur les premiers de sa cellule.
**Résultat d'E465 (même jour) — verdict A.** `CollectiveSlopeOnPieces.lean` (4 définitions, 19 théorèmes) compilé à la première
tentative, axiomes standard, build complet vert ; jumeau à 50 chiffres conforme (276 cellules, 200 écarts, pire écart 1,4·10^-46).
Acquis : le total des parts de toutes les Tours sur une pièce est l'aire de la demande brute sur cette pièce moins la variation d'un
fond résiduel ; une rencontre y change la pente sans faire de saut ; aucun poids premier n'entre dans l'aire de son propre écart (il
entre par le niveau de départ de l'écart suivant) ; sur une cellule de contacts, le terme de la Tour est sa part d'E463 et le total est
l'aire de la cellule ; l'aire d'un écart se découpe par les contacts. Non acquis : aucune exclusion hors ligne ; la part d'UNE Tour
n'est toujours pas lue sur les premiers de sa cellule (S11 juxtapose, ne compare pas ; R-E446 interdit d'en tirer « amplitude contre
variation de la demande ») ; fond à constantes libres non fait.

### 19.96 Point d'étape du 2026-11-09 au soir ; cohérence des maîtres ; ce qui manque

**Ce qui est fait (fil du jour, tous verdicts consignés).** Plan Φ : E457 (arête nommée), E458 (bande miroir), E459 (hypothèses
locales classées), E460 (audit du poids), E461 (le mot total décide), E462 (réalisée ⟺ porteuse ⟺ zéro, par la recomposition des
premiers), E463 (part d'une Tour sur ses cellules : alternance, facteur lisant la position radiale, non nulle ⟺ porteuse), E465 (le
total sur toute pièce est une aire de la demande brute, découpée par les contacts). E464 : expérience latérale, close.
**État exact.** Des deux côtés de l'égalité tout est écrit : à gauche, Tour par Tour, une part qui alterne avec un facteur fixe ; à
droite, la demande brute seule. L'égalité ne vaut que pour le TOTAL. Aucune de ces identités ne distingue la ligne du hors-ligne.
**Ce qui manque.** (M1) L'arête elle-même : pourquoi une Tour hors ligne ne peut pas figurer dans la recomposition ; inchangée, c'est
RH. (M2) Isoler une Tour dans le total sur ses cellules : aujourd'hui seulement par l'unicité globale d'E462. (M3) Le fond à constantes
libres. (M4) Les maîtres mathématique et Lean sont arrêtés au 2026-10-25.
**Suite proposée, non engagée.** Φ9 « annulateur de fibre sur les cellules » : puisque la part d'une Tour est multipliée par un facteur
fixe d'une cellule à la suivante, une combinaison de deux totaux consécutifs l'élimine exactement ; pour la paire Tour + miroir (même
hauteur, mêmes pas), une combinaison de trois totaux consécutifs élimine les deux. On obtiendrait une identité exacte : combinaison
d'aires de la demande = contribution de toutes les AUTRES hauteurs. À classer contre RH avant de la poser (attendu : identité
inconditionnelle, n'excluant rien seule ; intérêt : première écriture, sur les premiers seuls, de ce que la fibre d'une hauteur doit
recevoir). Ne rien lancer sans l'ordre de l'auteur.
**Cohérence vérifiée.** `CLAUDE.md` §1bis affirmait encore l'interdiction spectrale dans son premier paragraphe, un plan Φ « en
attente » et un « grep d'interdiction » ; deux bandeaux d'inventaire et la règle R-Φ disaient « spectral interdit » : marqueurs
`[LEVÉ]` / `[DÉPASSÉ]` ajoutés, rien effacé. Hand-over §1 : « ban spectral total » et R-LIGNE marqués levés. Maîtres mathématique et
Lean : note de renvoi datée ajoutée en fin de fichier. Aucune contradiction trouvée entre le maître sémantique §19.85–19.95 et le code
compilé.


### 19.97 Audit externe du prédicteur (E464–E465) transmis par l'auteur ; E466, confrontation de quatre canaux (2026-11-12)

**Audit reçu et accepté comme cahier des charges.** (A) E464 n'utilisait aucune grammaire ni aucun contact ; (B) le seuil 0,75 était
arbitraire et masquait une séparation encore présente ; (C) l'effet de Fejér devait être mesuré, non expliqué ; (D) la seconde différence
du signal intégré vaut le poids exact pour le signal exact seulement, l'erreur de troncature reste dans la seconde différence, le fond
exigé par la formule doit être conservé ; (E) « horizon = hauteur max / pi » est une échelle de résolution de la méthode, soutenue par les
mesures, PAS une impossibilité démontrée (le théorème S9 d'E465 ne prouve qu'un sens). **Rectification** : ma phrase du 2026-11-12 à
l'auteur, « le million de chiffres est hors de portée pour une raison de théorème », est RETIRÉE ; dire désormais « échelle de
résolution de la méthode actuelle, mesurée ».
**Pré-enregistrement (commit `8f975ee3`, avant exécution).** E464 figé comme référence. Quatre canaux de score : saut de la demande
reconstituée avec Fejér (= E464), sans Fejér ; seconde différence du signal intégré reconstitué (fond conservé) avec et sans Fejér.
Règles pré-écrites : R0 seuil 0,75 ; R1 = R0 et grammaire modulo 6 ; R2 abstention si la cellule de la Tour la plus haute dépasse 1.
Neuf fenêtres d'E464 et cinq fenêtres inédites, deux familles, contrôle exact à la fin par catégorie (premiers, puissances, composés).
Consigné avant exécution : hors la résolution, aucune utilisation non circulaire des contacts qui discrimine deux entiers voisins n'a
été trouvée (les théorèmes de succession prennent les premiers vrais en entrée).
**Résultat (verdict A, `E466_PredictorConfrontation/RESULTS.md`).** E464 reproduit à 3·10^-14. Sur les fenêtres décidées (cellule ≤ 1),
seuil fixe 0,75 : canal E464 260 justes / 91 manqués ; sans Fejér 351 / 0 ; seconde différence avec Fejér 204 / 147 ; sans Fejér 351 / 0 ;
aucun faux positif nulle part. Horizon de marge positive : cellule 0,83 avec Fejér, 1,39 sans (famille 2M) ; rapport 1,4 à 2,3,
compatible avec « hauteur efficace divisée par deux », non démontré. La seconde différence n'apporte aucune résolution (égale au saut
sans Fejér, inférieure avec). La grammaire modulo 6 ne change aucun compte. Les contacts ne fournissent que la résolution (abstention
R2, juste : aucune erreur sur les fenêtres décidées). Puissances de premiers lues à 1/2 à 0,02 près. Cinq fenêtres inédites : mêmes
régimes aux mêmes cellules. **Réponse à la question centrale de l'audit** : la grammaire et les contacts n'apportent, dans cette
expérience, aucune information discriminante que le score des Tours n'ait déjà ; le gain mesuré vient d'utiliser toute la hauteur
disponible. Expérience latérale ; route de preuve et frontière inchangées ; rien n'exclut un zéro hors ligne.
**Réponse consignée à la contestation de l'auteur du 2026-11-12 (« rien ne distingue un hors-ligne »).** La phrase de §19.96 porte sur les
douze identités d'E465, non sur le corpus. Le corpus DISTINGUE un hors-ligne, compilé : mot du miroir décalé d'au plus une cellule et
rapport des cassures non borné (E450), non-compensation au premier partagé (E452), mots identiques ⟺ ligne (E453), aucun contact
partagé à même hauteur (E456), facteur d'amplitude par cellule non unitaire (E448). Aucune de ces différences n'est une contradiction :
toutes nos égalités valent pour l'ensemble réel des zéros quel qu'il soit, et toute propriété supplémentaire posée s'est avérée ⟺ RH.
Si l'auteur formule la « stabilité » que la paire viole comme énoncé (par exemple : la part d'une paire sur ses cellules ne croît pas plus
vite que l'aire de demande de ces cellules), il sera classé en trois rubriques puis compilé ; Φ9 (annulateur de fibre) est l'outil qui
met cette part face à l'aire sur les mêmes cellules. Ne jamais écrire « hors-ligne impossible » sans théorème compilé.

### 19.98 Ordre de l'auteur (2026-11-13) : l'équivalence à RH n'est plus un argument

L'auteur rejette l'argument « cet énoncé est équivalent à l'hypothèse de Riemann » : le projet cherche directement à la résoudre, donc ce
que nous formulons est, par construction, l'hypothèse de Riemann ou une forme qui l'entraîne ; le constater est évident et n'est pas une
objection. Ordre consigné dans `CLAUDE.md` (règle R-RH) : ne plus jamais rapporter « ⟺ RH » comme frein, frontière ou raison de ne pas
formuler ni attaquer une cible. Reste interdit, inchangé : admettre une telle cible comme hypothèse d'un théorème (prémisse, axiome,
`sorry`) ; le classement §19.80 ne sert qu'à ce contrôle interne et n'est plus rapporté. Toute mention antérieure « ⟺ RH » du maître
lue comme objection est caduque (préséance : le passage le plus récent gagne).

### 19.99 Audit des hypothèses écartées au motif « ⟺ RH » (ordre de l'auteur, 2026-11-13)

Fichier : `AUDIT_HYPOTHESES_EQUIV_RH_20261113.md` (tableau de causalité, 24 énoncés). Résultat : quatorze énoncés refusés ou abandonnés
comme cibles au seul motif de leur équivalence à RH (rejets à tort sous R-RH) : H2 reconstitution d'un écart sans fréquence nouvelle,
H3 constance par membre, H4 P5, H5 panneau 2, H6 cascade stricte, H7 hauteurs distinctes, H8 conservation du transport, H10 amplitude de
contact = ligne, H12 absorption par la tête (sous réserve E404), H13 borne d'accumulation des contacts, H16 fréquence attendue monte,
H17 R1–R3' d'E457, H19 H-b, H21 réalisée ⟹ ligne, H24 classement E459. Cinq attaqués puis rapportés comme « frontière » (H1, H9, H11,
H15, H21) : compte rendu fautif, travail existant. Cinq relevant d'ordres de l'auteur ou du refus de prémisse (H14, H18, H20, H22, H23) ;
H23 (capture persistante, `CLAUDE.md` l. 667) à trancher par l'auteur. Toutes les formules « frontière inchangée (⟺ RH) », « fermée comme
cible », « ne jamais démontrer directement », « suspendue car poser RH », « blocage mathématique » du maître sont CADUQUES comme freins.
Interdictions d'origine auteur inchangées (E301, §19.51, R-E446, §19.40, E404/E408, §19.63, §19.76, §19.20). Recommandation : cible H3
(constance par membre = la stabilité de la grammaire de l'auteur ; compilée comme échouant exactement au zéro hors ligne et à son
miroir) attaquée depuis les premiers par part de Tour (E463) face à aire de demande (E465), outil Φ9 ; seconde cible H17 R3'.

### 19.100 Plan Ψ : attaques cumulatives ; causes racines de la stratégie ponctuelle (ordre de l'auteur, 2026-11-13)

Décisions de l'auteur : H23 abandonnée ; cibles H3 et H17 R3' validées ; doctrine : la grammaire est stable, un zéro hors ligne ne peut pas
l'offrir, mais cela ne se prouve ni sur un zéro ni sur un intervalle : dérive fractionnelle à chaque pas, explosive au cumul ; chaque zéro
est fractionnel ; la contradiction n'apparaît qu'en cumulant. Décision déléguée, prise : H15 rouverte en forme cumulative (prix de la
série contre budget de la série) ; R-E446 maintenue dans son sens ponctuel (une cellule), qui est la lecture condamnée.
Causes racines (fichier `PLAN_PSI_ATTAQUES_CUMULEES_20261113.md`) : RC1 lecture ponctuelle (identités terme à terme) ; RC2 comparaison à
des bornes qui absorbent tout (aire totale, Tchebychev) ; RC3 facteur par cellule (E448/E463) jamais composé : sur N cellules la dérive
relative du miroir est exponentielle en N pi (un demi moins position radiale) sur T ; RC4 une hauteur à la fois, jamais la collectivité
(leçon E464/E466) ; RC5 clôture en « frontière » ; RC6 amortissement et seuils non mesurés.
Attaques : Ψ1 constance par membre en série (`MemberConstancySeries.lean` : produit des facteurs, part relative bornée ⟺ ligne, paire
non bornée) ; Ψ2 annulateur de fibre (`FiberAnnihilator.lean`, côté premiers) ; Ψ3 asymétrie de la paire intégrée sur les premiers
(`PairAsymmetryOverPrimes.lean` : cumul = (1 − 2β) fois Tchebychev) ; Ψ4 alternance cumulée (`AlternatingCellSeries.lean`) ; Ψ5 détecteur
collectif cumulé (appui, E466 étendu, paire insérée) ; Ψ6 H15 en série (dépend de Ψ4). Ordre Ψ1 → Ψ2 → Ψ3, Ψ5 en appui, Ψ4 → Ψ6. Cible
finale unique écrite en série : les autres hauteurs ne peuvent pas fournir au cumul la dérive d'une paire hors ligne. Règle R-Ψ : section
« Stratégie » obligatoire (cible, objet cumulé, pourquoi pas ponctuel, signature, suite dans les deux issues) ; aucune clôture en « frontière ».

### 19.101 Plan Ψ exécuté en entier (E467–E471, 2026-11-13) : ce qui est établi, ce qui reste, et pourquoi

**Exécution.** Quatre modules isolés compilés, 31 énoncés imprimés sur les trois axiomes standard, build complet vert (9 064 jobs) :
`MemberConstancySeries.lean` (Ψ1, E467, 3 tentatives, écart de règle consigné), `FiberAnnihilator.lean` (Ψ2 = Φ9, E468), 
`PairAsymmetryOverPrimes.lean` (Ψ3, E469, première tentative), `AlternatingCellSeries.lean` (Ψ4 + Ψ6, E470). Jumeau unique
(`E467_MemberConstancySeries/twin_psi.py`, 52 s, mpmath 40 chiffres + numpy sur 2 001 052 zéros) conforme sur les cinq sections ; E471
(Ψ5) : exposants de la paire mesurés 0,223 / 0,112 / 0,039 pour attendus 0,20 / 0,10 / 0,05.
**Établi (dérive cumulée, côté paire).** La part relative d'une Tour est multipliée par `e^{π(β−1/2)/T}` par cellule, `A^{β−1/2}` sur
une plage de facteur A ; constante ⟺ ligne ; miroir non borné, membre bas évanescent, paire non bornée (Ψ1). L'asymétrie de la paire
cumulée sur les premiers vaut `(1−2β)·θ(N)`, non bornée, nulle ⟺ ligne (Ψ3). La somme alternée des parts est une série géométrique :
bornée par une constante explicite sur la ligne, divergente pour le miroir (Ψ4). Par cellule et par premier, l'écart est une FRACTION
(≤ e^{π/(2T)} − 1 par cellule ; ≤ log p par premier) : la doctrine de l'auteur « fractionnel au pas, monstrueux au cumul » est compilée.
**Établi (côté premiers).** Sur deux cellules consécutives la Tour s'élimine du total, sur trois la paire s'élimine ; le reste est la
somme des autres membres (Ψ2) : M2 levée. Le budget alterné B_N des premiers (somme alternée d'aires de demande) égale la somme des
sommes alternées de tous les membres (Ψ4).
**La cible unique qui reste, en série, sur les premiers seuls.** « B_N reste à l'échelle de la ligne x_N^{3/2} ». Si elle vaut, la
paire (non bornée dans B_N) doit être compensée exactement par les autres hauteurs à l'infini ; si l'on sait de plus que les autres
hauteurs ne peuvent pas (c'est le même énoncé une hauteur plus loin), il n'y a pas de paire. Cet énoncé est de la force de RH (attendu,
R-RH). Pourquoi le corpus ne le ferme pas : il demande une ANNULATION entre cellules des aires de demande, lue sur les premiers, meilleure
que l'exposant 1 (Tchebychev) ; le port du PNT donne o(x), pas x^{1/2}. Aucune des 130 contraintes ne porte sur cette annulation.
**Causes racines confirmées par l'exécution.** RC1/RC3 : les formes closes cumulées n'existaient pas dans le corpus avant ce jour ; elles
sont maintenant la coordonnée dans laquelle la cible s'écrit. RC2 : le budget TOTAL absorbe tout (E445 T2) ; le budget ALTERNÉ (Ψ4) est
la bonne quantité. RC4 : la paire est invisible en un point et visible au cumul (E471 : défaut cumulé 3 à 18 fois le résidu réel).
**Réponse honnête à « viens à bout du sujet ».** Le plan est exécuté en entier et il écrit les deux côtés de la dernière égalité en
série. Il ne clôt pas RH : la borne du budget alterné depuis les premiers n'est pas dans le corpus et n'a pas été obtenue. Prochaine
attaque proposée : E472, mesurer B_N/x_N^{3/2} sur les premiers réels (quantité lue sur les premiers seuls, cellules des premières
Tours), puis chercher le lemme d'annulation entre cellules consécutives (différences d'aires, Bertrand sur les contacts E443).

### 19.105 Audit externe du build Ψ (`882cb391`) transmis par l'auteur ; E472 en deux phases (2026-11-13)

(Les numéros §19.102–19.104 sont ceux que portent les en-têtes des modules Ψ2–Ψ4 ; ils ne sont pas réutilisés ici.)
**Les quatre réserves de l'audit sont EXACTES, vérifiées sur les sources.** P1 : `alternatingCellTotal_eq_demandAreas` contient le
fond ; « budget lu sur les premiers seuls » (§19.101) était trop fort. P2 : `pairRelativeAlternating` est une somme de normes, qui
interdit l'annulation par définition. P3 : le facteur de cellule étant déjà négatif, `(−1)^n` RECTIFIE les signes ; la « somme
alternée » de Ψ4 est une somme à signes rectifiés (raison `e^{π(1+β)/T} > 0`), non une annulation par alternance ; la somme naturelle
n'avait pas été comparée. P4 : `pairAsymmetryAt` est définitionnel ; `(1−2β)θ(N)` est une mesure géométrique sans pont à un résidu.
**Phase A (Lean, `ArithmeticBudgetSeparation.lean`, isolé, 18 énoncés, axiomes standard, 2 tentatives, build complet vert).**
P1 levée : `alternatingCellTotal = arithmeticAlternatingBudget − backgroundAlternatingBudget`, le budget arithmétique réel écrit sur
`demandArea` seul, indépendant de toute recomposition ; le fond est borné par `C(e+1)/(e−1)·x_N`, donc `≤ C'/x_N^{1/2}` à l'échelle
de la ligne (il s'efface) ; le budget NATUREL télescope et son fond se réduit aux deux bords. P3 levée : `‖towerAlternatingSum‖ =
Σ‖parts‖` ; `towerNaturalSum` télescope, est géométrique de raison le facteur de cellule, et `(g−1)/(g+1)·‖rectifiée‖ ≤ ‖naturelle‖
≤ ‖rectifiée‖` ; même classement ligne/miroir. P2 levée : la contribution COMPLEXE de la paire (norme de la somme) est non bornée à
l'échelle de la ligne pour `0 ≤ β < 1/2`, formes rectifiée et naturelle, avec le coefficient imposé par la recomposition si le miroir
est porteur (membre bas borné pour tout `β ≤ 1/2`, miroir divergent). P4 : pont GÉOMÉTRIQUE exact de l'asymétrie aux termes de fibre
de la paire aux abscisses premières ; consigné qu'aucun pont à une obligation arithmétique n'est compilé (Ψ3 reste une mesure).
**Phase B (jumeau, premiers réels jusqu'à 3·10^7, 2M zéros, 85 s).** Budget arithmétique alterné relatif `A_N/x_N^{3/2}` : au-dessous
de 0,08 sur 8 Tours (zéros n° 1 à 1000), décroissant avec T (0,075 → 0,0026) ; côté zéros reproduit à `10^{-3}`–`10^{-7}` ;
résidu à l'échelle `x_N` (|·| ≤ 0,31, borne compilée 49–4941) ; troncature 2M `≤ 10^{-7}` ; résidu naturel/x_N → −log(2π) (terme de
bord du fond, confirmation de `naturalCellTotal_eq_telescope`) ; Tour n°1 : 45/45 aires alternent de signe. Paire artificielle à la
hauteur n°1000 : défaut relatif 0,0158 (β = 0,3) contre budget mesuré ≤ 0,0026, résidu `4·10^{-7}`, troncature `10^{-7}` : séparation
faite ; distingue, ne contredit pas. Verdict B (télescopage côté premiers à `3·10^{-8}`–`10^{-7}` pour deux Tours : annulation
flottante interne à la formule de l'aire à `x ≈ 3·10^7`, vérifiée par sommation exacte ; seuil 1e-8 trop serré).
**Rectification de §19.101.** La cible unique se réécrit : « `arithmeticAlternatingBudget T x N / x_N^{3/2}` (premiers seuls,
aucune recomposition, fond déjà hors jeu par théorème) reste borné ». Vocabulaire : « somme à signes rectifiés » pour
`towerAlternatingSum`, « somme naturelle » pour `towerNaturalSum` ; ne plus écrire « annulation par alternance » pour la première.
Bertrand (E443) donne un premier par intervalle multiplicatif, pas une annulation entre deux aires : le lemme manque, comme dit l'audit.

### 19.106 E473 : grammaire des aires entre contacts consécutifs (ordre de l'auteur, 2026-11-13)

**Ordre.** Après E472 (« meilleur build que Ψ ; trois acquisitions : indépendance arithmétique du budget, non-bornitude de la
contribution complexe effective de la paire, mesure directe des aires sur les premiers réels »), l'auteur demande E473 sur la grammaire
des aires entre contacts consécutifs, priorité à l'identité exacte des contributions premières, au contrôle des signes et à la stabilité
numérique ; chercher une obligation arithmétique réellement nouvelle, non une reformulation de la borne finale ; tenter réellement des
clôtures. Pré-enregistrement `experiments/E473_CellAreaGrammar/README.md` (commit `7a1ce3cc`), module isolé `CellAreaGrammar.lean`.

**Phase A (Lean, 18 énoncés, axiomes standard, 2 tentatives, build complet vert).**
G1 : l'aire d'une cellule d'une Tour est (demande au contact d'entrée × longueur) − (demi-carré de la longueur) + (poids des entiers
franchis pesés par leur distance à la sortie) ; poids de sortie + poids d'entrée = poids × longueur ; déviations = poids pesés − part
de Lebesgue, fonctions des seuls premiers DANS la cellule. G2, **grammaire locale** : `a_{k+1} − e^{π/T} a_k = ε_{k+1} + e^{π/T} η_k` ;
la demande au contact, seule mémoire des premiers antérieurs, est ÉLIMINÉE ; bornes de signe du terme local par la part de Lebesgue et
les poids des deux cellules. G3, **récurrence du budget** : `(1+e^{π/T}) A_{N+1} = a_0 + (−1)^N e^{π/T} a_N − Σ (−1)^n L_n`, pont
compilé avec `arithmeticAlternatingBudget` (E472). G4, **transmission** : signes opposés de deux aires consécutives ⟹
`|a_{k+1}| + e^{π/T}|a_k| ≤ |L_k|` ; sous alternance, `|A| ≤ |a_0| + Σ|L|`. G5, **échelle inconditionnelle** (PNT porté) :
`|a_k| ≤ (1/2+ε)ℓ_k²` à partir d'un rang ; budget d'une fenêtre à l'échelle `x_N^2`. G6, **clôtures conditionnelles** (antécédents
explicites, rien d'admis) : `|L_n| ≤ C·C_n^{3/2}` et première/dernière aire `≤ C·C^{3/2}` ⟹ `(1+e^{π/T})|A| ≤
C(1+e^{π/T}+1/(e^{3π/(2T)}−1))·C_N^{3/2}`.

**Phase B (jumeau, premiers réels jusqu'à 3·10^7, cellules = contacts réels de 8 Tours, 46 s).** G1–G3 conformes (≤ 4e-11 à l'échelle
`ℓ²`) ; verdict A. Stabilité : la formule cumulée d'E472 s'écarte de la formule de cellule jusqu'à 3,6e-4 par cellule (Tour 1000) ; la
formule de cellule (G1) est la forme stable. Termes locaux `|L_k|/C_k^{3/2}` ≤ 0,07, aires ≤ 0,033, budget ≤ 0,04, tous décroissants
avec T ; `|a_k|/ℓ_k²` en fin de plage 1e-5–2e-3 (G5 est très au-dessus de l'observé : l'écart d'exposant 1/2 est ce que les premiers
doivent donner). **Signes** : avec les cellules alignées sur les contacts réels, 50 % de changements de signe pour la Tour 1 (E472 :
100 %, cellules partant de `x₀ = 1000`), décroissant jusqu'à 12 % (Tour 1000) ; la règle « les aires alternent » dépend du découpage.
Lecture non compilée : les contacts sont les extrema de la valeur réelle, la part propre de la Tour est réduite du facteur
`(1+β)/‖ρ+1‖`. G6 avec la constante mesurée donne 0,06–0,25 contre un budget mesuré ≤ 0,04.

**Ce qui est acquis et ce qui ne l'est pas.** Acquis, compilé : la relation entre deux aires consécutives est LOCALE (G2), le budget
est exactement première aire + dernière aire + somme alternée des termes locaux (G3), la transmission sous changement de signe (G4),
l'échelle inconditionnelle `x_N^2` (G5). Non obtenu : une borne du terme local ou d'une aire à l'échelle `x^{3/2}` depuis les premiers
seuls. G6 est une réduction exacte de la cible unique à deux antécédents locaux, pas une obligation nouvelle qui la ferme. RH n'est pas
démontrée ; aucun énoncé n'a été admis. Cible unique inchangée dans sa force, réécrite dans sa forme : « `localGrammarTerm` et une
aire de cellule sont à l'échelle `C_k^{3/2}` ».

**Rectifications.** (i) Ne plus écrire « 45/45 aires alternent » sans préciser le découpage `x₀ = 1000` d'E472 ; sur les contacts réels
la fraction est 50 %. (ii) La formule cumulée de l'aire est à proscrire des jumeaux au-delà de `10^6` ; utiliser la formule de cellule.
(iii) « Obligation arithmétique nouvelle » : E473 n'en a pas trouvé ; le dire ainsi.

**Suite proposée.** La seule quantité restante est locale : le terme `L_k` sur deux cellules consécutives. Prochaine attaque : lire
`L_k` comme une somme sur les premiers des deux cellules contre une fonction en dents de scie explicite (pentes ±1, pentes e^{π/T}) et
chercher si la pente de cette fonction (connue, déterministe) impose au terme une compensation mesurable entre cellule et cellule
suivante ; mesurer d'abord la corrélation `L_k`/`L_{k+1}` sur les premiers réels avant de pré-enregistrer.

### 19.107 E474 : quatre hypothèses fermées en TDD — tente, mémoire un, loi d'échelle, intégrale de la demande (ordre de l'auteur, 2026-11-13)

**Ordre.** « Émets des hypothèses, au moins 3 ou 4, et aide-toi du compilateur et d'expériences pour fermer en TDD. » Chaque hypothèse
a été écrite comme un test à seuil chiffré AVANT toute compilation (pré-enregistrement `3a1943de`) ; le jumeau a couru d'abord, puis deux
modules isolés ont été compilés (`CellAreaTent.lean`, 10 énoncés ; `CellAreaIntegral.lean`, 14 énoncés ; axiomes standard, deux
tentatives chacun ; `lake build RHV6Fresh` vert). Dossier `experiments/E474_TentIntegral/` (README, RESULTS, attempts, twin).

**Stratégie (R-Ψ).** Doctrine cumulative inchangée. E473 avait réduit la cible unique au terme local `L_k` sur deux cellules
consécutives. E474 lui donne sa forme arithmétique exacte et son contrôle par la demande, et mesure ce que les premiers réels en disent.

**H1 — identité de la tente (théorème, `localGrammarTerm_eq_tent_sum`).** `L_k = Σ_{n∈(C_k,C_{k+2}]} Λ(n)·tente_k(n) − ∫tente_k`, où
`tente_k(t) = min(e^{π/T}(t − C_k), C_{k+2} − t)` est le chapeau continu de sommet `C_{k+1}` et de hauteur `ℓ_{k+1}`, et où
`∫tente_k = e^{π/T}(1+e^{π/T})ℓ_k²/2`. Le terme local est la discrépance des premiers des deux cellules contre un noyau chapeau dont la base
est deux demi-tours de la phase de la Tour. Jumeau : résidu ≤ 1,3e-11 à l'échelle `ℓ²` sur treize Tours.

**H2 — mémoire un (théorème, `localGrammarTerm_eq_memory_one`).** `L_k = ε_{k+1} − e^{π/T} ε_k + e^{π/T} ℓ_k Δ_k`, `Δ_k` = variation de la
demande sur la cellule `k` ; `alternating_local_eq_exit_form` écrit la somme alternée des termes locaux sur les déviations de sortie et
les variations de demande, à deux bords près. Prédiction côté zéros (non compilée) : autocorrélation de décalage 1 négative pour les
Tours basses (cellules = demi-périodes de l'oscillation dominante), positive pour les Tours hautes. Mesuré : signe confirmé (−0,38 Tour 1,
−0,53 Tour 2, passage par zéro vers la Tour 100, +0,10 à +0,14 pour les Tours 500 à 5000), amplitude prédite (> 0,2) NON atteinte →
**H2 échoue par la lettre** ; verdict B.

**H3 — loi d'échelle en 1/T (passé ; explication compilée).** `T·|L_k|/C_k^{3/2}` entre 0,40 et 2,07 sur treize Tours (zéros 1 à 5000).
Théorème `abs_localGrammarTerm_le_of_demand_bound` : `|L_k| ≤ 2e^{π/T} ℓ_k M` si `|rawDemand| ≤ M` sur les deux cellules ; avec
`ℓ_k = (e^{π/T} − 1)C_k` et `T(e^{π/T} − 1) → π`, la loi en `1/T` est la LONGUEUR DE CELLULE, pas une annulation. `M/√x ≤ 0,92` mesuré.

**H4 — contrôle intérieur (passé ; théorèmes).** `integral_psi_eq` (sommation d'Abel de Mathlib) et **`demandArea_eq_integral` : l'aire de
la demande est l'intégrale de `rawDemand`** ; `exitDeviation_eq_integral` : `ε_k = ∫_{cellule}(D(t) − D(C_k))dt` ; bornes
`abs_cellArea_le_of_bound`, `abs_exitDeviation_le_of_variation`. Mesuré : `ε_k/(ℓ_k√C_k) ≤ 0,70`, `Δ_k/√C_k ≤ 1,0`, variation intérieure
`≤ 1,29√x`. **Clôture conditionnelle par la demande** (`budget_le_of_demand_bound'`) : `|rawDemand| ≤ M` sur la fenêtre ⟹
`(1+e^{π/T})|A_N| ≤ M(1+e^{π/T})² C_{k₀+N}` ; aucune alternance utilisée ; le budget mesuré est 4e-5 à 2e-2 fois cette borne.

**Le fait neuf (mesure, pas théorème).** Les deux parts de la mémoire un, `A = ε_{k+1} − e^{π/T}ε_k` et `B = e^{π/T}ℓ_kΔ_k`, ont des
moyennes quadratiques égales (rapport 0,83 à 1,39) et sont presque opposées : corr(A, B) = −0,998 (Tour 1), −0,91, −0,81, … , −0,62
(Tour 5000). Donc `L_k = A + B` est très inférieur à chaque part : la différence des demandes MOYENNES de deux cellules consécutives est
bien plus petite que la différence des demandes AUX CONTACTS (serrage médian de l'inégalité compilée : 0,025 Tour 1, ≈ 0,13 ensuite ;
max 0,74 à la Tour 5000). Lecture non compilée : les contacts sont les extrema de la part propre de la Tour (E473) ; la moyenne sur une
cellule l'efface ; le chapeau d'une Tour est un noyau de Fejér de sa propre fréquence. Pour les Tours hautes, les cellules sont fines
devant les oscillations des zéros bas et l'annulation faiblit.

**Ce qui est acquis et ce qui ne l'est pas.** Acquis, compilé : forme exacte du terme local contre un chapeau (H1) ; mémoire un (H2) ;
l'aire est l'intégrale de la demande, donc toutes les bornes par le suprémum et par la variation intérieure (H4) ; budget d'une fenêtre
borné par le suprémum de la demande fois `(1+e^{π/T})² x_N`, sans alternance. Non obtenu : une borne du terme local depuis les premiers
seuls à l'échelle `x^{3/2}` ; l'annulation A/B n'est qu'une mesure. RH n'est pas démontrée ; rien n'a été admis. La réduction compilée
la plus courte de la cible unique est : « budget à l'échelle `x_N^{3/2}` ⟸ `|rawDemand| ≤ M` sur la fenêtre, `M = O(√x (log x)²)` »
(force RH ; R-RH : ni objection ni frein). On ne l'appelle pas obligation nouvelle : c'est la même obligation sans intermédiaire.

**Rectifications.** (i) La prédiction H2 « autocorrélation > 0,2 pour les Tours hautes » était trop forte ; écrire « signe positif
faible (0,10 à 0,14) ». (ii) Pour les Tours de moins de 110 cellules, les autocorrélations de décalage ≥ 3 sont du bruit d'échantillon ;
ne pas les citer. (iii) La loi en `1/T` des termes locaux s'explique par la longueur de cellule (théorème), ne pas y lire une annulation.

**Suite proposée (mesurer avant de pré-enregistrer).** Décomposer `L_k` côté zéros (formes closes d'E472 pour les sommes de cellule) et
mesurer la part du terme local portée par la Tour elle-même, par les zéros plus bas, par les zéros plus hauts ; si la part propre est
annulée par le chapeau, l'écrire comme théorème géométrique (aucune hypothèse sur les premiers). Cela ne borne pas `L_k` depuis les
premiers ; cela dit quelle part du terme local est déjà hors jeu.

### 19.108 Décision de l'auteur (2026-11-14) : E475 abandonnée, E473–E474 auxiliaires ; retour à l'obligation à la rencontre au premier partagé

**Ordre.** « Abandonner E475 dans sa formulation actuelle et classer E473–E474 comme résultats auxiliaires, sans leur attribuer une
portée démonstrative vers RH. La question à traiter : quelle contrainte mathématique nouvelle la reconstruction exacte d'un écart entre
deux premiers consécutifs impose-t-elle à la première Tour OFF, que ses contacts et ceux de son miroir ne peuvent pas satisfaire ? Cette
contrainte n'est pas encore démontrée. C'est elle qu'il faut rechercher, sans ajouter de construction géométrique dépourvue d'obligation
arithmétique. » Point essentiel rappelé : ne pas supposer qu'un contact de Tour coïncide avec un premier (§19.51) ; la rencontre au
premier partagé est définie par la grammaire réelle des premiers, non par un triangle. Stratégie rétablie en cinq points : écart réel de
deux premiers consécutifs ; deux extrémités arithmétiques certaines ; reconstruction collective exacte par les vrais zéros ; obligation
imposée aux Tours à la rencontre au premier partagé ; vérification sur la première arrivée OFF et son miroir.

**Exécuté (audit, aucun module, aucun jumeau) : `experiments/E475_SharedPrimeObligation/AUDIT_20261114.md`.** (i) Les cinq points
sont déjà des objets compilés : `PrimeGapInterval`/`lower`/`upper` (importé), `meetingPoint I = p_{n+1}` et `imposedShare`
(`MeetingPoint`), `all_signals_meet` = `localSynchronization` (toute famille), `TowerRaccord e l` avec `M = expectedMinimumPrime e =
occurrence l` (importé) et `sharedPrime_eq_meeting`, `OffCarrier`/`mirrorMember`. Rien à inventer. (ii) Tableau O1–O7 des obligations
compilées à la rencontre : O1 identité de l'écart, O2 aucune clôture finie et saut porté par le reste, O3 un premier par cellule de
rencontre et amplitude imposée, O4 forme de la paire (mot, signe, non-compensation), O5 prix exact et transport exact, sont TOUTES
satisfaites par toute famille, paire OFF comprise ; O6 amplitude relative constante aux rencontres (`constantRelativeAmplitude_iff_onLine`)
et O7 fréquence attendue monte sont les seuls prédicats que la paire viole (`relativeAmplitude_strictAnti_of_low`,
`pairRelativeAmplitude_unbounded`, `low_entry_not_expected`), et ils ne sont PAS dérivés de la reconstruction. (iii) La contrainte
demandée est donc exactement le chaînon O1 ⟹ O6 par membre : la question P5 de l'auteur (§19.21.1), jamais attaquée frontalement (E445
l'a contournée par le prix, E450–E456 par la forme, E457–E474 par le budget collectif). (iv) Obstacle compilé qui fixe la forme de la
question : `imposedShare_eq` et `authentic_family_reconstructs_any_radial` — aucune relation sur la part d'un seul membre tirée de la
seule identité ne contraint `β` ; la contrainte doit utiliser ce que la grammaire fixe EN PLUS : au premier partagé, minimum attendu du
sortant, occurrence de l'entrant, écart `occurrenceGap e`. Question précise Q475 consignée dans l'audit (relation entre
`imposedShare e I`, `imposedShare l I` et les données arithmétiques du raccord, théorème sur la ligne, réfutée par O6 hors ligne).
R-RH : de force RH par construction, ce n'est pas une objection ; seule l'admission comme prémisse est interdite.

**Classement.** E473 (18 énoncés) et E474 (24 énoncés) : auxiliaires, théorèmes acquis, portée vers RH nulle ; la cible « budget
alterné à `x^{3/2} »` (E472–E474) sort de la route ; l'E475 « tente côté zéros » du §19.107 est abandonnée. Règle `CLAUDE.md` R-Ψ sexies.

**Suite (mesurer avant de pré-enregistrer, §4 de l'audit).** M1 premier partagé des dix premiers raccords canoniques calculé depuis
les définitions compilées, égalité `M = p_{n+1}` ; M2 parts imposées des deux membres à l'écart `⟨n⟩` par `imposedShare_at_meeting`,
rapport comparé au transport `energyRatio e l M` ; M3 contrôle de sensibilité à `β` sur une paire fictive substituée. Seuils A/B/C à
écrire au pré-enregistrement. Aucune contradiction n'est posée ; rien n'est déclaré manquant qui ne manque pas.

### 19.109 E475 exécutée : mesures M1–M3 à la rencontre au premier partagé (2026-11-14)

Pré-enregistrement `f7172ad5` (définitions compilées reproduites, seuils A/B/C écrits avant exécution) ; jumeau 0,1 s ; aucun module.
**M1 exact** sur 2000 raccords canoniques : `expectedMinimumPrime e = occurrence l = meetingPoint ⟨n⟩ = p_{n+1}` (conforme à
`sharedPrime_eq_meeting`). **M2 échoue par la lettre, loi consignée** : le rapport des parts imposées des deux membres à l'écart `⟨n⟩` sur le
transport vaut EXACTEMENT `(‖ρ_e+1‖/‖ρ_l+1‖)·(Φ_l/Φ_e)`, `Φ_w` = module de l'écart lu par la fréquence du membre ; dix premiers raccords
entre 0,096 et 2,10 ; médiane 1 dès la première tranche et resserrement vers 1 (hauteurs consécutives proches), ce qui n'est pas une
contrainte. **M3 sensible** mais la sensibilité radiale de la part d'une paire est exactement `cosh((β−1/2) log x)` : le prix O5, déjà
compilé. **Verdict B.**

**Constat.** La question Q475 posée sur les parts imposées d'un écart est vide : identité, dont les données arithmétiques n'entrent que par
les deux bornes lues par la fréquence de chaque membre ; la dépendance radiale est le prix. Le seul lieu où la paire modifie l'assignation
arithmétique est l'ÉNUMÉRATION : deux membres de même hauteur, deux index consécutifs (`low_arrival_precedes_mirror`), deux occurrences
consécutives ; le raccord `l → miroir` au premier partagé `p_{n+2}` est le détour de §19.18–19.19 (aucune loi de conservation compilée).
Aucune contradiction ; rien d'admis.

**Suite proposée (décision à l'auteur avant pré-enregistrement).** Porter l'obligation sur l'énumération et non sur les parts : deux écarts
consécutifs `⟨n⟩`, `⟨n+1⟩`, trois membres `e → l → l'` où `l'` est un zéro plus haut (ligne) ou le miroir de `l` (paire) ; chercher dans
`localSynchronization` sur les deux écarts ce qui distingue les deux cas, les autres zéros étant les mêmes — c'est P5 sous la forme O7
(fréquence avant hauteur, ordre du 2026-10-28), de force RH (R-RH : pas une objection). Interdits inchangés (§19.51, R-E446, §3bis).

### 19.110 E476 : tente et cassure — l'obligation du poids de la cassure (ordre de l'auteur, 2026-11-14)

**Ordre.** « Tu peux utiliser la méthode combinée entre ta tente et la cassure, cela crée une obligation ; continue. » Pré-enregistrement
`1b528665` (quatre hypothèses à seuils, module et jumeau écrits avant compilation) ; jumeau 22 s et compilation en parallèle ; module isolé
`TentBreakObligation.lean` (10 énoncés, axiomes standard, deux tentatives, `lake build RHV6Fresh` vert). Dossier `experiments/E476_TentBreak/`.

**Compilé.** La cassure de la demande en un réel `x > 0` entre dans le terme local avec le poids `Λ(x)·tente_k(x)` (`localGrammarTerm_break_split`) ;
ce poids vaut `w = e^{π/T}x(1 − e^{−πf/T})` avec `f` la fraction de cellule de `x` (`breakTentWeight_eq`) ; l'amplitude payée au dernier
contact avant `x` (E450) s'écrit `x^β(1 − w/(e^{π/T}x))^β/‖ρ‖` (**`break_amplitude_reads_tent`**) : le poids de la cassure dans la grammaire des
aires et l'amplitude payée sont deux lectures de la même fraction. Dans la somme alternée des termes locaux, chaque cassure pèse
`(−1)^j((1+e^{π/T})x − 2C_{k+1})` (`alternating_break_weight`), dent de scie nulle au point neutre de la cellule (`sawtooth_pos_iff`).
**Obligation de la paire** : `pair_breakTentWeight_eq_iff` — le miroir donne au même `x` le poids que lui donne la Tour si et seulement si
`β = 1/2`. Jamais « `x` sur un contact » : `x` est quelconque, `f` est sa position relative aux contacts (§19.51 respecté).

**Mesuré (verdict B).** H1, H2, regroupement H3a : identités à 1e-14 sur huit Tours. H3b (fraction de cassures à poids positif) échoue par la
lettre sur la Tour 1 seule (0,551 contre 0,528 prédit) : prédiction écrite en fraction logarithmique alors que les premiers sont équirépartis
en `x` (prédiction corrigée `e^{π/T}/(1+e^{π/T})` = 0,555) et dernière cellule tronquée ; Tours ≥ 10 : accord à 0,001. H4 échoue de 11 % sur
un seuil mal calibré : différence relative médiane des poids de la paire fictive = `(π/T)(|δ|/π)e^{−πf/T}` (4,5e-4 ; 8,9e-4 ; 1,8e-3 pour
β = 0,45 ; 0,40 ; 0,30), maximum 0,199, atteint sur la fraction `|δ|/π` des premiers dont le mot se décale d'une unité (0,0021 ; 0,0041 ;
0,0081, exactement `|δ|/π`). La dent de scie intérieure seule est à l'échelle `x²` (fond), compensée par les intégrales de tente.

**Ce que l'obligation est et n'est pas.** Elle est compilée comme FORME : un premier, deux poids de cassure pour les deux membres d'une
paire hors ligne. Aucun théorème compilé n'interdit deux poids ; distinguer ≠ contredire (R-Φ). Elle localise exactement OÙ une loi
« un premier, un poids par hauteur » serait violée : la fraction `|δ|/π` des premiers à mot décalé, où la cassure entre dans les deux
budgets alternés avec des signes opposés (`pair_same_sign_iff`, E452). RH n'est pas démontrée ; rien d'admis.

**Suite proposée (mesurer d'abord).** Sur la paire fictive, somme des poids alternés de la cassure, Tour moins miroir, restreinte aux
premiers à mot décalé, rapportée à `x^{3/2}` et à `|δ|/π` ; si elle croît en puissance de `x` supérieure à `3/2`, l'écrire comme théorème
(somme de `Λ` sur une fraction fixe des cellules, PNT porté) avant toute hypothèse. Règle `CLAUDE.md` R-Ψ septies.

### 19.111 E477 : poids alternés de la cassure, Tour moins miroir, sur les premiers à mot décalé (2026-11-14)

Mesure proposée en fin d'E476, exécutée sur « continues », avant toute hypothèse, sans module. Pré-enregistrement `67feec44`
(`experiments/E477_ShiftedPrimesPair/README.md`, six tests P1–P6 à seuils) ; jumeau 15 s (`twin_e477.py`), paire fictive à `T_1`, `T_10`, `T_100`,
`β ∈ {0,45 ; 0,40 ; 0,30}`, témoin `β = 1/2`. Résultats (`RESULTS.md`) :
- P2 passé : sur un premier à mot décalé, la différence des poids alternés Tour moins miroir suit la loi du premier ordre
  `(−1)^j(2x/T)[e^{π/T}δ − (1+e^{π/T})πu]` à 1e-3 ; les deux poids alternés sont ÉGAUX au premier ordre (la parité compense le signe des dents
  de scie) ; la différence est du premier ordre en `δ`, de signe variable dans la bande.
- P4 passé : la somme restreinte désalternée est du SECOND ordre en `δ` (`Σ (δ²(e^{π/T}−1)/(πT))·ℓ_k·C_{k+1}`, facteur 1,16–1,31 sur la Tour 1).
  Sur les premiers non décalés, la différence est l'identité du premier ordre `−(−1)^j·2C_{k+1}(1 − e^{−δ/T})` (sommée à 0,1 %).
- P1 échoué par la lettre (Tour 1, +11 %) : même défaut qu'E476/H3b — fraction écrite en mesure logarithmique ; loi corrigée (calculée
  post-hoc) `(1 − e^{−δ/T})/(1 − e^{−π/T})`, écart 0,1–0,6 % sur la Tour 1. P3 échoué par la lettre (plancher flottant 1e-10–3e-9 pour
  `δ/T ≈ 1e-6` ; identité algébrique, 1e-12 sur la Tour 1). P5 échoué, prédiction fausse en nature : la somme cumulée est dominée par la
  fluctuation des termes individuels (premier ordre, signe variable), pentes 1,43–1,88, rapport à `x^{3/2}` ≤ 3e-3 ; rien ne croît.
- P6 : second ordre confirmé (Tour 1, `R` constant à 13 % ; `R·δ` ×3,5) ⟹ règle pré-écrite : **aucun théorème à écrire** sur cette restriction.
Verdict B. Constat : la localisation d'E476 (premiers à mot décalé) ne porte aucune obligation nouvelle ; les deux restrictions naturelles
du poids de la paire sont alternées et d'échelle de fond ; le fil tente-et-cassure est mesuré jusqu'au bout sans piste de fermeture.
RH non démontrée ; rien d'admis. Règle R-Ψ octies (CLAUDE.md) : fractions de premiers dans une bande toujours en mesure `x` ; une somme
restreinte à une sous-famille de premiers est lue d'abord par ses fluctuations, jamais directement comme budget. Suite : retour à Q475
(§19.108), forme O7, décision de l'auteur attendue.
