# Plan Ψ — attaques cumulatives (ordre de l'auteur, 2026-11-13)

Décisions de l'auteur consignées : H23 (capture persistante) ABANDONNÉE. Cibles prioritaires H3 (constance par membre) et H17 R3' (même
module des termes du zéro et du miroir) VALIDÉES. Doctrine fixée par l'auteur : la grammaire est stable ; un zéro hors ligne ne peut pas
offrir cette stabilité ; mais cela ne se prouve ni sur un zéro, ni sur deux, ni sur un seul intervalle : c'est une dérive progressive,
fractionnelle à chaque pas, explosive au cumul ; chaque zéro est fractionnel dans sa contribution ; la contradiction n'apparaît qu'en
CUMULANT tous les éléments. Toute tentative doit avoir une stratégie écrite, logique et alignée sur elle.

Décision de l'exécutant sur H15 et R-E446 (l'auteur me l'a déléguée) : H15 (le prix de la rencontre contre le budget) est ROUVERTE sous
sa forme cumulative : prix cumulé sur la SÉRIE des rencontres contre budget cumulé des premiers. R-E446 reste en vigueur dans son sens
d'origine, qui est exactement la lecture ponctuelle que l'auteur condamne : ne jamais chercher la contradiction dans « amplitude d'une
Tour contre variation de la demande sur UNE cellule ». La forme en série n'est pas visée par R-E446.

## 1. Analyse des causes racines (pourquoi « aucune contradiction » à chaque fois)

RC1 — **Lecture ponctuelle.** Toutes les tentatives OFF (E450–E456, E437–E445, §19.9–19.37) lisent un zéro, une cellule, un premier
partagé, une rencontre. Cause structurelle : la formule explicite est une identité terme à terme ; sur un point ou une cellule, chaque
terme vaut pour toute position radiale. Un énoncé ponctuel ne peut donc produire que des identités ou des équivalences. Correction : ne
plus formuler que des énoncés sur la SÉRIE (toutes les cellules d'une Tour jusqu'à x, tous les premiers jusqu'à x, toutes les hauteurs
jusqu'à H).

RC2 — **Comparaison contre des bornes qui absorbent tout.** Le total des Tours vaut l'aire de la demande (E465), le budget de Tchebychev
borne la demande : ces bornes sont satisfaites par construction, zéro hors ligne inclus. Correction : comparer la dérive de la paire à ce
que la stabilité de la grammaire PERMET au cumul (annulation par alternance, E440–E441), non à ce que le total CONTIENT.

RC3 — **Facteur par cellule jamais cumulé.** E448 et E463 compilent que la part d'une Tour est multipliée par un facteur fixe à chaque
cellule, et qu'il lit la position radiale (`towerCellShare_next`, `cell_ratio_reads_radial`). Par cellule, l'écart à la ligne est
fractionnel : exposant pi fois (position radiale moins un demi) sur la hauteur. Jamais composé sur N cellules. Or sur N cellules il vaut
exposant N fois cela : sur une plage logarithmique d'un facteur A, N est T fois (A moins un) fois log x sur pi, et la dérive relative du
miroir est x à la puissance (A moins un) fois (un moins deux fois la position radiale) : c'est la dérive « monstrueuse » de l'auteur,
invisible à chaque pas. Correction : compiler le cumul (produit des facteurs = forme close) et travailler avec lui.

RC4 — **Une hauteur à la fois.** La leçon du prédicteur (E464/E466) : la collectivité des Tours jusqu'à H reproduit exactement les poids
des premiers tant que la cellule la plus fine est au plus un pas ; aucune Tour seule ne le fait ; chaque Tour n'est qu'une FRACTION.
Les attaques OFF n'ont jamais utilisé la collectivité comme détecteur cumulé. Correction : la paire hors ligne se lit dans le résidu
collectif cumulé, pas dans un terme.

RC5 — **Compte rendu en « frontière » après une tentative.** Chaque essai négatif était clos par « frontière inchangée (⟺ RH) » (audit
§19.99). Correction : règle R-Ψ ci-dessous ; chaque tentative porte sa stratégie et sa suite dans les deux issues.

RC6 — **Leçons de méthode d'E464/E466.** Un amortissement (Fejér) divisait l'information par deux sans qu'on le mesure ; un seuil
non étalonné a masqué une séparation présente. Correction : utiliser toute l'information disponible, mesurer avant d'affirmer, conserver
les scores bruts.

## 2. Les attaques (chacune : cible, objet cumulé, pourquoi le ponctuel échoue, Lean, jumeau, signature d'un hors-ligne, suite)

### Ψ1 — H3 cumulée : la constance par membre comme loi de série (cible prioritaire)
* Cible : la part relative d'une Tour réalisée reste bornée le long de la série de ses cellules (⟺ ligne ; accepté, R-RH).
* Objet cumulé : suite des parts `towerCellShare` sur les cellules consécutives d'une Tour, normalisée à l'échelle de la ligne.
* Ponctuel : sur une cellule, la part est non nulle pour toute Tour réalisée (E463) ; rien de plus.
* Lean (`MemberConstancySeries.lean`, isolé) : (a) produit des N facteurs de cellule = forme close ; (b) part relative après N cellules =
  part initiale fois exponentielle de N pi (position radiale moins un demi) sur T ; (c) bornée le long de la série ⟺ position radiale
  égale un demi ; non bornée pour le miroir d'une paire ; tend vers zéro pour le membre bas (forme cumulative compilée de
  `constantRelativeAmplitude_iff_onLine`) ; (d) pour la PAIRE : somme des deux parts relatives, non bornée (le miroir domine).
* Jumeau : parts cumulées des 20 premières Tours réelles sur 10^4 cellules (constantes à 10^-12) ; paire témoin 0,4 / 0,6 insérée
  (croissance mesurée contre la forme close).
* Signature d'un hors-ligne : croissance géométrique de la part relative, exposant (un demi moins position radiale) fois le nombre de
  cellules fois pi sur T.
* Suite dans les deux issues : si (a)–(d) compilent, Ψ2 fournit le côté arithmétique ; sinon consigner l'énoncé exact réclamé.

### Ψ2 — Annulateur de fibre (Φ9) : le côté arithmétique de Ψ1
* Cible : écrire, sur les premiers seuls, ce que les autres hauteurs déposent sur les cellules d'une Tour.
* Objet cumulé : sur trois cellules consécutives, combinaison des aires de demande (E465) à coefficients lisant la position radiale, qui
  élimine la Tour et son miroir ; puis la SUITE de ces combinaisons le long des cellules.
* Ponctuel : une aire seule contient tout.
* Lean (`FiberAnnihilator.lean`, isolé) : identité à deux cellules (élimine une Tour), à trois cellules (élimine la paire), reste = somme
  des autres hauteurs ; puis cumul : somme des N identités.
* Jumeau : identités vérifiées à 10^-40 sur 5 Tours réelles ; résidu « autres hauteurs » mesuré le long de 10^3 cellules.
* Signature : pour une paire hors ligne, la combinaison des aires annulée avec les coefficients de la LIGNE laisse un résidu qui croît
  comme la dérive de Ψ1 ; avec les vrais coefficients, zéro.
* Suite : Ψ1 + Ψ2 donnent la cible unique « les autres hauteurs ne peuvent fournir au cumul la dérive de la paire » (= H21, H1 écrites
  en série).

### Ψ3 — H17 R3' cumulée : asymétrie de la paire intégrée sur les premiers
* Cible : les termes du zéro et du miroir ont le même poids cumulé sur la série des premiers (⟺ ligne).
* Objet cumulé : somme sur les premiers jusqu'à x du logarithme du rapport des modules des deux termes = (un moins deux fois la
  position radiale) fois la somme des logarithmes des premiers (fonction de Tchebychev), donc non bornée hors ligne (Tchebychev
  inférieur, porté).
* Ponctuel : en un premier, le rapport est une puissance de ce premier (E450) ; identité.
* Lean (`PairAsymmetryOverPrimes.lean`, isolé) : forme close du cumul ; non borné ⟺ hors ligne ; borne inférieure explicite via
  Tchebychev porté.
* Jumeau : cumul sur les premiers ≤ 10^6 pour β témoin 0,3 / 0,4 / 0,45 contre la forme close.
* Signature : croissance linéaire en la fonction de Tchebychev ; c'est le « décalage progressif mais monstrueux ».
* Suite : côté arithmétique à écrire comme Ψ2 (la paire doit être payée par les autres hauteurs sur TOUS les premiers).

### Ψ4 — Alternance cumulée : la stabilité de la grammaire comme mécanisme d'annulation (RC2)
* Cible : la somme alternée des aires de cellules d'une Tour (E440–E441 : la descente s'annule par alternance à une cellule près) reste
  à l'échelle de la ligne.
* Objet cumulé : sommes partielles alternées des aires de cellule le long d'une Tour ; comparer aux parts cumulées de Ψ1.
* Ponctuel : une cellule ne s'annule avec rien.
* Lean (`AlternatingCellSeries.lean`, isolé) : la somme alternée des parts d'une Tour sur N cellules est une série géométrique de raison
  −facteur (forme close) ; sur la ligne, bornée relative à l'échelle ; la paire la fait diverger. Puis pont vers les aires (E465 S11).
* Jumeau : sommes alternées des aires réelles sur 10^3 cellules des 5 premières Tours, à l'échelle de la ligne.
* Signature : perte de l'annulation (termes voisins de plus en plus inégaux) pour la paire.
* Suite : si l'annulation mesurée tient à l'échelle de la ligne, chercher le lemme d'annulation depuis les premiers (monotonie locale des
  aires, Bertrand sur les contacts, E443).

### Ψ5 — Détecteur collectif cumulé (RC4, leçon du prédicteur)
* Cible : loi de résolution compilée (la collectivité jusqu'à H reproduit chaque poids premier quand la cellule la plus fine est au plus
  un pas) et résidu cumulé d'une paire insérée.
* Objet cumulé : somme sur toutes les fenêtres du résidu collectif ; avec la paire témoin insérée, compensation exigée cumulée.
* Lean : compilation de la loi de résolution (sens direct, S9 d'E465 ; réciproque mesurée, pas compilée).
* Jumeau : E466 étendu, résidu cumulé, paire 0,4 / 0,6 à une hauteur réelle (prolonge E402, qui mesurait « 2 800 fois le résidu »).
* Signature : croissance du résidu cumulé en x à la puissance (un demi moins position radiale).
* Statut : expérience d'appui et d'étalonnage pour Ψ1–Ψ4 ; ne démontre rien seule.

### Ψ6 — H15 cumulée : prix de la série contre budget de la série
* Cible : le prix cumulé des rencontres (E445, exact, non borné) dépasse ce que les autres hauteurs peuvent payer sur la série.
* Objet cumulé : somme des prix aux N premières rencontres contre somme des aires de demande (budget) ; E445 T2 l'avait tenté avec
  Tchebychev seul (rapport 892 à 5,7·10^8 : le budget total absorbe tout) — c'est RC2 : il faut le budget ALTERNÉ de Ψ4, pas le total.
* Dépendance : Ψ4.

## 3. Ordre d'exécution et règle de stratégie
Ordre : Ψ1 → Ψ2 → Ψ3 (modules Lean, un à la fois, isolés, deux tentatives, jumeau), Ψ5 en appui dès Ψ1, puis Ψ4 → Ψ6. Chaque module
compile d'abord la DÉRIVE CUMULÉE (forme close, non bornée hors ligne) : c'est le côté « paire » ; puis le côté « premiers » (aires,
annulateur, alternance). La cible finale unique, écrite en série : les autres hauteurs ne peuvent pas fournir au cumul la dérive d'une
paire hors ligne. Elle est RH (R-RH : ce n'est pas une objection).

Règle R-Ψ (ajoutée à `CLAUDE.md`) : tout README d'expérience ou de module porte une section « Stratégie » en cinq lignes : cible ;
objet CUMULÉ ; pourquoi la lecture ponctuelle ne suffit pas ; signature attendue d'un hors-ligne ; suite dans les deux issues. Aucune
tentative n'est close par « frontière » ; elle est close par sa suite.
