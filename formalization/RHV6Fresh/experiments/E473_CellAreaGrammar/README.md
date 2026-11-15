# E473 — grammaire des aires entre contacts consécutifs : identité exacte des contributions premières, contrôle des signes,
stabilité numérique, tentatives de clôture — pré-enregistrement (2026-11-13)

Déclencheur : décision de l'auteur après E472 (« E472 est un meilleur build que Ψ ; lancer E473 sur la grammaire des aires entre
contacts consécutifs, priorité à l'identité exacte des contributions premières, au contrôle des signes et à la stabilité numérique ;
chercher une obligation arithmétique réellement nouvelle, non une reformulation de la borne finale ; tenter réellement des clôtures »).

## Stratégie (règle R-Ψ)
* Cible : écrire l'aire de la demande d'une cellule d'une Tour (`cellArea β T k = demandArea C_k C_{k+1}`) avec les SEULS premiers
  franchis par la cellule et la demande au contact d'entrée, puis éliminer cette demande (l'histoire entière des premiers) par une
  récurrence entre deux cellules consécutives : ce qui reste est LOCAL (premiers des deux cellules, pesés par leur distance aux
  contacts) et c'est l'objet dont le budget arithmétique d'E472 est fait.
* Objet cumulé : le budget arithmétique alterné `arithmeticAlternatingBudget` d'E472, lu sur les cellules d'une Tour (pont compilé),
  réécrit par la récurrence comme : première aire + dernière aire + somme alternée des termes locaux (G3).
* Pourquoi le ponctuel ne suffit pas : inchangé ; ici la récurrence relie DEUX cellules consécutives, c'est la plus petite unité où une
  relation entre aires peut exister.
* Signature attendue d'un hors-ligne : inchangée (E472) ; la grammaire ne la modifie pas, elle en change la lecture : la borne du
  budget est équivalente à la borne de la dernière aire plus celle de la somme alternée des termes locaux (G6, clôture conditionnelle).
* Contrôle interne non rapporté : la clôture inconditionnelle compilée se fait à l'échelle `x_N^2` (PNT porté), la cible est à
  l'échelle `x_N^{3/2}` ; la différence d'exposant est exactement ce que les premiers doivent donner.
* Suite dans les deux issues : si tout compile, mesurer sur les premiers réels les termes locaux et la transmission sous changement
  de signe ; si un énoncé ne compile pas en deux tentatives, le consigner tel quel et mesurer ce qui est défini.

## Phase A — module isolé `Terminal/CellAreaGrammar.lean` (importe E472 `ArithmeticBudgetSeparation`, `BreakMechanismOnLine`)
Commit AVANT compilation ; deux tentatives au plus, journaux dans `attempts/`. Énoncés G1–G6 (voir l'en-tête du module) :
* G1 identité exacte : `cellArea = cellDescentArea + cellExitWeight` (demande au contact × longueur − demi-carré + poids premiers pesés
  par la distance à la sortie) ; `cellExitWeight + cellEntryWeight = cellWeight × cellLength` ; positivité des deux poids ;
  `exitDeviation = cellArea − demande d'entrée × longueur`, `entryDeviation = demande de sortie × longueur − cellArea`.
* G2 grammaire locale : `cellArea (k+1) − e^{π/T} cellArea k = exitDeviation (k+1) + e^{π/T} entryDeviation k` (la demande au contact,
  seule mémoire des premiers antérieurs, est ÉLIMINÉE) ; bornes de signe du terme local par les poids des deux cellules ; cas sans poids.
* G3 récurrence du budget : `(1+e^{π/T}) A_{N+1} = a_0 + (−1)^N e^{π/T} a_N − Σ_{n<N} (−1)^n L_n` ; pont
  `arithmeticAlternatingBudget T (C_{k₀}) N = Σ (−1)^n cellArea (k₀+n)`.
* G4 contrôle des signes : si deux aires consécutives sont de signes opposés, `|a_{k+1}| + e^{π/T}|a_k| ≤ |L_k|` ; sous alternance sur
  une fenêtre, `|A_{N+1}| ≤ |a_0| + Σ |L_n|` (transmission du local au budget).
* G5 échelle inconditionnelle (PNT porté) : `|cellArea| ≤ (1/2+ε) cellLength²` à partir d'un rang ; budget d'une fenêtre
  `≤ (1/2+ε) e^{2π/T}/(e^{2π/T}−1) × (dernière longueur)²` : échelle `x_N^2`.
* G6 clôtures conditionnelles (antécédents EXPLICITES, rien d'admis) : `(1+e^{π/T})|A_{N+1}| ≤ |a_0| + e^{π/T}|a_N| + Σ b_n` dès que
  `|L_n| ≤ b_n` ; forme à l'échelle de la ligne avec la somme géométrique des `C_k^{3/2}`.

## Phase B — jumeau `twin_e473.py` (premiers réels jusqu'à 3·10^7, Tours = zéros n° 1, 2, 3, 5, 10, 20, 100, 1000, β = 1/2)
Lancement `nohup`, journal `logs_twin_run.txt`, résultats `twin_results.json`. Cellules `[C_k, C_{k+1}]` avec `C_k ≥ 1000`,
`C_{k+2} ≤ 3·10^7`. Toutes les sommes de cellule (poids, poids pesés) calculées DIRECTEMENT sur les entiers de la cellule
(`math.fsum`), la demande au contact par ψ cumulée.
Mesures pré-enregistrées :
1. Jumeau de G1 : `cellExitWeight + cellEntryWeight − cellWeight × cellLength`, écart relatif < 1e-10 sur toutes les cellules.
2. Jumeau de G2 : `(a_{k+1} − e^{π/T} a_k) − L_k`, rapporté à `cellLength_k²`, < 1e-9 sur toutes les cellules.
3. Jumeau de G3 : résidu de la récurrence du budget rapporté à `cellLength_N²`, < 1e-9 pour tout N.
4. Stabilité : `cellArea` par la formule de cellule (G1) contre la formule cumulée d'E472 : écart relatif rapporté (aucun seuil).
5. Mesures (aucune borne supposée) : `|L_k|/C_k^{3/2}`, `|a_k|/C_k^{3/2}`, `|a_k|/cellLength_k²` (max et dernier) ; fraction des
   paires consécutives de signes opposés ; sous alternance, `|A_{N+1}|` contre `|a_0| + Σ|L_n|` ; constante C mesurée dans l'antécédent
   de G6 et borne compilée résultante contre `|A_N|/C_N^{3/2}` mesuré.
Verdicts : A = points 1–3 conformes et toutes les valeurs 4–5 rapportées ; B = un point 1–3 non conforme (consigné) ; C = exécution impossible.
