> Version française conservée à titre de référence. Main language: English, see README.md.

# E472 — budget arithmétique séparé du fond, contribution complexe de la paire, somme naturelle contre signes rectifiés, mesure sur les premiers réels — pré-enregistrement (2026-11-13)

Déclencheur : audit externe du commit `882cb391` transmis par l'auteur (quatre réserves P1–P4, recommandation « E472 en deux phases »).
Les quatre réserves ont été VÉRIFIÉES sur les sources avant ce pré-enregistrement :
* P1 `alternatingCellTotal_eq_demandAreas` contient `residualBackground` : le « budget lu sur les premiers seuls » était trop fort.
* P2 `pairRelativeAlternating` est une SOMME DE NORMES, pas la norme de la somme : elle interdit l'annulation par définition.
* P3 `towerAlternatingSum` multiplie par `(−1)^n` des parts dont le facteur de cellule est DÉJÀ négatif : la raison devient `e^{π(1+β)/T} > 0`.
  C'est une somme à signes RECTIFIÉS, non une annulation par alternance ; la somme naturelle n'avait pas été comparée.
* P4 `pairAsymmetryAt` est définitionnel ; `cumulativeAsymmetry = (1−2β)θ(N)` est une mesure géométrique sans pont compilé à un résidu.

## Stratégie (règle R-Ψ)
* Cible : lever P1–P4 en Lean (phase A) AVANT de mesurer (phase B), pour que la quantité mesurée soit exactement celle que la cible
  unique de §19.101 doit borner.
* Objet cumulé : les séries de cellules de Ψ4, séparées en budget arithmétique (premiers seuls) + budget du fond ; sommes naturelles
  et sommes à signes rectifiés des Tours ; contribution complexe de la paire.
* Pourquoi la lecture ponctuelle ne suffit pas : inchangé (une cellule ne s'annule avec rien).
* Signature attendue d'un hors-ligne : croissance `e^{Nπ(β−1/2)/T}` de la contribution COMPLEXE de la paire (norme de la somme),
  dans la forme rectifiée ET dans la forme naturelle.
* Suite dans les deux issues : si la phase A compile, la phase B mesure `arithmeticAlternatingBudget` sur les premiers réels ;
  si un énoncé ne compile pas en deux tentatives, le consigner tel quel (énoncé réclamé) et mesurer quand même ce qui est défini.

## Phase A — module isolé `Terminal/ArithmeticBudgetSeparation.lean` (importe Ψ4, Ψ3, RawMeetingRemainder)
Commit AVANT compilation ; deux tentatives au plus, journaux dans `attempts/`. Énoncés B1–B4 : voir l'en-tête du module.
Attendus : (B1) `alternatingCellTotal = arithmeticAlternatingBudget − backgroundAlternatingBudget`, indépendance de la recomposition,
fond borné par `C(e+1)/(e−1)·x_N` donc `≤ C'/x_N^{1/2}` à l'échelle de la ligne ; budget naturel télescopé (fond aux deux bords).
(B2) `‖towerAlternatingSum‖ = Σ‖parts‖` ; `towerNaturalSum` télescopée, encadrée : `(g−1)/(g+1)·‖rectifiée‖ ≤ ‖naturelle‖ ≤ ‖rectifiée‖` ;
même classement ligne / miroir. (B3) `‖S_β + S_{1−β}‖/x_N^{3/2}` non bornée pour `β < 1/2`, `w' ≠ 0`, formes rectifiée et naturelle ;
avec le coefficient de la recomposition si le miroir est porteur. (B4) `pairAsymmetryAt β p = log‖part'(p)‖ − log‖part(p)‖ − const`.

## Phase B — jumeau `twin_e472.py` (premiers réels jusqu'à 3·10^7, 2 001 052 zéros, formes closes)
Lancement `nohup`, journal `logs_twin_run.txt`, résultats `twin_results.json`. Tours : zéros n° 1, 2, 3, 5, 10, 20, 100, 1000 ;
`x_0 = 1000` ; cellules jusqu'à `x_N ≤ 3·10^7`.
Mesures pré-enregistrées :
1. Jumeaux de définitions : `demandArea` (forme cumulée contre somme directe) et `demandArea_add` : écart relatif < 1e-8.
2. Télescopage côté premiers du budget naturel (`Nat_N = demandArea(x_0, x_N)`) : écart relatif < 1e-8.
3. `A_N / x_N^{3/2}` (budget arithmétique alterné relatif), `Nat_N / x_N^{3/2}`, `Σ|a_n| / x_N^{3/2}` : valeurs rapportées, AUCUNE borne supposée.
4. Côté zéros `Z_N` (formes closes, 1M et 2M zéros) : résidu `A_N − Z_N` rapporté à `x_N` (attendu : sous la borne compilée du fond
   `C(e+1)/(e−1)`) et à `x_N^{3/2}` ; troncature `(Z_N^{2M} − Z_N^{1M})/x_N^{3/2}` rapportée séparément.
5. Tour n°1000, paire artificielle `β ∈ {0,3 ; 0,4 ; 0,45}` : contribution complexe (norme de la somme) ET somme des normes, défaut par
   rapport à la Tour de ligne, le tout relatif à `x_N^{3/2}` et mis en regard du résidu et de la troncature (séparation demandée par l'audit §4).
6. Pour chaque Tour : `‖naturelle‖/‖rectifiée‖ ∈ [(g−1)/(g+1), 1]` (jumeau de B2) ; fraction des aires de cellule qui alternent de signe.
Verdicts : A = points 1, 2, 6 conformes et toutes les valeurs des points 3–5 rapportées ; B = un point 1, 2 ou 6 non conforme (consigné) ;
C = exécution impossible. Aucune valeur de 3–5 ne peut à elle seule produire un verdict : ce sont des mesures, pas des théorèmes.
