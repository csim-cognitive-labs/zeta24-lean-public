# E423 — résultats (exécutée le 2026-11-03, 17 s, `nohup timeout 900 python3 -I`, journal `logs/e423.log`, `data/e423_synthetic.json`)

SYNTHÉTIQUE, séparé : Tours insérées aux hauteurs T* = 17,578 (milieu des zéros 1 et 2), 237,147 (100–101), 2 515,929 (2000–2001),
jamais à la hauteur d'un zéro réel ; β ∈ {0,3, 0,45, 0,49} ; fenêtre [100, 1000]. Aucune donnée arithmétique. Les prédictions
sont celles de `Terminal/ContactRealValue.lean`.

## Déplacement des contacts et valeurs aux contacts déplacés (ON ½ contre OFF β à même hauteur et même indice k)

| T* | β | contacts communs | déplacement log mesuré = prédit (φ(β)−φ(½))/T | constance sur k | en pas | accord de signe à même k | rapport des modules OFF/ON (min–max) | erreur sur le rapport prédit |
|---|---|---|---|---|---|---|---|---|
| 17,58 | 0,30 | 13 | 6,47e−4 | 0 | 3,6e−3 | 13/13 | 0,253–0,388 | 0 |
| 17,58 | 0,45 | 13 | 1,62e−4 | 0 | 9,0e−4 | 13/13 | 0,709–0,789 | 0 |
| 17,58 | 0,49 | 13 | 3,2e−5 | 0 | 1,8e−4 | 13/13 | 0,934–0,954 | 0 |
| 237,1 | 0,30 | 173 | 4,0e−6 | 0 | 2,7e−4 | 173/173 | 0,252–0,397 | 0 |
| 237,1 | 0,49 | 173 | 1,8e−7 | 0 | 1,3e−5 | 173/173 | 0,933–0,955 | 0 |
| 2 515,9 | 0,30 | 1 844 | 3,2e−8 | 0 | 2,5e−5 | 1844/1844 | 0,251–0,398 | 0 |
| 2 515,9 | 0,49 | 1 844 | 1,6e−9 | 0 | 1,1e−6 | 1844/1844 | 0,933–0,955 | 0 |

* Le déplacement est le même pour tous les k (identité `contact_radial_factor`), inférieur au demi-pas, et décroît en 1/T².
* Le signe à même indice est toujours le même (`contactRealValue_mul_pos`) ; l'OFF se distingue par l'amplitude seule :
  rapport C^{β−½}·|ρ_½|/|ρ_β|, soit x^{−0,2} pour β = 0,3 sur [100, 1000].
* Jumeau mpmath (25 chiffres) : écart relatif < 1e−15 sur les trois premiers contacts de chaque scénario.

## Paire miroir (β, 1−β) à même hauteur

| T* | β | distance minimale entre contacts des deux membres (pas) : mesurée = prédite | Im relative du membre miroir aux contacts de β (médiane) | passages sur l'axe de la somme de la paire | déplacement de ces passages par rapport aux contacts ON (médiane / max, en pas) | valeur réelle de la paire à ses passages (rms) | valeur ON aux mêmes positions (rms) |
|---|---|---|---|---|---|---|---|
| 17,58 | 0,30 | 7,2e−3 | 2,3e−2 | 13 (= ON) | −3,0e−3 / 3,2e−3 | 4,38 | 1,15 |
| 17,58 | 0,49 | 3,6e−4 | 1,1e−3 | 13 | −1,0e−5 / 1,2e−5 | 2,31 | 1,15 |
| 237,1 | 0,30 | 5,4e−4 | 1,7e−3 | 173 | −2,2e−4 / 2,4e−4 | 0,313 | 0,083 |
| 2 515,9 | 0,30 | 5,1e−5 | 1,6e−4 | 1 844 | −2,1e−5 / 2,2e−5 | 0,0296 | 0,0079 |
| 2 515,9 | 0,49 | 3,2e−6 | 8e−6 | 1 844 | 0 / 0 | 0,0157 | 0,0079 |

* Les deux membres passent sur l'axe en des positions distinctes (`mirror_contacts_coincide_iff`), à un écart de l'ordre de
  (1−2β)/(πT) pas ; au contact de l'un, l'autre n'est pas sur l'axe (partie imaginaire relative non nulle, petite).
* La somme de la paire (quatre termes avec conjugués) possède exactement autant de passages sur l'axe que la Tour ON, déplacés
  de moins d'un centième de pas ; ses valeurs y sont plus grandes que celles de la Tour ON (le membre 1−β domine, en x^{1−β}).

## Contexte collectif (famille réelle des 2 001 052 zéros de ligne, 15 premiers contacts ON de T*)

| T* | β | rms de S_F aux contacts ON | rms de la contribution ON (½+iT*) | rms OFF seule | rms paire | part médiane de la paire dans |S_F| | variation de S_F entre contacts ON et contacts déplacés (rms) |
|---|---|---|---|---|---|---|---|
| 17,58 | 0,30 | 4,88 | 2,31 | 0,68 | 8,77 | 1,91 | — (contacts hors fenêtre commune) |
| 237,1 | 0,30 | 2,58 | 0,089 | 0,035 | 0,263 | 0,150 | 7,5e−4 |
| 237,1 | 0,49 | 2,58 | 0,089 | 0,085 | 0,178 | 0,102 | 3,3e−5 |
| 2 515,9 | 0,30 | 3,44 | 0,0080 | 0,0032 | 0,0233 | 0,0055 | 2,5e−5 |
| 2 515,9 | 0,49 | 3,44 | 0,0080 | 0,0076 | 0,0160 | 0,0038 | 1e−6 |

* L'insertion change S_F exactement de la contribution insérée (identité) ; une paire insérée pèse, à T* = 2 516, moins d'un
  centième de la somme collective aux contacts ; à T* = 17,6 elle la domine.
* La somme collective réelle évaluée aux contacts déplacés diffère de celle aux contacts ON de 1e−6 à 7,5e−4 (rms) : le
  déplacement des contacts est invisible dans S_F à cette échelle.

Conclusion descriptive : à même hauteur, ON et OFF ne diffèrent aux contacts que par l'amplitude (x^β contre x^{½}) et par un
déplacement de phase inférieur au demi-pas (en (½−β)/T²) ; la paire miroir ajoute un membre dominant. Aucune de ces mesures
n'exclut un zéro OFF : elles décrivent ce qu'il ferait aux contacts.
