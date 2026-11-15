# E421 — résultats (exécutée le 2026-11-03 ; première passe 75 s puis passe corrigée 23 s ; journaux `logs/`)

Correction entre les deux passes (consignée) : la fenêtre d'un pas de la Tour 1 ne contient aucun intervalle complet de cette
Tour, donc les comptes des paires (1, j) étaient vides ; la passe corrigée compte sur une sous-famille dédiée (50 pas de la Tour
basse) ; les coïncidences sont aussi comptées relativement au pas moyen ; l'histogramme de phase est omis pour 2 001 052 (fenêtre de
10 pas de T_max, pas un cycle de la Tour 1). Aucune autre modification ; aucune donnée arithmétique.

## Fusion des contacts sur l'axe (fenêtre à partir de x = 1000)

| N Tours | contacts fusionnés | pas moyen (log) | espacement min (en pas moyen) | coïncidences < 1e−12 | < 1e−3 pas moyen | identité du décalage |
|---|---|---|---|---|---|---|
| 10 | 25 | 8,9e−3 | 8,7e−4 | 0 | 1 | 0 |
| 100 | 996 | 2,2e−4 | 2,8e−4 | 0 | 3 | 0 |
| 1 000 | 55 885 | 4,0e−6 | 1,1e−5 | 0 | 54 | 0 |
| 10 000 | 3 768 653 | 5,9e−8 | 2,1e−7 | 66 | 3 732 | 0 |
| 2 001 052 | 10 456 149 | 2,7e−12 | 0 (résolution float64 ≈ 3e−4 pas) | 3 280 654 | 8 697 | 0 |

* Le décalage exact `log C_j^{(2)} − log C_k^{(1)} = (φ₂+jπ)/T₂ − (φ₁+kπ)/T₁` est tenu à 0 (`interleaving_offset`).
* À 2 001 052 Tours la fusion n'est plus résolue en float64 (pas moyen 2,7e−12 contre résolution 9e−16 sur log x ≈ 6,9) :
  les « coïncidences » à ce niveau sont un artefact de résolution, consigné, non une mesure.
* Histogramme (10 classes) de la position des contacts des autres Tours dans le cycle de la Tour 1 : plat (N = 10⁴ :
  376 762 à 376 928 par classe) — les autres Tours ne se rangent nulle part en particulier dans le cycle de la plus basse.

## Comptes entre contacts consécutifs d'une Tour basse (49 intervalles chacun)

| paire (rangs) | T₂/T₁ | comptes observés | dans {⌊T₂/T₁⌋, ⌈T₂/T₁⌉} |
|---|---|---|---|
| 1–2 | 1,487 | 1 ou 2 | oui |
| 1–3 | 1,769 | 1 ou 2 | oui |
| 2–3 | 1,190 | 1 ou 2 | oui |
| 1–100 | 16,73 | 16 ou 17 | oui |
| 1–1 000 | 100,42 | 100 ou 101 | oui |
| 100–1 000 | 6,001 | 6 | oui |
| 1–10 000 | 698,8 | 698 ou 699 | oui |
| 100–10 000 | 41,76 | 41 ou 42 | oui |
| 1–2 001 052 | 80 121,2 | 80 121 ou 80 122 | oui |
| 100–2 001 052 | 4 788,05 | 4 788 ou 4 789 | oui |

Conforme à `interleavingCount_bounds` ; le compte ne dépend que des hauteurs.

## Sensibilité radiale (synthétique, séparé : Tour à T* = 237,147 insérée dans les 10 000 premières, fichier `data/e421_synthetic.json`)

| β | déplacement (en pas de la Tour) | changements de rang dans la fusion : somme / max | distance minimale miroir (β, 1−β) en pas : mesurée / prédite |
|---|---|---|---|
| ½ | 0 | 0 / 0 | 0 / 0 |
| 0,49 | 1,3e−5 | 53 / 6 | 2,68e−5 / 2,68e−5 |
| 0,45 | 6,7e−5 | 289 / 24 | 1,34e−4 / 1,34e−4 |
| 0,30 | 2,7e−4 | 1 047 / 72 | 5,37e−4 / 5,37e−4 |

* **Prédiction pré-enregistrée réfutée** : « l'ordre d'entrelacement peut changer d'au plus un cran par contact » est FAUX en
  général. Le déplacement est bien inférieur à un demi-pas de la Tour déplacée (`contact_displacement_lt_half_step`), mais ce
  demi-pas contient jusqu'à T'/(2T) contacts d'une Tour plus haute : ici jusqu'à 72 crans dans la fusion. Le module Lean énonce
  seulement la borne par demi-pas et le signale dans sa docstring.
* Les contacts d'une paire miroir hors ligne ne coïncident jamais (`mirror_contacts_coincide_iff`) ; leur écart minimal vaut
  exactement |φ(β) − φ(1−β)|/π pas, soit de 2,7e−5 à 5,4e−4 pas ici : distinct, mais petit devant le pas.

Aucune de ces mesures n'est lue comme une exclusion des zéros OFF : l'entrelacement est aveugle au radial à l'échelle du
comptage, et radialement sensible seulement par un décalage très inférieur au pas.
