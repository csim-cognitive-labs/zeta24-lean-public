# E420 — résultats (exécutée le 2026-11-03, durée 2,0 s, `nohup timeout 900 python3 -I`, journal `logs/e420.log`)

Données : 2 001 052 hauteurs d'Odlyzko (SHA-256 `2ef7b752…78e7c6` vérifié), posées sur la ligne (hypothèse de données) ; Tours
synthétiques séparées aux milieux des zéros (1,2), (100,101), (2000,2001) (`data/e420_synthetic.json`). Aucune donnée arithmétique.

## Identités (toutes à l'arrondi, sur 10 Tours réelles et 9 synthétiques, 5 221 783 contacts au total)

| Tour (rang) | contacts | max Im/|v| | forme fermée (−1)^k C^β/|ρ| | paires de même signe | rapport d'amplitude e^{βπ/T} | résidu affine de log|v| | jumeau mpmath |
|---|---|---|---|---|---|---|---|
| 1 | 38 | 1,4e−14 | 4,1e−16 | 0 | 7,9e−16 | 2,4e−15 | 1,1e−17 |
| 10 | 135 | 1,0e−13 | 4,0e−16 | 0 | 8,6e−16 | 1,6e−15 | 3,3e−17 |
| 100 | 641 | 4,5e−13 | 4,7e−16 | 0 | 1,1e−15 | 7,1e−15 | 2,4e−17 |
| 1 000 | 3 848 | 3,1e−12 | 5,5e−16 | 0 | 1,6e−15 | 4,0e−15 | 2,5e−17 |
| 10 000 | 26 780 | 2,8e−11 | 5,3e−16 | 0 | 1,3e−15 | 3,6e−15 | 2,7e−17 |
| 100 000 | 203 119 | 1,8e−10 | 6,3e−16 | 0 | 1,6e−15 | 5,3e−15 | 6,7e−18 |
| 1 000 000 | 1 627 395 | 1,5e−9 | 6,7e−16 | 0 | 1,6e−15 | 2,0e−14 | 1,9e−17 |
| 2 001 052 | 3 070 303 | 3,4e−9 | 6,4e−16 | 0 | 1,3e−15 | 3,4e−14 | 3,2e−17 |
| synthétiques (9) | 48 à 6 821 | ≤ 6,4e−12 | ≤ 8,1e−16 | 0 | ≤ 1,6e−15 | ≤ 1,1e−14 | ≤ 6,7e−17 |

* **Valeur réelle au contact** : la partie imaginaire relative croît comme T·ε (évaluation complexe de x^ρ avec T log x ≈ 10⁷) ;
  la forme fermée `(−1)^k C_k^β/|ρ|` est tenue à 7e−16 partout (théorème `towerValue_at_contact`).
* **Alternance** : zéro paire consécutive de même signe sur 5,2 M de contacts (`contactRealValue_alternates`).
* **Enroulement** : log|v_k| affine en k, pente mesurée = βπ/T à 16 chiffres (`log_abs_contactRealValue`) ; nombre de contacts
  pour doubler l'amplitude T·log 2/(βπ) : 6,2 (rang 1), 104 (rang 100), 4 359 (rang 10 000), 499 736 (rang 2 001 052).
  Amplitude du premier au dernier contact dans [2, 10⁴] : 0,104 → 6,36 (rang 1) ; 1,25e−6 → 8,83e−5 (rang 2 001 052).

## Inversion tangentielle depuis les contacts seuls

| Tour (rang) | T̂ = π/Δlog C (erreur rel.) | β̂ par le rapport d'amplitudes (erreur abs.) | β̂ par la tangente, T exact | β̂ par la tangente, T estimé |
|---|---|---|---|---|
| 1 | 6,8e−15 | 2,3e−15 | 1,9e−13 | 1,0e−11 |
| 100 | 1,4e−13 | 4,7e−14 | 7,3e−11 | 7,0e−8 |
| 10 000 | 6,3e−12 | 1,8e−12 | 1,7e−7 | 5,7e−3 |
| 100 000 | 4,3e−11 | 1,6e−11 | 1,1e−5 | 2,2 |
| 2 001 052 | 6,5e−10 | 2,9e−10 | 3,2e−3 | 7,7e+3 |
| synthétiques β = 0,3 / 0,45 / 0,49 | ≤ 1,9e−12 | ≤ 9,2e−13 | ≤ 1,3e−8 | ≤ 1,1e−4 |

* La hauteur et la position radiale sont **récupérables exactement** depuis les contacts et leurs valeurs (théorèmes
  `height_of_contact_log_step`, `radial_of_contact_value_ratio`, `radial_of_contact_tangent`).
* **Conditionnement** : l'inversion par la tangente lit β dans la phase résiduelle T·log C_k − kπ, différence de deux nombres
  de l'ordre de T·log x (≈ 10⁷ à T_max) ; son erreur croît comme T²·ε et devient inutilisable au-delà du rang 10⁵ en float64 si T
  est lui-même estimé. L'inversion par le rapport des amplitudes reste à 3e−10 jusqu'à 2 001 052. Les deux sont la même
  information (`β` entre par `arctan(T/β)` dans la position et par `C^β` dans l'amplitude), lue par deux canaux de précision
  différente.
* Critère pré-enregistré (≤ 1e−10 relatif pour T ≤ 10⁶) : tenu pour toutes les identités et pour l'inversion par amplitudes ;
  **non tenu** pour l'inversion par tangente au-delà du rang 10⁴ (consigné tel quel : limite numérique, pas mathématique).

Rien ici ne distingue une Tour OFF d'une Tour ON autrement que par la valeur de β lue : les identités sont les mêmes.
