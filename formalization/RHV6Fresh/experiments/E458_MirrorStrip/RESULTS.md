# E458 — Résultats (2026-11-09) : géométrie exacte de la bande miroir — verdict A

Pré-enregistrement : `README.md` (commit ce954280, avant toute compilation). Module `RHV6Fresh/Terminal/MirrorStrip.lean` : isolé,
20 déclarations, vert à la PREMIÈRE tentative après une sonde sans erreur (`attempts/probe1.txt`, `attempts/build_attempt1.txt`),
10 énoncés imprimés sur les trois axiomes standard, grep du ban à zéro, `lake build RHV6Fresh` complet vert (`logs/lake_build_full.txt`).

## Compilé (aucune hypothèse)
* **B0** : sur la bande, l'écart des deux mots vaut exactement un ; du côté bas, le mot du miroir vaut le mot de la Tour plus un.
* **B1** : bande vide ⟺ ligne. **B2** : bande infinie ⟺ hors ligne. **B3** : jamais non vide et finie (vide ou infinie).
* **B4** : du côté bas, un rang est dans la bande si et seulement si son premier est dans l'intervalle (fermé à gauche, ouvert à
  droite) qui va du contact d'un indice du miroir au contact de même indice de la Tour ; ces deux contacts ne sont jamais confondus
  (le miroir strictement avant) et leur rapport est strictement inférieur à une demi-cellule.
* **B5** : poids de fibre sous deux ⟹ bande vide ; bande non vide ⟹ poids de fibre au moins deux (seul point de contact entre le
  poids et la bande, issu de l'audit E460).
* **B6** (reformulations, jamais posées) : RH ⟺ bande de tout zéro vrai vide ⟺ bande de tout zéro vrai finie (H-c classée équivalente).

## Jumeau (`e458_mirror_strip.py`, une exécution sous nohup, `logs/e458_output.txt`)
200 premières hauteurs d'Odlyzko (lues dans `data/odlyzko_zeros1_first300.txt`), 78 498 premiers jusqu'à un million.
* Ligne : bande vide aux 200 hauteurs (attendu réalisé).
* Contrôles (Tours non porteuses, positions radiales 0,3 ; 0,4 ; 0,45) : aucune bande vide jusqu'à un million ; effectifs (minimum,
  médiane, maximum) 17 / 42,5 / 688 ; 7 / 22 / 335 ; 2 / 10 / 168. Rapportés tels quels : aucun attendu de positivité n'était écrit,
  aucune loi, aucune densité n'est affirmée.
* B0 et B4 (deux sens) : zéro violation sur les quatre familles ; un seul cas écarté sous le bruit de la double précision (contrôle
  0,45, hauteur 192,03, premier 709 703), recontrôlé à 40 chiffres : conforme (`logs/e458_noise_recheck_mp.txt`).
Limite dite : la vérification de B4 se fait en positions d'étage ; c'est le jumeau arithmétique d'un énoncé exact, pas une mesure
indépendante.

## Lecture
La bande est entièrement décrite : vide sur la ligne, infinie hors ligne, faite des premiers situés entre deux contacts de même indice
du miroir et de la Tour, intervalle de largeur relative inférieure à une demi-cellule. Toute Tour hors ligne, porteuse ou non, a cette
bande : **la géométrie de la bande ne porte pas la sélection des porteurs**. Le poids n'y entre que par B5, conséquence du comptage de
fibre. Aucune contradiction n'est tirée ; aucune densité n'est affirmée.

## Verdict
A : tous les énoncés pré-enregistrés compilés en une tentative ; attendus du jumeau réalisés ; aucune hypothèse posée.
