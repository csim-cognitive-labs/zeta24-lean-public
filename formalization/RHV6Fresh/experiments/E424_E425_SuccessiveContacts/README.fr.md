> Version française conservée à titre de référence. Main language: English, see README.md.

# E424–E425 — Contraintes entre Tours successives lues aux contacts (pré-enregistrées 2026-11-03)

Directive de l'auteur (« stratégie des contacts réels », §19.39) : exploiter les contacts des Tours avec l'axe réel pour
retrouver hauteur et partie réelle, les rapports d'amplitudes, les phases relatives entre Tours, les contacts miroirs, les
contraintes entre Tours successives et le raccordement aux événements premiers. Sans projection spectrale, sans détection
par seuils, sans primitives intégrées, sans cellules unitaires comme support de reconstruction, sans intégrale
logarithmique. Module Lean de référence : `Terminal/SuccessiveContactConstraints.lean` (isolé, compilé avant exécution).

## E424 — Lecture croisée entre Tours successives aux contacts du successeur
Pour chaque paire de zéros consécutifs (e, l) = (rang n, rang n+1) sur les 2 001 052 hauteurs d'Odlyzko (posées sur la
ligne), aux deux premiers contacts de l dans [2, ∞) :
* rapport croisé de e aux contacts de l : |e(C_{k+1}(l))|/|e(C_k(l))| ; rapport propre de l ;
* lecture de la différence des positions radiales : (T_l/π)·log(rapport_e/rapport_l) — **prédiction compilée
  (`radial_difference_of_crossRatios`) : 0 pour ON→ON, ½ − β_l pour un successeur synthétique OFF** ;
* lecture de la position radiale du prédécesseur : (T_l/π)·log(rapport_e) — prédiction ½ ;
* pas de phase relative de e entre deux contacts de l : arg(e(C_{k+1})/e(C_k)) = T_e·π/T_l modulo 2π
  (`towerValue_step_at_contacts`) ; comme T_e < T_l < 2T_l, la hauteur du prédécesseur est lue sans ambiguïté :
  T̂_e = (T_l/π)·(pas modulo 2π). Erreur maximale consignée ; elle est attendue croissante comme T·ε (conditionnement).
Synthétique séparé : prédécesseur réel ON (rangs 1, 100, 2 000, 100 000), successeur synthétique à la hauteur milieu des
zéros (n+1, n+2) — jamais la hauteur d'un zéro réel — avec β_l ∈ {0,3, 0,45, 0,49} ; lecture ½ − β_l attendue ; paire
miroir (β_l, 1−β_l) : lecture 2β_l − 1 attendue.
Jumeau déterministe : mpmath 30 chiffres sur 6 paires réelles et toutes les paires synthétiques.
Critère : lectures radiales à 10⁻⁹ près ; T̂_e à T_l·10⁻⁹ près ; sinon consigné tel quel.

## E425 — Paire miroir aux contacts du membre et position du premier de même rang
(a) Aux contacts d'un membre synthétique OFF (β ∈ {0,3, 0,45, 0,49}, hauteurs milieu des zéros (1,2), (100,101),
(2000,2001), (100000,100001)), partie imaginaire de la somme de la paire (membre + miroir) normalisée par le module du
miroir : **prédiction compilée (`mirror_im_at_contact`) : (−1)^k · sin(phase relative), phase relative =
arctan(T/β) − arctan(T/(1−β)), jamais nulle (`pair_axis_at_contact_iff`)**. Contrôle ON aux hauteurs réelles (β = ½) :
partie imaginaire nulle à l'arrondi. Jumeau mpmath sur 5 contacts par Tour.
(b) Raccordement : au zéro de rang m (1-indexé) est associé le m-ième premier p_m (`occurrence`, corpus : rang 0-indexé n
↦ `Nat.nth Nat.Prime n`). Position d'étage s = (T·log p_m − arctan(T/β))/π, indice de contact k = ⌊s⌋, fraction f = s − k,
signe de la valeur réelle au contact encadrant (−1)^k, cosinus de la phase à p_m (cos πs). Sur les 2 001 052 zéros :
histogramme déterministe de f (20 classes), proportion de k pairs, moyenne de cos πs. Jumeau de déplacement (comme E423) :
mêmes hauteurs avec β = 0,3 ; **prédiction compilée (`arrival_cell_same_or_previous`) : k(0,3) ∈ {k(½) − 1, k(½)} à
100 %** ; fréquence du cran consignée. Aucune prédiction n'est pré-enregistrée sur la forme de l'histogramme de f : il est
mesuré, pas lu comme une loi. Jumeau mpmath sur 10 rangs.

Rien ici ne présume que ces lectures excluent les zéros OFF ; une exclusion ne serait admise que compilée.
