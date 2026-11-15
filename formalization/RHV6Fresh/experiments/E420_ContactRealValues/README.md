# E420 — Valeurs réelles aux contacts, alternance, inversion tangentielle, évolution des amplitudes (pré-enregistrée 2026-11-03)

Objectif (auteur) : mesurer la valeur réelle de chaque Tour à chacun de ses contacts (signe et amplitude), l'alternance des
valeurs entre contacts consécutifs, la récupération de la hauteur T et de la position radiale β par inversion tangentielle des
contacts, et l'évolution des amplitudes quand la Tour s'enroule. **Sans premiers, sans écarts, sans cellules entières, sans
intégrale logarithmique** : seules les hauteurs des zéros (données d'Odlyzko, posées sur la ligne) et des Tours synthétiques
séparées (jamais à la hauteur d'un zéro réel) sont utilisées.

Prédictions à tester (identités du module Lean `Terminal/ContactRealValue.lean`, écrites avant exécution) :
* valeur au contact k : v_k = (−1)^k · C_k^β / √(β²+T²), partie imaginaire nulle ;
* alternance : v_{k+1} = −e^{βπ/T} · v_k (signe opposé, module multiplié par e^{βπ/T}) ;
* inversion : T = π/(log C_{k+1} − log C_k) ; β = T·log|v_{k+1}/v_k|/π ; β = T / tan(T·log C_k − kπ) (tangente) ;
* enroulement : log|v_k| est affine en k, pente βπ/T ; doublement du module après T·log 2/(βπ) contacts.
Jumeau déterministe : mpmath à 30 chiffres sur 5 contacts par Tour. Rien ici ne présume que ces identités excluent les zéros OFF.
