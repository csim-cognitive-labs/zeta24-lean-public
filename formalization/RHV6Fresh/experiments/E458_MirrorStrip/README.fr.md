> Version française conservée à titre de référence. Main language: English, see README.md.

# E458 — Φ2 : géométrie exacte de la bande miroir, B1–B4, plus B5 (poids de fibre ↔ bande) (pré-enregistrement, 2026-11-09)

Référence : `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.80 (plan Φ, étape Φ2), §19.85 (ordre de reprise validé), §19.86 (audit E460 : ajout de
B5). Aucune hypothèse admise, aucun axiome, aucun `sorry` ; module isolé `RHV6Fresh/Terminal/MirrorStrip.lean`, NON ajouté à
`RHV6Fresh.lean`. Aucune théorie spectrale. INTERDIT : affirmer une densité de la bande ; seule l'infinitude est visée.

## Objets nommés (avant compilation)
* `mirrorStrip β T` : ensemble des RANGS de premiers où le mot du miroir `(1 − β, T)` diffère du mot de la Tour `(β, T)`
  (`towerWord` d'E457) ;
* `zeroStrip z` : bande d'un zéro vrai.

## Énoncés à compiler
* **B0** (orientation) : sur la bande l'écart des deux mots vaut exactement un en valeur absolue ; pour `β < 1/2` le mot du miroir
  vaut le mot de la Tour plus un sur la bande, et lui est égal hors bande.
* **B1** : pour `0 < β < 1`, `T > 0` : bande vide ⟺ `β = 1/2`.
* **B2** : bande infinie ⟺ `β ≠ 1/2`.
* **B3** : bande non vide et finie impossible ; dichotomie : vide ou infinie.
* **B4** (encadrement, `0 < β < 1/2`, `T > 0`) : le rang `n` est dans la bande ⟺ il existe un indice entier `k` tel que le premier
  de rang `n` soit dans l'intervalle fermé à gauche, ouvert à droite, qui va du contact d'indice `k` du miroir au contact de MÊME
  indice de la Tour ; ces deux contacts ne sont jamais confondus (le miroir strictement avant) et leur rapport est strictement
  inférieur à une demi-cellule (`e^{π/(2T)}`). L'énoncé place un premier ENTRE deux contacts ; il n'affirme jamais qu'un contact
  est un premier (§19.51).
* **B5** (poids de fibre ↔ bande, sans hypothèse ; audit E460) : pour un zéro vrai, poids de fibre à sa hauteur strictement
  inférieur à deux ⟹ bande vide ; bande non vide ⟹ poids de fibre au moins deux.
* **B6** (reformulations, JAMAIS posées) : RH ⟺ la bande de tout zéro vrai est vide ⟺ la bande de tout zéro vrai est finie
  (c'est l'hypothèse H-c du plan, classée équivalente : consignée comme reformulation).

Prévision : tout compile ; aucune contradiction n'est attendue ni cherchée ; toute Tour hors ligne, porteuse ou non, a la même bande :
la géométrie de la bande ne porte pas l'arête.

## Volet déterministe (jumeau de B1, B4) — `e458_mirror_strip.py`
200 premières hauteurs d'Odlyzko ; premiers ≤ 10⁶ (crible) ; ligne (`β = 1/2`) et contrôles `β ∈ {0,3 ; 0,4 ; 0,45}` aux mêmes hauteurs
(Tours de contrôle, non porteuses : aucun zéro hors ligne n'est supposé ni testé). Mesures : effectif de la bande, premier rang de
bande ; vérification de B0 (écart exactement plus un sur la bande) et de B4 dans les deux sens (tout premier de bande est dans
l'intervalle de son indice ; aucun premier hors bande n'y est). Attendus écrits d'avance : ligne, effectif nul pour les 200 hauteurs ;
contrôles, B0 et B4 à zéro violation hors cas sous le bruit de la double précision (comptés à part et recontrôlés en précision
étendue s'il y en a) ; effectif de bande des contrôles : rapporté tel quel, AUCUN attendu de positivité jusqu'à 10⁶ (le théorème ne
donne que l'infinitude), aucune loi, aucune densité.

## Protocole
Deux tentatives au plus ; sondes `*_SCRATCH.lean` non versionnées supprimées après capture ; `attempts/` ; `#print axioms` ; grep du ban
à zéro sur le module ; `lake build RHV6Fresh` complet vert ; script une fois sous `nohup`, sortie dans `logs/`.
