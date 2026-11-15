# E434 — L'effet de bords de la paire lu par les contacts (2026-11-04)

Expérience de compilation seule (aucune mesure numérique ; aucun jumeau requis). Demande de l'auteur : « ok continues »,
après E433 (§19.48) : « absorber sur la série » est une équation par fenêtre entre le contenu arithmétique et l'effet de
bords de la paire. Directive : la lecture radiale des contacts et le contenu arithmétique doivent se faire face dans une
même équation.

## Question posée (avant toute compilation)
La partie réelle de l'effet de bords de la paire à un bord `x` de fenêtre se lit-elle exactement par le dernier contact
de chacun des deux membres (valeur au contact, facteur de croissance sur la fraction de cellule, fraction de cellule) ?
Attendu (écrit avant exécution) :
1. la partie imaginaire de la Tour se lit aussi par le dernier contact, en sinus de la fraction de cellule ;
2. la partie réelle du canal intégré (`Tour/(ρ+1)`) est une combinaison de la partie réelle et de la partie imaginaire
   de la Tour, à poids `β+1` et `T`, sur le carré de la norme de `ρ+1` : le canal intégré lit la fraction de cellule
   avec un retard d'angle propre (arctangente de `T/(β+1)`), différent pour le zéro et pour le miroir ;
3. la partie réelle de la primitive de la paire à `x` est `−2m·x` fois la somme des deux lectures intégrées ; elle se
   lit donc entièrement par les contacts des deux membres ;
4. le bilan de fenêtre (E433) s'écrit en partie réelle : contenu arithmétique de la fenêtre − partie réelle du complément
   = effet de bords lu par les contacts aux deux bords.

## Protocole
1. Pré-enregistrer (commit) avant la première compilation.
2. Sondes TDD dans `BoundaryContactProbe_SCRATCH.lean` (non versionné, supprimé après capture ; sorties exactes dans
   `logs/probe_attempt*.txt`).
3. Module isolé `Terminal/BoundaryContactReading.lean` (non ajouté à `RHV6Fresh.lean`) : points 1–4.
   Si le compilateur demande davantage que les objets listés, consigner le but exact et ne pas insister.
4. Deux tentatives de compilation au plus pour le module (`logs/lean_attempt{1,2}.txt`) ; aucune hypothèse posée ;
   aucun `sorry` ; `lake build RHV6Fresh` vert après.

## Sonde prévue
- S1 : « complément silencieux sur la fenêtre, et les deux bords sont des contacts du zéro (fraction de cellule nulle)
  ⟹ False » — attendu : pas de contradiction ; le compilateur laisse « contenu arithmétique de la fenêtre = combinaison
  des valeurs aux contacts du zéro et des lectures du miroir aux deux bords ».

## Objets réutilisés
`towerRe`, `towerValue_polar`, `towerRe_from_lastContact`, `height_mul_log_eq`, `contactRealValue`, `contactAt_pos`,
`norm_mk_pos`, `integratedTower_eq_geometric_div`, `pairPrimitive`, `pair_complement_series_balance`,
`remainderIncrement_series_arithmetic`, Mathlib `Complex.div_re`, `Real.sin_add_int_mul_pi`, `Real.cos_add_int_mul_pi`.
