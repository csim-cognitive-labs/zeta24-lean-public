> Version française conservée à titre de référence. Main language: English, see README.md.

# E457 — Φ0 + Φ1 : nommer l'arête manquante (trois reformulations exactes) et théorème d'isolement de la sélection des porteurs (pré-enregistrement, 2026-11-08)

Référence : `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.80 (plan Φ, validé par l'auteur le 2026-11-08 : « je valide le plan, consigne-le et
exécute chaque proposition »), §19.82. Aucune hypothèse admise, aucun axiome, aucun `sorry` ; module isolé `RHV6Fresh/Terminal/CarrierSelection.lean`,
NON ajouté à `RHV6Fresh.lean`.

## Objets nommés (avant compilation)
* `towerWord β T n` : mot de la Tour `(β, T)` au premier de rang `n` (= `lastContactBefore β T p_n`, E449/E453) ;
* `zeroWord z n` : mot d'un zéro vrai ; `IsCarrier β T` : la Tour `(β, T)` porte un zéro (poids `zeroMult` non nul, E451) ;
* `CarrierWordsSelfMirror` (R1) : tout mot porteur égale le mot de son miroir ;
* `HeightInjectiveOnCarriers` (R2) : deux zéros vrais supérieurs de même hauteur sont le même ;
* `PriceRadiallyBlindOnCarriers` (R3) : le prix d'E445 (`offPrice`) vaut celui de la ligne en tout premier pour tout zéro vrai ;
  variante R3' : les termes d'un zéro et de son miroir ont même module en tout premier.

## Énoncés à compiler (Φ0)
1. R1 ⟺ RH ; 2. R2 ⟺ RH ; 3. R3 ⟺ RH et R3' ⟺ RH ; 3bis. l'égalité des modules en DEUX premiers distincts force déjà `β = 1/2` ;
4. R2 ⟹ `NoMixedHeight` (FixedGapRaccords). Contrôle de non-trivialité : `NoMixedHeight ⟹ RH` ne doit PAS compiler sans RH ; une sonde
scratch l'essaie, l'échec est consigné dans `attempts/` (on ne peut pas prouver une non-implication en Lean : c'est un constat de sonde).

## Énoncés à compiler (Φ1 — isolement)
5. `stagePosition_floor_stable_right` : pour toute Tour `(β, T)`, tout premier de rang `n`, il existe `δ > 0` tel que toute Tour `(β', T)` avec
   `β < β' < β + δ` a le même mot au rang `n` (position d'étage croissante et continue en `β`, E444) ;
6. `exists_nonCarrier_same_word_on_finset` : pour tout zéro vrai `z`, tout ensemble FINI de rangs `S` et tout `ε > 0`, il existe `β'` avec
   `β < β' < min(β + ε, 1)` tel que `(β', T)` n'est PAS porteuse (zêta ne s'annule pas, poids nul) et a le même mot que `z` sur `S`
   (isolement des zéros : `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, `analyticOrderAt_riemannZeta_ne_top`) ;
7. `finite_window_predicate_not_carrier_selective` : tout prédicat sur les mots qui ne dépend que d'un nombre fini de rangs, vrai sur le mot d'un
   zéro, est vrai sur le mot d'une Tour non porteuse de même fréquence.
Écart par rapport au plan : la Tour voisine est prise à MÊME hauteur `T` et position radiale `β' > β` (plus simple : aucune borne sur `log q`
n'est requise) ; le plan proposait `T' > T`. L'énoncé 6 est donc plus fort sur un point : même fréquence exactement.

## Volet déterministe (jumeau de Φ1) — `e457_carrier_isolation.py`
Sur les 200 premières hauteurs d'Odlyzko (ligne, β = 1/2) et sur 200 contrôles à β perturbé (0,3 ; 0,4 ; 0,45 aux mêmes hauteurs),
premiers ≤ 10⁶ (crible) : (a) marge radiale maximale `Δβ_max` conservant tout le mot (exacte, par la formule tangentielle) ; (b) marge en
hauteur `ΔT_max` conservant tout le mot (résolution monotone), comparée au demi-écart à la hauteur suivante. Attendu consigné d'avance :
`Δβ_max > 0` et `ΔT_max > 0` toujours (jumeau de 6) ; `ΔT_max` très inférieur au demi-écart entre zéros (ordre 10⁻⁶ contre 10⁻¹…1) ; marges
des contrôles de même ordre que celles de la ligne (la marge est une propriété du mot, pas du poids). Mesure, aucune loi.

## Protocole
Deux tentatives au plus, sondes `*_SCRATCH.lean` non versionnées supprimées après capture ; `attempts/` ; `#print axioms` ; grep du ban à zéro
sur le module ; `lake build RHV6Fresh` complet vert ; script une fois sous `nohup`, sortie dans `logs/`.
