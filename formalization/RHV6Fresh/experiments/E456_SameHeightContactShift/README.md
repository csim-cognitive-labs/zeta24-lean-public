# E456 — K6 : décalage des contacts à même hauteur, audit du texte « transitions modulo 6 », causalité ON/OFF (pré-enregistrement, 2026-11-08)

Référence : `RHV6final_STRATEGIE_SEMANTIQUE.md` §19.79. Questions de l'auteur : (Q1) « si on affecte quelque chose à β, T en
souffre » à même hauteur visée ; (Q2) « les OFF sont peut-être nécessaires aux grandes hauteurs pour réaliser la cassure » ;
(Q3) corriger le texte collé sur les quatre transitions modulo 6 et conduire des études de causalité ON/OFF ; (Q4) la distribution
des transitions est-elle gaussienne ?

## Audit (avant exécution) — §19.79.2
* Q1 déjà étudiée : `gap_reading_height_only`, `windingContact_lt_of_radial_lt`, `windingContact_sameHeight`, `contact_eq_iff_phase`,
  `contact_radial_formula`, `tower_eq_of_same_word`. Compilable sans hypothèse : aucun contact partagé à même hauteur (tous indices) ;
  rencontre commune ⟹ hauteurs différentes ; décalage < demi-cellule ; rapport de cellule aveugle à β. → K6.
* Q2 : la phrase « hautes fréquences ⟹ cassure » vient du canal de sommation (E404/E408), interdit ; forme autorisée compilée pour
  toute Tour : `log_ratio_ge_cell_of_meeting`, `two_consecutive_contacts_finite` ; pouvoir de résolution = T seul.
* Q3 : le texte = E427 altéré ; erreurs e1–e5 (§19.79.2) ; compilé : `card_validWords_twelve`, `orientedBalance_abs_le_one`,
  `eventOrientation_of_gap`.
* Q4 : support fini de treize valeurs ⟹ pas gaussienne ; binomiale décalée attendue ; normale approchée aux longues fenêtres.

## Volet Lean
`RHV6Fresh/Terminal/SameHeightContactShift.lean`, isolé, M1–M5 (§19.79.3). Aucune amplitude, aucune hypothèse.

## Volet déterministe
`e456_causal_mod6_contact_shift.py` : P1 jumeau de K6 ; P2 recompte et énumération exacte ; P3 Gauss ; P4 intervention sur β à T
fixée et sur T à β fixée. Données : `experiments/data/odlyzko_zeros1_first5000.txt` ; premiers ≤ 10⁶ par crible.

## Réponses attendues (consignées d'avance)
P1 exact ; P2 effectifs du texte incohérents, |τ15 − τ51| ≤ 1, parts B + C + D = 1 ; P3 binomiale décalée, pas gaussienne à douze ;
P4 recouvrement élevé non total, composition mod 6 identique au bruit près, contingence nulle, T change tout. Aucune contradiction
OFF attendue.

## Protocole
Deux tentatives Lean au plus, sondes scratch non versionnées, sorties capturées dans `attempts/` ; grep du ban avant build ;
`lake build RHV6Fresh` complet après la tentative verte ; script exécuté une fois sous `nohup`, sortie dans `logs/`.
