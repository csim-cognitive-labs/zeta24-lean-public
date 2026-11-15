# E402 — Reconstruction collective par les contacts (mission R9, §19.30) — EXÉCUTÉE le 2026-11-01

Pré-enregistrement : maître §19.29.5 (2026-11-01, avant exécution), vérifié avant lancement ; extension demandée par la
mission R9 (phases d'entrée/sortie, contacts traversés, décalage à la rencontre, foule/queue/fond, résidu, bornes,
transitions, dérive séparée β / T, synthétique séparé). Feu vert de l'auteur : « exécute les expériences dont tu as besoin ».

## Protocole (tel qu'exécuté)
* Script : `e402_collective_contacts.py` (numpy + mpmath), lancé `nohup timeout 900 python3 -I … 10000 .`, durée 108,6 s.
* Zéros : `../data/odlyzko_zeros6_2001052.txt`, SHA-256 `2ef7b752…78e7c6` vérifié contre `.sha256` ; 2 001 052 hauteurs,
  strictement croissantes, `T_1 = 14.134725142`, `T_max = 1132490.658714411`. Hypothèse de données : hauteurs de zéros connus
  posés sur la ligne (`β = 1/2`) ; elles ne certifient pas l'absence de zéros OFF.
* Premiers : crible, `p ≤ 10 000` plus le suivant (1 229 écarts, de `[2, 3]` à `[9973, 10007]`) ; toute foule est dans les
  données (`K_max = 16 924 < 2 001 052`).
* Canal : le canal lissé compilé (même formule que E401, aucune autre). Demande première `D_n = Δ Σ_{m<x} Λ(m)(1 − m/x)` ;
  fond `B_n = Δ[x/2 − ζ'/ζ(0) + (ζ'/ζ)(−1)/x + Σ_j −x^{s_j}/(s_j(s_j+1))]` ; cible des zéros `Z_n = D_n − B_n` ; contribution
  complexe d'un zéro `c_ρ(n) = −(p_{n+1}^ρ − p_n^ρ)/(ρ(ρ+1))`, demande `= 2 Re Σ_ρ c_ρ(n)` (conjugués). Somme complexe
  conservée partout ; la somme des modules n'est donnée qu'à part (part de phase).
* Foule de l'écart : `T_ρ ≤ π/ℓ_n` ; queue : le reste des 2 001 052 zéros ; troncature au-delà de `T_max` bornée
  indépendamment du résidu : `Σ_{γ>T_max} 1/γ² ≤ 1,841·10⁻⁶` (N(T) ≤ N_up(T), Trudgian 2014, N(T_max) = 2 001 052 exact),
  `eps_uncond = 2(p_n + p_{n+1})·σ` (|x^ρ| ≤ x, toute position radiale de la queue), `eps_online = 2(√p_n + √p_{n+1})·σ`
  (si la queue est en ligne).
* Contacts : phase `θ = T log p − arctan(T/β)` à l'entrée et à la sortie, contacts traversés `⌊θ_out/π⌋ − ⌊θ_in/π⌋`,
  décalage du contact à la rencontre `(log p_{n+1} − log C_k)/ℓ` (quarts comptés), rencontres exactes `log C_k = log p_{n+1}`.
* Transitions : `K_{n+1} − K_n` (fenêtres d'un ensemble fixe).
* Dérive (3 écarts × 10 zéros) : `∂c/∂β = dc/dρ`, `∂c/∂T = i·dc/dρ` (analytiques), `∂u_k/∂β = −1/(β²+T²)`,
  `∂u_k/∂T = β/(T(β²+T²)) − u_k/T`, `∂(π/T)/∂β = 0` exact : les deux effets sont séparés.
* Jumeaux : E401 (dps 30, 168 écarts) contre `Z_n` ; télescopage 100 zéros ; identités compilées (`|u| = 2|sin(Tℓ/2)|/T`,
  plateau `≤ ℓ`, enveloppe `≤ 2/T`) sur toute la foule de trois écarts à deux précisions ; sommes de foule et `A(x)` en mpmath.
* Synthétique, SÉPARÉ (`e402_synthetic.txt`) : paire `β* = 0,3 / 0,7` à `T* = 2515,928766` (milieu des zéros 2000 et 2001,
  hauteur d'aucun zéro réel) ; contributions, complément exigé, résidu « avec paire » ; jamais lue comme mesure de β.

## Résultats (fichiers : `e402_summary.txt`, `e402_per_gap.txt`, `e402_members_chosen_gaps.txt`, `e402_drift.txt`, `e402_synthetic.txt`, `e402_run.log`)
| Quantité | Valeur |
|---|---|
| résidu `R_n = Z_n − 2Re(S_foule + S_queue)` | max 1,44·10⁻⁷ (n = 1), médiane 2,1·10⁻⁹ |
| `|R_n| ≤ eps_uncond` / `≤ eps_online` | 1229/1229 / 1229/1229 (eps_online de 1,2·10⁻⁵ à 7,4·10⁻⁴) |
| foules | `K_min = 0` ; 6 écarts à foule VIDE (rangs 0,1,2,3,5,8 : seuil `π/ℓ < T_1`) ; `K_max = 16 924` (n = 1223) |
| part de la foule / de la queue dans `Z_n` (médianes) | 1,0003 / 0,0335 |
| part de phase de la foule `|S|/Σ|c|` | min 0,0009, médiane 0,057, max 1 |
| contacts traversés par la foule | 1 655 515 au total ; 7 écarts sans aucun contact de foule ; rencontres exactes : 0 |
| quarts de l'écart (depuis la rencontre) | 414 409 / 414 234 / 413 158 / 413 714 |
| transitions `K_{n+1} − K_n` | de −15 025 à +15 544 ; 636 croissances, 587 décroissances, 5 constantes |
| jumeau E401 | max écart 4,7·10⁻¹³ ; télescopage 4,4·10⁻¹⁶ ; identités 2·10⁻¹⁶ à 1,8·10⁻¹⁵ ; foules mpmath ≤ 2,1·10⁻¹⁴ |
| synthétique | 468 écarts contiennent la paire dans leur foule ; complément exigé de 5,8·10⁻⁷ à 4,0·10⁻⁴ ; **0/468 dépasse `eps_online`, 0/468 dépasse `eps_uncond`** ; contre le résidu observé (1,4·10⁻⁷), 4,0·10⁻⁴ est 2 800 fois plus grand |

## Lecture honnête
1. **Identité exacte vérifiée numériquement** : la demande première de chaque écart est reconstituée par la somme complexe de
   tous les zéros (foule + queue) plus le fond, au niveau de la précision des données ; c'est `localSynchronization` (C126),
   pas un résultat nouveau. Les phases se compensent fortement dans la foule (part de phase médiane 0,057).
2. **Résultats dits d'avance** : foules immenses pour les écarts ordinaires (jusqu'à 16 924 pour `p ≈ 10⁴`) — mais les six
   premiers écarts courts ont une foule VIDE (ce qui n'avait pas été dit d'avance : consigné) ; aucun contact n'est une
   rencontre ; aucune comparaison à une moyenne ; aucune conclusion sur β.
3. **Le défaut de reconstruction n'est pas un détecteur** : la borne d'erreur compilée (exposant 1, `collective_residual_bound`)
   et même la borne à l'échelle de la ligne ne sont jamais dépassées par le complément exigé par la paire synthétique
   (0/468). Seule la comparaison au résidu OBSERVÉ (qui repose sur la complétude de la liste des zéros) le distingue : c'est un
   contrôle numérique, jamais une preuve concernant les vrais zéros (mission §7).
4. **Rien n'est conclu sur β.** La rigidité des contacts n'est pas supposée ; elle n'est pas obtenue.
