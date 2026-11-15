# E403 — Somme réelle des dépôts aux vrais points de rencontre, avec les vraies amplitudes (2026-11-02)

## Pré-enregistrement (écrit AVANT exécution)

Question de l'auteur (2026-11-02) : les affirmations « le OFF ne viole aucune contrainte des rencontres » reposent-elles
sur la projection (π(x), li(x), comptage de Riemann–von Mangoldt) ou sur les vrais écarts et la somme des contacts sur
l'axe réel ? Réponse consignée : sur la projection ou sur une définition de contact sans amplitude. E403 fait la
comparaison qui n'avait jamais été faite, avec le canal lissé COMPILÉ (`smoothedRemainder`, `nontrivialZeroResidueTerm`,
module `Terminal/AmplitudeContact.lean`) et aucun autre.

### Objets (tous déterministes)
* **Vrais écarts** : premiers `p ≤ 10 000` plus le suivant (1 229 écarts, mêmes que E402), vrais points de rencontre
  `p_{n+1}`. Demande première exacte `A(x) = Σ_{m<x} Λ(m)(1 − m/x)` (crible, aucune formule asymptotique), fond `B(x)`
  (formule E401/E402), cible des zéros `Z_n = ΔA − ΔB`.
* **Zéros** : `../data/odlyzko_zeros6_2001052.txt` (SHA-256 vérifié), hauteurs posées sur la ligne (hypothèse de données).
* **Dépôt d'un zéro au point de rencontre** : `d_ρ(x) = −x^ρ/(ρ(ρ+1))` (multiplicité 1), module `|d_ρ(x)| = x^β/(|ρ||ρ+1|)`
  (= `meetingDeposit_norm`). Contribution à l'écart : `c_ρ(n) = d_ρ(p_{n+1}) − d_ρ(p_n)`.
* **Contact porteur d'amplitude** : pour chaque membre de la foule qui traverse un contact `C_k` dans l'écart,
  amplitude `A_k = |d_ρ(C_k)|` et pas d'amplitude `A_{k+1}/A_k` ; lecture `β_lue = T·log(A_{k+1}/A_k)/π`
  (= `radial_from_amplitude_step`).
* **Somme des amplitudes** (modules) de la foule à la rencontre, `Σ|c_ρ(n)|` ; somme signée `2Re Σ c_ρ(n)`.

### Jumeau synthétique, SÉPARÉ (jamais lu comme mesure de β)
Un zéro ON est REMPLACÉ par une paire OFF : le zéro réel de rang `j₀ = 2000` est retiré de la somme, la paire
`β* = 0,3 / 0,7` est ajoutée à la hauteur `T* = (T_{2000} + T_{2001})/2` (hauteur d'aucun zéro existant, distance
vérifiée `> 10⁻³`). Pour chaque vrai écart : complément exigé `Δ_n = 2Re(c_paire(n) − c_{j₀}(n))`, comparé
(a) au résidu observé `|R_n|` de la reconstruction réelle, (b) à la borne de queue à l'échelle de la ligne `eps_online`,
(c) à la borne inconditionnelle `eps_uncond` ; amplitudes `|d_{0,3}(p_{n+1})|`, `|d_{0,7}(p_{n+1})|`, `|d_{j₀}(p_{n+1})|`
et leur croissance avec `p_{n+1}` (pente de `log|d_{0,7}/d_{0,3}|` contre `log p_{n+1}` : attendue exactement `0,4`).
Second jumeau, mpmath dps 30, sur 3 écarts (premier à foule non vide, médian, dernier).

### Prédictions dites d'avance
1. Identité réelle `Z_n = 2Re Σ_ρ c_ρ(n)` au niveau des données (résidu ~10⁻⁷, comme E402) : c'est `gap_demand_eq_deposits`.
2. `β_lue = 0,5` sur tous les contacts réels (à l'erreur flottante) : c'est l'hypothèse de données, pas une mesure.
   Sur le synthétique : `β_lue = 0,3` et `0,7` exactement : le contact porteur d'amplitude N'EST PAS aveugle au radial.
3. La somme des amplitudes `Σ|c|` de la foule est très supérieure à `|2Re Σ c|` (part de phase médiane ~0,06 en E402) ;
   la somme des modules n'est pas la demande.
4. Synthétique : `Δ_n` dépasse le résidu observé pour la plupart des écarts (E402 : 468 écarts avec paire, complément
   jusqu'à 2 800× le résidu) ; `Δ_n` ne dépasse `eps_online` ni `eps_uncond` pour aucun écart (E402 : 0/468).
   Le rapport `|d_{0,7}|/|d_{0,3}|` croît comme `p_{n+1}^{0,4}` (= `mirror_deposit_ratio`).
5. **Aucune conclusion sur β des vrais zéros.** Ce que l'expérience peut dire : la comparaison réelle (vrais écarts ×
   vraies amplitudes) distingue une paire du zéro remplacé SEULEMENT par rapport au résidu observé, lequel dépend de la
   complétude de la liste des zéros ; aucune borne compilée (toutes à exposant 1 ou à l'échelle de la ligne) ne la
   distingue. Si ce point 5 est contredit, il sera consigné tel quel.

### Protocole
`nohup timeout 900 python3 -I e403_amplitude_meetings.py ../data/odlyzko_zeros6_2001052.txt 10000 . > e403_run.log`
(borné < 5 min, numpy + mpmath ; aucune sortie fabriquée). Sorties : `e403_summary.txt`, `e403_per_gap.txt`,
`e403_contacts_chosen_gaps.txt`, `e403_synthetic.txt`, `e403_run.log`.

## Exécution (2026-11-02, 103,2 s, `e403_run.log`) — résultats contre les prédictions

| # | Prédiction | Résultat |
|---|---|---|
| 1 | identité réelle au niveau des données | max résidu 1,44·10⁻⁷ (n = 1), médiane 2,1·10⁻⁹ ; 1229/1229 sous `eps_online` ; jumeaux mpmath dps 30 : écarts ≤ 2,1·10⁻¹⁴ (sommes), ≤ 1,6·10⁻¹² (demande exacte) |
| 2 | `β_lue = 0,5` sur le réel (donnée), `0,3 / 0,7` sur le synthétique | 1 655 515 contacts de foule, max écart 8,3·10⁻¹² ; synthétique 0,300000000000 ± 10⁻¹², 0,700000000000 ± 2·10⁻¹² : **le contact porteur d'amplitude lit la position radiale** |
| 3 | somme des modules ≫ somme signée | part de phase médiane 0,057 ; somme des amplitudes au point de rencontre = 103 × la demande (médiane) ; somme des modules des contributions = 17 × la demande |
| 4 | complément du remplacement > résidu observé pour la plupart des écarts ; jamais > bornes ; croissance `p^{0,4}` | **1229/1229** écarts (pas seulement les 468 dont la foule contient la paire : consigné, non dit d'avance) ; rapport complément/résidu jusqu'à 3,4·10⁷ ; `> eps_online` : 0/1229 ; `> eps_uncond` : 0/1229 ; pente mesurée 0,400000000000 ; `|d_{0,7}|/|d_{0,3}|` de 1,55 à 39,8 |
| 5 | aucune conclusion sur β des vrais zéros | tenue |

## Lecture honnête
1. La comparaison demandée par l'auteur est faite : vrais écarts à gauche, somme des dépôts de tous les zéros aux vrais
   points de rencontre avec leurs vraies amplitudes à droite. Elle est une identité (`gap_demand_eq_deposits`), vérifiée
   au niveau des données.
2. Le contact porteur d'amplitude n'est pas aveugle : sur le synthétique, il rend `β* = 0,3` et `0,7` à `10⁻¹²`. Sur le
   réel il rend `0,5` parce que les données posent `0,5`. Ce n'est pas une mesure de `β` : c'est la lecture d'une donnée.
3. Le remplacement d'un zéro ON par une paire OFF modifie la somme réelle à TOUS les points de rencontre, d'une quantité
   jusqu'à 3,4·10⁷ fois le résidu observé, et croissante comme `p^{0,4}` ; mais cette quantité reste sous toute borne
   compilée (ligne, exposant 1). Le détecteur est donc le résidu observé, qui dépend de la complétude de la liste des
   zéros ; aucune contrainte compilée sur l'axe réel n'est violée par la paire. L'affirmation « le OFF ne viole aucune
   contrainte des rencontres » est remplacée par : « la paire change la somme réelle à chaque rencontre, et aucune borne
   compilée ne voit ce changement ».
4. Rien n'est conclu sur β des vrais zéros.
