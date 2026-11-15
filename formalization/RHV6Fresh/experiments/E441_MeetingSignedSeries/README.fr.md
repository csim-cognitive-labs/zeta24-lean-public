> Version française conservée à titre de référence. Main language: English, see README.md.

# E441 — Le bilan signé des rencontres le long de la série : indexation explicite des cellules de rencontre, ce que la croissance des longueurs impose à la borne, et règles chiffrées

Pré-enregistrement (2026-11-07), avant toute compilation et toute exécution. Ordre de l'auteur : « OK tranche la
Question suivante. En plus conduis une ou plusieurs expériences chiffrées pour déterminer les règles à partir de ces
expérimentations. Attention définis-les bien avec les acquis déjà constatés dans les théorèmes liés aux contacts
nouveaux et anciens. » Interdiction spectrale en vigueur (§19.55) ; ordre de travail §19.53.

## Vérification des neuf erreurs
1. Aucune hypothèse nouvelle (les hypothèses `GapHasContact` et « la rencontre n'est pas un contact » sont celles
   d'E439–E440, et leur fréquence de validité est MESURÉE ici). 2. Le compilateur décide. 3. Noms vérifiés par grep
   (`meetingSignedSum`, `signedPrimeSum`, `signedNonPrimeSum`, `signedLengthSum`, `meetingOffset` libres ;
   `meetingCell`, `cellPrimeWeight`, `cellNonPrimeWeight`, `cellLength`, `signedCellSum`, `meeting_cell_primes`,
   `cellPrimeWeight_inner_eq_zero`, `lt_contact_succ`, `lastContact_le`, `cell_linear_length`,
   `signed_cells_bounded_by_last` réutilisés). 4. `lake build RHV6Fresh` après tout changement. 5. Aucun premier ni
   OFF testé directement : une seule Tour, β = ½ fixé, hauteurs de la Tour = hauteurs d'Odlyzko (données). 6. Aucune
   position radiale. 7. Aucune famille, aucune somme de Tours. 8. Module isolé. 9. Intervalles = restes partiels.

## Question tranchée
Sur la série d'écarts ⟨n⟩, …, ⟨n+J⟩ d'UNE Tour, écrire le bilan signé des cellules entre la cellule de rencontre de
⟨n⟩ et celle de ⟨n+J⟩ avec l'indexation explicite des rencontres : le poids premier signé est exactement la somme sur
les rencontres de `(−1)^{décalage de la cellule de rencontre} · log p`, le reste du bilan est le poids non premier
signé moins la descente signée ; la descente signée a une forme close géométrique (rapport `e^{π/T}`) et sa borne est
encadrée par les deux rencontres extrêmes de la série et la fréquence seule.

## Énoncés visés (module isolé `Terminal/MeetingSignedSeries.lean`, importe `SignedCellBalance`)
- M1 `meetingOffset`, `meetingSignedSum` : décalage de la cellule de rencontre de ⟨n+j⟩ par rapport à celle de ⟨n⟩ ;
  somme signée des rencontres `Σ_{j<J} (−1)^{décalage_j} · log p_{n+j+1}`.
- M2 `meetingOffset_succ_pos`, `meetingOffset_mono` : les décalages croissent strictement si chaque écart a un
  contact.
- M3 `signedPrimeSum_eq_meetings` : la somme signée des poids premiers des cellules `[m_n, m_{n+J})` est exactement
  `meetingSignedSum` (hypothèses : chaque écart de la série a un contact et aucune rencontre n'est un contact).
- M4 `series_signed_balance` : la somme signée des pentes sur ces cellules = `meetingSignedSum` + poids non premiers
  signés − longueurs signées.
- M5 `signedLengthSum_closed_form` : longueurs signées = `L_{k₀} · (1 − (−r)^{M}) / (1 + r)`, `r = e^{π/T}` (forme
  close, aucune borne approchée).
- M6 `signedLengthSum_bounds_by_meetings` : la longueur de la dernière cellule de la série est < `p_{n+J+1}·(r − 1)`
  et la première > `p_{n+1}·(1 − 1/r)` : la borne de la descente non annulée est encadrée par les deux rencontres
  extrêmes et la fréquence seule.
- M7 `series_balance_near_meetings` : |somme signée des pentes − meetingSignedSum − poids non premiers signés| <
  `p_{n+J+1}·(r − 1)`.

## Expériences chiffrées (scripts `scripts/e441a_series_balance.py`, jumeau `scripts/e441b_twin_mpmath.py`)
Objets autorisés seulement : contacts d'une Tour (β = ½, T = hauteur d'Odlyzko de rang 1, 100, 10³, 10⁴, 10⁵, 10⁶,
2 001 052), cellules, signes `(−1)^k`, écarts, Λ exact (crible entier), demande brute `ψ(x) − x`.
Mesures (toutes avec les identités compilées comme contrôle, 0 violation attendue sur les identités) :
- (a) fréquence de validité des hypothèses : part des écarts avec contact ; part des rencontres qui sont des contacts
  (attendu 0) ; contacts par écart contre `T·log(p'/p)/π` (compilé : écart < 1).
- (b) identité M3 sur toutes les séries maximales où chaque écart a un contact (exacte, 0 violation) ; dans le cas
  général (écarts sans contact), mesure de la différence et de ce que porte une cellule à deux rencontres.
- (c) forme close M5 : erreur relative ; rapport |longueurs signées| / dernière cellule (attendu : `1/(1+r)` ≈ ½ à
  l'alternance près) ; encadrement M6 : 0 violation.
- (d) règle de signe entre rencontres consécutives : part de changements de signe ; prédiction par la parité de
  l'entier le plus proche de `T·log(p'/p)/π` (lecture par la fréquence, E439) : taux d'accord mesuré.
- (e) règle de montée : part des cellules de rencontre où `L ≤ log p` (B7) contre le seuil déterministe
  `x* : x*(r−1) = log x*` ; prédiction du seuil contre la mesure.
- (f) croissance de `meetingSignedSum` avec J : |S_J| contre `√J · log p` et contre la borne `p_{n+J+1}(r−1)` ;
  règle de régime (où le poids signé des rencontres domine ou non la descente non annulée).
Jumeau déterministe : mpmath 30 chiffres sur un sous-échantillon (indices de cellule, signes, longueurs, forme close).

## Protocole et critères
Sonde non versionnée, deux tentatives au plus pour le module définitif, journaux, `#print axioms`, build complet ;
scripts bornés (< 10 min), `nohup`, pas de sondage en boucle, aucune sortie fabriquée.
A : contradiction ; B : tout compile et toutes les identités à 0 violation ; C : échec en deux tentatives. Attendu : B.
Les « règles » ne seront déclarées que si (i) elles sont lues des journaux, (ii) elles sont cohérentes avec un énoncé
compilé ou désignées explicitement comme mesure sans théorème.
