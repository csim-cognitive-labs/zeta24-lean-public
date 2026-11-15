# E424–E425 — protocole (pré-enregistré 2026-11-03)
1. Données : `experiments/data/odlyzko_zeros6_2001052.txt` (SHA-256 vérifié au chargement). Premiers : crible d'Ératosthène
   jusqu'à 3,6·10⁷ (p_{2 001 052} ≈ 3,4·10⁷), vérifié par comptage.
2. E424 : vectorisé par blocs de 262 144 paires ; k = premier contact de l au-delà de 2 ; valeurs des Tours évaluées
   en complexe depuis la position du contact (pas depuis l'angle exact) ; erreurs maximales et quantiles consignés.
   Synthétique : 4 prédécesseurs × 3 positions radiales ; jumeau mpmath (30 chiffres) sur 6 paires réelles
   (rangs 1, 100, 2 000, 100 000, 1 000 000, 2 001 051) et sur les 12 cas synthétiques.
3. E425(a) : 4 hauteurs × 3 positions radiales, contacts dans [2, 10⁴] ; contrôle ON à 4 hauteurs réelles.
   E425(b) : 2 001 052 zéros ; jumeau de déplacement β = 0,3 aux mêmes hauteurs ; jumeau mpmath sur 10 rangs.
4. Critères déclarés avant exécution : E424 lectures radiales ≤ 10⁻⁹, T̂_e ≤ T_l·10⁻⁹ ; E425(a) Im non nulle à chaque
   contact OFF et |Im/|miroir| − |sin φ_rel|| ≤ 10⁻¹⁰, contrôle ON ≤ 10⁻¹⁰ ; E425(b) cran ∈ {−1, 0} à 100 %.
   Tout critère non tenu est consigné tel quel.
5. Durée bornée < 10 min par script, nohup, pas de sondage en boucle. Deux tentatives maximum par script ; toute
   correction de script est consignée dans RESULTS.md.
