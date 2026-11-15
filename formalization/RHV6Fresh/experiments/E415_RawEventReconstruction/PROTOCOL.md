# E415 — protocole (pré-enregistré 2026-11-03)

1. Troncatures : N ∈ {3, 10, 40, 100, 300, 1000, 5000, 10000, 100000, 1000000, 2001052} (sommes cumulées, un seul passage).
2. Fenêtres : W1 = [3, 300], W2 = [10000, 10060], W3 = [100000, 100030].
3. Pour chaque n de chaque fenêtre et chaque troncature : Λ̂ᴬ et Λ̂ᴮ (= D) ; enregistrement brut (.npy) avant validation.
4. Validation (après) : E_H(n) = Λ̂_H(n) − Λ(n) ; rms et max par troncature, par classe (premier / puissance / vide).
5. C = D : accumulation par contacts complexes sur [n−1, n] et [n, n+1] (5000 zéros, n = 3..60) comparée à la somme directe.
6. Critères déclarés : (i) B converge en rms comme O(1/T_max) hors et aux événements (série absolument convergente) ;
   (ii) A présente un résidu de Gibbs non décroissant aux événements (E332, E404) ; (iii) |C − D| à l'arrondi.
7. Durée bornée : < 10 min.
