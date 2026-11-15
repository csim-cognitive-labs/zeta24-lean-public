# E421 — protocole (pré-enregistré 2026-11-03)
1. Familles : N ∈ {10, 100, 1 000, 10 000} premiers zéros sur la fenêtre logarithmique [log 1000, log 1000 + π/T₁] (un pas de la
   Tour la plus basse) ; N = 2 001 052 sur [log 1000, log 1000 + 10π/T_max]. Fusion triée de tous les contacts avec étiquette.
2. Mesures : nombre total ; pour les paires (1,2), (1,3), (2,3), (1,100), (1,N) : comptes de contacts de la Tour haute entre
   contacts consécutifs de la Tour basse, vérifiés dans {⌊T₂/T₁⌋, ⌈T₂/T₁⌉} ; décalage exact vérifié (identité) ; espacements
   consécutifs de la fusion (min, médiane, max, rapport au pas moyen) ; coïncidences exactes (|Δlog| < 10⁻¹²) ; pour chaque
   Tour, position de ses contacts dans le cycle de la Tour 1 (phase T₁ log C − φ₁ mod π, en fraction de π) : histogramme.
3. Sensibilité radiale (synthétique, séparée) : Tour de hauteur T* = milieu des zéros (100,101), β ∈ {½, 0,3, 0,45, 0,49},
   insérée dans la famille des 10 000 ; nombre d'inversions d'ordre dans la fusion entre β et ½ ; déplacement en fraction de pas.
   Paire miroir (β, 1−β) à T* : distance minimale entre les deux ensembles de contacts (fraction de pas), attendue > 0 pour β ≠ ½.
4. Durée < 5 min, nohup, pas de sondage.
