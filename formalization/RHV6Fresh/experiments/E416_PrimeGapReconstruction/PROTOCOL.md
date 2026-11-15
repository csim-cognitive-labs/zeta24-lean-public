# E416 — protocole (pré-enregistré 2026-11-03)

1. Entrées du moteur : `lamA_W*.npy`, `lamB_W*.npy` (E415, calculés des seuls zéros) ; fenêtres W1, W2, W3 ; toutes les troncatures.
2. Reconstruction : étiquette par plus proche valeur admissible (ci-dessus) ; premiers reconstruits = n étiquetés
   « prime » ; écarts reconstruits = différences consécutives. Le premier suivant n'est jamais fourni.
3. Validation après coup : crible (VALIDATION) ; comptages ; première divergence d'écart.
4. Critère déclaré : la reconstruction est dite exacte sur une fenêtre et une troncature si tous les écarts de la fenêtre
   coïncident ; on rapporte la plus petite troncature exacte par canal (E417 §3). Aucune annonce d'exactitude si le
   résultat dépend d'un seuil choisi après coup (il n'y a pas de seuil).
5. Durée bornée : < 2 min.
