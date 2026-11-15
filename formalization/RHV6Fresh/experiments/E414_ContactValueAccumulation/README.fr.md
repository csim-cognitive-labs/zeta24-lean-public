> Version française conservée à titre de référence. Main language: English, see README.md.

# E414 — Identité des accumulations par contacts (pré-enregistrée le 2026-11-03, avant exécution)

**Question.** L'accumulation signée des VALEURS complexes d'une Tour sur ses intervalles de contacts successifs
(portions de bord comprises) est-elle égale à la différence directe de sa contribution spectrale, zéro par zéro et
collectivement, pour le canal brut (x^ρ/ρ) et le canal intégré (x^ρ/(ρ(ρ+1))) ?

**Théorème Lean correspondant (compilé avant l'exécution).** `Terminal/ContactValueGeometry.lean` :
`contact_accumulation_eq_endpoint_difference` (toute F, tout découpage) et
`Terminal/CollectiveContactAccumulation.lean` : `finite_contact_accumulation_eq_spectral_difference`.
Le jumeau numérique ne peut donc que vérifier l'identité à l'arrondi près ; une erreur HORS ARRONDI signalerait
un défaut du code, pas des mathématiques.

**Données.** 2 001 052 hauteurs d'Odlyzko (`data/odlyzko_zeros6_2001052.txt`, SHA-256 vérifié), posées sur la
ligne (hypothèse de données), multiplicité 1, deux branches (2·Re).

**Protocole.** Voir `PROTOCOL.md`. **Résultats.** `RESULTS.md` (rempli après exécution), `data/e414_results.json`,
`logs/e414.log`.
