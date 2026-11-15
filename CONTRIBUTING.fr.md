> Version française conservée à titre de référence. Main language: English, see CONTRIBUTING.md.

# Contribuer

Propriété © Charles S. (voir `COPYRIGHT.md`). Le code tiers (`Zeta23Port`, `PNTPort`) reste sous sa licence Apache 2.0 (voir `THIRD_PARTY_NOTICES.md`).

Avant toute contribution, lire `README.md`, puis les trois maîtres `formalization/RHV6Fresh/RHV6final_STRATEGIE_{SEMANTIQUE,MATHEMATIQUE,LEAN}.md` (ordres de l'auteur, interdits, état de la route ; en particulier le maître sémantique, §19.98 à §19.111) et le présent fichier. Le journal interne de travail du dépôt de recherche privé n'est pas publié. En cas de conflit, un théorème compilé l'emporte.

Règles :

1. Aucun `sorry`, aucun `admit`, aucun axiome ajouté, aucune hypothèse non déchargée ; `#print axioms` sur chaque énoncé.
2. `lake build RHV6Fresh` doit rester vert après tout changement Lean.
3. Pré-enregistrement (commit) avant toute compilation définitive ou exécution numérique.
4. Jumeau déterministe pour toute conclusion numérique ; ne jamais fabriquer de sortie.
5. Les modules isolés ne sont pas importés par `RHV6Fresh.lean`.
6. Deux tentatives de compilation au plus par module définitif, chacune consignée (dossier `attempts/`, erreurs exactes).
7. Ni fichier de plus de 50 Mo, ni modèle (`*.pt`, `*.safetensors`, `*.gguf`), ni dossier `venv/` ou `.lake/`.
8. Attribution : toute contribution cite l'auteur du dépôt et conserve les notices de copyright et de provenance existantes.

Toute erreur trouvée (énoncé faux, preuve incomplète, résultat numérique non reproductible) se signale par une issue, avec la référence du fichier et du commit.
Toute modification passe par une pull request citant l'auteur.

Toute contribution est cédée à l'auteur à titre exclusif, mondial et gratuit dans les termes de `LICENSE` art. 4(g) ; en soumettant une PR ou une issue contenant une contribution, vous acceptez ces termes.
