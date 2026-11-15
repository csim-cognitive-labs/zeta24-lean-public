# Contributing

> Français : [CONTRIBUTING.fr.md](CONTRIBUTING.fr.md)

Owner: © Charles S. (see `COPYRIGHT.md`). The third-party code (`Zeta23Port`, `PNTPort`) remains under its Apache 2.0 licence (see `THIRD_PARTY_NOTICES.md`).

Before any contribution, read `README.md`, then the three master documents `formalization/RHV6Fresh/RHV6final_STRATEGIE_{SEMANTIQUE,MATHEMATIQUE,LEAN}.md` (the author's orders, prohibitions and the state of the route; in particular the semantic master, §19.98 to §19.111), and this file. The internal working log of the private research repository is not published. In case of conflict, a compiled theorem prevails. Some historical documents and experiment notes remain in French.

Rules:

1. No `sorry`, no `admit`, no added axiom, no undischarged hypothesis; run `#print axioms` on every statement.
2. `lake build RHV6Fresh` must stay green after every Lean change.
3. Pre-registration (commit) before any final compilation or numerical run.
4. A deterministic twin for every numerical conclusion; never fabricate output.
5. Isolated modules are not imported by `RHV6Fresh.lean`.
6. At most two compilation attempts per final module, each one logged (`attempts/` folder, exact errors).
7. No file larger than 50 MB, no model (`*.pt`, `*.safetensors`, `*.gguf`), no `venv/` or `.lake/` folder.
8. Attribution: every contribution cites the repository author and keeps the existing copyright and provenance notices. The attribution form is "Charles S. — CSIM Cognitive Labs".

Any error found (false statement, incomplete proof, non-reproducible numerical result) is reported through an issue, with the file and commit reference.
Every change goes through a pull request citing the author.

Licence and ownership: the project is under the Zeta24-Lean Research Licence — Proprietary, strict non-commercial use, version 1.0 (Licence de recherche Zeta24-Lean — Propriétaire, usage non commercial strict, version 1.0), see `LICENSE`. No commercial exploitation is allowed, and modified versions may not be redistributed.

Every contribution is assigned to the author on an exclusive, worldwide, royalty-free basis under the terms of `LICENSE` art. 4(g); by submitting a PR or an issue containing a contribution, you accept these terms. Contributors own nothing in the project.
