#!/usr/bin/env python3
"""Sélection et classement (lecture seule) des théorèmes touchant la Tour / grille.

Sources : jsonl de l'audit (commit 003f31fc) + grep des fichiers RHV6Fresh actuels.
Sortie : selected.json (liste brute, avant surcharge manuelle).
"""
import json, re, glob, os

ROOT = "/opt/NeuroSymbolicModel/formalization"
DATA = f"{ROOT}/RHV6Fresh/experiments/audit_semantique/data"
OUT = os.path.dirname(os.path.abspath(__file__))
CAP = 1300

KW = re.compile(
    r"tower|\btour|contact|cell|pivot|occurrence|expectedMinimum|pMin|p_min|raccord|"
    r"countedPrime|lastPrime|reached|reach|mirror|secondTower|regime|translation|pitch|"
    r"radial|changeResidue|entry|ledger|fibre|fiber|charge|eulerTerm|eulerFactor|localEuler|"
    r"local_euler|euler_term|euler_factor", re.I)


def load(base):
    return [json.loads(l) for l in open(f"{DATA}/{base}.jsonl")]


def short(n):
    return n.split(".")[-1]


# ---------- RHV6Fresh : état actuel du code ----------
def scan_rhv6():
    """Tous les théorèmes présents dans RHV6Fresh/RHV6Fresh actuel, avec énoncé et docstring."""
    out = {}
    for f in sorted(glob.glob(f"{ROOT}/RHV6Fresh/RHV6Fresh/**/*.lean", recursive=True)):
        lines = open(f).read().split("\n")
        rel = os.path.relpath(f, f"{ROOT}/RHV6Fresh")
        for i, l in enumerate(lines):
            m = re.match(r"^(?:private |protected )?(?:theorem|lemma) (\S+)", l)
            if not m:
                continue
            name = m.group(1)
            stmt = []
            for j in range(i, min(i + 40, len(lines))):
                s = lines[j]
                stmt.append(s.strip())
                if re.search(r":=\s*(by)?\s*$|:= by\b|:=\s*\S", s) and j >= i:
                    break
            st = " ".join(stmt)
            st = re.sub(r":=.*$", "", st)
            # docstring
            doc = ""
            k = i - 1
            if k >= 0 and lines[k].strip().endswith("-/"):
                buf = []
                while k >= 0:
                    buf.append(lines[k])
                    if "/--" in lines[k]:
                        break
                    k -= 1
                doc = " ".join(x.strip() for x in reversed(buf))
            out.setdefault(short(name), []).append(
                dict(name=name, file=rel, line=i + 1, type=st, docstring=doc))
    return out


def main():
    cur = scan_rhv6()
    rows = []
    # RHV6Fresh : jsonl + nouveaux
    js = load("RHV6Fresh")
    seen = set()
    for x in js:
        sn = short(x["name"])
        present = sn in cur or os.path.exists(f"{ROOT}/RHV6Fresh/{x['file']}") and False
        if sn not in cur:
            continue  # retiré du code (ménage 2026-09-29 ou suivants)
        c = cur[sn][0]
        seen.add(sn)
        rows.append(dict(base="RHV6Fresh", name=x["name"], file=c["file"], line=c["line"],
                         type=x["type"], docstring=x.get("docstring") or c["docstring"],
                         mentions_RH=x["mentions_RH"], source="jsonl"))
    for sn, lst in cur.items():
        if sn in seen:
            continue
        c = lst[0]
        rows.append(dict(base="RHV6Fresh", name=c["name"], file=c["file"], line=c["line"],
                         type=c["type"], docstring=c["docstring"],
                         mentions_RH="RiemannHypothesis" in c["type"], source="grep"))
    retired = sum(1 for x in js if short(x["name"]) not in cur)
    for b in ["rhv3_lean", "RHV5Fresh", "rhv2_fresh", "rhv4_lean", "rh_gap_criterion"]:
        for x in load(b):
            if x.get("kind") not in (None, "theorem"):
                continue
            rows.append(dict(base=b, name=x["name"], file=x["file"], line=x["line"],
                             type=x["type"], docstring=x.get("docstring") or "",
                             mentions_RH=x["mentions_RH"], source="jsonl"))

    def themed(r):
        return bool(KW.search(r["name"]) or KW.search(r["type"]) or KW.search(r["file"]))

    T1RX = re.compile(r"PUniqueCenterRegime|CountOne|countOne|PCanonicalT1\b|\.PT1\b|uniquePrime|UniquePrime|"
                      r"UniqueCanonicalPrime|plural|containsTwo|twoPrimes|not_subsingleton|notSubsingleton|"
                      r"count_not_determined|foundPrimes_generallyPlural|windowSatisfiesT1|\.t1\b")
    STRONG = re.compile(r"occurrence|expectedMinimum|countOne|CountOne|singlePrime|uniquePrime|UniqueCenter|"
                        r"plural|twoPrimes|lastPrime|countedPrime|reached|pivot|cell|raccord|contact", re.I)
    sel, stats, taken = [], {}, set()

    def take(b, cand, label, cap=None):
        room = CAP - len(sel) if cap is None else min(cap, CAP - len(sel))
        cand = [r for r in cand if (r["base"], r["name"], r["file"]) not in taken]
        cand.sort(key=lambda r: (0 if T1RX.search(r["name"]) else 1 if STRONG.search(r["name"]) else
                                 2 if KW.search(r["name"]) else 3,
                                 r["file"] or "", r["line"] or 0))
        k = cand[:max(room, 0)]
        for r in k:
            taken.add((r["base"], r["name"], r["file"]))
        sel.extend(k)
        stats[label] = (len(cand), len(k))

    # 1. RHV6Fresh entier sur les thèmes
    take("RHV6Fresh", [r for r in rows if r["base"] == "RHV6Fresh" and themed(r)], "RHV6Fresh")
    # 2. rhv3_lean (Certification/Solution.lean rejoue Challenge.lean : exclu)
    take("rhv3_lean", [r for r in rows if r["base"] == "rhv3_lean" and themed(r)
                       and not (r["file"] or "").endswith("Certification/Solution.lean")], "rhv3_lean")
    # 3. candidats S (T1, cellule à un premier) et réfutations anticipatrices, autres bases
    take("S-autres", [r for r in rows if r["base"] not in ("RHV6Fresh", "rhv3_lean")
                      and T1RX.search(r["name"] + " " + (r["type"] or ""))
                      and not (r["file"] or "").endswith("SemanticSolution.lean")], "S-candidats autres bases", cap=45)
    # 4. RHV5Fresh, puis le reste
    for b in ["RHV5Fresh", "rhv4_lean", "rhv2_fresh", "rh_gap_criterion"]:
        take(b, [r for r in rows if r["base"] == b and themed(r)], b)
    json.dump(sel, open(f"{OUT}/selected.json", "w"), ensure_ascii=False, indent=0)
    print("RHV6Fresh retirés du code depuis 003f31fc :", retired)
    for b, (c, k) in stats.items():
        print(f"{b:26s} candidats={c:5d} retenus={k}")
    print("sélection", len(sel))


if __name__ == "__main__":
    main()
