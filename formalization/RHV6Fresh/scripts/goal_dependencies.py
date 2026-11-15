#!/usr/bin/env python3
"""Graphe de dépendances du théorème ouvert (auteur, 2026-10-17, point E ; retiré sur le théorème ouvert courant le
2026-10-25) : pour chaque fait du contexte de `authentic_engaged_cascade_forbids_insertion` (but `False`), la liste des faits du
même contexte qui l'utilisent (référence textuelle dans leur preuve ou leur énoncé). Le but étant `False`, aucune ligne
d'obligation ne consomme rien : la mesure de progrès est le nombre de faits qui seraient consommés par une fermeture, jamais
l'empreinte du texte de l'erreur."""
import re, sys
src = open(sys.argv[1] if len(sys.argv) > 1 else 'RHV6Fresh/Terminal/DemonstrationChain.lean').read()
m = re.search(r'^theorem authentic_engaged_cascade_forbids_insertion(.*?)^(?:/--|theorem )', src, re.S | re.M)
if not m:
    print('  théorème `authentic_engaged_cascade_forbids_insertion` introuvable'); sys.exit(0)
blk = m.group(1)
head, body = blk.split(':= by', 1)
names = re.findall(r'\(([\w₀-₉\']+) :', head)
items = []  # (name, text)
cur = None
for line in body.split('\n'):
    if line.startswith('  have '):
        mm = re.match(r'^  have ([\w₀-₉\']+)', line)
        if mm:
            cur = [mm.group(1), line]; items.append(cur)
    elif line.startswith('  obtain ⟨'):
        inner = re.match(r'^  obtain ⟨(.*?)⟩', line).group(1)
        cur = None
        for nm in [x.strip() for x in inner.split(',')]:
            if re.fullmatch(r'[\w₀-₉\']+', nm) and nm != '_':
                items.append([nm, line])
        cur = items[-1] if items else None
    elif line.startswith('  intro '):
        for nm in line.split()[1:]:
            items.append([nm, line])
    elif line.startswith('    ') and cur is not None:
        cur[1] += '\n' + line
allnames = names + [n for n, _ in items]
used = {n: [] for n in allnames}
for n, txt in items:
    for k in allnames:
        if k != n and re.search(r'(?<![\w₀-₉\'])' + re.escape(k) + r'(?![\w₀-₉\'])', txt):
            used[k].append(n)
print("  théorème ouvert : `authentic_engaged_cascade_forbids_insertion`, but `False` ; aucune ligne d'obligation : 0 fait consommé")
print(f"  faits en contexte (hypothèses, obtain, have) : {len(allnames)}")
for k in allnames:
    print(f"    {k:22s} ← {', '.join(dict.fromkeys(used[k])) if used[k] else '—'}")
