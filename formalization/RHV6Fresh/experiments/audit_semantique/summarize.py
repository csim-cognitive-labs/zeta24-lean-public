import json,re,os,collections
F='/opt/NeuroSymbolicModel/formalization'; A=F+'/RHV6Fresh/experiments/audit_semantique'; D=A+'/data'
P=['RHV6Fresh','rhv3_lean','rhv2_fresh','rhv4_lean','RHV5Fresh','rh_gap_criterion']
br={l.split()[0]:l.strip() for l in open(D+'/build_results.txt') if 'exit=' in l}
gc=json.load(open(D+'/grepcounts.json')) if os.path.exists(D+'/grepcounts.json') else {}
inc=[];sec=[]
STD={'propext','Classical.choice','Quot.sound'}
for p in P:
    log=open(f'{D}/{p}_build.log',errors='ignore').read()
    ok=re.findall(r'Build completed successfully \((\d+) jobs\)',log)
    errs=[l for l in log.splitlines() if re.search(r'\berror\b',l) and not l.startswith('info:')][:10]
    sorrywarn=[l for l in log.splitlines() if re.search(r"declaration uses [`']sorry[`']",l)]
    mods=[l.rstrip('\n').split('\t') for l in open(f'{D}/{p}_modules.tsv')][1:]
    comp=sum(m[2].startswith('compilé') for m in mods); non=[m for m in mods if m[2].startswith('NON')]; orph=[m for m in mods if m[2].startswith('ORPH')]
    th=[json.loads(l) for l in open(f'{D}/{p}.jsonl')]
    defs=[json.loads(l) for l in open(f'{D}/{p}_defs.jsonl')]
    meta=json.load(open(f'{D}/{p}_extract_meta.json'))
    sor=[t for t in th if t['uses_sorry']]
    ns=[t for t in th if t['nonstandard_axioms']]
    axdecl=[d for d in defs if d['kind']=='axiom']
    rh=[t for t in th if t['mentions_RH']]
    s=f'## {p}\n\n- Build (`lake build`, cibles par défaut): {"PASS" if ok and br.get(p,"").find("exit=0")>=0 else "FAIL"} ; {ok[-1] if ok else "?"} jobs ; {br.get(p,"")} ; lignes error: {len(errs)} ; warnings sorry: {len(sorrywarn)}\n'
    s+=f'- Modules sources: {len(mods)-len(orph)} ; compilés: {comp} ; NON COMPILÉ: {len(non)} ; oleans orphelins (sans source): {len(orph)}\n'
    s+=f'- Théorèmes extraits: {len(th)} (grep source `theorem|lemma` sur modules compilés: {gc.get(p,["?"])[0]}) ; définitions/structures/inductifs/axiomes: {len(defs)}\n'
    s+=f'- avec sorryAx: {len(sor)} ; axiomes non standard: {len(ns)} (déclarations `axiom` dans le projet: {len(axdecl)}) ; mentions_RH: {len(rh)} ; théorèmes privés: {sum(1 for t in th if t.get("private"))}\n'
    if meta['incidents']: s+='- Incidents d\'import: '+'; '.join(meta['incidents'])+'\n'
    if non: s+='- NON COMPILÉ: '+', '.join(m[0]+' ('+m[2][13:-1]+')' for m in non)+'\n'
    if orph: s+=f'- Orphelins: {len(orph)} (liste dans {p}_modules.tsv)\n'
    for t in sor: inc.append(f'{p}: sorryAx dans `{t["name"]}`')
    if ns:
        axs=collections.Counter(a for t in ns for a in t['nonstandard_axioms'])
        with open(f'{D}/{p}_nonstandard_axioms.tsv','w') as f:
            for t in ns: f.write(t['name']+'\t'+t['module']+'\t'+','.join(t['nonstandard_axioms'])+'\n')
        inc.append(f'{p}: {len(ns)} théorèmes dépendent d\'axiomes non standard ({len(axs)} axiomes distincts, tous de la forme `*.native_decide.ax_*` = native_decide/ofReduceBool ? : '+('OUI' if all('native_decide' in a or 'ofReduceBool' in a for a in axs) else 'NON, autres: '+str([a for a in axs if 'native_decide' not in a][:5]))+') ; liste complète: data/'+p+'_nonstandard_axioms.tsv ; axiomes: '+'; '.join(sorted(axs))[:600])
    if sorrywarn: inc.append(f'{p}: {len(sorrywarn)} warnings « declaration uses sorry » dans le log de build: '+' | '.join(w[:140] for w in sorrywarn[:6]))
    for d in axdecl: inc.append(f'{p}: déclaration `axiom` {d["name"]} ({d["module"]})')
    if not ok or br.get(p,'').find('exit=0')<0: inc.append(f'{p}: lake build en échec')
    for e in errs: inc.append(f'{p}: build error line: {e[:200]}')
    for m in non: inc.append(f'{p}: module NON COMPILÉ {m[0]} ({m[2]})')
    if orph: inc.append(f'{p}: {len(orph)} oleans orphelins (source absente) dans .lake/build, exclus de l\'extraction')
    for i in meta['incidents']: inc.append(i)
    # RH theorems
    def cat(t):
        ty=t['type'].strip()
        if re.fullmatch(r'(\w+\.)*RiemannHypothesis',ty): return 'TERME FERMÉ (type exact RiemannHypothesis)'
        parts=re.split(r'\s→\s',ty)
        if '↔' in parts[-1]: return 'iff'
        if 'RiemannHypothesis' in parts[-1]: return 'conclusion RH'
        return 'RH en hypothèse/ailleurs'
    cats=collections.Counter(cat(t) for t in rh)
    s+='- mentions_RH par catégorie: '+', '.join(f'{k}: {v}' for k,v in cats.items())+'\n'
    for t in rh:
        if cat(t).startswith('TERME'): inc.append(f'{p}: TERME FERMÉ RiemannHypothesis `{t["name"]}` axiomes={t["axioms"]}')
    s+='\n| théorème | catégorie | hyp_count | axiomes | module |\n|---|---|---|---|---|\n'
    for t in rh: s+=f'| `{t["name"]}` | {cat(t)} | {t["hyp_count"]} | {",".join(t["axioms"])} | {t["module"]} |\n'
    sec.append(s+'\n')
o='# SUMMARY — Phase A (collecte mécanique, 2026-09-29)\n\n## INCIDENTS\n\n'
o+=('\n'.join('- '+i for i in inc) if inc else '- aucun')+'\n\n'
o+='Outils: `DumpTheorems.lean` (extracteur), `modules.py`, `run_extract.py`, `build_all.sh`, `summarize.py`. Données: `data/`.\n\n'
o+=''.join(sec)
o+='## Contrôle grep vs extraction (RHV6Fresh et autres)\n\n'+'\n'.join(f'- {p}: grep {gc[p][0]} ; extraits {gc[p][1]}' for p in P)+'''

Écarts expliqués (`data/miss_check.txt`, contrôle par nom après retrait des commentaires de bloc : 0 déclaration source absente de l'extraction pour les 6 projets) :
- extraits > grep : théorèmes non écrits par `theorem|lemma` dans la source — champs Prop de structures (`X.field`), `*.mk.congr_simp`, `ext_iff`, `ofNat_ctorIdx`, instances de classes Prop (`instTotal…`), théorèmes auxiliaires générés.
- grep > extraits (rhv3_lean : Solution) : les modules `Certification.Solution` rejouent les MÊMES noms que `Certification.Challenge` (Comparator) ; un import conjoint ne garde qu'une copie silencieusement (pas d'erreur pour les théorèmes en double) — extraction dédiée par module dans une ronde séparée. Même mécanisme pour 3 modules de `rh_gap_criterion` (noms de théorèmes dupliqués entre modules).
- le grep brut compte aussi des mots de prose (`theorem to`, `theorem of`… en tête de ligne de docstring).
- Les théorèmes `private` sont conservés (nom utilisateur via `privateToUserName?`, champ `private`, `full_name`).
- `deps_project` peut contenir des constantes auxiliaires `*._proof_N` (le terme de preuve les référence).

'''
o+='## Hors périmètre\n\n'+open(D+'/out_of_scope.txt').read().split('STRAY')[0].replace('\n','\n\n')
o+='\nFichiers `.lean` isolés hors bibliothèques des projets lake (liste complète dans `data/out_of_scope.txt`): '+str(open(D+'/out_of_scope.txt').read().count('\n./'))+'.\n'
open(D+'/SUMMARY.md','w').write(o)
print(o[:3000])
