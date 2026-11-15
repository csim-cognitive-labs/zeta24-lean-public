import os,sys,glob
F='/opt/NeuroSymbolicModel/formalization'
D=F+'/RHV6Fresh/experiments/audit_semantique/data'
PROJ={
 'RHV6Fresh':dict(libs={'RHV6Fresh':True,'RHV6Demonstration':True},base='RHV3Lean'),
 'rhv3_lean':dict(libs={'RHV3Lean':True,'Certification':True},base=''),
 'rhv2_fresh':dict(libs={'RHV2Fresh':True,'Certification':False},base=''),
 'rhv4_lean':dict(libs={'RHV4Lean':True,'RHV4Certification':False},base='RHV3Lean'),
 'RHV5Fresh':dict(libs={'RHV5Fresh':True},base='RHV3Lean'),
 'rh_gap_criterion':dict(libs={'RhGapCriterion':True,'RhGapCriterionTerminal':True,'RiemannHypothesisProof':False},base=''),
}
# extra: RHV3 Certification and RHV2 Certification are 'Certification.+' ; rhv3 default includes both
DEFAULT_LIBS={'rhv3_lean':{'RHV3Lean','Certification'},'rhv2_fresh':{'RHV2Fresh'},'rhv4_lean':{'RHV4Lean'},'RHV5Fresh':{'RHV5Fresh'},
 'RHV6Fresh':{'RHV6Fresh','RHV6Demonstration'},'rh_gap_criterion':{'RhGapCriterion','RhGapCriterionTerminal'}}
import re
# libs whose glob is '.+' (all submodules) -> every source is in the default target if lib is default; else import closure of root
ALLGLOB={'rhv3_lean':{'RHV3Lean','Certification'},'rhv2_fresh':{'RHV2Fresh','Certification'},'rhv4_lean':{'RHV4Lean','RHV4Certification'},'RHV5Fresh':{'RHV5Fresh'},'RHV6Fresh':set(),'rh_gap_criterion':{'RhGapCriterion','RiemannHypothesisProof'}}
def closure(root,roots):
    seen=set();st=list(roots)
    while st:
        m=st.pop()
        if m in seen: continue
        f=f'{root}/'+m.replace('.','/')+'.lean'
        if not os.path.exists(f): continue
        seen.add(m)
        for l in open(f,errors='ignore'):
            mm=re.match(r'\s*(?:public\s+)?import\s+(\S+)',l)
            if mm: st.append(mm.group(1))
    return seen
for p,c in PROJ.items():
    root=F+'/'+p; bl=root+'/.lake/build/lib/lean'
    defroots=[l for l in DEFAULT_LIBS[p]]
    clo=closure(root,defroots)
    rows=[];seen=set()
    for lib in c['libs']:
        srcs=[]
        if os.path.isfile(f'{root}/{lib}.lean'): srcs.append(f'{lib}.lean')
        for dp,_,fs in os.walk(f'{root}/{lib}'):
            for f in fs:
                if f.endswith('.lean'): srcs.append(os.path.relpath(os.path.join(dp,f),root))
        for s in sorted(srcs):
            mod=s[:-5].replace('/','.'); seen.add(mod)
            o=f'{bl}/{s[:-5]}.olean'
            indef=(lib in DEFAULT_LIBS[p] and ((lib in ALLGLOB[p] and mod!=lib) or mod in clo)) or mod in clo
            if indef and mod in clo|{m for m in [mod] if lib in ALLGLOB[p] and lib in DEFAULT_LIBS[p] and mod!=lib} and os.path.exists(o): st='compilé (lake build, cible par défaut)'
            elif not os.path.exists(o): st='NON COMPILÉ (olean absent)'
            elif os.path.getmtime(o)+1<os.path.getmtime(f'{root}/{s}'): st='NON COMPILÉ (source plus récent)'
            else: st='compilé'
            rows.append((mod,s,st,'yes' if indef else 'no'))
    # orphans
    for lib in c['libs']:
        for o in glob.glob(f'{bl}/{lib}/**/*.olean',recursive=True)+glob.glob(f'{bl}/{lib}.olean'):
            mod=os.path.relpath(o,bl)[:-6].replace('/','.')
            if mod not in seen: rows.append((mod,'(source absent)','ORPHELIN (olean sans source)','n/a'))
    with open(f'{D}/{p}_modules.tsv','w') as f:
        f.write('module\tfile\tolean_status\tin_default_target\n')
        for r in rows: f.write('\t'.join(r)+'\n')
    with open(f'{D}/{p}_mods.txt','w') as f:
        for r in rows:
            if r[2].startswith('compilé'): f.write(r[0]+'\n')
    print(p,len(rows),sum(r[2].startswith('compilé') for r in rows),sum(r[2].startswith('ORPH') for r in rows))
