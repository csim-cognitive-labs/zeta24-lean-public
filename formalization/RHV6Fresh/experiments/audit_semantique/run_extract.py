import subprocess,sys,re,os,json
F='/opt/NeuroSymbolicModel/formalization'
A=F+'/RHV6Fresh/experiments/audit_semantique'; D=A+'/data'
p=sys.argv[1]
OWN={'RHV6Fresh':'RHV6Fresh,RHV6Demonstration','rhv3_lean':'RHV3Lean,Certification','rhv2_fresh':'RHV2Fresh,Certification',
'rhv4_lean':'RHV4Lean,RHV4Certification','RHV5Fresh':'RHV5Fresh','rh_gap_criterion':'RhGapCriterion,RhGapCriterionTerminal,RiemannHypothesisProof'}
BASE={'RHV6Fresh':'RHV3Lean','rhv4_lean':'RHV3Lean','RHV5Fresh':'RHV3Lean'}
_re={}
def reach(m):
    if m in _re: return _re[m]
    seen=set(); st=[m]
    while st:
        x=st.pop(); f=F+'/'+p+'/'+x.replace('.','/')+'.lean'
        if not os.path.exists(f): continue
        for l in open(f,errors='ignore'):
            mm=re.match(r'\s*(?:public\s+)?import\s+(\S+)',l)
            if mm and mm.group(1) not in seen: seen.add(mm.group(1)); st.append(mm.group(1))
    _re[m]=seen; return seen
mods=[l.strip() for l in open(f'{D}/{p}_mods.txt') if l.strip()]
special=[m for m in mods if re.search(r'\.(Semantic)?Solution$',m)]
if os.path.exists(f'{D}/{p}_special.txt'): special+=[l.strip() for l in open(f'{D}/{p}_special.txt') if l.strip() and l.strip() not in special]
remaining=[m for m in mods if m not in special]; rnd=0; incidents=[]; outs=[]
while remaining:
    rnd+=1
    group=list(remaining); conflicts=[]
    while True:
        open(f'{D}/{p}_round.txt','w').write('\n'.join(group)+'\n')
        pre=f'{D}/{p}_r{rnd}'
        r=subprocess.run(['lake','env','lean','--run',A+'/DumpTheorems.lean',OWN[p],BASE.get(p,''),pre,f'{D}/{p}_round.txt'],cwd=F+'/'+p,capture_output=True,text=True)
        m=re.search(r'import (\S+) failed, environment already contains',r.stdout+r.stderr)
        if r.returncode==0: outs.append(pre); break
        if m:
            off=m.group(1)
            # all group modules that are the offender or transitively import it
            bad=[g for g in group if g==off or off in reach(g)]
            if not bad: print('FATAL no importer',off); sys.exit(1)
            for g in bad: group.remove(g); conflicts.append(g)
            incidents.append(f'{p}: import conflict (duplicate decl) at {off}: {len(bad)} module(s) moved to a separate extraction round'); continue
        print('FATAL',p,(r.stdout+r.stderr)[-1500:]); sys.exit(1)
    remaining=conflicts
    if rnd>60: print('too many rounds'); break
for m in special:
    rnd+=1; open(f'{D}/{p}_round.txt','w').write(m+'\n'); pre=f'{D}/{p}_r{rnd}'
    r=subprocess.run(['lake','env','lean','--run',A+'/DumpTheorems.lean',OWN[p],BASE.get(p,''),pre,f'{D}/{p}_round.txt'],cwd=F+'/'+p,capture_output=True,text=True)
    if r.returncode!=0: print('FATAL special',m,(r.stdout+r.stderr)[-800:]); sys.exit(1)
    outs.append(pre); incidents.append(f'{p}: module {m} shares theorem names with another module (Comparator Challenge/Solution or duplicate names); extracted in its own round (a joint import silently keeps only one copy)')
for suf in ['.jsonl','_defs.jsonl']:
    with open(f'{D}/{p}{suf}','w') as f:
        for o in outs:
            f.write(open(o+suf).read())
json.dump({'rounds':rnd,'incidents':incidents},open(f'{D}/{p}_extract_meta.json','w'))
print(p,'rounds',rnd,'incidents',len(incidents))
