import re,json,sys
F='/opt/NeuroSymbolicModel/formalization'; D=F+'/RHV6Fresh/experiments/audit_semantique/data'
for p in ['RHV6Fresh','rhv3_lean','rhv2_fresh','rhv4_lean','RHV5Fresh','rh_gap_criterion']:
    comp=[l.strip().split('\t') for l in open(f'{D}/{p}_modules.tsv')][1:]
    comp=[c for c in comp if c[2].startswith('compilé')]
    ex=set(); exm={}
    for l in open(f'{D}/{p}.jsonl'):
        d=json.loads(l); ex.add(d['name'].split('.')[-1]); exm.setdefault(d['module'],set()).add(d['name'].split('.')[-1])
    miss=[]; total=0
    for c in comp:
        t=open(f'{F}/{p}/{c[1]}',errors='ignore').read()
        t=re.sub(r'/-.*?-/','',t,flags=re.S)  # strip block comments
        for m in re.finditer(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|nonrec|noncomputable)\s+)*(?:theorem|lemma)\s+([^\s:({\[]+)',t,re.M):
            total+=1
            if m.group(1).split('.')[-1] not in exm.get(c[0],set()): miss.append((c[0],m.group(1)))
    print(p,'source decls (comments stripped):',total,'missing from extraction:',len(miss),miss[:5])
