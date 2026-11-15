import re,json,sys
F='/opt/NeuroSymbolicModel/formalization'; D=F+'/RHV6Fresh/experiments/audit_semantique/data'
p=sys.argv[1]
comp=[l.strip().split('\t') for l in open(f'{D}/{p}_modules.tsv')][1:]
comp=[c for c in comp if c[2].startswith('compilé')]
src={}
for c in comp:
    t=open(f'{F}/{p}/{c[1]}',errors='ignore').read()
    for m in re.finditer(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|nonrec|noncomputable)\s+)*(?:theorem|lemma)\s+(\S+)',t,re.M):
        src.setdefault(c[0],[]).append(m.group(1))
ex={}
for l in open(f'{D}/{p}.jsonl'):
    d=json.loads(l); ex.setdefault(d['module'],[]).append(d['name'])
onlysrc=[];onlyex=[]
for m in set(src)|set(ex):
    s=src.get(m,[]); e=ex.get(m,[])
    el=set(n.split('.')[-1] for n in e); sl=set(n.split('.')[-1] for n in s)
    onlysrc+=[(m,n) for n in s if n.split('.')[-1] not in el]
    onlyex+=[(m,n) for n in e if n.split('.')[-1] not in sl]
print(p,'only in source:',len(onlysrc),onlysrc[:6]); print('only extracted:',len(onlyex),onlyex[:8])
