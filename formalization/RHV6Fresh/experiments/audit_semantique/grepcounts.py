import re,json,os
F='/opt/NeuroSymbolicModel/formalization'; D=F+'/RHV6Fresh/experiments/audit_semantique/data'
out={}
for p in ['RHV6Fresh','rhv3_lean','rhv2_fresh','rhv4_lean','RHV5Fresh','rh_gap_criterion']:
    comp=[l.strip().split('\t') for l in open(f'{D}/{p}_modules.tsv')][1:]
    comp=[c for c in comp if c[2].startswith('compilé')]
    n=0; nsorry_src=0
    for c in comp:
        t=open(f'{F}/{p}/{c[1]}',errors='ignore').read()
        n+=len(re.findall(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|nonrec|noncomputable)\s+)*(?:theorem|lemma)\s',t,re.M))
    ex=sum(1 for _ in open(f'{D}/{p}.jsonl')) if os.path.exists(f'{D}/{p}.jsonl') else None
    out[p]=(n,ex); print(p,'grep',n,'extracted',ex)
json.dump(out,open(f'{D}/grepcounts.json','w'))
