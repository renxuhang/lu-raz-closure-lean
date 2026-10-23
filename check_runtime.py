"""Finite cross-check; universal proofs are separate Lean declarations."""
import json
from pathlib import Path
from normal_forms import generators,closure

QS=[4,6,13,33,65]
CORES=[0,1,2,3,4,5,6,7,9,10,11,13,14,15]

def main():
    root=Path(__file__).resolve().parent
    sources={}
    source_records=[]
    for line in (root/'runtime-source-masks.tsv').read_text(encoding='utf-8').splitlines():
        q,encoded=line.split('\t');q=int(q)
        assert q not in sources
        rows=list(map(int,encoded.split(',')))
        assert rows==generators(q),(q,'Lean source rows differ from independent explicit construction')
        assert len(rows)==4*q+3
        sources[q]=closure(rows)
        source_records.append(dict(q=q,x=q-1,rows=len(rows),ordered_source_masks_exact=True))
    assert set(sources)==set(QS)
    records=[];seen=set();combined={q:set()for q in QS}
    for line in (root/'runtime-masks.tsv').read_text(encoding='utf-8').splitlines():
        q,core,encoded=line.split('\t');q,core=int(q),int(core)
        assert (q,core) not in seen
        seen.add((q,core));masks=list(map(int,encoded.split(',')))
        assert len(masks)==len(set(masks)),(q,core,'duplicate enumeration')
        expected={u for u in sources[q]if u&15==core}
        assert set(masks)==expected,(q,core,len(masks),len(expected))
        formula={0:1,1:2,2:1,3:1,4:2,5:5,6:2*q*q-q-3,7:(3*q*q+7*q-14)//2,9:3*q*q-5*q+2,10:6,11:9*q-10,13:10*q-16,14:6*q-6,15:5*q*q-5*q+1}[core]
        assert len(masks)==formula
        assert not combined[q].intersection(masks)
        combined[q].update(masks)
        records.append(dict(q=q,x=q-1,core_bitmask=core,count=len(masks),exact_set_equality=True,enumeration_nodup=True))
    assert seen=={(q,c)for q in QS for c in CORES}
    totals=[]
    for q in QS:
        assert combined[q]==sources[q]
        assert len(combined[q])==(23*q*q+35*q-42)//2
        x=q-1
        assert len(combined[q])==(23*x*x+81*x+16)//2
        totals.append(dict(q=q,x=x,closure_size=len(combined[q]),complete_set_equality=True,formula_exact=True))
    result=dict(success=True,scope='finite independent transcription checks; not a substitute for the universal Lean proof',class_comparisons=len(records),source_rows_compared=sum(r['rows']for r in source_records),source_comparisons=source_records,totals=totals,rows=records)
    reports=root/'reports';reports.mkdir(exist_ok=True)
    (reports/'runtime-crosscheck.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items()if k!='rows'},ensure_ascii=False,indent=2))

if __name__=='__main__':main()
