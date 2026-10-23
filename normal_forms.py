"""Explicit disjoint normal forms for the completed Lu--Raz construction.

This is a finite cross-check of the accompanying all-parameter written argument.
It is not itself an all-parameter Lean proof. Coordinates are one-based.
"""
from collections import Counter


def interval(a, b):
    return ((1 << (b-a+1))-1) << (a-1) if a <= b else 0


def singleton(e):
    return 1 << (e-1)


def generators(q):
    """Independent explicit definition, including the missing row h+1."""
    assert q >= 4
    h, n = 2*q, 4*q
    I, s = interval, singleton
    rows = [I(1,n), s(2)|I(h+1,n), s(1)|I(3,h)|s(n),
            s(1)|I(4,h+2), s(1)|s(3)|I(h+3,n)]
    rows += [s(1)|s(4)|I(i+1,h+i-2) for i in range(5,q+3)]
    rows += [s(1)|s(4)|I(i+1,h+i-3) for i in range(q+3,h+1)]
    rows += [s(2)|s(4)|I(h+2,n-2), s(2)|s(4)|I(h+3,n-1),
             s(2)|s(3)|I(h+4,n)]
    rows += [s(2)|s(3)|I(5,i-h+1)|I(i+1,n) for i in range(h+4,3*q+1)]
    rows += [s(2)|s(3)|I(5,q+3)|I(3*q+2,n-1)]
    rows += [s(2)|s(3)|I(5,i-h+2)|I(i+1,n) for i in range(3*q+2,n)]
    rows += [s(3)|I(5,h+2)|s(3*q+1), I(3*q+2,n), s(1)|I(5,q+2)]
    assert len(rows) == n+3
    return rows


def closure(rows):
    result = set()
    for a in rows:
        result |= {a} | {a|b for b in result}
    return result


def normal_forms(q):
    assert q >= 4
    h, n, r, e = 2*q, 4*q, 3*q+1, q+3
    I, s = interval, singleton
    A, B, C, D, E, Z = I(5,q+2), I(r+1,n), I(5,h+2)|s(r), I(h+1,n), I(h+3,n), I(5,h)|s(n)
    P = list(range(4,q+2)) + list(range(q+3,h+2))
    def b(p): return h+p if p<=q+1 else h+p-1
    def g(a): return h+a-3 if a<=q+3 else h+a-4
    groups = {}
    def add(core, label, values):
        values = list(values)
        assert len(values)==len(set(values)), (q,core,label,'internal duplicate')
        assert all(v&15==0 for v in values)
        groups.setdefault(core,{})[label] = {v|core for v in values}
    add(0,'B',[B]); add(1,'A,AB',[A,A|B]); add(2,'D',[D]); add(3,'AD',[A|D])
    add(4,'C,CB',[C,C|B]); add(5,'five',[E,A|E,I(5,n),C,C|B])

    # Core {2,3}: increasing prefixes and decreasing suffixes.
    add(6,'L_pairs', [I(5,p)|I(b(t),n-(p==e and t==e)) for p in P for t in P if t<=p])
    add(6,'M_filled',[I(5,e)|I(r+1,n)])
    add(6,'D',[I(5,p)|D for p in P if p<=h-1]+[I(5,n)])
    add(6,'C_regular',[I(5,h+2)|s(r)|I(b(t),n) for t in P if t!=e])
    add(6,'C_exception',[I(5,h+2)|I(r,n-1)])
    # Core {1,2,3}: explicit normalized A-images, then new E-images.
    add(7,'A_L_low',[A|I(b(t),n) for t in P if t<=q+1])
    add(7,'A_L_high',[I(5,p)|I(b(t),n-(p==e and t==e))
                      for p in P if p>=e for t in P if t<=p])
    add(7,'A_M_filled',[I(5,e)|I(r+1,n)])
    add(7,'A_D',[I(5,p)|D for p in [q+2]+[t for t in P if e<=t<=h-1]]+[I(5,n)])
    add(7,'A_C_regular',[I(5,h+2)|s(r)|I(b(t),n) for t in P if t!=e])
    add(7,'A_C_exception',[I(5,h+2)|I(r,n-1)])
    add(7,'E_new_right',[I(5,p)|I(h+3,n) for p in P+[q+2]])
    add(7,'E_new_D',[I(5,p)|D for p in P if p<=q+1])

    add(9,'J_intervals',[I(a,t) for a in range(5,h+2) for t in range(g(a),n-2)])
    add(9,'AJ_gaps',[A|I(a,t) for a in range(q+4,h+2) for t in range(g(a),n-2)])
    add(9,'JB_gaps',[I(a,t)|B for a in range(5,h+2) for t in range(g(a),r)])
    add(9,'JB_join',[I(a,n) for a in range(5,h+2)])
    add(9,'AJB_double_gap',[A|I(q+4,3*q)|B])
    add(9,'AJB_join',[A|I(a,n) for a in range(q+4,h+2)])
    k_tails = [I(h+2,n-2),I(h+3,n-1),I(h+2,n-1),I(h+2,n),I(h+3,n),D]
    add(10,'six',k_tails)
    add(11,'J_right',[I(a,t) for a in range(5,h+2) for t in (n-2,n-1,n)])
    add(11,'AJ_right',[A|I(a,t) for a in range(q+4,h+2) for t in (n-2,n-1,n)])
    add(11,'AK',[A|k for k in k_tails[:-1]])

    add(13,'EJ',[I(a,n) for a in range(5,h+2)])
    add(13,'AEJ',[A|I(a,n) for a in range(q+4,h+2)])
    add(13,'CJ',[I(5,t)|s(r) for t in range(h+2,n-2) if t!=r-1])
    add(13,'ZJ',[I(5,t)|s(n) for t in range(h+2,n-2)])
    add(13,'CZJ_extra',[I(5,t)|s(r)|s(n) for t in range(h+2,r-1)])
    add(13,'ZJB_extra',[I(5,t)|B for t in range(h+2,r)])
    add(13,'CJB_extra',[I(5,t)|I(r,n) for t in range(h+2,r-1)])
    add(13,'Z_extras',[Z,Z|B,Z|E])

    add(14,'K_L',[I(5,p)|I(t,n) for p in P for t in (h+2,h+3)])
    add(14,'D_L_new',[I(5,p)|D for p in P if p<=h-1])
    add(14,'K_M',[I(5,e)|I(t,n-1) for t in (h+2,h+3)])
    add(14,'C_K_new',[I(5,n-2),I(5,n-1)])
    add(14,'last_gap',[I(5,n-2)|s(n)])

    # Core {1,2,3,4}, partitioned by n,h+1,h+2 and the left gap.
    add(15,'no_n_intervals',[I(5,n-2),I(5,n-1)])
    add(15,'no_n_MJ_right',[I(5,t)|I(r+1,n-1) for t in range(h+2,r)])
    add(15,'no_n_MJ_left',[I(5,e)|I(a,n-1) for a in range(q+5,h+2)])
    add(15,'no_n_MK',[I(5,e)|I(t,n-1) for t in (h+2,h+3)])
    add(15,'no_n_CMJ',[I(5,t)|I(r,n-1) for t in range(h+2,r-1)])
    add(15,'no_h1_short',[I(5,p)|I(t,n) for p in range(4,h+1) for t in (h+2,h+3)])
    add(15,'no_h1_ZL',[I(5,h)|I(t,n) for t in range(h+4,n)])
    add(15,'no_h1_exception',[I(5,h)|I(h+2,n-2)|s(n)])
    add(15,'no_h2',[I(5,h+1)|I(t,n) for t in range(h+3,n+1)])
    add(15,'no_five',[I(a,n) for a in range(6,h+2)])
    add(15,'left_gap',[I(5,p)|I(a,n) for p in range(5,h) for a in range(p+2,h+2)])
    add(15,'full',[I(5,n)])
    add(15,'right_gap',[I(5,t)|I(a,n) for t in range(h+2,n-1) for a in range(t+2,n+1)])
    add(15,'isolated_r',[I(5,t)|s(r)|I(a,n) for t in range(h+2,r-1) for a in range(r+2,n+1)])

    formulas = {0:1,1:2,2:1,3:1,4:2,5:5,6:2*q*q-q-3,
                7:(3*q*q+7*q-14)//2,9:3*q*q-5*q+2,10:6,
                11:9*q-10,13:10*q-16,14:6*q-6,15:5*q*q-5*q+1}
    all_values = set()
    for core, subgroups in groups.items():
        merged = set().union(*subgroups.values())
        assert len(merged)==sum(map(len,subgroups.values())), (q,core,'overlapping groups')
        assert len(merged)==formulas[core], (q,core,len(merged),formulas[core])
        all_values |= merged
    assert len(all_values)==(23*q*q+35*q-42)//2
    return all_values, groups


def audit(q):
    normal, groups = normal_forms(q)
    actual = closure(generators(q))
    assert normal == actual, (q,len(normal),len(actual),len(normal-actual),len(actual-normal))
    return dict(q=q,x=q-1,n=4*q,closure_nonempty=len(actual),
                normal_forms_exact=True,groups_disjoint=True,
                by_core={str(c):{k:len(v) for k,v in gs.items()} for c,gs in groups.items()})


if __name__ == '__main__':
    import argparse, json
    from pathlib import Path
    p=argparse.ArgumentParser()
    p.add_argument('--max-q',type=int,default=40)
    p.add_argument('--output',default='normal-form-audit.json')
    args=p.parse_args()
    rows=[]
    for q in range(4,args.max_q+1):
        rows.append(audit(q))
        print(f'q={q}: {rows[-1]["closure_nonempty"]} exact',flush=True)
    Path(args.output).write_text(json.dumps({'scope':'finite cross-check; all-parameter argument is separate',
         'rows':rows},ensure_ascii=False,indent=2),encoding='utf-8')
