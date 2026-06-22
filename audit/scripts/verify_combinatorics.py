#!/usr/bin/env python3
"""Independent finite checks for the colored Turan and matrix arguments."""
from __future__ import annotations
from itertools import combinations
from math import comb
from pathlib import Path
import json
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix


def M2(n:int):
    best=None; arg=None
    for a in range(n+1):
      for b in range(n-a+1):
       for c in range(n-a-b+1):
        d=n-a-b-c
        val=3*(a*a+b*b+c*c+d*d)+4*a*b
        if best is None or val<best:
            best,arg=val,(a,b,c,d)
    return best,arg

def S(n:int):
    m2,arg=M2(n)
    return (3*n*n-m2)//2, tuple(sorted(arg))

def region(n:int):
    s,_=S(n)
    return 4*comb(n,2)+s+n+1


def compositions(total:int,k:int,prefix=()):
    if k==1:
        yield prefix+(total,); return
    for x in range(total+1):
        yield from compositions(total-x,k-1,prefix+(x,))

def F2(cells):
    rows=[sum(cells[4*i:4*i+4]) for i in range(3)]
    cols=[sum(cells[j::4]) for j in range(4)]
    return 2*sum(x*x for x in rows)+2*sum(x*x for x in cols)-sum(x*x for x in cells)

def exhaustive_matrix(limit=10):
    out=[]
    for n in range(limit+1):
        target,_=M2(n)
        mn=None; witness=None; count=0
        for u in compositions(n,12):
            count+=1
            v=F2(u)
            if mn is None or v<mn:
                mn,witness=v,u
        if mn!=target:
            raise AssertionError((n,mn,target,witness))
        out.append({"n":n,"matrices":count,"minimum_2F":mn,"M2":target,"witness":witness})
    return out


def colored_milp(n:int):
    edges=list(combinations(range(n),2)); m=len(edges)
    # Variables d_e, e_e, x_e, all binary. Maximize sum d+e+x.
    c=-np.ones(3*m)
    rows=[]; lbs=[]; ubs=[]
    # x <= d, x <= e, x >= d+e-1
    for k in range(m):
        row={2*m+k:1,k:-1}; rows.append(row); lbs.append(-np.inf); ubs.append(0)
        row={2*m+k:1,m+k:-1}; rows.append(row); lbs.append(-np.inf); ubs.append(0)
        row={2*m+k:1,k:-1,m+k:-1}; rows.append(row); lbs.append(-1); ubs.append(np.inf)
    idx={e:k for k,e in enumerate(edges)}
    for vs in combinations(range(n),4):
        row={idx[e]:1 for e in combinations(vs,2)}
        rows.append(row); lbs.append(-np.inf); ubs.append(5)
    for vs in combinations(range(n),5):
        row={m+idx[e]:1 for e in combinations(vs,2)}
        rows.append(row); lbs.append(-np.inf); ubs.append(9)
    A=lil_matrix((len(rows),3*m),dtype=float)
    for i,row in enumerate(rows):
        for j,v in row.items(): A[i,j]=v
    con=LinearConstraint(A.tocsr(),np.array(lbs),np.array(ubs))
    res=milp(c,integrality=np.ones(3*m),bounds=Bounds(np.zeros(3*m),np.ones(3*m)),
             constraints=con,options={"time_limit":60})
    if not res.success:
        raise RuntimeError((n,res.message))
    val=int(round(-res.fun))
    target,_=S(n)
    if val!=target:
        raise AssertionError((n,val,target))
    return {"n":n,"edges":m,"milp_optimum":val,"S(n)":target,"status":res.message}


def main():
    outdir=Path(__file__).resolve().parents[1]/"verification"; outdir.mkdir(exist_ok=True)
    matrix=exhaustive_matrix(10)
    colored=[{"n":1,"edges":0,"milp_optimum":0,"S(n)":0,"status":"trivial"}] + [colored_milp(n) for n in range(2,10)]
    values=[{"n":n,"optimal_sorted_quadruple":S(n)[1],"S":S(n)[0],"regions":region(n)} for n in range(0,41)]
    data={"matrix_exhaustive":matrix,"colored_turan_milp":colored,"formula_values":values,"result":"PASSED"}
    (outdir/"combinatorial_verification.json").write_text(json.dumps(data,indent=2))
    total=sum(x["matrices"] for x in matrix)
    lines=["Independent combinatorial verification","======================================",f"Exhaustively checked every 3x4 nonnegative integer matrix of total mass n <= 10 ({total:,} matrices).",f"Solved the colored Turan 0-1 MILP independently for n=1,...,9; every optimum equals S(n).","Computed formula and optimizing quadruples for n=0,...,40.","RESULT: PASSED"]
    (outdir/"combinatorial_verification.txt").write_text("\n".join(lines)+"\n")
    print("\n".join(lines))

if __name__=="__main__": main()
