"""
Certificate-grade fibre-Jacobian rank check via Singular, for ARBITRARY (d, r).

For the fibre ideal I = (mult - E_r):
  - primary-decompose I over Q (primdecGTZ),
  - find TOP components (max dim), report #top = theta and their dims,
  - for EACH top prime p: reduce J mod p and report
        #nonzero Q-minors mod p   (rank >= Q on the component iff > 0)
        #nonzero (Q+1)-minors mod p (rank > Q iff > 0)
    so rank J = Q on the component  <=>  (#Q>0 and #(Q+1)==0).

This is the exact analogue of thread-13's minor_singular.py, generalized to any
(d,r) and emitting Q from our own QIP engine (cross-checked against Singular's
own codim computation).

Usage:  python3 singular_rank.py 333r1     (prints Singular source to stdout)
        python3 singular_rank.py 333r1 | Singular -q
"""
import sys
import sympy as sp

# reuse thread-13's symbolic Jacobian builder
sys.path.insert(0, "/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/expeditions/2026-06-25-theta-components/threads/13-smoothness-S1/scripts")
from fibjac import build_symbolic, mult_product, E_r  # noqa: E402
sys.path.insert(0, "/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/expeditions/2026-06-25-theta-components/threads/14-rank-witness/scripts")
from qip import fibre_data  # noqa: E402


CASES = {
    "222r1": ([2, 2, 2], 1),
    "2222r1": ([2, 2, 2, 2], 1),
    "333r2": ([3, 3, 3], 2),
    "22222r0": ([2, 2, 2, 2, 2], 0),
    # discriminating
    "333r1": ([3, 3, 3], 1),      # theta=1 boundary
    "323r1": ([3, 2, 3], 1),      # valley, theta=2, delta>0
    # adversarial
    "324r1": ([3, 2, 4], 1),      # asymmetric endpoints, theta=1
    "423r1": ([4, 2, 3], 1),      # asymmetric mirror, theta=1
    "323r0": ([3, 2, 3], 0),      # valley zero-product
    "4444r2": ([4, 4, 4, 4], 2),  # wider, theta=3
    "232r1": ([2, 3, 2], 1),      # bump (internal larger), theta=1
    # adversarial sweep 2
    "223r0": ([2, 2, 3], 0),      # asymmetric endpoints, theta=2, delta=0 zero-product
    "322r0": ([3, 2, 2], 0),      # mirror
    "1222r0": ([1, 2, 2, 2], 0),  # 4-node, m=3, theta=3, asymmetric
    "222222r0": ([2, 2, 2, 2, 2, 2], 0),  # m=5, |qd|=2, theta=10 (widest)
    "1223r0": ([1, 2, 2, 3], 0),  # 4-node asymmetric theta=2
}


def gen(d, r):
    N = len(d) - 1
    factors_sym, syms = build_symbolic(d)
    dimRep = len(syms)
    varlist = ",".join(str(s) for s in syms)
    P = mult_product(factors_sym)
    E = E_r(d[-1], d[0], r)
    Fm = P - E
    Fentries = [sp.expand(Fm[a, b]) for a in range(d[-1]) for b in range(d[0])]
    nrows = len(Fentries)
    ncols = dimRep
    Jrows = [[sp.expand(sp.diff(f, s)) for s in syms] for f in Fentries]

    fd = fibre_data(d, r)
    Qpred = fd["Q"]
    thetapred = fd["theta"]

    L = []
    L.append('LIB "primdec.lib";')
    L.append(f'ring R=0,({varlist}),dp;')
    L.append(f'ideal I = {", ".join(str(f) for f in Fentries)};')
    L.append('I=std(I);')
    L.append(f'int dimRep={dimRep};')
    L.append('int fibdim=dim(I); int fibcodim=dimRep-fibdim;')
    L.append(f'"CASE d={d} r={r}: dimRep=",dimRep," cuteqs={nrows}";')
    L.append(f'"  PREDICTED (QIP engine):  Q(=C+delta)=",{Qpred},"  theta=",{thetapred}," (delta=",{fd["delta"]},", C_sh=",{fd["Csh"]},")";')
    L.append('"  SINGULAR fib codim =", fibcodim;')
    L.append(f'int Q={Qpred};')
    # Jacobian
    L.append(f'matrix J[{nrows}][{ncols}];')
    for i in range(nrows):
        for j in range(ncols):
            if Jrows[i][j] != 0:
                L.append(f'J[{i+1},{j+1}]={Jrows[i][j]};')
    L.append('list pd=primdecGTZ(I);')
    L.append('int ncomp=size(pd); int i; intvec dims; int maxd=-1;')
    L.append('for(i=1;i<=ncomp;i++){int di=dim(std(pd[i][1]));dims[i]=di;if(di>maxd){maxd=di;}}')
    L.append('"  #components=",ncomp,"  component dims=",dims,"  topdim=",maxd,"  topcodim=",dimRep-maxd;')
    L.append('int t=0; for(i=1;i<=ncomp;i++){ if(dims[i]==maxd){ t++; } }')
    L.append('"  #TOP components (=theta?):", t;')
    # per top component rank check
    L.append('int a,b; int ci=0;')
    L.append('for(i=1;i<=ncomp;i++){')
    L.append('  if(dims[i]==maxd){')
    L.append('    ci++;')
    L.append('    ideal p=std(pd[i][1]);')
    L.append('    matrix Jp=J;')
    L.append(f'    for(a=1;a<={nrows};a++){{ for(b=1;b<={ncols};b++){{ Jp[a,b]=reduce(J[a,b],p); }} }}')
    L.append('    ideal mQ=minor(Jp,Q); mQ=reduce(mQ,p);')
    L.append('    ideal mQ1=minor(Jp,Q+1); mQ1=reduce(mQ1,p);')
    L.append('    "    top comp #",ci,"(dim",dims[i],"): #Q-minors!=0 mod p=",size(mQ),"  #(Q+1)-minors!=0 mod p=",size(mQ1),"  => rank=Q?",(size(mQ)>0 && size(mQ1)==0);')
    L.append('  }')
    L.append('}')
    L.append('quit;')
    return "\n".join(L)


if __name__ == "__main__":
    which = sys.argv[1]
    d, r = CASES[which]
    print(gen(d, r))
