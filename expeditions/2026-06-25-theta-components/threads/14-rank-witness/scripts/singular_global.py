"""
GLOBAL vs PER-COMPONENT minor verdict via Singular, for ARBITRARY (d, r).

Enumerate all (Q-row, Q-col) submatrices of the fibre Jacobian J; for each, reduce
its determinant mod every top prime. Count:
  globalcount   = # minors nonzero on EVERY top component simultaneously (a single
                  fixed coordinate Q-minor that is a global submersive witness);
  percompcount  = # surviving minors per top component (individually).

VERDICT:
  globalcount > 0  => a SINGLE GLOBAL minor exists (expected when theta=1);
  globalcount == 0 => witnessing minor is PER-COMPONENT (expected when theta>=2).

Generalized form of thread-13's minor_global.py; same combinatorial loop, our
own case table. WARNING: row/col combos blow up; only run on small Q / small J.

Usage:  python3 singular_global.py 323r1 | Singular -q
"""
import sys
import sympy as sp

sys.path.insert(0, "/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/expeditions/2026-06-25-theta-components/threads/13-smoothness-S1/scripts")
from fibjac import build_symbolic, mult_product, E_r  # noqa: E402
sys.path.insert(0, "/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/expeditions/2026-06-25-theta-components/threads/14-rank-witness/scripts")
from singular_rank import CASES  # noqa: E402
from qip import fibre_data  # noqa: E402


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
    Qpred = fibre_data(d, r)["Q"]

    L = []
    L.append('LIB "primdec.lib";')
    L.append(f'ring R=0,({varlist}),dp;')
    L.append(f'ideal I = {", ".join(str(f) for f in Fentries)};')
    L.append('attrib(I,"isSB",0);')
    L.append('list pd=primdecGTZ(I);')
    L.append(f'int dimRep={dimRep};')
    L.append('int ncomp=size(pd); int i; intvec dims; int maxd=-1;')
    L.append('for(i=1;i<=ncomp;i++){int di=dim(std(pd[i][1]));dims[i]=di;if(di>maxd){maxd=di;}}')
    L.append(f'int Q={Qpred};')
    L.append(f'"CASE d={d} r={r}: Q=",Q,"  ncomp=",ncomp,"  dims=",dims,"  topdim=",maxd;')
    L.append(f'matrix J[{nrows}][{ncols}];')
    for i in range(nrows):
        for j in range(ncols):
            if Jrows[i][j] != 0:
                L.append(f'J[{i+1},{j+1}]={Jrows[i][j]};')
    L.append('list tops; int t=0;')
    L.append('for(i=1;i<=ncomp;i++){ if(dims[i]==maxd){ t++; tops[t]=std(pd[i][1]); } }')
    L.append('"num TOP components:", t;')
    L.append(r'''
proc combos(int n, int q){
  list out; intvec cur; int j;
  for(j=1;j<=q;j++){cur[j]=j;}
  while(1){
    out[size(out)+1]=cur;
    int k=q; int go=1;
    while(go==1){
      if(k<1){go=0;}
      else{ if(cur[k]==n-q+k){k--;}else{go=0;} }
    }
    if(k<1){break;}
    cur[k]=cur[k]+1;
    for(j=k+1;j<=q;j++){cur[j]=cur[j-1]+1;}
  }
  return(out);
}
''')
    L.append(f'list rowcombos = combos({nrows}, Q);')
    L.append(f'list colcombos = combos({ncols}, Q);')
    L.append('"num row-combos:", size(rowcombos), " num col-combos:", size(colcombos);')
    L.append('int rc, cc, ti; int globalcount=0; int firstglobal_r=0; int firstglobal_c=0;')
    L.append('intvec percompcount; for(ti=1;ti<=t;ti++){percompcount[ti]=0;}')
    L.append('for(rc=1;rc<=size(rowcombos);rc++){')
    L.append('  intvec rr=rowcombos[rc];')
    L.append('  for(cc=1;cc<=size(colcombos);cc++){')
    L.append('    intvec ccv=colcombos[cc];')
    L.append('    matrix sub=submat(J,rr,ccv);')
    L.append('    poly mdet=det(sub);')
    L.append('    int survAll=1;')
    L.append('    for(ti=1;ti<=t;ti++){')
    L.append('      poly nf=reduce(mdet,tops[ti]);')
    L.append('      if(nf==0){survAll=0;}else{percompcount[ti]=percompcount[ti]+1;}')
    L.append('    }')
    L.append('    if(survAll==1){globalcount++; if(firstglobal_r==0){firstglobal_r=rc;firstglobal_c=cc;}}')
    L.append('  }')
    L.append('}')
    L.append('"=> #minors nonzero on EVERY top component (GLOBAL witnesses):", globalcount;')
    L.append('if(globalcount>0){ "   first global: rows=",rowcombos[firstglobal_r]," cols=",colcombos[firstglobal_c]; }')
    L.append('"=> per-component #surviving minors:", percompcount;')
    L.append('quit;')
    return "\n".join(L)


if __name__ == "__main__":
    which = sys.argv[1]
    d, r = CASES[which]
    print(gen(d, r))
