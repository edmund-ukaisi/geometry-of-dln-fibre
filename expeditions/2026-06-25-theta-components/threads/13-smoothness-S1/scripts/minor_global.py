"""
For (d,r): build fibre ideal + Jacobian, primary-decompose, and for each TOP
component p enumerate WHICH size-Q minors (choice of Q rows + Q cols of J) are
nonzero mod p. Then intersect across components to decide:
   GLOBAL  : exists a fixed (rows, cols) minor nonzero on every top component;
   PER-COMP: no such fixed minor (the witnessing minor depends on the component).

We do the enumeration in Singular but it is expensive; instead we do it in
sympy + exact-rational sampling validated against the Singular generic rank, OR
directly in Singular with explicit submatrix minors. Here: emit Singular that
loops over all (Q-row, Q-col) submatrices, reduces the minor mod each top p, and
records a 0/1 incidence; then prints the AND across top components.
"""
import sys, itertools
import sympy as sp
from fibjac import build_symbolic, mult_product, E_r

def gen(d, r):
    N=len(d)-1
    factors_sym, syms = build_symbolic(d)
    dimRep=len(syms)
    varlist=",".join(str(s) for s in syms)
    P=mult_product(factors_sym); E=E_r(d[-1],d[0],r); Fm=P-E
    Fentries=[sp.expand(Fm[a,b]) for a in range(d[-1]) for b in range(d[0])]
    nrows=len(Fentries); ncols=dimRep
    Jrows=[[sp.expand(sp.diff(f,s)) for s in syms] for f in Fentries]
    L=[]
    L.append('LIB "primdec.lib";')
    L.append(f'ring R=0,({varlist}),dp;')
    L.append(f'ideal I = {", ".join(str(f) for f in Fentries)};')
    L.append('attrib(I,"isSB",0);')
    L.append('list pd = primdecGTZ(I);')
    L.append('int dimRep='+str(dimRep)+';')
    L.append('int ncomp=size(pd); int i;')
    L.append('intvec dims; int maxd=-1;')
    L.append('for(i=1;i<=ncomp;i++){int di=dim(std(pd[i][1]));dims[i]=di;if(di>maxd){maxd=di;}}')
    L.append('int Q=dimRep-maxd;')
    L.append('"FIB codim/Q =", Q, "  ncomp=",ncomp," dims=",dims," topdim=",maxd;')
    # Jacobian
    L.append(f'matrix J[{nrows}][{ncols}];')
    for i in range(nrows):
        for j in range(ncols):
            if Jrows[i][j]!=0:
                L.append(f'J[{i+1},{j+1}]={Jrows[i][j]};')
    # collect top primes into a list
    L.append('list tops;')
    L.append('int t=0;')
    L.append('for(i=1;i<=ncomp;i++){ if(dims[i]==maxd){ t++; tops[t]=std(pd[i][1]); } }')
    L.append('"num TOP components:", t;')
    # We will, for each top prime, compute the set of column-subsets (if Q==nrows)
    # OR (row,col) subsets giving nonzero minor. To keep it tractable we report,
    # per top component, the FIRST few surviving (rows;cols) and also test a fixed
    # candidate. Strategy: pick rows = first Q rows that work on comp 1, then check
    # the SAME (rows,cols) on all comps. We implement a generic search:
    L.append('int rowsel, colsel;')
    L.append('// enumerate all Q-subsets of rows and cols via Singular intvec combos in proc')
    L.append(r'''
proc combos(int n, int q){
  // returns list of intvecs: all q-subsets of 1..n (lexicographic)
  list out; intvec cur; int j;
  for(j=1;j<=q;j++){cur[j]=j;}
  while(1){
    out[size(out)+1]=cur;
    int k=q;
    int go=1;
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
    # for global: maintain count of (rc,cc) that survive on ALL tops
    L.append('int rc, cc, ti; int globalcount=0; int firstglobal_r=0; int firstglobal_c=0;')
    L.append('intvec percompcount;')  # how many survive per comp individually
    L.append('for(ti=1;ti<=t;ti++){percompcount[ti]=0;}')
    L.append('for(rc=1;rc<=size(rowcombos);rc++){')
    L.append('  intvec rr=rowcombos[rc];')
    L.append('  for(cc=1;cc<=size(colcombos);cc++){')
    L.append('    intvec ccv=colcombos[cc];')
    L.append('    matrix sub = submat(J, rr, ccv);')
    L.append('    poly mdet = det(sub);')
    L.append('    int survAll=1;')
    L.append('    for(ti=1;ti<=t;ti++){')
    L.append('      poly nf = reduce(mdet, tops[ti]);')
    L.append('      if(nf==0){ survAll=0; }')
    L.append('      else { percompcount[ti]=percompcount[ti]+1; }')
    L.append('    }')
    L.append('    if(survAll==1){ globalcount++; if(firstglobal_r==0){firstglobal_r=rc; firstglobal_c=cc;} }')
    L.append('  }')
    L.append('}')
    L.append('"=> #minors nonzero on EVERY top component (GLOBAL witnesses):", globalcount;')
    L.append('if(globalcount>0){ "   first global: rows=",rowcombos[firstglobal_r]," cols=",colcombos[firstglobal_c]; }')
    L.append('"=> per-component #surviving minors:", percompcount;')
    L.append('quit;')
    return "\n".join(L)

if __name__=="__main__":
    cases={"222r1":([2,2,2],1),"2222r1":([2,2,2,2],1),"333r2":([3,3,3],2),"22222r0":([2,2,2,2,2],0)}
    which=sys.argv[1]
    d,r=cases[which]
    print(gen(d,r))
