"""
Generate a Singular script that, for a given (d, r):
  - builds the fibre ideal I = (mult - E_r),
  - builds the fibre Jacobian J (symbolic, d_N*d_0 rows x dimRep cols),
  - primary-decomposes I, finds the TOP components (max dim),
  - for each top component p: computes the rank of J modulo p (generic rank on
    the component) via the determinantal-ideal-of-minors test, and
  - tests a CANDIDATE fixed Q x Q minor for membership in p (NF != 0 means the
    minor is nonzero on the component => the minor is a unit-ish witness there).

We emit Singular source; the heavy lifting (minor ideals, primdec) is exact over Q.
"""
import sympy as sp
from fibjac import build_symbolic, mult_product, E_r

def varname(i, a, b):
    return f"a{i+1}_{a}_{b}"

def gen_singular(d, r, candidate_rows=None, candidate_cols=None):
    N = len(d)-1
    factors_sym, syms = build_symbolic(d)
    dimRep = len(syms)
    # variable list in Singular order = syms order
    varlist = ",".join(str(s) for s in syms)
    P = mult_product(factors_sym)
    E = E_r(d[-1], d[0], r)
    F = P - E
    Fentries = [sp.expand(F[a,b]) for a in range(d[-1]) for b in range(d[0])]
    # Jacobian entries
    Jrows = []
    for f in Fentries:
        Jrows.append([sp.expand(sp.diff(f, s)) for s in syms])
    nrows = len(Fentries); ncols = dimRep

    lines = []
    lines.append('LIB "primdec.lib";')
    lines.append('LIB "matrix.lib";')
    lines.append(f'ring R = 0, ({varlist}), dp;')
    # fibre ideal
    geni = ", ".join(str(f) for f in Fentries)
    lines.append(f'ideal I = {geni};')
    lines.append('I = std(I);')
    lines.append(f'int dimRep = {dimRep};')
    lines.append('int fibdim = dim(I);')
    lines.append('int fibcodim = dimRep - fibdim;')
    lines.append('"FIBRE dim =", fibdim, " codim =", fibcodim;')
    # Jacobian matrix
    lines.append(f'matrix J[{nrows}][{ncols}];')
    for i in range(nrows):
        for j in range(ncols):
            e = Jrows[i][j]
            if e != 0:
                lines.append(f'J[{i+1},{j+1}] = {e};')
    # primary decomposition
    lines.append('list pd = primdecGTZ(I);')
    lines.append('int ncomp = size(pd);')
    lines.append('"num components:", ncomp;')
    lines.append('int i; intvec dims;')
    lines.append('int maxd = -1;')
    lines.append('for(i=1;i<=ncomp;i++){ int di = dim(std(pd[i][1])); dims[i]=di; if(di>maxd){maxd=di;} }')
    lines.append('"component dims:", dims;')
    lines.append('"TOP dim =", maxd, " => top codim =", dimRep-maxd;')
    lines.append('int Q = dimRep - maxd;')
    # for each component compute generic rank of J mod p:
    # rank mod p = largest t with minor-ideal of size t not subset of p.
    # We test: is ideal of Q-minors NOT contained in p? (rank>=Q on comp) and
    # is ideal of (Q+1)-minors contained in p? (rank<=Q). Use: rank=Q iff
    #   minor_(Q) ideil reduces to nonzero mod p AND minor_(Q+1) reduces to 0.
    lines.append('for(i=1;i<=ncomp;i++){')
    lines.append('  if(dims[i]==maxd){')
    lines.append('    ideal p = std(pd[i][1]);')
    lines.append('    // rank of J modulo p:')
    lines.append('    matrix Jp = J;')
    lines.append('    // reduce each entry mod p')
    lines.append('    int a,b;')
    lines.append(f'    for(a=1;a<={nrows};a++){{ for(b=1;b<={ncols};b++){{ Jp[a,b]=reduce(J[a,b],p); }} }}')
    lines.append('    "=== TOP component", i, " (dim",dims[i],") ===";')
    # minor ideal of size Q reduced mod p: if it is the zero ideal, rank<Q.
    lines.append('    ideal mQ = minor(Jp, Q);')
    lines.append('    mQ = reduce(mQ, p);')
    lines.append('    ideal mQ1 = minor(Jp, Q+1);')
    lines.append('    mQ1 = reduce(mQ1, p);')
    lines.append('    "   #nonzero Q-minors mod p (rank>=Q if >0):", size(mQ);')
    lines.append('    "   #nonzero (Q+1)-minors mod p (rank>Q if >0):", size(mQ1);')
    lines.append('  }')
    lines.append('}')
    lines.append('quit;')
    return "\n".join(lines)

if __name__ == "__main__":
    import sys
    cases = {
        "222r1": ([2,2,2],1),
        "2222r1": ([2,2,2,2],1),
        "333r2": ([3,3,3],2),
        "22222r0": ([2,2,2,2,2],0),
    }
    which = sys.argv[1] if len(sys.argv)>1 else "222r1"
    d,r = cases[which]
    print(gen_singular(d,r))
