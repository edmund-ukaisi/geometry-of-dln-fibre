#!/usr/bin/env python3
"""
TRUE codimension of the descent's sub-generic strata, via the paper's orbit machinery.

The descent peels boundary 0 and stratifies by the rank of the tail product on the non-pivot rows.
The CLEAN orbit descriptor for "tail product rank" is r_{1,N} (rank of the sub-product node 1 -> node N).
We compute, for the zero-product locus Sigma^0 (r_{0N}=0), the MIN codim over orbits with a FIXED
tail rank r_{1N} = rho, for each rho from generic down to 0.

Closure mechanism to test:  is  min-codim(Sigma^0 & r_{1N}=rho)  NON-INCREASING as rho grows, i.e.
does forcing the tail rank DOWN (rho small = more deficient) never DECREASE the codim below minAdm?
Equivalently: the generic tail rank sets the minimum codim (= minAdm); deficient-tail strata are
higher codim (less binding).

We also directly compare to the additive C2 accounting on the binding cases.
"""
import io, contextlib
_buf = io.StringIO()
with contextlib.redirect_stdout(_buf):
    import rankcharge as R
import orbit_codim as OC

def sigma0_by_tailrank(d):
    """for Sigma^0 (r_{0N}=0), min codim over orbits with r_{1N}=rho, per rho."""
    N = len(d)-1
    orbs = OC.sigma0(d)          # (m, codim) with m[(0,N)]=0
    by = {}
    for m, c in orbs:
        rho = OC.rank_ij(m, 1, N, N)      # rank node1 -> nodeN = tail product rank
        by.setdefault(rho, []).append(c)
    return {rho: min(cs) for rho, cs in by.items()}

def sigma0_by_pair(d, ii, jj):
    """min codim over Sigma^0 orbits, keyed by r_{ii,jj}."""
    N = len(d)-1
    orbs = OC.sigma0(d)
    by = {}
    for m, c in orbs:
        key = OC.rank_ij(m, ii, jj, N, N)
        by.setdefault(key, []).append(c)
    return {k: min(cs) for k, cs in by.items()}

if __name__ == "__main__":
    print("=== TRUE min codim of Sigma^0 stratified by TAIL product rank r_{1N} ===")
    print("    (closure: deficient tail rank => codim >= minAdm, generic rank binds at minAdm)")
    for d in [(4,4,2),(3,3,4),(3,3,3,4),(4,4,2,2),(2,4,1),(4,4,4,2),(3,3,3),(2,2,2,2),(5,4,3,2)]:
        d=tuple(d); N=len(d)-1
        mAdm=R.minAdmRec(d)
        by=sigma0_by_tailrank(list(d))
        gen_tail = min(d[1:])   # generic rank of tail product node1->nodeN = min(d1,...,dN)
        items=sorted(by.items())
        s=", ".join(f"rho={rho}:cod={c}{'(BIND)' if c==mAdm else ''}{'*' if rho==gen_tail else ''}" for rho,c in items)
        below=[ (rho,c) for rho,c in items if c<mAdm ]
        print(f"  d={d} minAdm={mAdm} gen_tail_rank={gen_tail}:  {s}"
              + (f"   <<< BELOW minAdm at {below}" if below else ""))
    print("  legend: *=generic tail rank, (BIND)=codim equals minAdm")
