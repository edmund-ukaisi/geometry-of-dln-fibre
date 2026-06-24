#!/usr/bin/env python3
"""
The CORRECT experiment for the HARD-direction crux.

The irreducible components of F = mult^{-1}(E) are NOT orbit closures of single
normal-form representatives. They are the closures of the FACTOR-RANK STRATA: for a
"rank profile" rho = (rho_0,...,rho_{N-1}) (rho_i = rank A_i) with rho_i in [r, min(d_{i+1},d_i)]
and the composite product rank = r, the stratum
    S_rho = { A in F : rank A_i = rho_i for all i }
is irreducible (it fibres over a product of rank-strata with the E-pinning), and the
top-dimensional ones are the components of F. A GENERIC point of the (closure of the)
component is a generic A in S_rho with mult(A)=E.

So: to read rank(d mult_A) at a generic point of each fibre component, build a generic
A in S_rho with mult(A)=E. We do this by a SECTION construction:
  pick the END factors to absorb E and the inner factors generic of the prescribed rank,
then verify mult(A)=E and read the EXACT Jacobian rank.

We compare to:
  - C = cCodim(d,r) (taken as the MINIMUM, over strata, of card - rank(d mult)),
    i.e. we *measure* C+delta = the top value;
  - the hoped UNIFORM bound: is rank(d mult_A) >= C + delta at a generic point of EVERY
    component (every rank profile that yields product rank r)?
  - and the dim of each component dim S_rho = card - rank(d mult_A) (generic smoothness).

We construct a generic A in S_rho with mult=E as follows. Build each factor of rank rho_i
as  A_i = L_i R_i  with L_i (d_{i+1} x rho_i) and R_i (rho_i x d_i) generic full-rank,
then the product is L_{N-1} (R_{N-1}L_{N-2}) ... (R_1 L_0) R_0. To force the product = E we
do NOT try to solve exactly; instead we use a GENERIC point of the stratum that lands in
the fibre over SOME rank-r matrix B, and use the base-change invariance (codim and the
generic Jacobian rank are GL_{d_N} x GL_{d_0} invariant) to relate the fibre over B to the
fibre over E. Concretely: rank(d mult_A) is invariant under A -> (P,Q).A (left/right
endpoint gauge), which sends mult(A)=B to mult=P B Q^{-1}. So the EXACT Jacobian rank at a
generic stratum point of the fibre over E equals that at a generic stratum point of the
fibre over ANY rank-r B. Hence we may build a generic A with rank A_i = rho_i and
rank(mult A) = r WITHOUT pinning B=E, and read rank(d mult_A) there.
"""
import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros
from itertools import product as iproduct
import random

random.seed(424242)

def chain(factors):
    M = factors[-1]
    for k in range(len(factors)-2,-1,-1):
        M = M*factors[k]
    return M

def suffix(factors,i):
    N=len(factors)
    if i==N-1: return eye(factors[N-1].rows)
    M=factors[N-1]
    for k in range(N-2,i,-1): M=M*factors[k]
    return M

def prefix(factors,i):
    if i==0: return eye(factors[0].cols)
    M=factors[i-1]
    for k in range(i-2,-1,-1): M=M*factors[k]
    return M

def jac(factors,d):
    N=len(factors); dN=d[N]; d0=d[0]
    out=[(r,c) for r in range(dN) for c in range(d0)]
    cols=[(i,s,t) for i in range(N) for s in range(d[i+1]) for t in range(d[i])]
    J=zeros(len(out),len(cols))
    S=[suffix(factors,i) for i in range(N)]
    P=[prefix(factors,i) for i in range(N)]
    for ri,(r,c) in enumerate(out):
        for ci,(i,s,t) in enumerate(cols):
            J[ri,ci]=S[i][r,s]*P[i][t,c]
    return J

def card(d):
    N=len(d)-1
    return sum(d[i+1]*d[i] for i in range(N))

def delta(d,r):
    N=len(d)-1
    return r*(d[N]+d[0]-r)

def rand_fullrank(rows,cols,rk,lo=-4,hi=4):
    """rows x cols matrix of rank exactly rk = L*R, L: rows x rk, R: rk x cols, both full col/row rank."""
    while True:
        L=randMatrix(rows,rk,min=lo,max=hi)
        if L.rank()==rk: break
    while True:
        R=randMatrix(rk,cols,min=lo,max=hi)
        if R.rank()==rk: break
    return L*R

def generic_stratum_point(d, profile, tries=40):
    """Generic A with rank A_i = profile[i] and product rank = r (=composite rank).
       Returns (factors, composite_rank)."""
    for _ in range(tries):
        facs=[rand_fullrank(d[i+1],d[i],profile[i]) for i in range(len(profile))]
        prod=chain(facs)
        yield facs, prod.rank()

def enumerate_profiles(d,r):
    N=len(d)-1
    ranges=[range(r,min(d[i+1],d[i])+1) for i in range(N)]
    res=[]
    for prof in iproduct(*ranges):
        # check that SOME generic choice gives composite rank exactly r (and not lower-generic)
        res.append(list(prof))
    return res

# ---------------------------------------------------------------------------
cases = [
    ([2,2,2],0),([2,2,2],1),([2,2,2],2),
    ([2,2,3],1),([3,2,3],1),
    ([3,3,3],1),([3,3,3],2),
    ([1,2,1],0),([1,2,1],1),
    ([2,2,2,2],1),([2,3,2],1),
    ([4,4,4],2),([3,4,3],1),   # new larger cases
]

print("="*92)
print("rank(d mult_A) at a GENERIC point of each fibre-component STRATUM S_rho")
print("  (generic full-rank factors of the profile; composite rank read off)")
print("  C+delta = top value (min codim); test UNIFORM bound rank >= C+delta on every stratum")
print("="*92)

summary=[]
for d,r in cases:
    N=len(d)-1; cd=card(d); dl=delta(d,r)
    profs=enumerate_profiles(d,r)
    rows=[]
    for prof in profs:
        # take a generic stratum point; require composite rank == r (else this profile's
        # generic product rank is != r => different fibre, skip)
        best=None
        for facs,crank in generic_stratum_point(d,prof,tries=12):
            if crank==r:
                J=jac(facs,d); rk=J.rank()
                best=(rk,crank); break
            else:
                best=(None,crank)
        if best is None: continue
        rk,crank=best
        if rk is None:
            rows.append((prof,None,crank))
        else:
            rows.append((prof,rk,crank))
    # measured C+delta = MIN over strata with composite rank r of rank(d mult)
    valid=[rk for (prof,rk,cr) in rows if rk is not None]
    if not valid:
        print(f"\nd={d} r={r}: NO stratum gives composite rank {r}? (skipped)")
        continue
    Cplusdelta = min(valid)
    C_meas = Cplusdelta - dl
    print(f"\nd={d}, r={r}: card={cd}, delta={dl}; measured C+delta={Cplusdelta} => C={C_meas}")
    uniform_ok=True
    for (prof,rk,cr) in rows:
        if rk is None:
            print(f"   profile={prof}: composite rank={cr} (!= r, different fibre) — skip")
            continue
        dimcomp = cd - rk
        ge = (rk >= Cplusdelta)
        uniform_ok = uniform_ok and ge
        tag = "OK>=C+d" if ge else "**< C+delta**"
        print(f"   profile={prof}: rank(dmult)={rk:2d}  dim S_rho={dimcomp:2d}  "
              f"{'[TOP]' if rk==Cplusdelta else '     '} {tag}")
    summary.append((d,r,Cplusdelta,uniform_ok))
    print(f"   uniform rank>=C+delta over strata: {uniform_ok}")

print("\n"+"="*92)
print("SUMMARY: uniform bound rank(d mult) >= C+delta at generic stratum points")
for d,r,cpd,ok in summary:
    print(f"   d={d} r={r}: C+delta={cpd}  uniform={ok}")
print("="*92)
