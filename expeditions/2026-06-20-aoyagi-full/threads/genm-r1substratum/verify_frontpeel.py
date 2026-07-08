#!/usr/bin/env python3
"""
DECORRELATED cross-check of Codex's closure result for the sub-generic strata.

Claims to verify EXACTLY (integer arithmetic), against the faithful minAdm:

(I)   FRONT-PEEL IDENTITY:
        minAdm(M_0,...,M_L) == min_{q=0..min(M_1,...,M_L)} [ M_0*q + minAdm((M_1,...,M_L) - q) ]
      where (W)-q subtracts q from every width.  (New alternative peel: peel A_0 against the whole
      tail product P=A_1..A_{L-1}, stratified by rank(P)=q.)

(II)  CHARGE = TRUE ORBIT-STRATUM CODIM (cross-check vs the paper's Voight/Ext formula):
        charge(q) := M_0*q + minAdm((M_1,...,M_L)-q)  ==  min codim over Sigma^0 orbits with r_{1N}=q.

(III) CHARGE >= minAdm for every q, with equality at the minimizing q (closure + tightness).

(IV)  ENTANGLEMENT: Codex's per-piece intermediate collapses:
        min_{r=q..n} [ t*r + (b-q)(r-q) + minAdm((M_2,...,M_L)-r) ]  ==  t*q + minAdm((M_1,...,M_L)-q)
      for all cuts t (b=M_1-t, n=min(M_2..M_L)); hence charge is t-INDEPENDENT.

(V)   C2 OVER-COUNTS: the additive C2 = a*s' + minAdm((b,M_2..M_L)-s') + minAdm(t,M_2..M_L)
        satisfies C2 >= charge(s') (>= minAdm), i.e. additive is an over-estimate, never tight below.
"""
import io, contextlib
_buf = io.StringIO()
with contextlib.redirect_stdout(_buf):
    import rankcharge as R
import orbit_codim as OC
import stratum_codim as SC
from itertools import product as iproduct

minAdm = R.minAdmRec
redChain = R.redChain

def sub(W, q): return tuple(max(0, w-q) for w in W)

def charge_front(M, q):
    """M_0*q + minAdm((M_1,...,M_L) - q)."""
    return M[0]*q + minAdm(sub(M[1:], q))

def frontpeel(M):
    lo = min(M[1:])
    return min(charge_front(M, q) for q in range(lo+1))

def C_tail_pieces(M, t, q):
    """Codex intermediate: min_{r=q..n}[ t*r + (b-q)(r-q) + minAdm((M_2..M_L)-r) ]."""
    b = M[1]-t; n = min(M[2:])
    return min(t*r + (b-q)*(r-q) + minAdm(sub(M[2:], r)) for r in range(q, n+1))

def C_tail_closed(M, t, q):
    """claimed closed form: t*q + minAdm((M_1..M_L)-q)."""
    return t*q + minAdm(sub(M[1:], q))

# ---- (I) + (III) front-peel identity and charge>=minAdm ----
def sweep_frontpeel(Lp1, wmax):
    fails_id=0; fails_ge=0; nontight=0; ch=0; ex=[]
    for M in iproduct(range(0,wmax+1),repeat=Lp1):
        ch+=1; m=minAdm(M)
        fp=frontpeel(M)
        if fp!=m:
            fails_id+=1
            if len(ex)<6: ex.append(('ID',M,fp,m))
        lo=min(M[1:]); mn=None
        for q in range(lo+1):
            c=charge_front(M,q)
            if c<m: fails_ge+=1
            if mn is None or c<mn: mn=c
        if mn!=m: nontight+=1
    return ch,fails_id,fails_ge,nontight,ex

# ---- (IV) entanglement collapse ----
def sweep_ctail(Lp1, wmax):
    fails=0; ch=0; ex=[]
    for M in iproduct(range(0,wmax+1),repeat=Lp1):
        if Lp1<3: continue
        for t in range(min(M[0],M[1])+1):
            n=min(M[2:]); b=M[1]-t
            for q in range(0, min(b,n)+1):
                cp=C_tail_pieces(M,t,q); cc=C_tail_closed(M,t,q)
                ch+=1
                if cp!=cc:
                    fails+=1
                    if len(ex)<8: ex.append((M,t,q,cp,cc))
    return ch,fails,ex

# ---- (V) C2 over-count ----
def kappa(M,t,sp):
    b=M[1]-t
    return minAdm(sub((b,)+tuple(M[2:]), sp))
def sweep_c2_overcount(Lp1, wmax):
    ch=0; c2_lt_charge=0; charge_lt_min=0; ex=[]
    for M in iproduct(range(0,wmax+1),repeat=Lp1):
        if Lp1<3: continue
        m=minAdm(M); n=min(M[2:])
        for t in range(min(M[0],M[1])+1):
            b=M[1]-t; s=min(b,n)
            for sp in range(0,s+1):
                a=M[0]-t
                C2 = a*sp + kappa(M,t,sp) + minAdm(redChain(t,M))
                chg = charge_front(M, sp)      # true charge (t-independent), evaluated at q=sp
                ch+=1
                if C2 < chg:
                    c2_lt_charge+=1
                    if len(ex)<8: ex.append(('C2<charge',M,t,sp,C2,chg))
                if chg < m:
                    charge_lt_min+=1
    return ch,c2_lt_charge,charge_lt_min,ex

if __name__ == "__main__":
    print("=== (I)+(III) FRONT-PEEL identity + charge>=minAdm + tightness ===")
    for Lp1,wmax in [(2,12),(3,8),(4,6),(5,4),(3,12),(6,3)]:
        ch,fi,fg,nt,ex=sweep_frontpeel(Lp1,wmax)
        print(f"  L+1={Lp1} w0..{wmax}: chains={ch}  identity_fails={fi}  charge<minAdm={fg}  nontight(min!=minAdm)={nt}")
        if ex: print("    ex:",ex[:4])

    print("\n=== (II) charge(q) == TRUE orbit codim (r_{1N}=q), decorrelated Voight/Ext check ===")
    for d in [(4,4,2),(3,3,4),(3,3,3,4),(4,4,2,2),(2,4,1),(4,4,4,2),(3,3,3),(5,4,3,2),(2,3,2,4)]:
        d=tuple(d); N=len(d)-1
        by=SC.sigma0_by_tailrank(list(d))
        ok=all(by.get(q, None)==charge_front(d,q) for q in range(min(d[1:])+1) if q in by)
        detail=", ".join(f"q={q}: orbit={by.get(q)} charge={charge_front(d,q)}" for q in sorted(by))
        print(f"  d={d}: {'MATCH' if ok else 'MISMATCH!!'}   [{detail}]")

    print("\n=== (IV) ENTANGLEMENT collapse: C_tail pieces == closed form (t-independence) ===")
    for Lp1,wmax in [(3,7),(4,5),(5,4)]:
        ch,fa,ex=sweep_ctail(Lp1,wmax)
        print(f"  L+1={Lp1} w0..{wmax}: checked={ch}  collapse_fails={fa}")
        if ex: print("    ex:",ex[:4])

    print("\n=== (V) C2 additive OVER-COUNTS true charge (C2>=charge>=minAdm) ===")
    for Lp1,wmax in [(3,7),(4,5),(5,4)]:
        ch,c2lt,chlt,ex=sweep_c2_overcount(Lp1,wmax)
        print(f"  L+1={Lp1} w0..{wmax}: checked={ch}  (C2<charge)={c2lt}  (charge<minAdm)={chlt}")
        if ex: print("    ex:",ex[:4])
