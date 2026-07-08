#!/usr/bin/env python3
"""
genm-r1substratum -- EXACT adjudication of the SUB-GENERIC stratum charge for the R1-UPPER descent.

Uses the FAITHFUL minAdm (imported from rankcharge.py, itself brute-validated against Adm/Mval).

Geometry recap (peel boundary 0 of chain M=(M0,...,ML), L>=2, at cut t):
  a = M0 - t,  b = M1 - t,  n = min(M2,...,ML)  (tail bottleneck)
  tail chain feeding Q_b:  (b, M2, ..., ML)      [Q_b = product of this chain]
  generic rank of Q_b:     s = min(b, n)
  sub-generic strata:      { rank Q_b = s' },  0 <= s' < s
  active-block shift:      a * s' / 2   (Gamma |-> Gamma*Q_b has rank a*s')

CODIM of the sub-generic stratum (PAPER, peeling identity line 826):
  codim{ rank(product of chain W) <= s' }  =  minAdm( W - s' )    (subtract s' from every width of W)
  Here W = (b, M2, ..., ML).  So  kappa(t, s') = minAdm(b-s', M2-s', ..., ML-s').

We test candidate per-stratum "method charges" against minAdm(M):
  C1(t,s') = a*s' + kappa(t,s')                          (active + stratum codim, NO extra recursion)
  C2(t,s') = a*s' + kappa(t,s') + minAdm(redChain t M)   (active + stratum codim + deeper recursion)
  Cfree(t,s') = a*s' + (b-s')(n-s')                       (the CRUDE free-matrix heuristic, for contrast)

For each we ask:  is C >= minAdm(M) for ALL (t, s')?  (finiteness certified by the method)
and does min over (t,s') of C == minAdm(M)? (tightness / the generic stratum binds)

The generic stratum s'=s must reproduce the cert charge  a*s + minAdm(redChain t M).
"""
import io, contextlib
_buf = io.StringIO()
with contextlib.redirect_stdout(_buf):
    import rankcharge as R
from itertools import product
from functools import lru_cache

minAdm = R.minAdmRec          # faithful, == brute
redChain = R.redChain

def clamp_sub(W, r):
    """entrywise subtract r, clamp at 0 (widths can't be negative)."""
    return tuple(max(0, w - r) for w in W)

@lru_cache(maxsize=None)
def minAdm_t(W):
    return minAdm(tuple(W))

def kappa(t, M, sp):
    """codim of {rank Q_b = s'} = minAdm(tailchain - s'),  tailchain = (b, M2,...,ML)."""
    b = M[1] - t
    tailchain = (b,) + tuple(M[2:])           # (b, M2, ..., ML)
    return minAdm_t(clamp_sub(tailchain, sp))

def charges(t, M, sp):
    a = M[0] - t; b = M[1] - t; n = min(M[2:])
    k = kappa(t, M, sp)
    rc = minAdm(redChain(t, M))
    C1 = a*sp + k
    C2 = a*sp + k + rc
    Cfree = a*sp + (b-sp)*(n-sp)
    return dict(a=a, b=b, n=n, s=min(b,n), kappa=k, rc=rc, C1=C1, C2=C2, Cfree=Cfree)

def audit_chain(M, verbose=False):
    """Return per-cut, per-s' failures for each candidate charge; also generic-stratum consistency."""
    M = tuple(M)
    m = minAdm(M)
    n = min(M[2:])
    fails = {'C1': [], 'C2': [], 'Cfree': []}
    generic_mismatch = []       # generic stratum charge != cert charge a*s + minAdm(redChain)
    mins = {'C1': None, 'C2': None, 'Cfree': None}
    for t in range(min(M[0], M[1])+1):
        b = M[1]-t; s = min(b, n)
        for sp in range(0, s+1):          # s'=0..s (s' = s is the generic stratum)
            ch = charges(t, M, sp)
            for key in ('C1','C2','Cfree'):
                v = ch[key]
                if mins[key] is None or v < mins[key]: mins[key] = v
                if v < m:
                    fails[key].append((t, sp, v, ch))
            # generic consistency at s'=s: cert charge = a*s + minAdm(redChain)
            if sp == s:
                cert = ch['a']*s + ch['rc']
                # on generic stratum kappa should be 0 (whole tail space)
                if ch['kappa'] != 0 and s == min(b, n):
                    generic_mismatch.append(('kappa!=0 at generic', t, s, ch['kappa']))
    if verbose:
        print(f"M={M} minAdm={m}: minC1={mins['C1']} minC2={mins['C2']} minCfree={mins['Cfree']}  "
              f"C1fails={len(fails['C1'])} C2fails={len(fails['C2'])} Cfreefails={len(fails['Cfree'])}"
              f"  gen_kappa_nonzero={len(generic_mismatch)}")
    return m, mins, fails, generic_mismatch

if __name__ == "__main__":
    print("=== mission anchors + flagged case ===")
    for M in [(4,4,2),(4,4,2,2),(3,3,3,4),(2,4,1),(3,3,4),(4,4,4,2),(3,3,2,2)]:
        m, mins, fails, gm = audit_chain(M, verbose=True)
        for key in ('C1','C2','Cfree'):
            if fails[key]:
                print(f"    {key} SHORTFALLS (t,s',val,detail):")
                for (t,sp,v,ch) in fails[key][:6]:
                    print(f"      t={t} s'={sp}: {key}={v} < minAdm={m}   a={ch['a']} b={ch['b']} "
                          f"n={ch['n']} s={ch['s']} kappa={ch['kappa']} rc={ch['rc']}")
