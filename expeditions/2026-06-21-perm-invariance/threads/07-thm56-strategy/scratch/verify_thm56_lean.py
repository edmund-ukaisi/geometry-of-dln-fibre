"""Thread 07 — Thm 5.6 (5gon) Lean-strategy certificate, against the REAL Core.CTheta encoding.

Exact integer arithmetic only (PowerSeries truncated to PREC). Mirrors the LANDED Lean definitions
(codimForm ℤ-indexed via extendℤ zero-pad; kostantPartitions corner-graded; P/Pm/Pmult/transferRHS).
Verifies, on the Fin-index peel scheme (peel Fin.last N, residual d∘Fin.castSucc, merge col N into N-1):

  (A) corner range of kostantPartitions d r is nonempty exactly for r in 0..min_k d_k  (N>=1); ={d0} (N=0).
  (B) biUnion_{r=0..cap} kostantPartitions d r = all Kostant partitions, for cap in {min(d0,dN), d0, min_k d_k}.
  (C) Thm 5.6 corner-free single sum:  Pmult d = sum_{m in kostantAll d} X^{codimForm} Pm m.
  (C') biUnion-of-Qseries form: Pmult d = sum_{r=0..cap} Qseries d r, all three caps.
  (D) codimForm split (real ℤ-form): codimForm(N) (extendℤ m) = codimForm(N-1)(extendℤ m') + Delta_b(x).
  (E) per-fibre collapse: sum_{m in fibre(m')} X^{c(m)} Pm(N) m = X^{c(m')} Pm(N-1) m' * P_{dN}.
  (F) inner fibre-sum recursion == transferRHS (so transferRHS_eq, LANDED, discharges it).
  (G) full forward/inverse bijection on the Fin encoding (round-trip + coverage + no collision).
"""
import sys, os
from itertools import product as iproduct
sys.path.insert(0, os.path.join(os.path.dirname(__file__),
    '..','..','03-qseries-route','scratch'))
from ctheta import intervals, kostant_partitions
from qseries import P_s, pmul, padd, trunc, PREC, pscale_shift, Q_rd, P_multiset

def kostant_all(d):
    N=len(d)-1; ivs=intervals(N)
    out=[]
    for combo in iproduct(*[range(d[i]+1) for (i,j) in ivs]):
        m={iv:c for iv,c in zip(ivs,combo)}
        if all(sum(m[(i,j)] for (i,j) in ivs if i<=k<=j)==d[k] for k in range(N+1)):
            out.append(m)
    return out

def codimReal(N,m):
    def M(a,b): return m.get((a,b),0) if 0<=a<=b<=N else 0
    return sum(M(i-1,j-1)*M(u,v) for i in range(1,N+1) for u in range(i,N+1)
               for j in range(u,N+1) for v in range(j,N+1))

def Pm_dict(m):
    r=[1]+[0]*(PREC-1)
    for (i,j),v in m.items():
        if v: r=pmul(r,P_s(v))
    return r

def mprime_lean(N,m):
    mp={}
    for I in range(N):
        for J in range(I,N):
            v=(m.get((I,N-1),0)+m.get((I,N),0)) if J==N-1 else m.get((I,J),0)
            if v: mp[(I,J)]=v
    return mp

def delta_b(N,m):
    b={i:m.get((i,N-1),0)+m.get((i,N),0) for i in range(N)}; b[N]=0
    x={i:m.get((i,N),0) for i in range(N)}; x[N]=m.get((N,N),0)
    return sum((b.get(a,0)-x.get(a,0))*x.get(u,0) for a in range(N+1) for u in range(a+1,N+1))

def transferRHS(b,d):
    if not b: return P_s(d)
    b0,bs=b[0],b[1:]
    acc=[0]*PREC
    for x0 in range(min(b0,d)+1):
        term=pmul(pmul(P_s(b0-x0),P_s(x0)),transferRHS(bs,d-x0))
        acc=padd(acc,pscale_shift(term,1,(b0-x0)*(d-x0)))
    return trunc(acc)

def canon(m): return frozenset((k,v) for k,v in m.items() if v)

TESTS=[(2,2,2),(2,3,2),(1,2,3),(3,2,1),(2,1,3),(1,3,2),(2,1,3,2),(1,2,2,3),
       (4,4,4),(0,2,1),(2,0,2),(5,),(0,),(3,),(2,3),(4,2,3,1),(1,1,1,1),
       (2,1,2),(3,1,4,2),(2,4,2)]

def main():
    cnt={'A':0,'B':0,'C':0,'Cp':0,'D':0,'E':0,'F':0,'G':0}
    fail=0
    # A: corner range
    for d in TESTS:
        N=len(d)-1
        ne=[r for r in range(0,max(d)+2) if kostant_partitions(list(d),r)]
        exp=[d[0]] if N==0 else list(range(0,min(d)+1))
        cnt['A']+=1
        if ne!=exp: fail+=1; print('A FAIL',d,ne,exp)
    # B,Cp: biUnion ranges
    for d in TESTS:
        N=len(d)-1
        allset=set(canon(m) for m in kostant_all(d))
        lhs=P_multiset(d)
        for cap in [min(d[0],d[-1]),d[0],min(d)]:
            s=set(); acc=[0]*PREC
            for r in range(0,cap+1):
                for m in kostant_partitions(list(d),r): s.add(canon(m))
                acc=padd(acc,Q_rd(list(d),r))
            cnt['B']+=1; cnt['Cp']+=1
            if s!=allset: fail+=1; print('B FAIL',d,cap)
            if trunc(acc)!=lhs: fail+=1; print('Cp FAIL',d,cap)
    # C: corner-free single sum
    for d in TESTS:
        N=len(d)-1; lhs=P_multiset(d); rhs=[0]*PREC
        for m in kostant_all(d):
            c=codimReal(N,m)
            if c<PREC: rhs=padd(rhs,pscale_shift(Pm_dict(m),1,c))
        cnt['C']+=1
        if trunc(rhs)!=lhs: fail+=1; print('C FAIL',d)
    # D,E,G: split, fibre-collapse, bijection
    for d in TESTS:
        N=len(d)-1
        if N<1: continue
        dN=d[-1]; dprime=tuple(d[:-1])
        allm=kostant_all(d)
        # D
        for m in allm:
            cnt['D']+=1
            if codimReal(N,m)!=codimReal(N-1,mprime_lean(N,m))+delta_b(N,m):
                fail+=1; print('D FAIL',d,m)
        # E: per-fibre collapse
        fibres={}
        for m in allm: fibres.setdefault(canon(mprime_lean(N,m)),[]).append(m)
        for cmp_,ms in fibres.items():
            mp=dict(cmp_); lhs=[0]*PREC
            for m in ms: lhs=padd(lhs,pscale_shift(Pm_dict(m),1,codimReal(N,m)))
            rhs=trunc(pscale_shift(pmul(Pm_dict(mp),P_s(dN)),1,codimReal(N-1,mp)))
            cnt['E']+=1
            if trunc(lhs)!=rhs: fail+=1; print('E FAIL',d,cmp_)
        # G: bijection round-trip + coverage
        def lastcol(m): return {i:m.get((i,N),0) for i in range(N+1)}
        def reconstruct(mp,x):
            m={}
            for (I,J),v in mp.items():
                if J<N-1:
                    if v: m[(I,J)]=m.get((I,J),0)+v
                else:
                    if v-x.get(I,0)>0: m[(I,N-1)]=v-x.get(I,0)
                    if x.get(I,0)>0: m[(I,N)]=m.get((I,N),0)+x.get(I,0)
            if x.get(N,0)>0: m[(N,N)]=x[N]
            return {k:v for k,v in m.items() if v}
        for m in allm:
            cnt['G']+=1
            if canon(reconstruct(mprime_lean(N,m),lastcol(m)))!=canon(m):
                fail+=1; print('G roundtrip FAIL',d)
        built=set(); allmp={canon(mp):mp for mp in kostant_all(dprime)}
        for mp in allmp.values():
            b={i:mp.get((i,N-1),0) for i in range(N)}
            for xs in iproduct(*[range(b[i]+1) for i in range(N)]):
                xN=dN-sum(xs)
                if xN<0: continue
                x={i:xs[i] for i in range(N)}; x[N]=xN
                c=canon(reconstruct(mp,x))
                if c in built: fail+=1; print('G collision',d)
                built.add(c)
        if built!=set(map(canon,allm)): fail+=1; print('G coverage FAIL',d)
    # F: inner fibre-sum recursion == transferRHS
    for b in [[],[1],[2,1],[1,2],[2,2],[1,1,1],[2,1,3],[0,2],[3],[1,2,1,2]]:
        for dN in range(0,8):
            acc=[0]*PREC
            for xs in iproduct(*[range(bi+1) for bi in b]):
                xN=dN-sum(xs)
                if xN<0: continue
                x={i:xs[i] for i in range(len(b))}; x[len(b)]=xN
                bb={i:b[i] for i in range(len(b))}; bb[len(b)]=0
                Delta=sum((bb[a]-x.get(a,0))*x.get(u,0) for a in range(len(b)+1) for u in range(a+1,len(b)+1))
                term=P_s(xN)
                for i in range(len(b)): term=pmul(term,pmul(P_s(b[i]-xs[i]),P_s(xs[i])))
                acc=padd(acc,pscale_shift(term,1,Delta))
            cnt['F']+=1
            if trunc(acc)!=transferRHS(b,dN): fail+=1; print('F FAIL',b,dN)
    print('=== Thm 5.6 Lean-strategy certificate (exact integer) ===')
    for k in ['A','B','C','Cp','D','E','F','G']:
        print(f'  ({k}) checks: {cnt[k]}')
    print('ALL OK' if fail==0 else f'{fail} FAILURES')
    return fail

if __name__=='__main__':
    sys.exit(1 if main() else 0)
