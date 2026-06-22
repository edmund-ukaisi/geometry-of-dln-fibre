"""Verify Codex's SYMMETRIC A/R/L decomposition (decorrelated route), exactly.

A  = extendℤ of the lower unmerged part m₀(p)=m(castSucc,castSucc), box bound N:
       A α β = m(α,β) if 0<=α<=β<=N else 0.   [NOTE: A IGNORES column N+1 AND the merge;
                                                A α N = m(α,N) (raw, NOT merged).]
R  : R α β = m(α,N+1) if (0<=α<=N and β=N) else 0       (peeled last col, at bound N)
L  : L α β = m(α,N+1) if (0<=α<=N+1 and β=N+1) else 0   (true last col, at bound N+1)

Codex claims:
 (peel) extendℤ(peelPart m) = A + R   on box {0<=α<=β<=N}
 (big)  extendℤ m           = A + L   on box {0<=α<=β<=N+1}
 codimForm N (A+R)   = codimForm N A + codimBil N A R   [R-first terms vanish]
 codimForm(N+1)(A+L) = codimForm(N+1) A + codimBil(N+1) A L  [L-first vanish]
 codimForm(N+1) A = codimForm N A                      [A u (N+1)=0]
 Δ = codimBil(N+1) A L − codimBil N A R
   = controller Δ
Check ALL of these exactly.
"""
import sys, random
def extend(mdict,bound):
    def M(a,b): return mdict.get((a,b),0) if 0<=a<=b<=bound else 0
    return M
def peelPart(N,m):
    mp={}
    for I in range(N+1):
        for J in range(N+1):
            v=(m.get((I,N),0)+m.get((I,N+1),0)) if J==N else m.get((I,J),0)
            if v: mp[(I,J)]=v
    return mp
def codimForm(K,F):
    return sum(F(i-1,j-1)*F(u,v) for i in range(1,K+1) for u in range(i,K+1)
               for j in range(u,K+1) for v in range(j,K+1))
def codimBil(K,Af,Bf):
    return sum(Af(i-1,j-1)*Bf(u,v) for i in range(1,K+1) for u in range(i,K+1)
               for j in range(u,K+1) for v in range(j,K+1))
def main():
    fail=0;c=0
    R_=random.Random(555)
    for N in (1,2,3):
        for _ in range(8000):
            m={(a,b):R_.randint(0,3) for a in range(N+2) for b in range(N+2)
               if a<=b and R_.random()<0.7}
            E=extend(m,N+1); Ep=extend(peelPart(N,m),N)
            # A = m₀ extended to bound N (m₀(α,β)=m(α,β), so A = m restricted to box N, RAW col N)
            def A(a,b,m=m,N=N): return m.get((a,b),0) if 0<=a<=b<=N else 0
            def Rf(a,b,m=m,N=N): return m.get((a,N+1),0) if (0<=a<=N and b==N) else 0
            def Lf(a,b,m=m,N=N): return m.get((a,N+1),0) if (0<=a<=N+1 and b==N+1) else 0
            c+=1
            # (peel) on box 0<=a<=b<=N
            for a in range(0,N+1):
                for b in range(a,N+1):
                    if Ep(a,b)!=A(a,b)+Rf(a,b): fail+=1;print("PEEL onbox FAIL",N,a,b)
            # (big) on box 0<=a<=b<=N+1
            for a in range(0,N+2):
                for b in range(a,N+2):
                    if E(a,b)!=A(a,b)+Lf(a,b): fail+=1;print("BIG onbox FAIL",N,a,b)
            # codimForm N (A+R) expansion vanishings
            cfNApR=codimForm(N,lambda a,b:A(a,b)+Rf(a,b))
            if codimBil(N,Rf,A)!=0: fail+=1;print("bil N R A !=0",N)
            if codimForm(N,Rf)!=0: fail+=1;print("cf N R !=0",N)
            if cfNApR!=codimForm(N,A)+codimBil(N,A,Rf): fail+=1;print("N expand FAIL",N)
            # codimForm(N+1)(A+L) expansion vanishings
            cfBig=codimForm(N+1,lambda a,b:A(a,b)+Lf(a,b))
            if codimBil(N+1,Lf,A)!=0: fail+=1;print("bil N+1 L A!=0",N)
            if codimForm(N+1,Lf)!=0: fail+=1;print("cf N+1 L!=0",N)
            if cfBig!=codimForm(N+1,A)+codimBil(N+1,A,Lf): fail+=1;print("N+1 expand FAIL",N)
            # codimForm(N+1) A = codimForm N A
            if codimForm(N+1,A)!=codimForm(N,A): fail+=1;print("cf(N+1)A!=cf(N)A",N)
            # the two onbox identifications transport to codimForm equality:
            if cfNApR!=codimForm(N,Ep): fail+=1;print("peel transport FAIL",N)
            if cfBig!=codimForm(N+1,E): fail+=1;print("big transport FAIL",N)
            # Δ
            delta=codimBil(N+1,A,Lf)-codimBil(N,A,Rf)
            dctrl=sum(E(a,N)*E(u,N+1) for a in range(N+2) for u in range(a+1,N+2))
            if delta!=dctrl: fail+=1;print("Δ FAIL",N)
            # full endpoint via this route
            if codimForm(N+1,E)!=codimForm(N,Ep)+delta: fail+=1;print("endpoint FAIL",N)
    print("=== Codex symmetric A/R/L route certificate (exact) ===")
    print(f"  all onbox + vanishings + cf(N+1)A=cf(N)A + Δ + endpoint: {c}")
    print("ALL OK" if fail==0 else f"{fail} FAILURES")
    return fail
sys.exit(1 if main() else 0)
