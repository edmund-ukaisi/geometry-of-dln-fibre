"""Pin the EXACT on-box relation between extendℤ(peelPart m) and extendℤ m,
which is the bridge the Lean proof needs (the index correspondence).

Lean: peelPart m (I,J) : Fin(N+1)^2.  extendℤ(peelPart m) a b (box 0..N):
   = peelPart m (a,b)  for 0<=a<=b<=N, else 0.
And peelPart m (I,J) under castSucc lands on m's entries:
   J<N  : m(I,J)              (= m(castSucc I, castSucc J), same nat indices)
   J=N  : m(I,N)+m(I,N+1)

So, as ℤ→ℤ→ℤ functions:
   extendℤ(peelPart m)(a,b) = [0<=a<=b<=N] * ( m(a,b)             if b<N
                                               m(a,N)+m(a,N+1)    if b=N )
   extendℤ(m)(a,b)          = [0<=a<=b<=N+1] * m(a,b)

CLAIM (the ℤ-bridge, what Lean rewrites with):
  For 0<=a<=b<=N :  extendℤ(peelPart m)(a,b) = extendℤ(m)(a,b) + [b=N]*extendℤ(m)(a,N+1).
  Off that box (b>N or a>b or a<0): extendℤ(peelPart m)(a,b)=0.

We verify this AND re-derive Δ purely as ℤ-codimForm/codimBil algebra:
  Let E  = extendℤ m              (box N+1)
      Ep = extendℤ(peelPart m)    (box N)
      G  = the "ℤ correction" : G a b = [0<=a<=N][b=N]*E(a,N+1)   (so Ep = E_restrictedToBoxN + G on box N)
  Actually cleaner: define Ē = E but viewed for codimForm N (only reads box 1..N for u,v and i-1,j-1 in 0..N-1).
  Then Ep = Ē + Gcol  on the box codimForm N reads, where Gcol a b = [b=N]*E(a,N+1) (for 0<=a<=N).
  codimForm N Ep = codimForm N (Ē+Gcol)
                 = codimForm N Ē + codimBil N Ē Gcol + codimBil N Gcol Ē + codimForm N Gcol
  We check which of these vanish and that the surviving combination + Δ = codimForm(N+1) E.
"""
import sys, random

def extend(mdict, bound):
    def M(a,b):
        return mdict.get((a,b),0) if 0<=a<=b<=bound else 0
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

def codimBil(K,A,B):
    return sum(A(i-1,j-1)*B(u,v) for i in range(1,K+1) for u in range(i,K+1)
               for j in range(u,K+1) for v in range(j,K+1))

def main():
    fail=0; cB=0; cS=0; cT=0
    R=random.Random(7)
    for N in (1,2,3):
        for _ in range(6000):
            m={(a,b):R.randint(0,3) for a in range(N+2) for b in range(N+2)
               if a<=b and R.random()<0.7}
            E=extend(m,N+1); Ep=extend(peelPart(N,m),N)
            # ℤ-bridge: Ep(a,b) = E(a,b) + [b==N]*E(a,N+1)  on 0<=a<=b<=N ; else 0
            for a in range(-1,N+3):
                for b in range(-1,N+3):
                    cB+=1
                    if 0<=a<=b<=N:
                        want = E(a,b) + (E(a,N+1) if b==N else 0)
                    else:
                        want = 0
                    if Ep(a,b)!=want: fail+=1; print("BRIDGE FAIL",N,a,b,Ep(a,b),want)
            # Now define Gcol on ALL ℤ: Gcol(a,b) = [b==N]*E(a,N+1) when 0<=a<=N else 0
            def Gcol(a,b, E=E,N=N):
                return E(a,N+1) if (0<=a<=N and b==N) else 0
            # And Ebar = E itself; on the box codimForm N reads (u,v in 1..N, i-1,j-1 in 0..N-1),
            # Ep = Ebar + Gcol pointwise? check on that box:
            for a in range(0,N+1):
                for b in range(0,N+1):
                    cS+=1
                    if Ep(a,b) != E(a,b)+Gcol(a,b): fail+=1; print("EpEbarG FAIL",N,a,b)
            # codimForm N Ep expansion
            cf_Ep = codimForm(N,Ep)
            cf_Eb = codimForm(N,E)
            bil1  = codimBil(N,E,Gcol)
            bil2  = codimBil(N,Gcol,E)
            cf_G  = codimForm(N,Gcol)
            cT+=1
            if cf_Ep != cf_Eb+bil1+bil2+cf_G: fail+=1; print("EXPAND FAIL",N)
            # Which vanish? Gcol has b=N as SECOND index -> appears as B(u,v) with v=N (bil1) ok,
            #   and as A(i-1,j-1) i.e. column index j-1=N => j=N+1 OUT of range in codimForm N -> bil2=0, cf_G=0.
            if bil2!=0: fail+=1; print("bil2 NONZERO",N,bil2)
            if cf_G!=0: fail+=1; print("cf_G NONZERO",N,cf_G)
            # So codimForm N Ep = codimForm N E + codimBil N E Gcol.
            # Target: codimForm(N+1) E = codimForm N Ep + Δ
            # => Δ = codimForm(N+1)E - codimForm N E - codimBil N E Gcol
            delta = codimForm(N+1,E) - cf_Ep
            delta_alt = codimForm(N+1,E) - cf_Eb - bil1
            if delta!=delta_alt: fail+=1; print("delta alt FAIL",N)
            # controller Δ:
            dctrl = sum(E(a,N)*E(u,N+1) for a in range(N+2) for u in range(a+1,N+2))
            if delta!=dctrl: fail+=1; print("delta ctrl FAIL",N)
    print("=== ℤ-bridge + codimForm-expansion certificate (exact) ===")
    print(f"  ℤ-bridge pointwise checks:     {cB}")
    print(f"  Ep = E + Gcol on read-box:     {cS}")
    print(f"  expansion + vanishing + Δ:     {cT}")
    print("ALL OK" if fail==0 else f"{fail} FAILURES")
    return fail

sys.exit(1 if main() else 0)
