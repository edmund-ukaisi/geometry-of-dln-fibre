"""Pin the OUTER-sum split of codimForm(N+1) by the v-layer, in ℤ-Icc form.

codimForm(N+1) E = Σ_{i=1..N+1}Σ_{u=i..N+1}Σ_{j=u..N+1}Σ_{v=j..N+1} E(i-1,j-1)E(u,v).

We want to show this equals  codimForm(N) E  +  L,  where L is "everything touching v=N+1 or
j=N+1 or u=N+1 or i=N+1" — i.e. the part NOT inside 1≤i≤u≤j≤v≤N.

KEY question for the Lean strategy: is the simplest peel to split the OUTERMOST sum (i: 1..N+1 =
1..N ∪ {N+1}) or the INNERMOST (v: j..N+1)? And does codimForm(N) E literally appear as the
"all indices ≤ N" block?

We test the decomposition by INDEX-SET partition:
  S(K) = {(i,u,j,v): 1≤i≤u≤j≤v≤K}.
  S(N+1) = S(N)  ⊔  T,  where T = {(i,u,j,v)∈S(N+1): v=N+1}  (since v is the max, v≤N <=> all ≤N).
  Wait: 1≤i≤u≤j≤v, so v is the LARGEST. v≤N ⟺ the whole tuple ≤N ⟺ in S(N). v=N+1 is the
  only other option (v≤N+1). So S(N+1) = S(N) ⊔ {v=N+1}. CLEAN — the innermost index v alone
  decides membership. So L = Σ_{1≤i≤u≤j≤N+1, v=N+1} E(i-1,j-1)E(u,N+1).

Check this L equals controllerΔ + codimBil(N) E Gcol (consistency with the other route),
and that codimForm(N+1)=codimForm(N)+L.
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
def codimBil(K,A,B):
    return sum(A(i-1,j-1)*B(u,v) for i in range(1,K+1) for u in range(i,K+1)
               for j in range(u,K+1) for v in range(j,K+1))
def main():
    fail=0;c=0
    R=random.Random(99)
    for N in (1,2,3):
        for _ in range(8000):
            m={(a,b):R.randint(0,3) for a in range(N+2) for b in range(N+2)
               if a<=b and R.random()<0.7}
            E=extend(m,N+1)
            # L = innermost v=N+1 layer of the (N+1)-form
            K=N+1
            L=sum(E(i-1,j-1)*E(u,K) for i in range(1,K+1) for u in range(i,K+1) for j in range(u,K+1))
            c+=1
            if codimForm(K,E)!=codimForm(N,E)+L: fail+=1; print("PEEL FAIL",N)
            # Gcol route consistency
            def Gcol(a,b,E=E,N=N): return E(a,N+1) if (0<=a<=N and b==N) else 0
            bil=codimBil(N,E,Gcol)
            dctrl=sum(E(a,N)*E(u,N+1) for a in range(N+2) for u in range(a+1,N+2))
            # L - bil should equal Δctrl (since codimForm(N) Ep = codimForm N E + bil, and
            #   codimForm(N+1) = codimForm N E + L, Δ = codimForm(N+1)-codimForm(N) Ep = L - bil)
            if L-bil!=dctrl: fail+=1; print("L-bil FAIL",N,L,bil,dctrl)
    print("=== peel-layer (innermost v=N+1) certificate ===")
    print(f"  codimForm(N+1)=codimForm(N)+L AND L-bil=Δctrl: {c}")
    print("ALL OK" if fail==0 else f"{fail} FAILURES")
    return fail
sys.exit(1 if main() else 0)
