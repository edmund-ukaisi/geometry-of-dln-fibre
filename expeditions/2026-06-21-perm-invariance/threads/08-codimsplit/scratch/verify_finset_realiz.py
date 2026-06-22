"""Determine the MINIMAL Finset realization of S(N+1)=S(N) ⊔ {v=N+1}.

In Lean codimForm(N+1) is literally:
  Σ_{i∈Icc 1 (N+1)} Σ_{u∈Icc i (N+1)} Σ_{j∈Icc u (N+1)} Σ_{v∈Icc j (N+1)} E(i-1,j-1)E(u,v).

To peel v=N+1 we peel the INNERMOST sum:  Icc j (N+1) = insert (N+1) (Icc j N)  [needs j≤N+1, true].
   -> inner = E(...)·E(u,N+1) [v=N+1 term] + Σ_{v∈Icc j N} E(i-1,j-1)E(u,v).
The residual Σ_{v∈Icc j N} part, summed over i,u,j∈Icc·(N+1), is NOT codimForm(N): the OUTER ranges
still go to N+1. BUT the v∈Icc j N inner sum is EMPTY when j=N+1 (Icc (N+1) N = ∅). So the j=N+1
slice of the residual vanishes; likewise need u=N+1, i=N+1 slices to vanish.

So the residual after peeling v:  Σ_{i,u,j∈Icc·(N+1)} [Σ_{v∈Icc j N} E(i-1,j-1)E(u,v)].
Claim: this equals codimForm(N) E because:
   - j=N+1 slice: Icc(N+1)N=∅ inner -> 0. So j effectively ∈ Icc u N.
   - then with j≤N: u≤j≤N so u≤N, and the u=N+1 slice forces u≤j≤N impossible -> u∈Icc i N.
   - then i≤u≤N so i≤N, i=N+1 slice empty -> i∈Icc 1 N.
   => residual = Σ_{i∈Icc 1 N}Σ_{u∈Icc i N}Σ_{j∈Icc u N}Σ_{v∈Icc j N} E(i-1,j-1)E(u,v)=codimForm(N)E. ✓

TEST the cascade of empties + the residual=codimForm(N).
Also test the ALTERNATIVE: does each of the four nested sums need the SAME insert peel, or does
peeling just the innermost v + the auto-empty cascade suffice? (The cascade means: after peeling v,
codimForm(N) E falls out by Finset.sum_congr that drops the top elements via empty-inner-sum, i.e.
NO need to peel i,u,j explicitly — they collapse because the inner Icc becomes empty.)
"""
import sys, random
def extend(mdict,bound):
    def M(a,b): return mdict.get((a,b),0) if 0<=a<=b<=bound else 0
    return M
def main():
    fail=0;c=0
    R=random.Random(3)
    for N in (1,2,3):
        for _ in range(8000):
            m={(a,b):R.randint(0,3) for a in range(N+2) for b in range(N+2)
               if a<=b and R.random()<0.7}
            E=extend(m,N+1); K=N+1
            full=sum(E(i-1,j-1)*E(u,v) for i in range(1,K+1) for u in range(i,K+1)
                     for j in range(u,K+1) for v in range(j,K+1))
            # peel innermost v: split each inner sum into {v=N+1 if N+1>=j} + {v in [j,N]}
            Lterm=0; residual=0
            for i in range(1,K+1):
                for u in range(i,K+1):
                    for j in range(u,K+1):
                        # v=N+1 contributes iff N+1>=j (always, since j<=N+1)
                        Lterm += E(i-1,j-1)*E(u,K)
                        for v in range(j,N+1):   # Icc j N
                            residual += E(i-1,j-1)*E(u,v)
            cN=sum(E(i-1,j-1)*E(u,v) for i in range(1,N+1) for u in range(i,N+1)
                   for j in range(u,N+1) for v in range(j,N+1))
            c+=1
            if residual!=cN: fail+=1; print("residual!=cN",N)
            if full!=Lterm+residual: fail+=1; print("full split FAIL",N)
    print("=== minimal Finset realization (peel innermost v, cascade-empty) ===")
    print(f"  residual==codimForm(N) AND full=L+residual: {c}")
    print("ALL OK" if fail==0 else f"{fail} FAILURES")
    return fail
sys.exit(1 if main() else 0)
