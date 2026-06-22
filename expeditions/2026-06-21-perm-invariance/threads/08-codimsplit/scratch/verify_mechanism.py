"""Verify the STAGED mechanism of the codimForm split (the controller's math path),
not just the endpoint. We decompose

  codimForm(N+1)(extendℤ m)  -  codimForm(N)(extendℤ(peelPart m))

into named pieces and check EACH piece, so the Lean proof can mirror the decomposition.

Let M = extendℤ m (box 0..N+1),  M' = extendℤ(peelPart m) (box 0..N).
Note M'(u,v) = M(u,v) for v<N ; M'(u,N) = M(u,N)+M(u,N+1) ; (rows/cols up to N).

codimForm(K)(F) = Σ_{1≤i≤u≤j≤v≤K} F(i-1,j-1) F(u,v).

STAGE 1 (peel v=N+1 from the big form):
  codimForm(N+1)(M)
    = [terms with v ≤ N]  +  [terms with v = N+1].
  Claim 1a: [terms with v ≤ N of the (N+1)-form]
            = Σ_{1≤i≤u≤j≤v≤N} M(i-1,j-1) M(u,v).
            (this is codimForm(N)(M) — same form but M not M', box N+1 but only entries ≤N used,
             and M=M' on the box 0..N except column N.)
  Claim 1b: [terms with v=N+1] = Σ_{1≤i≤u≤j≤N+1} M(i-1,j-1) M(u,N+1).

STAGE 2 (relate codimForm(N)(M) to codimForm(N)(M')):
  M and M' agree everywhere on box 0..N EXCEPT M'(u,N) = M(u,N) + M(u,N+1).
  In codimForm(N)(F)= Σ_{1≤i≤u≤j≤v≤N} F(i-1,j-1)F(u,v), the entry "(u,N)" (with v=N) and the
  entry "(i-1,j-1)=(·,N)" (with j-1=N i.e. j=N+1 — impossible since j≤N). So column N appears
  ONLY through F(u,v) with v=N (the second factor), AND through F(i-1,j-1) with j-1 = N i.e.
  j=N+1, which is OUT of range (j≤N). So M' differs from M in codimForm(N) ONLY in the v=N
  second-factor slot:
  Claim 2: codimForm(N)(M') - codimForm(N)(M)
           = Σ_{1≤i≤u≤j≤v≤N, v=N} M(i-1,j-1) (M'(u,N) - M(u,N))
           = Σ_{1≤i≤u≤j≤N} M(i-1,j-1) M(u,N+1).
   ( using M'(u,N)-M(u,N) = M(u,N+1), and j ranges u..N with v fixed =N.)

PUTTING TOGETHER:
  codimForm(N+1)(M)
    = codimForm(N)(M) + [v=N+1 terms]                                  (Stage 1)
    = [codimForm(N)(M') - Σ_{1≤i≤u≤j≤N} M(i-1,j-1)M(u,N+1)] + [v=N+1 terms]  (Stage 2)
  So  codimForm(N+1)(M) - codimForm(N)(M')
    = [v=N+1 terms] - Σ_{1≤i≤u≤j≤N} M(i-1,j-1) M(u,N+1)
    =: Δ.
  And we must check Δ == Σ_{0≤a<u≤N+1} M(a,N) M(u,N+1)   (controller's form).

We verify Claims 1a,1b,2 and the final Δ identity, separately, exactly.
"""
import sys, random

def extend(mdict, bound):
    def M(a, b):
        if 0 <= a <= b <= bound: return mdict.get((a,b),0)
        return 0
    return M

def peelPart(N, m):
    mp = {}
    for I in range(N+1):
        for J in range(N+1):
            v = (m.get((I,N),0)+m.get((I,N+1),0)) if J==N else m.get((I,J),0)
            if v: mp[(I,J)] = v
    return mp

def codim_full(K, F):
    return sum(F(i-1,j-1)*F(u,v)
               for i in range(1,K+1) for u in range(i,K+1)
               for j in range(u,K+1) for v in range(j,K+1))

def codim_v_le(K, F, vmax):
    # terms of the K-form with v <= vmax
    return sum(F(i-1,j-1)*F(u,v)
               for i in range(1,K+1) for u in range(i,K+1)
               for j in range(u,K+1) for v in range(j,min(K,vmax)+1))

def stage1b(N, M):
    # v = N+1 terms of (N+1)-form:  1<=i<=u<=j<=N+1, v=N+1
    K = N+1
    return sum(M(i-1,j-1)*M(u,K)
               for i in range(1,K+1) for u in range(i,K+1) for j in range(u,K+1))

def stage2_correction(N, M):
    # Σ_{1<=i<=u<=j<=N} M(i-1,j-1) M(u,N+1)
    return sum(M(i-1,j-1)*M(u,N+1)
               for i in range(1,N+1) for u in range(i,N+1) for j in range(u,N+1))

def delta_controller(N, M):
    return sum(M(a,N)*M(u,N+1) for a in range(N+2) for u in range(a+1,N+2))

def main():
    fail=0; c1a=c1b=c2=cD=0
    R = random.Random(20260622)
    for N in (1,2,3):
        for _ in range(8000):
            m = {(a,b): R.randint(0,3) for a in range(N+2) for b in range(N+2)
                 if R.random()<0.7 and a<=b}
            M  = extend(m, N+1)
            Mp = extend(peelPart(N,m), N)
            # Claim 1a: v<=N terms of (N+1)-form == codimForm(N)(M) (same M, full N-form)
            lhs1a = codim_v_le(N+1, M, N)
            rhs1a = codim_full(N, M)
            c1a+=1
            if lhs1a != rhs1a: fail+=1; print("1a FAIL",N,m); 
            # Stage1 total: full(N+1)(M) == v<=N part + v=N+1 part
            if codim_full(N+1,M) != lhs1a + stage1b(N,M):
                fail+=1; print("STAGE1 FAIL",N,m)
            c1b+=1
            # Claim 2: codimForm(N)(M') - codimForm(N)(M) == correction
            lhs2 = codim_full(N,Mp) - codim_full(N,M)
            rhs2 = stage2_correction(N,M)
            c2+=1
            if lhs2 != rhs2: fail+=1; print("2 FAIL",N,m, lhs2, rhs2)
            # Final Δ: full(N+1)(M)-full(N)(M') == Δ_controller, and ==stage1b - correction
            D = codim_full(N+1,M) - codim_full(N,Mp)
            cD+=1
            if D != delta_controller(N,M): fail+=1; print("Δctrl FAIL",N,m)
            if D != stage1b(N,M) - stage2_correction(N,M): fail+=1; print("Δstage FAIL",N,m)
    print("=== staged-mechanism certificate (exact int) ===")
    print(f"  Claim 1a (v<=N part == N-form on M): {c1a}")
    print(f"  Stage 1 split (peel v=N+1):          {c1b}")
    print(f"  Claim 2 (M'->M correction, v=N col): {c2}")
    print(f"  Δ == ctrl AND == stage1b-correction: {cD}")
    print("ALL OK" if fail==0 else f"{fail} FAILURES")
    return fail

sys.exit(1 if main() else 0)
