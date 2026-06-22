"""Verify the RWY (Rimanyi-Weigandt-Yong, arXiv:1608.02030, JACO 2018) reduction
for the EQUIORIENTED type-A quiver matches the paper (Lehalleur-Rimanyi) objects.

Paper LR uses vertices 0..N (N+1 of them); intervals [i,j], 0<=i<=j<=N.
RWY uses columns 1..n (n = N+1 of them); intervals [i,j], 1<=i<=j<=n.
Map: LR vertex k  <->  RWY column k+1.  LR interval [i,j] <-> RWY interval [i+1,j+1].

For the EQUIORIENTED quiver, all arrows point the SAME direction, so RWY's permutations
w_Q^{(i)} are ALL the identity (the "same direction" branch). Hence w(k)(i)=i.

RWY codimension (Prop 3.3): codim = sum over (I,J) in ConditionStrands of m_I m_J,
where for the EQUIORIENTED case (all arrows right) only types (I),(II) occur:
  (I)  I=[w,x-1], J=[x,z]   with w < x <= z
  (II) I=[w,y],   J=[x,z]   with w < x <= y < z   (both arrows same dir = right: always)
Type (III) needs opposite directions -> absent for equioriented.

RWY BoxStrands (Prop 3.5, with w=id): ([i, k-1],[j,l]) with 1<=i<j<=k<=l<=n.
Lemma 3.6: BoxStrands = ConditionStrands.  So
  r_w(eta) = sum_{1<=i<j<=k<=l<=n} m_{[i,k-1]} m_{[j,l]}.

We verify (in LR 0..N indexing) that this equals codimForm(m) = LR eqn dim_formula:
  c(m) = sum_{1<=i<=u<=j<=v<=N} m_{(i-1)(j-1)} m_{uv}.
"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from ctheta import kostant_fast, codimForm, intervals

def rwy_box_codim_LRindex(N, m):
    """RWY Prop 3.5/3.6 codim in LR 0..N indexing.
    RWY columns 1..n  with n=N+1.  RWY interval [a,b] (1-based) = LR interval [a-1,b-1].
    BoxStrands (w=id): I=[i,k-1], J=[j,l] with 1<=i<j<=k<=l<=n (1-based RWY columns).
    Convert: LR i' = i-1, etc.  Strand types:
       I_RWY=[i,k-1] -> LR [i-1, k-2]
       J_RWY=[j,l]   -> LR [j-1, l-1]
    with 1<=i<j<=k<=l<=n=N+1.
    """
    n = N+1
    def mm(a,b):  # LR interval [a,b]
        return m.get((a,b),0)
    total = 0
    for i in range(1, n+1):
        for j in range(i+1, n+1):
            for k in range(j, n+1):
                for l in range(k, n+1):
                    # I=[i,k-1] (RWY) requires i<=k-1 i.e. k>=i+1; since j>i and k>=j>i, ok if k-1>=i
                    if k-1 < i:
                        continue
                    I = (i-1, k-2)   # LR
                    J = (j-1, l-1)   # LR
                    total += mm(*I) * mm(*J)
    return total

def rwy_conditionstrands_codim_LRindex(N, m):
    """Direct ConditionStrands for equioriented (types I and II), LR 0..N indexing.
    RWY 1-based intervals; convert to LR by subtracting 1 from each endpoint.
    Type (I):  I=[w,x-1], J=[x,z], w<x<=z         (1-based)
    Type (II): I=[w,y],  J=[x,z], w<x<=y<z        (1-based)
    """
    n = N+1
    def mm(a,b):
        return m.get((a,b),0)
    total = 0
    seen = set()
    # enumerate all interval pairs (I,J) 1-based and test type I/II
    ivs1 = [(a,b) for a in range(1,n+1) for b in range(a,n+1)]
    for (w1,x1b) in ivs1:       # I = [w1, x1b]
        for (x2,z2) in ivs1:    # J = [x2, z2]
            I=(w1,x1b); J=(x2,z2)
            # Type I: I=[w,x-1], J=[x,z], w<x<=z  => x1b = x2-1, w1 < x2 <= z2
            isI = (x1b == x2-1) and (w1 < x2 <= z2)
            # Type II: I=[w,y], J=[x,z], w<x<=y<z  (arrows same dir, equioriented => holds)
            isII = (w1 < x2 <= x1b < z2)
            if isI or isII:
                # convert to LR and add
                total += mm(w1-1, x1b-1) * mm(x2-1, z2-1)
    return total

if __name__ == "__main__":
    import itertools, random
    print("Checking: codimForm(m) == RWY-BoxStrands == RWY-ConditionStrands (equioriented)")
    fails=0; checked=0
    tests = [(2,2,2),(2,3,2),(1,2,3),(3,2,1),(2,1,3,2),(4,4,4),(1,2,3,4),(3,3,3),(2,4,2),(5,5,6),(1,2,2,3)]
    for d in tests:
        N=len(d)-1
        for r in range(0,min(d)+1):
            for m in kostant_fast(list(d), r):
                cf  = codimForm(N, m)
                box = rwy_box_codim_LRindex(N, m)
                cond= rwy_conditionstrands_codim_LRindex(N, m)
                checked+=1
                if not (cf==box==cond):
                    fails+=1
                    if fails<=8:
                        print(f"  MISMATCH d={d} r={r} m={m}: codimForm={cf} box={box} cond={cond}")
    print(f"checked {checked} Kostant partitions; mismatches: {fails}")
    print("OK" if fails==0 else "FAIL")
