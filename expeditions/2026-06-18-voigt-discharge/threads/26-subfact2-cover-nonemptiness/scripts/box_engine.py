"""
Exact combinatorial engine for the orbit-closure box-move generation problem.

Coordinates
-----------
Vertices 0..N (N+1 of them). Intervals [a,b], 0<=a<=b<=N.
Multiplicity array m[(a,b)] >= 0 (a Kostant partition / lace data).
Dimension vector d_t = sum_{a<=t<=b} m[(a,b)].
Rank pattern (cumul): r[(i,j)] = sum_{a<=i and j<=b} m[(a,b)], for i<=j.
  (matches DLNFibre.Core: rankPattern = cumul N (multiplicityArray L);
   diagonal r[(i,i)] = d_i.)
Order: s <= r  iff  for all i<=j, s[(i,j)] <= r[(i,j)].

Box move (linked, a < c <= b+1 <= e):
  m[(a,e)] -= 1; m[(c,b)] -= 1;  m[(a,b)] += 1; m[(c,e)] += 1.
  (split case c=b+1: the [c,b] interval is empty, omit its -1.)
Rank drop: r'[(i,j)] = r[(i,j)] - 1  iff  a<=i<c and b<j<=e ; else unchanged.
  Drop rectangle D = [a, c-1] x [b+1, e].
"""
from itertools import product
from fractions import Fraction

def intervals(N):
    return [(a,b) for a in range(N+1) for b in range(a,N+1)]

def dim_vector(m, N):
    d = [0]*(N+1)
    for (a,b),mult in m.items():
        for t in range(a,b+1):
            d[t]+=mult
    return tuple(d)

def rank_pattern(m, N):
    """r[(i,j)] for i<=j, via cumul: sum of m[(a,b)] with a<=i and j<=b."""
    r={}
    for i in range(N+1):
        for j in range(i,N+1):
            s=0
            for (a,b),mult in m.items():
                if a<=i and j<=b:
                    s+=mult
            r[(i,j)]=s
    return r

def diff_from_rank(r, N):
    """Invert: m[(a,b)] = second difference of r. m[(a,b)] = r[a][b] - r[a][b+1] - r[a-1][b] + r[a-1][b+1],
    with out-of-range r = 0 (a<0 or b>N)."""
    def R(i,j):
        if i<0 or j>N or i>j:
            # r only defined on i<=j; for i>j (a>b after shift) treat as 0?
            # Standard: cumul defined for all (i,j) via the box-sum; for i<j region it is the real r.
            # For the diff we need r at (a,b),(a,b+1),(a-1,b),(a-1,b+1). All have first<=second when a<=b.
            return 0
        return r.get((i,j),0)
    m={}
    for a in range(N+1):
        for b in range(a,N+1):
            val=R(a,b)-R(a,b+1)-R(a-1,b)+R(a-1,b+1)
            m[(a,b)]=val
    return m

def le(s,r,N):
    """s <= r pointwise on the upper triangle."""
    for i in range(N+1):
        for j in range(i,N+1):
            if s[(i,j)]>r[(i,j)]:
                return False
    return True

def lt(s,r,N):
    return le(s,r,N) and any(s[(i,j)]<r[(i,j)] for i in range(N+1) for j in range(i,N+1))

def apply_box_move(m, a,c,b,e):
    """Apply linked box move with a < c <= b+1 <= e. Returns new multiplicity dict."""
    assert a < c <= b+1 <= e, (a,c,b,e)
    m2=dict(m)
    def add(key,delta):
        m2[key]=m2.get(key,0)+delta
    add((a,e),-1)
    if c<=b:           # overlapping case: [c,b] nonempty
        add((c,b),-1)
    add((a,b),+1)
    add((c,e),+1)
    return m2

def is_achievable_m(m):
    return all(v>=0 for v in m.values())

if __name__=="__main__":
    # Sanity: the (2,2,2) witness m00=m01=m12=m22=1
    N=2
    m={(0,0):1,(0,1):1,(1,2):1,(2,2):1}
    r=rank_pattern(m,N)
    print("witness m:",{k:v for k,v in m.items() if v})
    print("dim:",dim_vector(m,N))
    print("rank pattern r:",{k:v for k,v in r.items()})
    m_back=diff_from_rank(r,N)
    print("diff(r) recovers m:", {k:v for k,v in m_back.items() if v} == {k:v for k,v in m.items() if v},
          {k:v for k,v in m_back.items() if v})
