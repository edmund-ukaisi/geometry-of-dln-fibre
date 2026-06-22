"""Exact-arithmetic reimplementation of Core.CTheta (codimForm, kostantPartitions, cCodim, numTop).
Mirrors the Lean definitions exactly. Integer arithmetic only (no float)."""
from itertools import product
from functools import lru_cache
from math import comb

def intervals(N):
    # all [i,j] with 0 <= i <= j <= N
    return [(i,j) for i in range(N+1) for j in range(i, N+1)]

def kostant_partitions(d, r):
    """All m : dict {(i,j):mult} with 0<=i<=j<=N, d_k = sum_{i<=k<=j} m_{ij}, m_{0N}=r.
    Returns list of dicts. Bound m_{ij} <= d_i (since i in [i,j])."""
    N = len(d) - 1
    ivs = intervals(N)
    # candidate ranges: m_{ij} in 0..d_i, but m_{0N} fixed = r
    ranges = []
    for (i,j) in ivs:
        if (i,j) == (0,N):
            ranges.append([r])
        else:
            ranges.append(range(d[i]+1))
    out = []
    for combo in product(*ranges):
        m = {iv: c for iv, c in zip(ivs, combo)}
        ok = True
        for k in range(N+1):
            s = sum(m[(i,j)] for (i,j) in ivs if i <= k <= j)
            if s != d[k]:
                ok = False; break
        if ok:
            out.append(m)
    return out

def codimForm(N, m):
    """codimForm = sum over 1<=i<=u<=j<=v<=N of m[(i-1,j-1)] * m[(u,v)].
    m is a dict over intervals (0..N box); missing keys are 0."""
    def mm(a,b):
        return m.get((a,b), 0)
    total = 0
    for i in range(1, N+1):
        for u in range(i, N+1):
            for j in range(u, N+1):
                for v in range(j, N+1):
                    total += mm(i-1, j-1) * mm(u, v)
    return total

def cCodim_numTop(d, r):
    N = len(d) - 1
    parts = kostant_partitions(d, r)
    if not parts:
        return None, 0, []
    vals = [codimForm(N, m) for m in parts]
    C = min(vals)
    theta = sum(1 for v in vals if v == C)
    return C, theta, vals

# --- reindexed "Ext-pairing" form, per lean/CLAUDE.md gotcha ---
# codimForm = sum over A=[a,b], B=[c,e] with a<c<=b+1 and b<e of mbar(A)*mbar(B)
# where mbar(A) = m[A]. Let's CHECK this matches codimForm.
def codimForm_pairing(N, m):
    ivs = intervals(N)
    total = 0
    for (a,b) in ivs:
        for (c,e) in ivs:
            if a < c <= b+1 and b < e:
                total += m.get((a,b),0) * m.get((c,e),0)
    return total

if __name__ == "__main__":
    # sanity: the two forms agree
    import random
    for _ in range(2000):
        N = random.randint(1,4)
        d = [random.randint(0,3) for _ in range(N+1)]
        for m in kostant_partitions(d, 0)[:5]:
            a = codimForm(N, m); b = codimForm_pairing(N, m)
            assert a == b, (N, d, m, a, b)
    print("codimForm == codimForm_pairing : OK (reindexed Ext-pairing form confirmed)")

# --- fast constructive Kostant enumerator ---
def kostant_fast(d, r):
    """Enumerate Kostant partitions by sweeping vertices left->right.
    State: for each open interval start i<=current k, how many copies are 'open'
    (will close at some j>=k). At vertex k we must have (open intervals covering k) == d[k].
    We decide, at each vertex, how many currently-open laces close here and how many new ones open.
    Equivalent: m_{ij} = number of laces with span [i,j]. We track active laces by their start.
    """
    N=len(d)-1
    results=[]
    # active[i] = number of laces currently open that started at column i (i<=k), still uncovered-by-close
    # At column k: total open = sum active must equal? No: a lace [i,j] covers columns i..j.
    # Standard: process columns; 'rows' = laces. At column k, #laces covering k = d[k].
    # Transition k->k+1: some laces covering k end at k (don't cover k+1); new laces may start at k+1.
    # We enumerate, for each lace covering k, whether it ends at k. And new laces starting k+1.
    # Represent laces by start index; m[(i,j)] computed at close.
    # state: multiset of starts of laces currently 'alive' covering current column.
    from collections import Counter
    def rec(k, alive, m):
        # alive: Counter {start: count} of laces covering column k-? -> we set so that at column k, alive covers k
        if k==N:
            # all alive laces must close at N (j=N). record their starts.
            mm=dict(m)
            for i,c in alive.items():
                if c: mm[(i,N)]=mm.get((i,N),0)+c
            # corner check
            if mm.get((0,N),0)==r:
                results.append(mm)
            return
        # decide how many of the alive laces (by start) close at column k (j=k)
        # then new laces opening at k+1. Constraint at k+1: alive_next covers d[k+1].
        # alive currently covers d[k] (invariant). For each start i, choose 0..count to close at k.
        starts=sorted(alive)
        def choose(idx, closed):
            if idx==len(starts):
                # closed: Counter of how many laces ended at k by start
                # remaining alive after closing
                remaining=Counter()
                for i in starts:
                    rem=alive[i]-closed.get(i,0)
                    if rem: remaining[i]=rem
                stay=sum(remaining.values())
                # need new laces starting at k+1: count = d[k+1]-stay, must be >=0
                new=d[k+1]-stay
                if new<0: return
                m2=dict(m)
                for i,c in closed.items():
                    if c: m2[(i,k)]=m2.get((i,k),0)+c
                nxt=Counter(remaining)
                if new>0: nxt[k+1]=nxt.get(k+1,0)+new
                rec(k+1, nxt, m2)
                return
            i=starts[idx]
            for c in range(alive[i]+1):
                cl=dict(closed); 
                if c: cl[i]=c
                choose(idx+1, cl)
        choose(0, {})
    # init at column 0: d[0] laces start at 0
    start=Counter()
    if d[0]>0: start[0]=d[0]
    if N==0:
        # single column: m_{00}=d0, corner (0,0)=r
        if d[0]==r: return [{(0,0):d[0]}] if d[0]>0 else ([{}] if r==0 else [])
        return []
    rec(0, start, {})
    return results

def cCodim_numTop_fast(d,r):
    N=len(d)-1
    parts=kostant_fast(d,r)
    if not parts: return None,0
    vals=[codimForm(N,m) for m in parts]
    C=min(vals)
    return C, sum(1 for v in vals if v==C)
