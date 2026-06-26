import sympy as sp
from sympy import Integer, Rational, Abs, floor

# Exact engine cValue (LR closed form for C = codim Sigma^0, MONOTONE d, weakly increasing, d0>=1).
# Indices: d = [d_0,...,d_N], N = len-1.
# qipA(l) = sum_{i=0}^{l} d_min(i,N) - l * d_min(l,N)
# qipM = max{ l in 0..N : qipA(l) >= 0 } (findGreatest over 0..N, with Pred(1) always true)
# qipS = sum_{i=0}^{m} d_i
# qipRound a = (2S + m) div (2m)    [Int floor division]
# qipDelta = S - m*a
# cValue = ( d0^2 - sum_{i=1}^{m} (d_i - d_0)^2 + m*(a-d0)^2 + 2*(a-d0)*delta + |delta| ) / 2

def intdiv_floor(num, den):
    # Lean Int division is T-division? Lean's `/` on Int is `Int.div` = T-division (truncation toward 0)
    # BUT qipRound uses Int `/`. Mathlib `Int./` is `Int.div` which rounds toward zero (T-division).
    # For (2S+m)/(2m) with positive operands it's floor. Operands positive here, so floor == trunc.
    return num // den if (num>=0 and den>0) else int(sp.Integer(num)/sp.Integer(den))  # positive case

def qipA(d, l):
    N=len(d)-1
    s=sum(d[min(i,N)] for i in range(l+1))
    return s - l*d[min(l,N)]

def qipM(d):
    N=len(d)-1
    best=0
    for l in range(0,N+1):
        if qipA(d,l)>=0: best=l   # findGreatest: greatest l with Pred
    # Pred(1) true ensures best>=1 when N>=1
    return best

def cValue(d):
    N=len(d)-1
    assert N>=1
    m=qipM(d)
    S=sum(d[i] for i in range(m+1))
    a=(2*S+m)//(2*m)          # positive operands -> floor
    delta=S-m*a
    d0=d[0]
    val = ( d0**2
            - sum((d[i]-d0)**2 for i in range(1,m+1))
            + m*(a-d0)**2
            + 2*(a-d0)*delta
            + abs(delta) )
    assert val % 2 == 0, f"cValue not even: {val}"
    return val//2

def C_of(d, r):
    """C(d,r) = cValue(d - r) via rank shift (subtract r from each d_i). Needs r<=min(d)."""
    dr=[x-r for x in d]
    if min(dr)<0: return None
    if any(x==0 for x in dr):
        # if some d_i - r = 0, the shifted chain has a zero vertex -> zero-product locus is everything?
        # Actually width 0 means that vertex space is 0, the rank-<=0 product is automatic on that edge.
        pass
    return cValue(dr)

if __name__=="__main__":
    tests=[
        ([2,2,2],0),([2,2,2],1),([2,2,2],2),
        ([2,2,2,2],0),([2,2,2,2],1),([2,2,2,2],2),
        ([2,3,2],0),  # NOT monotone! cValue assumes monotone. test invariance separately
        ([2,2,3],0),([2,2,3],1),([2,2,3],2),  # monotone
        ([1,2,2],0),([1,2,2],1),  # monotone
        ([2,3,3],0),([2,3,3],1),([2,3,3],2),
        ([3,3,3],0),([3,3,3],1),([3,3,3],2),([3,3,3],3),
        ([2,2,2,3],0),([2,2,2,3],1),([2,2,2,3],2),
    ]
    for d,r in tests:
        print(d,"r=",r," C =", C_of(d,r))
