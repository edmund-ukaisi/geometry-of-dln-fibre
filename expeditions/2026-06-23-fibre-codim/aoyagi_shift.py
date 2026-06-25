import itertools, os
from fractions import Fraction as F
# reuse engine — read the committed sibling (reproducible from a clean checkout)
_here = os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(_here, 'aoyagi_check.py')).read().split('# ---- enumerate')[0])

def shiftedSorted(d, r):
    return sorted(max(x-r,0) for x in d)   # dminus (truncated) then ascending sort

def codimFormula(d, r):
    M = shiftedSorted(d, r)
    # cValue on the monotone M; need qipM>=1 i.e. M[0]>=1 effectively
    cv = cValue_(M) if (len(M)>=1 and qipM_(M)>=1) else None
    d0, dlast = d[0], d[-1]
    shift = r*(d0+dlast-r) if (d0+dlast)>=r else r*0  # ℕ truncation: (d0+dlast-r) truncates to 0
    # actually ℕ: max(d0+dlast-r,0)
    shift = r*max(d0+dlast-r,0)
    return (cv + shift) if cv is not None else None

def two_lambda(d, r):
    M = shiftedSorted(d, r)
    if qipM_(M) < 1: return None
    cv = cValue_(M)
    d0, dlast = d[0], d[-1]
    # 2*lambdaCore = cValue (verified); 2*lambdaShift = -r^2 + r*(d0+dlast) over ℚ
    return F(cv) + (-(r**2) + r*(d0+dlast))

fail_norankbound=[]; fail_with_rle_dlast=[]; checked=0
for N1 in range(2,5):
    for tup in itertools.combinations_with_replacement(range(1,7), N1):
        d=list(tup)
        for r in range(0, 12):   # include r > min(d) and r > d0+dlast
            M=shiftedSorted(d,r)
            if qipM_(M)<1: continue
            checked+=1
            lhs=two_lambda(d,r); rhs=codimFormula(d,r)
            if lhs is None or rhs is None: continue
            if F(lhs)!=F(rhs):
                fail_norankbound.append((d,r,lhs,rhs,min(d)))
                if r <= d[-1]:
                    fail_with_rle_dlast.append((d,r,lhs,rhs))
print(f"checked {checked} (d entries 1..6, r 0..11)")
print(f"two_lambda == codimFormula  FAILS (no rank bound): {len(fail_norankbound)}")
for x in fail_norankbound[:10]: print("   d,r,2lam,codimF,min(d):",x)
print(f"  ... of which with r <= d_last: {len(fail_with_rle_dlast)}")
for x in fail_with_rle_dlast[:10]: print("   ",x)
# Confirm: among ALL failures, is r > d0+dlast always the cause?
print(f"  all failures have r > d0+dlast ? ",
      all(r > d[0]+d[-1] for (d,r,_,_,_) in fail_norankbound))
