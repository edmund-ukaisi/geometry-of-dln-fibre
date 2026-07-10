"""
Case-2 adjudication: printed (actual-width) pivot vector vs the prefix-min "correction".
Source-pinned formulas (Aoyagi 2023, p.20 + p.22, 1-indexed M^{(1..L+1)}):

  p.20 (Case-2 step at stage S, block dropped, chart index J):
     pivot vector   t^{(i)} = M^{(i+1)}  (i=1..S-1),   t^{(i)} = J  (i=S..L)
     divisor exp    M'_{S,J+1} = (M(S) - J)(M^{(S+1)} - J),   M(S) = prefix-min = min{M^{(1)},...,M^{(S)}}
  p.22 (terminal accumulated exponent, RLCT candidate = 1/2 min{M_{s,k}: t~=0}):
     M_{s,k} = (M^{(1)}-t^{(1)})(M^{(2)}-t^{(1)}) + sum_{j=2}^{L} (t^{(j-1)}-t^{(j)})(M^{(j+1)}-t^{(j)})
     admissibility (reindexed): H_j <= H_{j-1}, H_j <= M^{(S_{j+1})}, H_ell = 0.

We test, over many chains INCLUDING M(S) < M^{(S)} (narrow-early-layer):
  (a) Mval(printed Case-2 vector, J=0)  ==  M^{(S)} * M^{(S+1)}   (the telescoping claim)
  (b) is  M^{(S)} M^{(S+1)}  >= minAdm  (printed never binds)?
  (c) is the prefix-min single-step codim  M(S) M^{(S+1)}  >= minAdm  (does the prefix-min form bind)?
  (d) does the naive "prefix-min pivot vector" (t^{(i)} = M(i+1)) stay admissible / nonnegative,
      or does it produce sub-2lambda / negative Mval (lessons.md claim)?
"""
from functools import lru_cache
from itertools import product

# 1-indexed helpers: M is a python tuple (M^{(1)},...,M^{(L+1)}), length L+1.
def prefmin(M, S):  # M(S) = min{M^{(1)},...,M^{(S)}}, 1-indexed  -> M[0..S-1]
    return min(M[:S])

@lru_cache(None)
def minAdm(M):
    M = tuple(M)
    if len(M) == 2:
        return M[0]*M[1]
    best = None
    for t in range(min(M[0], M[1]) + 1):
        red = (t,) + M[2:]                       # peel front two widths -> pivot rank t
        v = (M[0]-t)*(M[1]-t) + minAdm(red)
        best = v if best is None else min(best, v)
    return best

def Mval(M, t):
    """p.22 terminal exponent, t = (t^{(1)},...,t^{(L)}), 1-indexed widths M^{(1..L+1)}."""
    L = len(M) - 1
    assert len(t) == L
    val = (M[0]-t[0])*(M[1]-t[0])                 # (M^{(1)}-t1)(M^{(2)}-t1)
    for j in range(2, L+1):                       # j = 2..L
        val += (t[j-2]-t[j-1])*(M[j]-t[j-1])      # (t^{(j-1)}-t^{(j)})(M^{(j+1)}-t^{(j)})
    return val

def printed_case2_vector(M, S, J=0):
    """p.20: t^{(i)}=M^{(i+1)} (i<S), t^{(i)}=J (i>=S).  1-indexed -> python list len L."""
    L = len(M) - 1
    return [ (M[i] if (i+1) < S else J) for i in range(L) ]   # t^{(i+1)} in python i; M^{(i+2)}=M[i+1]... careful below

def printed_case2_vector_correct(M, S, J=0):
    L = len(M) - 1
    t = []
    for i in range(1, L+1):                       # i = 1..L (Aoyagi index)
        if i < S:
            t.append(M[i])                        # t^{(i)} = M^{(i+1)} = M[i] (0-based python)
        else:
            t.append(J)
    return t

def prefmin_case2_vector(M, S, J=0):
    """the 'correction': t^{(i)} = M(i+1) (prefix-min) for i<S, else J."""
    L = len(M) - 1
    t = []
    for i in range(1, L+1):
        if i < S:
            t.append(prefmin(M, i+1))             # M(i+1) prefix-min
        else:
            t.append(J)
    return t

# ---------------------------------------------------------------------------
print("="*78)
print("(a) telescoping check: Mval(printed Case-2 vector, J=0) == M^{(S)} M^{(S+1)} ?")
print("="*78)
fails_a = 0
tested = 0
for L in [2,3,4]:
    for M in product(range(1,5), repeat=L+1):
        for S in range(1, L+1):
            t = printed_case2_vector_correct(M, S, 0)
            lhs = Mval(M, t)
            rhs = M[S-1]*M[S]                      # M^{(S)} M^{(S+1)} = M[S-1]*M[S]
            tested += 1
            if lhs != rhs:
                fails_a += 1
                if fails_a <= 5:
                    print(f"  FAIL M={M} S={S}: Mval={lhs} vs M^(S)M^(S+1)={rhs}")
print(f"  tested {tested},  telescoping failures: {fails_a}")

print()
print("="*78)
print("(b)/(c): does the printed (actual) or prefix-min single-step codim bind (< minAdm)?")
print("="*78)
printed_binds = 0; pref_binds = 0; examples_pref = []
tested = 0
for L in [2,3,4]:
    for M in product(range(1,5), repeat=L+1):
        ma = minAdm(M)
        for S in range(1, L+1):
            printed_exp = M[S-1]*M[S]              # actual widths (terminal Mval of printed vector)
            pref_exp    = prefmin(M,S)*M[S]        # prefix-min single-step codim (M(S) M^{(S+1)})
            tested += 1
            if printed_exp < ma:
                printed_binds += 1
            if pref_exp < ma:
                pref_binds += 1
                if len(examples_pref) < 8:
                    examples_pref.append((M,S,pref_exp,ma))
print(f"  tested {tested} (M,S) pairs, minAdm ground truth")
print(f"  PRINTED  M^(S)M^(S+1) < minAdm  count: {printed_binds}   (0 => printed NEVER binds)")
print(f"  PREFMIN  M(S)M^(S+1)  < minAdm  count: {pref_binds}")
for (M,S,pe,ma) in examples_pref:
    print(f"     e.g. M={M} S={S}: prefmin-codim M(S)M^(S+1)={pe} < minAdm={ma}  (M(S)={prefmin(M,S)}<M^(S)={M[S-1]})")

print()
print("="*78)
print("(d): the prefix-min PIVOT VECTOR 'correction' -- admissible? sub-2lambda / negative Mval?")
print("="*78)
neg = 0; sub = 0; inadm = 0; ex = []
tested = 0
for L in [2,3,4]:
    for M in product(range(1,5), repeat=L+1):
        ma = minAdm(M)
        for S in range(1, L+1):
            t = prefmin_case2_vector(M, S, 0)
            # admissibility (p.22): weakly decreasing, t^{(j)} <= M^{(j+1)}, last handled
            wd = all(t[i] >= t[i+1] for i in range(len(t)-1))
            bound = all(t[i] <= M[i+1] for i in range(len(t)))   # t^{(i)} <= M^{(i+1)}
            v = Mval(M, t)
            tested += 1
            if v < 0: neg += 1
            if v < ma: sub += 1
            if not (wd and bound):
                inadm += 1
            if (v < 0 or not (wd and bound)) and len(ex) < 8:
                ex.append((M,S,t,v,ma,wd,bound))
print(f"  tested {tested}: prefix-min pivot-vector Mval  negative: {neg},  < minAdm: {sub},  inadmissible: {inadm}")
for (M,S,t,v,ma,wd,bound) in ex:
    print(f"     M={M} S={S}: t={t} Mval={v} (minAdm={ma})  weaklyDecr={wd} boundOK={bound}")
