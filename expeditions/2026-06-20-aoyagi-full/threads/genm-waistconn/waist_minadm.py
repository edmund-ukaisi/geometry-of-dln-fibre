from functools import lru_cache
from itertools import product

@lru_cache(maxsize=None)
def minadm(M):
    # M is a tuple of widths (M0,...,ML), L+1 widths, L matrices
    L1 = len(M)
    if L1 == 1:
        return 0
    if L1 == 2:
        return M[0]*M[1]
    M0,M1 = M[0],M[1]
    best = None
    for t in range(0, min(M0,M1)+1):
        red = (t,) + M[2:]
        val = (M0-t)*(M1-t) + minadm(red)
        if best is None or val < best:
            best = val
    return best

def tailmin(M):  # min(M1,...,Mlast)
    return min(M[1:])

def is_waist(M):  # M1 < min(M2,...,Mlast)  (strict front pinch)
    if len(M) < 3: return False
    return M[1] < min(M[2:])

# Enumerate chains up to widths 5, lengths 3..5 (widths incl.), and test relations
maxw = 5
print("Testing waist chains: minAdm(M) vs minAdm(M0,M1,Mlast) vs minAdm(M0,M1,min(tail)) vs M0*M1")
rows = []
for nwid in range(3,6):
    for M in product(range(1,maxw+1), repeat=nwid):
        if not is_waist(M): continue
        mA = minadm(M)
        m3_last = minadm((M[0],M[1],M[-1]))
        W = min(M[2:])
        m3_W = minadm((M[0],M[1],W))
        m00 = M[0]*M[1]
        rows.append((M, mA, m3_last, m3_W, m00))

# Check candidate identities / inequalities
def check(name, pred):
    bad = [r for r in rows if not pred(*r)]
    print(f"{name}: {'OK all '+str(len(rows)) if not bad else 'FAIL '+str(len(bad))+' e.g. '+str(bad[:4])}")

check("minAdm(M) == minAdm(M0,M1,Mlast)", lambda M,mA,m3l,m3W,m00: mA==m3l)
check("minAdm(M) <= minAdm(M0,M1,Mlast)", lambda M,mA,m3l,m3W,m00: mA<=m3l)
check("minAdm(M) == minAdm(M0,M1,W=min tail)", lambda M,mA,m3l,m3W,m00: mA==m3W)
check("minAdm(M) <= minAdm(M0,M1,W)", lambda M,mA,m3l,m3W,m00: mA<=m3W)
check("minAdm(M) == M0*M1", lambda M,mA,m3l,m3W,m00: mA==m00)
check("minAdm(M) <= M0*M1", lambda M,mA,m3l,m3W,m00: mA<=m00)
# print a few examples
print("\nExamples (M, minAdm, mA_last, mA_W, M0M1):")
for r in rows[:14]:
    print(r)
