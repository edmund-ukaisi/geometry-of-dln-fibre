from functools import lru_cache
from itertools import product

@lru_cache(maxsize=None)
def minadm(M):
    L1=len(M)
    if L1==1: return 0
    if L1==2: return M[0]*M[1]
    M0,M1=M[0],M[1]
    return min((M0-t)*(M1-t)+minadm((t,)+M[2:]) for t in range(min(M0,M1)+1))

def is_waist(M):
    return len(M)>=3 and M[1] < min(M[2:])

maxw=6
rows=[]
for nw in range(3,6):
    for M in product(range(1,maxw+1),repeat=nw):
        if not is_waist(M): continue
        mA=minadm(M)
        m_MM1=minadm((M[0],M[1],M[1]))          # Cholesky-effective (M0,M1,M1)
        m_last=minadm((M[0],M[1],M[-1]))
        m_tail=minadm(M[1:])                     # tail subchain (M1,...,Mlast)
        # candidate: does minAdm(M) = (M0-M1... ) hmm; also peel-off-A0 relation:
        # I(M) via free front A0 (M0xM1) + tail: front charge M0*M1? tail charge minAdm(tail)?
        rows.append((M,mA,m_MM1,m_last,m_tail))

def chk(name,p):
    bad=[r for r in rows if not p(*r)]
    print(f"{name}: {'OK '+str(len(rows)) if not bad else 'FAIL '+str(len(bad))+' eg '+str(bad[:5])}")

# thresholds for candidate targets
chk("minAdm(M) <= minAdm(M0,M1,M1)", lambda M,a,mm,ml,mt: a<=mm)
chk("minAdm(M) == minAdm(M0,M1,M1)", lambda M,a,mm,ml,mt: a==mm)
# tail-IH 'charges add' candidate: minAdm(M) == M0*M1 - correction? or relation to tail
chk("minAdm(M) == minAdm(M0,M1,M1) MIN minAdm(M0,M1,Mlast)", lambda M,a,mm,ml,mt: a==min(mm,ml))
# free-front-peel: does minAdm(M) <= M0*M1 (front) AND relation
chk("minAdm(M) <= min(M0*M1, M0*minAdm? )", lambda M,a,mm,ml,mt: a<=M[0]*M[1])
# is minAdm(M) determined by (M0,M1, min-over-tail-of-rest)? test tail collapse
print("\n examples (M, minAdm, mA(M0,M1,M1), mA(M0,M1,Mlast), minAdm(tail)):")
for r in rows[:20]: print(r)
# specifically the (2,1,2,2) and deep-waist tailMinWidth-small-vs-ab
for M in [(2,1,2),(2,1,2,2),(3,1,2,3),(4,3,4),(4,3,4,4),(3,2,4),(5,2,3,3)]:
    if len(M)>=3:
        print(M,"minAdm",minadm(M),"| (M0,M1,M1)",minadm((M[0],M[1],M[1])),"| (M0,M1,Ml)",minadm((M[0],M[1],M[-1])),"| tail",minadm(M[1:]))

print("\n=== tail-IH threshold coverage: minAdm(tail=(M1..Mlast)) >= minAdm(M) ? ===")
bad=[r for r in rows if not (minadm(r[0][1:]) >= r[1])]
print("minAdm(tail) >= minAdm(M):", "OK all "+str(len(rows)) if not bad else "FAIL "+str(len(bad))+" eg "+str(bad[:5]))
# also for ALL chains (not just waist) - is dropHead IH always >= ? 
allbad=[]
for nw in range(3,6):
    for M in product(range(1,7),repeat=nw):
        if minadm(M[1:]) < minadm(M): allbad.append((M,minadm(M),minadm(M[1:])))
print("minAdm(dropHead M) >= minAdm(M) for ALL chains:", "OK" if not allbad else "FAIL "+str(len(allbad))+" eg "+str(allbad[:5]))
