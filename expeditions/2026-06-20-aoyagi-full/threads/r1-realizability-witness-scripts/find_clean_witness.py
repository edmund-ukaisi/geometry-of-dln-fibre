# Find the CLEANEST property-breaking witness: an admissible M whose UNIQUE achiever T* has
#   (A) >=2 DISTINCT nonzero running-rank levels (running-min genuinely selects),
#   (B) a j with t*_j < min(M_0,M_j) and t*_j>0 (survivors cap non-binding),
#   (incr) an increasing-width step M_s < M_{s+1}.
# Prefer: unique achiever, smallest widths, L=3 (decide-check feasible), and ideally also a
# WIDTH-DIP M_s > M_{s+1} so the diagonal r*(i,i)=M_i is genuinely != t*_i at interior i.
from itertools import product
def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
def admPred(M,T):
    L=len(M)-1
    if any(T[j]>admBound(M,j) for j in range(L)): return False
    for i in range(L):
        for j in range(i,L):
            if T[j]>T[i]: return False
    if L>=1 and T[L-1]!=0: return False
    return True
def Adm(M):
    L=len(M)-1
    return [list(T) for T in product(*[range(admBound(M,j)+1) for j in range(L)]) if admPred(M,list(T))]
def tPrev(M,T,j): return M[0] if j==0 else T[j-1]
def Mval(M,T):
    L=len(M)-1; return sum((tPrev(M,T,j)-T[j])*(M[j+1]-T[j]) for j in range(L))
def achievers(M):
    adm=Adm(M); vals=[(T,Mval(M,T)) for T in adm]; mn=min(v for _,v in vals)
    return mn,[T for T,v in vals if v==mn]

results=[]
for M in product(range(1,7),repeat=4):  # L=3
    M=list(M)
    mn,ach=achievers(M)
    if len(ach)!=1: continue
    T=ach[0]; t=[M[0]]+list(T); L=3
    distinct_nz=sorted(set(x for x in t[1:] if x>0),reverse=True)
    A=len(distinct_nz)>=2
    Bjs=[j for j in range(1,L+1) if t[j]<min(M[0],M[j]) and t[j]>0]
    incr=[s for s in range(L) if M[s]<M[s+1]]
    if A and Bjs and incr:
        widthsum=sum(M); results.append((widthsum,M,T,t,distinct_nz,Bjs,incr,mn))
results.sort()
print(f"UNIQUE-achiever witnesses (L=3) exercising (A)+(B)+(incr), sorted by width-sum:")
for widthsum,M,T,t,dnz,Bjs,incr,mn in results[:12]:
    dip=[s for s in range(3) if M[s]>M[s+1]]
    print(f"  M={M}  T*={T}  t*={t}  minAdm={mn}  distinct-nz-levels={dnz}  (B)j={Bjs}  incr={incr}  dip={dip}")
