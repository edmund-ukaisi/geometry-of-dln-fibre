from functools import lru_cache
import itertools

# ---- combinatorial spine (mirrors Lean minAdmRec / redChain / Mval) ----
def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
def is_adm(M,T):
    L=len(T)
    for j in range(L):
        if T[j]>admBound(M,j): return False
    for i in range(L):
        for j in range(L):
            if i<=j and T[j]>T[i]: return False
    if L>=1 and T[L-1]!=0: return False
    return True
def adm_cone(M):
    L=len(M)-1
    ranges=[range(admBound(M,j)+1) for j in range(L)]
    return [T for T in itertools.product(*ranges) if is_adm(M,T)]
def Mval(M,T):
    L=len(T); s=0
    for j in range(L):
        tprev=M[0] if j==0 else T[j-1]
        s+=(tprev-T[j])*(M[j+1]-T[j])
    return s
@lru_cache(None)
def minAdm(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-x)*(M[1]-x)+minAdm((x,)+M[2:]) for x in range(min(M[0],M[1])+1))

def redChain(t,M): return (t,)+M[2:]

M=(3,3,3,4)
print("M =",M,"  minAdm =",minAdm(M),"  rlct = minAdm/2 =",minAdm(M)/2)
cone=adm_cone(M); mm=minAdm(M)
binding=[T for T in cone if Mval(M,T)==mm]
print("\nALL binding admissible profiles T (Mval == minAdm):")
for T in binding:
    # trace the layer-peel charges via the native recursion (peel T0, redChain, ...)
    charges=[]; cur=M; Tj=list(T)
    for j in range(len(T)):
        t=Tj[j]
        charges.append((cur[0]-t)*(cur[1]-t))
        cur=redChain(t,cur)
    print(f"  T={T}  layer-charges={charges}  sum={sum(charges)}  (== minAdm {mm}: {sum(charges)==mm})")

# equal-run detection: consecutive equal widths M_{j}=M_{j+1} with the profile flat there
print("\nEqual-run structure of M:")
runs=[]; i=0
while i<len(M):
    j=i
    while j+1<len(M) and M[j+1]==M[i]: j+=1
    runs.append((i,j,M[i])); i=j+1
print("  runs (start,end,width):",runs)
print("  => equal run of width 3 across nodes 0..2 (layers 1,2 are 3x3); node 3 = 4.")

# Which binding profiles have an equal-run flat (t_j == t_{j-1} across an equal-width pair)?
print("\nBinding profiles with an equal-run flat (t_{j}=t_{j-1} on an equal-width pair):")
for T in binding:
    Tfull=(M[0],)+tuple(T)  # t_0 := M0 convention for run detection of the pivot
    flats=[]
    for j in range(1,len(T)):
        # layers j-1,j share width if M[j]==M[j+1]; equal-run flat if T[j-1]==T[j]
        if M[j]==M[j+1] and T[j-1]==T[j]:
            flats.append(j)
    print(f"  T={T}  equal-run-flat layers={flats}")
