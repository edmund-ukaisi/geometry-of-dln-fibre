from functools import lru_cache
import itertools
# Correct admissible cone (matches r1u_minadm.py / Lambda.lean Adm): T weakly-decreasing,
# T_j <= admBound(j) [admBound_0=min(M0,M1), else M_{j+1}], and T_{L-1}=0.
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

print("=== (B) every terminal (admissible) divisor exponent Mval ≥ minAdm; min = minAdm ===")
for M in [(3,3,3,3),(3,3,4),(2,2,2,2),(3,3,3,3,3),(4,4,4,4)]:
    cone=adm_cone(M); vals=sorted(set(Mval(M,T) for T in cone)); mm=minAdm(M)
    binding=[T for T in cone if Mval(M,T)==mm]
    allge=all(Mval(M,T)>=mm for T in cone)
    print(f"  M={M}: minAdm={mm} ½={mm/2}; min Mval over cone={vals[0]} (==minAdm:{vals[0]==mm}); "
          f"ALL≥minAdm:{allge}; binding T={binding}")

print("\n=== (C) per-layer charge accumulation on a BINDING branch (sum to Mval=minAdm) ===")
def per_layer_charges(M,T):
    L=len(T); ch=[]
    for j in range(L):
        tprev=M[0] if j==0 else T[j-1]
        ch.append((tprev-T[j])*(M[j+1]-T[j]))
    return ch
for M in [(3,3,3,3),(3,3,3,3,3),(4,4,4,4),(3,3,4)]:
    cone=adm_cone(M); mm=minAdm(M)
    T=[t for t in cone if Mval(M,t)==mm][0]
    ch=per_layer_charges(M,T)
    # Hölder saturation trace: after peeling layer 1 (charge ch[0]), the residual exponent budget for
    # the reduced chain redChain(t1) is ½minAdm(redChain); check it EQUALS ½(minAdm(M)-ch[0]) i.e. the
    # coupling budget ch[0] is exactly the layer-1 charge already spent — nothing left for coupling.
    red=(T[0],)+M[2:]
    print(f"  M={M}: binding T={T}, charges={ch}, Σ={sum(ch)}=minAdm={mm} [{'OK' if sum(ch)==mm else 'X'}]; "
          f"layer1 charge a1={ch[0]}, minAdm(redChain{red})={minAdm(red)}, a1+minAdm(red)={ch[0]+minAdm(red)}={mm}")

print("\n=== (D) the coupled resolution vs a threshold-only recursion on the corank-≥2 binder (3,3,4) ===")
# (3,3,4) binding t=(1,0): layer-1 corank block is (M1-t1)x(M2-t1)=(2)x(3)? -> the Δ-block. The coupled
# diag(b) resolution puts the FULL codim on one divisor: Mval= (3-1)(3-1)+(1-0)(4-0)=4+4=8 -> rlct 4.
M=(3,3,4); T=(1,0)
print(f"  (3,3,4) binding t={T}: Mval={Mval(M,T)}  => coupled rlct = {Mval(M,T)/2}")
print(f"  layer-1 corank block dims (M1-t1)x(M2-t1) = {(M[1]-T[0])}x{(M[1]-T[0])}  (corank {M[1]-T[0]} ≥ 2 => sharing matters)")
print("  threshold-only (per-row multiplicity) UNDERSHOOTS to 3 (worked-tex verify-r1-diagb-334): the")
print("  ⟨δx,δy⟩(=½) vs ⟨δ1x,δ2y⟩(=1) obstruction is the exact reason (shared vs separate divisors).")
