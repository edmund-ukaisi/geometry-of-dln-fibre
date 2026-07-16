import itertools
def mval(M,T):
    L=len(M)-1; v=0
    for j in range(L):
        tp=M[0] if j==0 else T[j-1]; v+=(tp-T[j])*(M[j+1]-T[j])
    return v
def minAdm(M):
    L=len(M)-1
    if L==0: return 0
    bnd=[min(M[0],M[1])]+[M[j+1] for j in range(1,L)]
    best=None
    for T in itertools.product(*[range(bnd[j]+1) for j in range(L)]):
        if T[-1]!=0: continue
        if any(T[i]<T[i+1] for i in range(L-1)): continue
        v=mval(M,T); best=v if best is None or v<best else best
    return best
def rho(M): return min(M[2:])

# interior cell u: a=M0-u, b=M1-u, a+b<=rho.  condition: 2c' < u*M2 + b*M0, c'<minAdm/2 => need minAdm<=u*M2+b*M0.
# BINDING: min over interior u of (u*M2 + b*M0);  b=M1-u => u*M2+(M1-u)*M0 = M0*M1 + u*(M2-M0)
print("Check: minAdm(M) <= u*M2 + (M1-u)*M0  for ALL interior u ; report worst (min RHS) per M")
def interior_us(M): 
    r=rho(M); return [u for u in range(0,min(M[0],M[1])+1) if (M[0]-u)+(M[1]-u)<=r]
fails=0; tot=0; tights=0; minmargin=999
worstex=[]
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        ius=interior_us(M)
        if not ius: continue
        ma=minAdm(M); M0,M1,M2=M[0],M[1],M[2]
        rhss=[u*M2+(M1-u)*M0 for u in ius]
        worst=min(rhss)
        tot+=1
        margin=worst-ma
        if margin<minmargin: minmargin=margin; worstex=[(M,ius,ma,worst)]
        elif margin==minmargin: worstex.append((M,ius,ma,worst))
        if ma>worst: 
            fails+=1
            if fails<=20: print(f"  FAIL M={M} interior_u={ius} minAdm={ma} > min_u(uM2+bM0)={worst}")
        elif ma==worst: tights+=1
print(f"\n  interior M's={tot}  FAILS={fails}  tight(minAdm==worst RHS)={tights}  min margin={minmargin}")
print(f"  worst-margin examples: {worstex[:6]}")

# Also compare to the PROVEN bound minAdm<=M0*min(M1,rho): is uM2+bM0 >= that automatically? not needed, direct check above suffices.
# sanity witnesses
print("\n witnesses:")
for M in [(4,4,4,4),(3,4,5,4),(5,4,5,6),(2,3,2,2)]:
    ius=interior_us(M); ma=minAdm(M)
    rhss={u:u*M[2]+(M[1]-u)*M[0] for u in ius}
    print(f"  M={M} minAdm={ma} interior_u->uM2+bM0: {rhss}  min={min(rhss.values()) if rhss else 'NA'}  ok={ma<=min(rhss.values()) if rhss else 'NA'}")
