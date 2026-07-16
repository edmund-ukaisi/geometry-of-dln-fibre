import itertools
def mval(M,T):
    L=len(M)-1;v=0
    for j in range(L):
        tp=M[0] if j==0 else T[j-1];v+=(tp-T[j])*(M[j+1]-T[j])
    return v
def minAdm(M):
    L=len(M)-1
    if L==0:return 0
    bnd=[min(M[0],M[1])]+[M[j+1] for j in range(1,L)]
    best=None
    for T in itertools.product(*[range(bnd[j]+1) for j in range(L)]):
        if T[-1]!=0:continue
        if any(T[i]<T[i+1] for i in range(L-1)):continue
        v=mval(M,T);best=v if best is None or v<best else best
    return best
def rho(M):return min(M[2:])
def interior_us(M):
    r=rho(M);return [u for u in range(0,min(M[0],M[1])+1) if (M[0]-u)+(M[1]-u)<=r]

print("MERGE test: minAdm(![u+a,u,d]) >= 1 across ALL interior cells? (d=rho_d-b)")
zero=0; tot=0; zex=[]; d0=0; d0_only=0
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        for u in interior_us(M):
            M0,M1=M[0],M[1];a,b=M0-u,M1-u;d=rho(M)-b
            tot+=1
            m3=minAdm((u+a,u,d))
            if m3<1:
                zero+=1
                if d==0: d0+=1
                if len(zex)<15: zex.append((M,u,a,b,d,m3))
print(f"  interior cells={tot}  minAdm(![u+a,u,d])==0 (merge fails there): {zero}   of which d==0: {d0}")
for e in zex: print(f"   ZERO: M={e[0]} u={e[1]} a={e[2]} b={e[3]} d={e[4]} minAdm3={e[5]}")
# for the d=0 (zero) cells: confirm 2q<ub in the whole c'-window (so pure ① bounded, finite)
print("\n  d=0 cells: is 2q<ub guaranteed in c'-window? need minAdm M <= ab+ub (=> 2q<minAdm M-ab<=ub):")
bad=0
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        for u in interior_us(M):
            M0,M1=M[0],M[1];a,b=M0-u,M1-u;d=rho(M)-b
            if minAdm((u+a,u,d))<1:  # includes d=0
                if minAdm(M) > a*b+u*b: bad+=1
print(f"   d=0/zero cells with minAdm M > ab+ub (2q could reach ub, ① insufficient): {bad}")

print("\n=== REFINED: are the zero cells exactly {u=0} ∪ {a=0}?  Does merge hold for u>=1 AND a>=1? ===")
zero_genuine=0; genuine=0; z_u0=0; z_a0=0; z_other=0
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        for u in interior_us(M):
            M0,M1=M[0],M[1];a,b=M0-u,M1-u;d=rho(M)-b
            m3=minAdm((u+a,u,d))
            if m3<1:
                if u==0: z_u0+=1
                elif a==0: z_a0+=1
                else: z_other+=1
            if u>=1 and a>=1:  # genuinely interior-hard (real pivot + real obstruction block)
                genuine+=1
                if m3<1: zero_genuine+=1
print(f"  zero cells: u==0: {z_u0}   a==0 (u>=1): {z_a0}   OTHER (u>=1,a>=1): {z_other}")
print(f"  genuine interior-hard cells (u>=1 AND a>=1): {genuine}   of which minAdm3==0 (merge fails): {zero_genuine}")
print(f"  => merge {'HOLDS for all genuine (u>=1,a>=1) cells' if zero_genuine==0 else 'FAILS at %d genuine cells'%zero_genuine}")
# for a=0 cells: loss = ||B~Qb||^2 only (Y=0 since d=0), finite iff 2q<ub; confirm d=0 there
a0_d_not0=0
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        for u in interior_us(M):
            M0,M1=M[0],M[1];a,b=M0-u,M1-u;d=rho(M)-b
            if u>=1 and a==0 and d!=0: a0_d_not0+=1
print(f"  a==0 (u>=1) cells with d!=0: {a0_d_not0}  (0 => a=0 <=> d=0 <=> Y≡0, loss=||B~Qb||^2 pure)")
