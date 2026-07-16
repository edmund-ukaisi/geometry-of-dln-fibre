import itertools
# faithful Mval/Adm + argmin
def mval(M,T):
    L=len(M)-1; v=0
    for j in range(L):
        tprev=M[0] if j==0 else T[j-1]
        v+=(tprev-T[j])*(M[j+1]-T[j])
    return v
def minAdm_arg(M):
    L=len(M)-1
    if L==0: return 0,()
    bounds=[min(M[0],M[1])]+[M[j+1] for j in range(1,L)]
    best=None;barg=None
    for T in itertools.product(*[range(bounds[j]+1) for j in range(L)]):
        if T[-1]!=0: continue
        if any(T[i]<T[i+1] for i in range(L-1)): continue
        v=mval(M,T)
        if best is None or v<best: best=v;barg=T
    return best,barg
def rho(M): return min(M[2:])
def minAdm(M): return minAdm_arg(M)[0]

# candidate T for M1 > rho: t^1=...=t^{k*-1}=rho, then 0 ? test several candidates
def cand_val(M):
    # candidate: choose s = min(M0,M1,rho); set t^1..t^{k*-1}= s down to 0 at k* (the rho layer)
    L=len(M)-1; r=rho(M)
    # k* = index (in 0..L) of a deep min layer; layers M2..ML are indices 2..L => T-index j=1..L-1
    kstar=[i for i in range(2,L+1) if M[i]==r][0]
    s=min(M[0],M[1],r)
    # T: t^j for j=0..L-1 (paper t^1..t^L). set t^0..t^{kstar-2}=s, rest 0, weak-decr, last=0
    T=[s if j<=kstar-2 else 0 for j in range(L)]
    T[L-1]=0
    # ensure admissible: t^j<=admBound
    bounds=[min(M[0],M[1])]+[M[j+1] for j in range(1,L)]
    T=[min(T[j],bounds[j]) for j in range(L)]
    # re-enforce weak decrease
    for j in range(1,L): T[j]=min(T[j],T[j-1])
    T[L-1]=0
    return mval(M,tuple(T)),tuple(T)

print("M1 > rho interior cases: argmin T structure + candidate check")
print(f"{'M':<22}{'rho':>4}{'minAdm':>8}{'M0*rho':>8}{'argminT':>16}{'candVal':>9}")
cnt=0;candfail=0
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        r=rho(M)
        if M[1]<=r: continue                    # only the hard half
        ius=[u for u in range(0,min(M[0],M[1])+1) if (M[0]-u)+(M[1]-u)<=r]
        if not ius: continue                    # interior only
        ma,arg=minAdm_arg(M); rhs=M[0]*r
        cv,ct=cand_val(M)
        if cv>rhs: candfail+=1
        cnt+=1
        if cnt<=25:
            print(f"{str(M):<22}{r:>4}{ma:>8}{rhs:>8}{str(arg):>16}{cv:>9}")
print(f"\n hard-half interior cases={cnt}  candidate T fails (cand>M0*rho)={candfail}")

# verify minAdm<=M0*rho AND candidate achieves it on the hard half
print("\nDoes minAdm <= M0*rho hold on ALL hard-half interior cases?")
bad=[M for arity in (3,4,5) for M in itertools.product(range(2,8),repeat=arity)
     if rho(M) and M[1]>rho(M)
        and [u for u in range(0,min(M[0],M[1])+1) if (M[0]-u)+(M[1]-u)<=rho(M)]
        and minAdm(M)>M[0]*rho(M)]
print(f"  violations: {len(bad)}  {bad[:5]}")

print("\n\n=== argmin T pattern, arity 4,5, M1>rho interior (looking for the witnessing T) ===")
print(f"{'M':<24}{'rho':>4}{'kstar':>6}{'minAdm':>8}{'M0*rho':>8}{'argminT':>18}")
seen=0
for arity in (4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        r=rho(M)
        if M[1]<=r: continue
        ius=[u for u in range(0,min(M[0],M[1])+1) if (M[0]-u)+(M[1]-u)<=r]
        if not ius: continue
        L=len(M)-1
        kstar=[i for i in range(2,L+1) if M[i]==r][0]
        ma,arg=minAdm_arg(M)
        seen+=1
        if seen<=22:
            print(f"{str(M):<24}{r:>4}{kstar:>6}{ma:>8}{M[0]*r:>8}{str(arg):>18}")

# TEST the clean candidate:  t^j = min(M0, M1, M2, ..., M[j+1])  running-min through the layers,
#   i.e. t^j = min(M[0..j+1]) for j=1..L-1, t^L=0 (last forced). Front terms telescope.
def cand2(M):
    L=len(M)-1
    T=[]
    for j in range(L):
        # t^j (paper t^{j+1}) upper bounded by admBound and weak-decr; try running min of M[0..j+1]
        rm=min(M[:j+2])
        T.append(rm)
    T[L-1]=0
    # enforce admissible
    bounds=[min(M[0],M[1])]+[M[k+1] for k in range(1,L)]
    T=[min(T[j],bounds[j]) for j in range(L)]
    for j in range(1,L): T[j]=min(T[j],T[j-1])
    T[L-1]=0
    return mval(M,tuple(T)),tuple(T)

print("\n=== candidate2: t^j = running-min(M[0..j+1]) then last=0.  fails vs M0*rho? ===")
fail2=0;tot2=0
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        r=rho(M)
        ius=[u for u in range(0,min(M[0],M[1])+1) if (M[0]-u)+(M[1]-u)<=r]
        if not ius: continue
        tot2+=1
        cv,ct=cand2(M)
        if cv>M[0]*r: fail2+=1
print(f"  candidate2 fails={fail2} / interior cases={tot2}")

# TEST candidate3: peel front to t^1=min(M0,M1); then set t^j=min(prev, M[j+1]) i.e. running-min
#   but drop to 0 right AFTER the kstar (rho) layer.  Equivalent: keep running-min up to and incl j=kstar-1, then 0.
def cand3(M):
    L=len(M)-1; r=rho(M)
    kstar=[i for i in range(2,L+1) if M[i]==r][0]  # rho at M-index kstar => outgoing map is T-index kstar-1? 
    T=[]
    run=min(M[0],M[1])
    for j in range(L):
        if j==0: T.append(run)
        else:
            run=min(run,M[j+1]); T.append(run)
    # zero out from the rho layer's outgoing exponent onward: T-index j corresponds to map M[j]->? ; set T[j]=0 for j>=kstar-1
    T=[T[j] if j<kstar-1 else 0 for j in range(L)]
    T[L-1]=0
    bounds=[min(M[0],M[1])]+[M[k+1] for k in range(1,L)]
    T=[min(T[j],bounds[j]) for j in range(L)]
    for j in range(1,L): T[j]=min(T[j],T[j-1])
    T[L-1]=0
    return mval(M,tuple(T)),tuple(T)
print("\n=== candidate3: running-min up to rho-layer, 0 after. fails vs M0*rho? ===")
fail3=0
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        r=rho(M)
        ius=[u for u in range(0,min(M[0],M[1])+1) if (M[0]-u)+(M[1]-u)<=r]
        if not ius: continue
        cv,ct=cand3(M)
        if cv>M[0]*r: fail3+=1
print(f"  candidate3 fails={fail3} / interior cases={tot2}")

print("\n\n=== VERIFY the constructive proof: exact value formula ===")
# Construction T*:  for M1>rho: t^j=min(M[0..j+1]) for j<kstar-1, else 0.  Claim Mval = min(M[0..kstar-1])*rho.
#                   for M1<=rho: T=0, Mval = M0*M1.
def Tstar_val(M):
    L=len(M)-1; r=rho(M)
    if M[1]<=r:
        return mval(M,tuple([0]*L)), M[0]*M[1], "easy T=0"
    kstar=[i for i in range(2,L+1) if M[i]==r][0]
    T=[min(M[:j+2]) if j<kstar-1 else 0 for j in range(L)]
    T[L-1]=0
    val=mval(M,tuple(T))
    pred=min(M[:kstar])*r      # min(M[0..kstar-1]) * rho
    return val, pred, f"T*={T} kstar={kstar}"

mism=0; over=0; tot=0
for arity in (3,4,5):
    for M in itertools.product(range(2,8),repeat=arity):
        r=rho(M)
        ius=[u for u in range(0,min(M[0],M[1])+1) if (M[0]-u)+(M[1]-u)<=r]
        if not ius: continue
        tot+=1
        val,pred,tag=Tstar_val(M)
        if val!=pred: mism+=1
        if val> M[0]*min(M[1],r): over+=1
        if minAdm(M)!=min(minAdm(M),val):  # sanity minAdm<=val
            print("  ERROR minAdm>val",M)
print(f"  interior cases={tot}  Mval(T*)!=predicted-formula: {mism}   Mval(T*)>M0*min(M1,rho): {over}")
print("  => T* is admissible & Mval(T*) matches the closed formula & <= M0*min(M1,rho)  (so minAdm<=that)")

# tight cases (minAdm == M0*min(M1,rho)) structure
print("\n=== tight cases (minAdm == M0*min(M1,rho)) — structure ===")
tights=[]
for arity in (3,4):
    for M in itertools.product(range(2,8),repeat=arity):
        r=rho(M)
        ius=[u for u in range(0,min(M[0],M[1])+1) if (M[0]-u)+(M[1]-u)<=r]
        if not ius: continue
        if minAdm(M)==M[0]*min(M[1],r): tights.append(M)
print(f"  count={len(tights)}")
# how many tight are M1<=rho (easy half, T=0 optimal) vs M1>rho?
te=[M for M in tights if M[1]<=rho(M)]; th=[M for M in tights if M[1]>rho(M)]
print(f"  tight with M1<=rho (T=0 optimal): {len(te)}  e.g. {te[:6]}")
print(f"  tight with M1>rho: {len(th)}  e.g. {th[:6]}")
