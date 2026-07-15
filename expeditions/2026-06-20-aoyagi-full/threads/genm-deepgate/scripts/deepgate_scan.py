"""
UNIFIED deep-stratum codim-with-charge scan, arity 4/5/6 (EXACT).

For each binding cut u=t*+j (strict shell 1<=j<r), for every deep rank-drop k=1..rho:
   kappa_k   = CR(deep_widths, rho-k)      [exact parameter-space codim of {rank Z_deep <= rho-k}]
   G(k)      = u*(rho-k) + kappa_k - a*max(0, k-d)     d = rho-b   [charge bites only when k>d]
   C*(k)     = min( u*rho , G(k) )                     [u*rho = generic front-transverse cap]
BOUNDED (deep strata do not undercut) iff  min_k C*(k) >= minAdm(M)-a*b (=2*T1_q)  AND  u*rho >= minAdm-ab.
GENUINE GAP iff some C*(k) < minAdm(M)-a*b.
"""
from functools import lru_cache

@lru_cache(maxsize=None)
def CR(widths, s):
    v = tuple(widths)
    if len(v) == 2:
        v0, v1 = v
        return 0 if s >= min(v0, v1) else (v0 - s)*(v1 - s)
    vpm1, vp = v[-2], v[-1]
    best = None
    for r in range(0, min(vpm1, vp)+1):
        outer = (vpm1 - r)*(vp - r)
        inner = 0 if r <= s else CR(v[:-2] + (r,), s)
        val = outer + inner
        if best is None or val < best: best = val
    return best

@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(M)
    if len(M) == 2: return M[0]*M[1]
    m0, m1 = M[0], M[1]; rest = M[2:]
    best = None
    for t in range(0, min(m0, m1)+1):
        val = (m0-t)*(m1-t) + minAdm((t,)+rest)
        if best is None or val < best: best = val
    return best

def binding_cut(M):
    m0, m1 = M[0], M[1]; rest = M[2:]
    best=None; targ=None
    for t in range(0, min(m0,m1)+1):
        val=(m0-t)*(m1-t)+minAdm((t,)+rest)
        if best is None or val<best: best=val; targ=t
    return targ, min(m0-targ, m1-targ)

def analyze(M, u):
    M0, M1 = M[0], M[1]
    deep = M[2:]
    a = M0-u; b = M1-u
    rho = min(deep); n = deep[-1]; M2 = deep[0]
    d = rho - b
    mA = minAdm(M); target = mA - a*b; urho = u*rho
    recs=[]; worst=None; worst_k=None
    for k in range(1, rho+1):
        s = rho-k
        kap = CR(deep, s)
        G = u*(rho-k) + kap - a*max(0, k-d)
        Cs = min(urho, G)
        recs.append((k,s,kap,G,Cs))
        if worst is None or Cs<worst: worst=Cs; worst_k=k
    return dict(a=a,b=b,rho=rho,n=n,M2=M2,d=d,minAdm=mA,target=target,urho=urho,
                worst=worst,worst_k=worst_k,recs=recs, deep=deep)

def scan(arity, Wmax):
    """arity = number of widths - 1 (paper arity). widths tuple length = arity+1."""
    nwidths = arity+1
    viol=[]; tight=[]; cnt=0
    ranges=[range(1,Wmax+1)]*nwidths
    import itertools
    for M in itertools.product(*ranges):
        # require a genuine deep chain: skip degenerate
        tstar, r = binding_cut(M)
        for j in range(1, r):
            u = tstar+j; a=M[0]-u; b=M[1]-u
            if a<1 or b<1: continue
            info=analyze(M,u)
            # rankgen sanity: at binding strict shell a+b <= rho-1
            cnt+=1
            sd = info['worst']-info['target']
            su = info['urho']-info['target']
            rankgen_ok = (a+b <= info['rho']-1)
            if sd<0 or su<0:
                viol.append((M,u,info,sd,su,rankgen_ok))
            elif sd==0:
                tight.append((M,u,info,rankgen_ok))
    return cnt, viol, tight

if __name__=="__main__":
    for arity, Wmax in [(4,8),(5,6),(6,5)]:
        cnt, viol, tight = scan(arity, Wmax)
        print(f"=== arity {arity} (widths 1..{Wmax}): {cnt} binding strict-shell cuts ===")
        print(f"    VIOLATIONS (some C*(k) < minAdm-ab OR u*rho < minAdm-ab): {len(viol)}")
        for (M,u,info,sd,su,rg) in viol[:30]:
            print(f"      VIOL M={M} u={u} a={info['a']} b={info['b']} rho={info['rho']} d={info['d']} "
                  f"minAdm={info['minAdm']} target={info['target']} worstC*={info['worst']}(k={info['worst_k']}) "
                  f"urho={info['urho']} sd={sd} su={su} rankgen_ok={rg}")
        print(f"    TIGHT (min_k C*(k)==target): {len(tight)}")
        # show a few tight with rankgen check
        bad_rg = [x for x in tight if not x[3]]
        print(f"    (tight cases violating rankgen a+b<=rho-1: {len(bad_rg)})")
    print("\n--- spotlight: charge-biting deep strata for a few multi-layer chains ---")
    for M in [(4,4,4,4,4),(5,5,4,4,4),(4,4,4,2,4),(5,5,3,5,5),(6,6,4,4,6),(4,4,4,4,4,4)]:
        tstar,r=binding_cut(M)
        print(f"M={M} deep={M[2:]} t*={tstar} r={r} minAdm={minAdm(M)}")
        for j in range(1,r):
            u=tstar+j; a=M[0]-u; b=M[1]-u
            if a<1 or b<1: continue
            info=analyze(M,u)
            print(f"  u={u}(j={j}) a={a} b={b} rho={info['rho']} d={info['d']} target(2T1q)={info['target']} urho={info['urho']}")
            for (k,s,kap,G,Cs) in info['recs']:
                mk=" <== charge (k>d)" if k>info['d'] else ""
                tm=" [==target]" if Cs==info['target'] else (" [UNDER!]" if Cs<info['target'] else "")
                print(f"     k={k}(rankZ={s}) kappa={kap} G={G} C*={Cs}{mk}{tm}")
