"""
deepgate arity-4 exhaustive scan (EXACT Nat).

Question (the CRUX): at every deep rank-drop stratum {rank Z_deep = rho - k}, is the
LOCAL codimension INCLUDING the peeled corank det charge  det(Q_b Q_b^T)^{-a/2}
>= 2*T1_q = minAdm(M) - a*b  ?   If yes at every k -> BOUNDED. If some k undercuts -> GENUINE GAP.

Arity 4: deep tail = (M2, M3), Z_deep = single generic M2 x M3 matrix.
  rho = deepTailMin = min(M2, M3),  n = M3.
  parameter-space codim of {rank Z <= s} = determinantal = (M2 - s)(M3 - s)  [single free matrix].

Local model (derived pen-and-paper, cross-checked vs stepdesign 4.1 at k=1 and Codex ibuniform at k=rho):
  At a k-drop (k lost singular values), with d = rho - b:
    charge exponent in the lost-singular scale:  t^{ -a * max(0, k-d) }   (Q_b keeps full rank b while k<=d)
    loss local model: |y|^2 + t^2 |W_lost|^2,  y in R^{u(rho-k)}, W_lost in R^{u k}
    deep-degeneration codim (param space): kappa_k
  => codim-with-charge at k-drop:
       C*(k) = min( u*rho ,  G(k) ),   G(k) = u*(rho-k) + kappa_k - a*max(0, k-d)
  BOUNDED (deep strata do not undercut the generic threshold) iff  min_k C*(k) >= minAdm(M) - a*b.
"""
from functools import lru_cache

@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(M)
    if len(M) == 2:
        return M[0]*M[1]
    m0, m1 = M[0], M[1]
    rest = M[2:]
    best = None
    for t in range(0, min(m0, m1)+1):
        red = (t,) + rest
        val = (m0-t)*(m1-t) + minAdm(red)
        if best is None or val < best:
            best = val
    return best

def binding_cut(M):
    m0, m1 = M[0], M[1]
    rest = M[2:]
    best = None; targ = None
    for t in range(0, min(m0,m1)+1):
        red = (t,)+rest
        val = (m0-t)*(m1-t) + minAdm(red)
        if best is None or val < best:
            best = val; targ = t
    r = min(m0-targ, m1-targ)
    return targ, r

def kappa_det(M2, M3, s):
    return (M2 - s)*(M3 - s)

def analyze_cut(M, u):
    M0,M1,M2,M3 = M
    a = M0 - u; b = M1 - u
    rho = min(M2, M3); n = M3
    d = rho - b
    mA = minAdm(M)
    target = mA - a*b
    urho = u*rho
    records = []
    worst = None; worst_k = None
    for k in range(1, rho+1):
        s = rho - k
        kap = kappa_det(M2, M3, s)
        G = u*(rho-k) + kap - a*max(0, k-d)
        Cstar = min(urho, G)
        records.append((k, s, kap, G, Cstar))
        if worst is None or Cstar < worst:
            worst = Cstar; worst_k = k
    return dict(a=a,b=b,rho=rho,n=n,d=d,minAdm=mA,target=target,urho=urho,
                worst=worst, worst_k=worst_k, records=records)

def scan(Wmax=8):
    viol = []; tight = []; allcnt = 0
    for M0 in range(1,Wmax+1):
     for M1 in range(1,Wmax+1):
      for M2 in range(1,Wmax+1):
       for M3 in range(1,Wmax+1):
        M=(M0,M1,M2,M3)
        tstar, r = binding_cut(M)
        for j in range(1, r):
            u = tstar + j
            a = M0-u; b=M1-u
            if a<1 or b<1: continue
            info = analyze_cut(M,u)
            allcnt += 1
            slack_deep = info['worst'] - info['target']
            slack_urho = info['urho'] - info['target']
            if slack_deep < 0 or slack_urho < 0:
                viol.append((M,u,info,slack_deep,slack_urho))
            elif slack_deep == 0:
                tight.append((M,u,info))
    return allcnt, viol, tight

if __name__ == "__main__":
    allcnt, viol, tight = scan(Wmax=8)
    print(f"arity-4 binding strict-shell cuts scanned (widths 1..8): {allcnt}")
    print(f"VIOLATIONS (min_k C*(k) < minAdm-ab, OR u*rho < minAdm-ab): {len(viol)}")
    for (M,u,info,sd,su) in viol[:60]:
        print(f"  VIOL M={M} u={u} a={info['a']} b={info['b']} rho={info['rho']} d={info['d']} "
              f"minAdm={info['minAdm']} target(2T1q)={info['target']} worstC*={info['worst']}(k={info['worst_k']}) "
              f"urho={info['urho']}  slack_deep={sd} slack_urho={su}")
    print(f"TIGHT (min_k C*(k) == target exactly): {len(tight)}")
    for (M,u,info) in tight[:30]:
        print(f"  TIGHT M={M} u={u} a={info['a']} b={info['b']} rho={info['rho']} d={info['d']} "
              f"minAdm={info['minAdm']} target={info['target']} worstC*={info['worst']} (k={info['worst_k']})")
    print("\n--- design canonical examples ---")
    for M in [(3,3,3,3),(4,4,4,4),(3,4,4,4),(4,4,3,3),(3,3,5,5),(5,5,3,3),(3,3,7,7),(4,4,6,6),(5,5,5,5)]:
        tstar,r = binding_cut(M)
        print(f"M={M}: t*={tstar} r={r} minAdm={minAdm(M)}")
        for j in range(1,r):
            u=tstar+j; a=M[0]-u; b=M[1]-u
            if a<1 or b<1: continue
            info=analyze_cut(M,u)
            print(f"   u={u}(j={j}) a={a} b={b} rho={info['rho']} d={info['d']} target(2T1q)={info['target']} urho={info['urho']}")
            for (k,s,kap,G,Cstar) in info['records']:
                mark = "  <== charge bites (k>d)" if k>info['d'] else ""
                tightmark = "  [TIGHT=target]" if Cstar==info['target'] else ("  [UNDER target!]" if Cstar<info['target'] else "")
                print(f"       k={k} (rankZ={s}): kappa={kap} G(k)={G} C*={Cstar}{mark}{tightmark}")
