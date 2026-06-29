"""
M-VALIDATION of the per-piece factorization at corrected 2nd/3rd M.
Hand-built SQUARE charts (budget verified). For each: confirm
  (i) factored chart == fused chart (map equality),
  (ii) chain shears det 1 (unipotent),
  (iii) global det == u^{front} * prod_s [(det K_s)^{r_s+c_s} * lduMon_s],  front = #angular.
with EXACT sympy. lduMon_s = prod_i q_i^{2(t_s-1-i)} (lduCoreDeriv_det).
"""
import sympy as sp
from sympy import symbols, eye, zeros, Matrix, expand, factor, Poly
from decompose import build_direct, build_factored
from perpiece_v2 import chainQ, chainA

def lduMon(q):
    """q = pivot list (length t).  prod_i q_i^{2(t-1-i)}."""
    t = len(q); m = sp.Integer(1)
    for i in range(t):
        m *= q[i]**(2*(t-1-i))
    return expand(m)

def schur_block(get, Tk, Tk1):
    """B_k = [X ; K] (Tk x Tk1), K = LDU core (Tk1 x Tk1). Returns B, detK, pivots q."""
    t = Tk1; rk = Tk - Tk1
    if t == 0:
        return zeros(Tk,0), sp.Integer(1), []
    q = [get() for _ in range(t)]
    Lm = eye(t); Um = eye(t)
    for i in range(t):
        for j in range(i): Lm[i,j] = get()
    for i in range(t):
        for j in range(i+1,t): Um[i,j] = get()
    K = Lm*sp.diag(*q)*Um
    detK = sp.Integer(1)
    for qi in q: detK *= qi
    X = zeros(rk, t)
    for i in range(rk):
        for j in range(t): X[i,j] = get()
    B = zeros(Tk, Tk1)
    for i in range(rk):
        for j in range(Tk1): B[i,j] = X[i,j]
    for i in range(t):
        for j in range(Tk1): B[rk+i,j] = K[i,j]
    return B, expand(detK), q

def run(label, M, Text, leaf_pivot_pos, intR_free):
    """leaf_pivot_pos: (i,j) entry of Rfin fixed = 1.  intR_free: dict k -> list of (i,j) free-eta in R_k.
       Returns whether all checks pass + the global det."""
    L = len(M)-1
    flat = sum(M[k]*M[k+1] for k in range(L))
    # allocate coords: x0=u, then sequentially.
    coords = []
    cnt = [0]
    pool = symbols('x0:200', real=True)
    def get():
        v = pool[cnt[0]+1]; cnt[0]+=1; return v   # +1 so x0 reserved for u
    u = pool[0]
    bl = {}
    boundaries = []  # per boundary: detK, pivots, r, c
    for k in range(L):
        Tk=Text[k]; Tk1=Text[k+1]; Mk=M[k]; ck=Mk-Tk1; rk=Tk-Tk1; Mk1=M[k+1]
        identity0 = (k==0 and rk==0 and ck==0)
        if identity0:
            B = eye(Tk); detK = sp.Integer(1); q = [sp.Integer(1)]*Tk  # fixed identity, det 1
        else:
            B, detK, q = schur_block(get, Tk, Tk1)
        N = zeros(Tk1, ck)
        for i in range(Tk1):
            for j in range(ck): N[i,j] = get()
        W = zeros(ck, Mk1)
        for i in range(ck):
            for j in range(Mk1): W[i,j] = get()
        # interior R_k : fixed 0 except free-eta (u-scaled) at intR_free[k], and the structural pivot
        R = zeros(Tk, Mk)
        for (i,j) in intR_free.get(k, []):
            R[i,j] = get()
        bl[k] = {'B':B,'N':N,'W':W,'R':R}
        boundaries.append(dict(name=str(k), detK=detK, q=q, r=rk, c=ck, t=Tk1, id0=identity0))
    # leaf Rfin: Text[L] x M[L], one pivot fixed=1, rest free
    TL=Text[L]; ML=M[L]
    Rfin = zeros(TL, ML)
    for i in range(TL):
        for j in range(ML):
            if (i,j)==leaf_pivot_pos:
                Rfin[i,j] = sp.Integer(1)
            else:
                Rfin[i,j] = get()
    bl[L] = {'Rfin':Rfin}
    nfree = cnt[0]+1  # +u
    print(f"\n===== {label}: M={M} Text={Text} =====")
    print(f"   flatDim={flat}  #free coords={nfree}  square={nfree==flat}")
    if nfree != flat:
        print("   *** NON-SQUARE — fix allocation, abort ***"); return False
    Ad, Cd = build_direct(L, M, Text, bl, u)
    Af, Cfull, schur_out, shears = build_factored(L, M, Text, bl, u)
    eqA = all(expand(Ad[k]-Af[k])==zeros(*Ad[k].shape) for k in range(L))
    print("   (i) factored==fused MAP equality:", eqA)
    detsh = [shears[k].det() for k in range(L)]
    print("   (ii) chain shear dets (all 1?):", detsh, "->", all(d==1 for d in detsh))
    # global det
    vec = []
    for k in range(L):
        for i in range(Ad[k].rows):
            for j in range(Ad[k].cols): vec.append(Ad[k][i,j])
    n = len(vec)
    Xs = [u] + [pool[i+1] for i in range(cnt[0])]
    J = Matrix(n, n, lambda r,c: sp.diff(vec[r], Xs[c]))
    det = expand(J.det())
    if det==0:
        print("   *** global det 0 (degenerate) ***"); return False
    P = Poly(det, u); lo=min(m[0] for m in P.monoms()); hi=P.degree()
    print("   global det =", factor(det))
    print(f"   u-power [{lo}..{hi}] sep={lo==hi}  front={lo}")
    # predicted per-piece product
    pred = u**lo
    parts=[f"u^{lo}"]
    for s in boundaries:
        if s['id0']:
            continue
        f1 = s['detK']**(s['r']+s['c'])
        f2 = lduMon(s['q'])
        pred = pred*f1*f2
        parts.append(f"(detK_{s['name']})^{s['r']+s['c']}*lduMon_{s['name']}")
    pred = expand(pred)
    ok = (expand(det-pred)==0 or expand(det+pred)==0)
    print("   (iii) per-piece product:", " * ".join(parts))
    print("        =", factor(pred))
    print("   *** (iii) reproduces global det (up to sign)?", ok, "***")
    if not ok:
        print("   residual det/pred =", factor(expand(det)/pred))
    return eqA and all(d==1 for d in detsh) and ok
