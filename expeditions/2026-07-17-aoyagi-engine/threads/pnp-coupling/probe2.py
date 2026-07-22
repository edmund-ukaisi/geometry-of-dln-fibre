#!/usr/bin/env python3
"""
Second probe. Two experiments, exact algebra.

EXP-B (Gap B descent): is the property the descent needs = MULTI-AFFINITY (residual vanishes at each
  layer >= fromLayer set to 0, i.e. homogeneous degree-1 there), and is it (i) preserved by the fold
  regardless of shear, and (ii) NOT implied by the stated Deg1SupportedSlot conjuncts?  Also probe a
  width-3 layer so a delta=0 blow-up is NON-trivial (center has >1 coord).

EXP-A (Gap A boost): the battery's b-chain residual model resid[i][j] = r_i*(D H)[i][j].  Compare
  D = Schur-CLEARED (fresh generic block, canonShearOf output) vs D = UN-cleared (an extra gamma*beta
  cross term left in an interior entry = R_bad / identity-shear).  Does boost-readiness (Deg1 on the
  small center {u_p} U partial-block) hold for cleared and FAIL for uncleared?  Isolates the shear's role.
"""
import sympy as sp, copy

# ============================================================================================
# EXP-B : multi-affinity vs Deg1SupportedSlot, width-3, shear-independence
# ============================================================================================
print("="*92); print("EXP-B  multi-affinity is what the descent needs; shear-independent"); print("="*92)

def run_widthW(dvec, verbose=False):
    """fold on d = dvec (list of widths, len N+1). return (canon_ok, ident_ok, homogeneity_trace)."""
    N = len(dvec)-1
    Wm = {s: (dvec[s+1], dvec[s]) for s in range(N)}   # layer s block is d_{s+1} x d_s
    C = {(s,r,c): sp.Symbol(f"u_{s}_{r}_{c}") for s in range(N) for r in range(dvec[s+1]) for c in range(dvec[s])}
    ALL = list(C.values())
    def A(s): return sp.Matrix(dvec[s+1], dvec[s], lambda r,c: C[(s,r,c)])
    P = A(N-1)
    for s in range(N-2,-1,-1): P = P*A(s)
    P = sp.expand(P)
    core = [P[i,j] for i in range(dvec[N]) for j in range(dvec[0])]
    def layer_syms(s): return [C[(s,r,c)] for r in range(dvec[s+1]) for c in range(dvec[s])]
    def wmin(s): return min(dvec[:s+1])          # widthMinUpto proxy (running min of widths <= s)
    def shear_val(k,S,J,use):
        base=C[k]
        if use and k[0]==S and k[1]>J and k[2]>J and (S,k[1],J) in C and (S,J,k[2]) in C:
            return base - C[(S,k[1],J)]*C[(S,J,k[2])]
        return base
    def center(S,J):
        return [(S,r,c) for r in range(dvec[S+1]) for c in range(dvec[S]) if r>=J and c>=J and c< wmin(S)]
    def qm(S,J,use):
        p=(S,J,J); return {C[k]:(sp.Integer(1) if k==p else shear_val(k,S,J,use)) for k in C}
    def stepmap(S,J,use):
        p=(S,J,J); Cs=set(center(S,J)); out={}
        for k in C:
            v=shear_val(k,S,J,use)
            out[C[k]] = (shear_val(p,S,J,use) if k==p else (shear_val(p,S,J,use)*v if k in Cs else v))
        return out
    def maxdeg(expr,s):
        expr=sp.expand(expr)
        if expr==0: return 0
        idx=[ALL.index(x) for x in layer_syms(s)]; pol=sp.Poly(expr,*ALL)
        return max(sum(m[i] for i in idx) for m in pol.monoms())
    def homog1(expr,s):   # homogeneous degree-1 in layer s: vanishes at layer s=0 AND maxdeg<=1
        z={x:0 for x in layer_syms(s)}
        return sp.expand(sp.expand(expr).subs(z))==0 and maxdeg(expr,s)<=1
    def fold(use):
        resid=list(core); trace=[]
        # branch: each layer S: delta=1 clear at J=0 ; delta=0 clears J=1..min-1 ; rollover.
        for S in range(N-1):        # stop before last layer (terminal)
            capJ=min(wmin(S), dvec[S+1])
            for J in range(capJ):
                fromLayer = S if J==0 else S+1
                # record homogeneity from fromLayer up (multi-affinity) BEFORE stepping
                homs={s: all(homog1(r,s) for r in resid) for s in range(N)}
                bad=[s for s in range(N) if s>=fromLayer and not homs[s]]
                trace.append((S,J,fromLayer,bad))
                sub = qm(S,J,use) if J==0 else stepmap(S,J,use)
                resid=[sp.expand(r.subs(sub,simultaneous=True)) for r in resid]
        return trace
    tc=fold(True); ti=fold(False)
    return tc, ti

for dvec in [[2,2,2,2],[3,3,3,3],[2,3,2,2]]:
    tc,ti = run_widthW(dvec)
    same = (tc==ti)
    # multi-affinity (bad==[]) at every node?
    canon_ma = all(b==[] for (_,_,_,b) in tc)
    ident_ma = all(b==[] for (_,_,_,b) in ti)
    print(f"  d={dvec}:  multi-affinity(from fromLayer up) held  canon={canon_ma} ident={ident_ma}"
          f"   canon==ident trace: {same}")
    if not canon_ma:
        print("     canon bad nodes:", [(S,J,b) for (S,J,_,b) in tc if b])

# Deg1SupportedSlot does NOT imply the descent-needed homogeneity: explicit witness
print("\n  witness: F = u_{S,0,0} (a bare layer-S pivot coord).")
print("    - satisfies Deg1SupportedSlot(support=layerS, fromLayer=S): vanishes at layerS=0, per-layer deg<=1.")
print("    - NOT homogeneous in layer S+1 (no layer-(S+1) factor); strict transform qm sets pivot->1 => F(qm)=1,")
print("      a CONSTANT, so NOT supported on layer S+1.  => Deg1SupportedSlot is too weak for the descent;")
print("      MULTI-AFFINITY (vanish at each layer>=fromLayer =0) is the missing carried structure.")

# ============================================================================================
# EXP-A : boost readiness — Schur-CLEARED vs UN-cleared block (R_bad), b-chain model
# ============================================================================================
print("\n"+"="*92); print("EXP-A  boost readiness: does canonShearOf's gamma-clearing matter (vs the b-chain)?")
print("="*92)

def boost_test(cleared):
    """(2,2,2,2)-style boost parent: MS=2 rows (running-min), MS1=2 block cols, deeper H 2x1.
       b-chain (u_p-free dominant row i<J1=1 ; u_p on row i>=1).  D = 2x2 layer block.
       cleared=True: D generic fresh (Schur done).  cleared=False: inject an uncleared cross term into D[1][1]
       = the surviving gamma*beta an identity (un-Q'd) shear leaves -> R_bad."""
    up = sp.Symbol('u_p')
    # b-chain: J1=1 dominant row. r_0 = 1 (dominant, u_p-free); r_1 = u_p (non-dominant carries u_p).
    r = [sp.Integer(1), up]
    # D block fresh coords
    d = sp.Matrix(2,2, lambda i,k: sp.Symbol(f'x_{i}_{k}'))
    gam, bet = sp.Symbol('x_1_0'), sp.Symbol('x_0_1')   # pivot-col tail, pivot-row tail (interior=(1,1))
    if not cleared:
        # R_bad: the (1,1) interior entry still carries gamma*beta (Q-shear NOT applied)
        d[1,1] = sp.Symbol('x_1_1') + gam*bet
    H = sp.Matrix(2,1, lambda k,j: sp.Symbol(f'z_{k}'))
    DH = sp.expand(d*H)
    resid = [sp.expand(r[i]*DH[i,0]) for i in range(2)]
    # boost center = {u_p} U partial block (dominant rows i<J1=1, all cols) = {u_p, x_0_0, x_0_1}
    center = [up, sp.Symbol('x_0_0'), sp.Symbol('x_0_1')]
    # check Deg1SupportedOn center: vanish at center=0, and joint center-degree per monomial <=1
    def jdeg(mono, syms):
        return sum(sp.degree(sp.Poly(mono, s), s) if mono.has(s) else 0 for s in syms)
    A1 = all(sp.expand(r_.subs({c:0 for c in center}))==0 for r_ in resid)          # center->0 kills
    A2 = all(jdeg(t, center)<=1 for r_ in resid for t in (sp.expand(r_).as_ordered_terms() if r_!=0 else []))
    return A1, A2, resid, center

for cleared in (True, False):
    A1,A2,resid,center = boost_test(cleared)
    tag = "Schur-CLEARED (canonShearOf)" if cleared else "UN-cleared  (R_bad / identity shear)"
    print(f"\n  {tag}:")
    print(f"     resid[0] = {resid[0]}")
    print(f"     resid[1] = {resid[1]}")
    print(f"     boost center = {center}")
    print(f"     A1 (center->0 kills resid): {A1}    A2 (joint center-deg<=1 => Deg1SupportedOn): {A2}"
          f"    ==> boost-ready: {A1 and A2}")
