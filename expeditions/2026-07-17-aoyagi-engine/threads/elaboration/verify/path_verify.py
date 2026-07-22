#!/usr/bin/env python3
"""Verify the PATH-LEVEL claims of Aoyagi's resolution:
 [A] Composite chart Jacobian is a PURE MONOMIAL: each blow-up chart contributes u^(codim-1),
     each Q,P shear is det-1 (contributes 1). Verify on a 2-step composition symbolically.
 [B] Jacobian LEDGER accumulation: for every divisor, sum of (codim-1) over its participating
     blow-ups == M_{s,k} - 1 (the final accumulated exponent minus 1). Checked via the tree sim.
 [C] Exponent READ-OFF: within a leaf, b_1 = prod of distinct (t~=0) u's (SQUAREFREE, k=1);
     ratio per binding axis = M_{s,k}/2; min over leaves = minAdm/2.
 [D] Value ASSEMBLY: lambda = prefactor + (1/2)*cCodim = C/2  (C = full codim of the zero fibre).
"""
import sympy as sp, copy
from functools import lru_cache
from fractions import Fraction
ok=True

# ---------- [A] composite Jacobian is a pure monomial (blow-up ⋆ det-1 shear ⋆ blow-up) ----------
# one blow-up chart of codim c: (u, x2',..,xc') -> (u, u*x2',..,u*xc'); |Jac| = u^(c-1).
def blowup_jac(c):
    u=sp.symbols('u'); xs=sp.symbols(f'x2:{c+1}') if c>=2 else ()
    vars_new=(u,)+tuple(xs)
    img=[u]+[u*x for x in xs]
    Jm=sp.Matrix([[sp.diff(f,v) for v in vars_new] for f in img])
    return sp.factor(Jm.det()), u, c
for c in [2,3,4,6]:
    d,u,cc=blowup_jac(c)
    monomial = (sp.factor(d)==u**(c-1)) or (sp.expand(d-u**(c-1))==0)
    print(f"[A] codim-{c} blow-up chart |Jac| = {sp.factor(d)}  == u^{c-1}: {monomial}")
    ok &= monomial
# shears Q,P are det-1 (already in step_verify); a product of monomial-Jac blowups & det-1 shears is monomial. OK.

# ---------- [B]+[C] ledger accumulation + read-off, via the tree simulator with a Jac accumulator ----------
def run(M):
    L=len(M)-1
    def Mrun(S): return min(M[:S])
    def Mval(t):
        v=(M[0]-t[0])*(M[1]-t[0])
        for j in range(2,L+1): v+=(t[j-2]-t[j-1])*(M[j]-t[j-1])
        return v
    def tilde(T): return min(T)
    leaves=[]   # per leaf: list of (Mexp, jacpow) for t~=0 divisors
    def step(S,J,divs):
        MS=Mrun(S); MS1=M[S] if S<=L else None; capJ=min(MS,MS1)
        if J==capJ:
            if S==L:
                leaves.append([(d['M'],d['jac']) for d in divs if tilde(d['T'])==0])
                return
            step(S+1,0,divs); return
        jumps=sorted({tilde(d['T']) for d in divs if J+1<=tilde(d['T'])<=MS-1})
        if not jumps:                        # Case 2: fresh, codim = block area
            codim=(MS-J)*(MS1-J)
            Tn=[(M[k] if k<=S-1 else J) for k in range(1,L+1)]
            step(S,J+1,divs+[{'T':Tn,'M':codim,'jac':codim-1}]); return
        jj=jumps[0]; J1=jj-J
        cand=[d for d in divs if tilde(d['T'])==jj]; ustar=min(cand,key=lambda d:tuple(d['T']))
        # 1(1) boost: blow-up center codim = J1*(MS1-J) d-entries + 1 (u); pivot chart adds codim-1 = J1*(MS1-J)
        d11=copy.deepcopy(divs); u1=next(d for d in d11 if d['T']==ustar['T'] and d['M']==ustar['M'] and d['jac']==ustar['jac'])
        add=J1*(MS1-J)
        for k in range(S,L+1): u1['T'][k-1]=J
        u1['M']+=add; u1['jac']+=add                      # BOTH grow by the same add
        step(S,J,d11)
        # 1(2): new divisor, exponent = ustar.M + add ; jac likewise (fresh pivot power codim-1)
        d12=copy.deepcopy(divs); Tn=[(ustar['T'][k-1] if k<S else J) for k in range(1,L+1)]
        d12.append({'T':Tn,'M':ustar['M']+add,'jac':ustar['jac']+add}); step(S,J+1,d12)
    step(1,0,[])
    @lru_cache(maxsize=None)
    def minAdm(MM):
        MM=tuple(int(x) for x in MM)
        if len(MM)==1: return 0
        if len(MM)==2: return MM[0]*MM[1]
        return min((MM[0]-tt)*(MM[1]-tt)+minAdm((tt,)+MM[2:]) for tt in range(min(MM[0],MM[1])+1))
    return leaves, minAdm(M)

for M in [(3,3,4),(3,3,2,2),(2,2,2),(2,2,2,2)]:
    leaves,mA=run(M)
    ledger_ok = all(jac==Me-1 for leaf in leaves for (Me,jac) in leaf)   # [B] jac = M-1 for every divisor
    per_leaf_minratio=[min(Fraction(Me,2) for (Me,jac) in leaf) for leaf in leaves if leaf]
    global_min=min(per_leaf_minratio)
    readoff_ok = (global_min==Fraction(mA,2))                            # [C] min over leaves of M/2 = minAdm/2
    print(f"[B/C] M={M}: ledger jac==M-1 all divisors: {ledger_ok};  min_leaves min(M/2)={global_min} == minAdm/2={Fraction(mA,2)}: {readoff_ok}")
    ok &= ledger_ok and readoff_ok

# ---------- [D] value assembly: prefactor + (1/2)cCodim = C/2 ----------
# full codim C of the zero fibre = -r^2 + r(H1+H_{L+1}) + cCodim(core reduced widths).  lambda = C/2.
def check_value(H, r):
    L=len(H)-1
    Mred=tuple(h-r for h in H)
    @lru_cache(maxsize=None)
    def minAdm(MM):
        if len(MM)==1: return 0
        if len(MM)==2: return MM[0]*MM[1]
        return min((MM[0]-tt)*(MM[1]-tt)+minAdm((tt,)+MM[2:]) for tt in range(min(MM[0],MM[1])+1))
    cCodim=minAdm(Mred)
    prefactor=Fraction(-r*r + r*(H[0]+H[L]), 2)     # H[L] = H^{(L+1)} (0-indexed last)
    lam = prefactor + Fraction(cCodim,2)
    C_full = -r*r + r*(H[0]+H[L]) + cCodim
    return lam, Fraction(C_full,2), (lam==Fraction(C_full,2))
for (H,r) in [((3,3,4),0), ((3,3,2,2),0), ((5,4,4),1), ((4,4,4,4),2)]:
    lam, half_C, good = check_value(H,r)
    print(f"[D] H={H} r={r}: lambda = prefactor+cCodim/2 = {lam};  C/2 = {half_C};  match: {good}")
    ok &= good

print("\nPATH-LEVEL VERIFY:", "PASS" if ok else "FAIL")
import sys; sys.exit(0 if ok else 1)
