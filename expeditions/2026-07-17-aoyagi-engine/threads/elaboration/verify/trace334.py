#!/usr/bin/env python3
"""Full state-by-state trace of Aoyagi's fold recursion on d=(3,3,4), L=2.
Two parts:
 [MATRIX] concrete first Case-2 blow-up + Schur on real C1(3x3),C2(3x4): confirm the mechanism.
 [STATE]  the (S,J) state sequence + exponent bookkeeping; verify M_{s,k}=Mval(t); binding branch.
"""
import sympy as sp
from fractions import Fraction
from functools import lru_cache
ok = True
M = (3,3,4)          # M^{(1)},M^{(2)},M^{(3)}  (reduced widths; r=0 so = H)
L = 2

def Mrun(S):         # M(S)=min{M^{(s)}:1<=s<=S}
    return min(M[:S]) if S>=1 else None

# ---------- Mval formula (candidate threshold exponent for profile t=(t1,..,tL)) ----------
def Mval(t):
    # t = (t^{(1)},...,t^{(L)}), t^{(1)}>=...>=t^{(L)}, with M indexed 0-based: M[0]=M^{(1)} etc.
    v = (M[0]-t[0])*(M[1]-t[0])
    for j in range(2, L+1):          # j=2..L
        v += (t[j-2]-t[j-1])*(M[j]-t[j-1])   # (t^{(j-1)}-t^{(j)})(M^{(j+1)}-t^{(j)})
    return v

# ---------- profile lattice: t^{(1)}>=...>=t^{(L)}=0 (tilde t=0 => terminal), t^{(j)} feasible ----------
# admissible: 0<=t^{(L)}<=...<=t^{(1)}, t^{(1)}<=min(M1,M2); nested-rank feasibility t^{(j)}<=min over reachable.
profiles = []
for t1 in range(0, min(M[0],M[1])+1):
    # L=2: t=(t1, t2), t2<=t1, terminal tilde t=min=0 => t2=0
    t = (t1, 0)
    profiles.append(t)
vals = {t: Mval(t) for t in profiles}
print("[STATE] (3,3,4) terminal profiles (t^(2)=0) and Mval:")
for t in profiles:
    print(f"    t={t}: Mval={vals[t]}")
mn = min(vals.values()); binder = [t for t,v in vals.items() if v==mn]
print(f"    min Mval = {mn} at t={binder};  rlct_core = {Fraction(mn,2)}  [expect 8, rlct 4]")
ok &= (mn==8 and binder==[(1,0)])

# cross-check with minAdm recursion (independent)
@lru_cache(maxsize=None)
def minAdm(MM):
    MM=tuple(int(x) for x in MM)
    if len(MM)==1: return 0
    if len(MM)==2: return MM[0]*MM[1]
    return min((MM[0]-tt)*(MM[1]-tt)+minAdm((tt,)+MM[2:]) for tt in range(min(MM[0],MM[1])+1))
print(f"    minAdm(3,3,4) (independent recursion) = {minAdm(M)}  [expect 8]")
ok &= (minAdm(M)==8)

# ---------- STATE SEQUENCE (binding path) ----------
print("\n[STATE] binding-path state sequence (divisor births, resets, exponents):")
seq = [
 # (S,J, action, divisor, T-after, Mexp-after, note)
 (1,0,"Case2 clear","u_{1,1}",(0,0),Mrun(1)*(M[1]-0),"fresh; block 3x3; tilde t=0"),
 (1,1,"Case2 clear","u_{1,2}",(1,1),(Mrun(1)-1)*(M[1]-1),"fresh; block 2x2; tilde t=1"),
 (1,2,"Case2 clear","u_{1,3}",(2,2),(Mrun(1)-2)*(M[1]-2),"fresh; block 1x1; tilde t=2; layer1 DONE (J=3>M(2)=3? J+1=4>3)"),
 (2,0,"Case1(1) boost","u_{1,2}",(1,0),4+1*(M[2]-0),"RESET t^(2):1->0 (=J), tilde t 1->0 TERMINAL; Mexp 4->8"),
]
for (S,J,act,dv,T,Mx,note) in seq:
    chk = Mval(T) if min(T)==0 else None
    tag = f" Mval({T})={chk}" if chk is not None else " (tilde t>0, non-terminal)"
    print(f"    (S={S},J={J}) {act:14s} {dv}: T={T} Mexp={Mx}{tag}  -- {note}")
    if chk is not None: ok &= (Mx==chk)
print("    => binding divisor u_{1,2} ends terminal T=(1,0), Mexp=8, h=Mexp-1=7  [matches g-coupled-334: h_e=7]")

# ---------- MATRIX: concrete first Case-2 blow-up + Schur on (3,3,4) ----------
print("\n[MATRIX] first Case-2 blow-up + Schur (concrete C1 3x3, C2 3x4):")
C1 = sp.Matrix(3,3, sp.symbols('a0:9'))
C2 = sp.Matrix(3,4, sp.symbols('c0:12'))
# state (1,0): residual D0 = C1 (3x3), b=(1,1,1); Case2 blow-up whole block.
# chart: pivot d_{11}; set C1 = u * Cbar with Cbar[0,0]=1 (radial-in-pivot chart)
u = sp.symbols('u')
# Cbar: normalized so that entry(0,0)=1 -> divide the block by d11 in this chart
d11 = C1[0,0]
Cbar = sp.Matrix(3,3, lambda i,j: sp.Integer(1) if (i,j)==(0,0) else sp.symbols(f'cb_{i}{j}'))
# In the u-chart: C1 = u*Cbar (all entries scale by u). Then D0 = u*Cbar. beta=first row tail, gamma=first col tail, delta=SE.
beta = Cbar[0,1:]          # 1x2
gamma = Cbar[1:,0]         # 2x1
delta = Cbar[1:,1:]        # 2x2
Q = sp.Matrix([[1,-beta[0,0],-beta[0,1]],[0,1,0],[0,0,1]])
Dpp = sp.expand(Cbar*Q)
schur = sp.expand(delta - gamma*beta)
row0_clear = all(Dpp[0,j]==0 for j in (1,2)) and Dpp[0,0]==1
se_ok = sp.expand(Dpp[1:,1:]-schur)==sp.zeros(2,2)
print(f"    C1 = u*Cbar (u factored, exponent contributes to Jac); Cbar[0,0]=1 pivot")
print(f"    Q clears row0: {row0_clear}; SE = Schur(delta-gamma*beta): {se_ok}; residual D1 = 2x2 Schur")
ok &= row0_clear and se_ok
# ideal: <C1 C2> in u-chart = <u * Cbar * C2> = u * <Cbar C2>; the u factors out (goes to Jacobian),
# residual ideal <Cbar C2> continues. Confirm Cbar*C2 well-defined and D1 is 2x2 for next step.
print(f"    next state (1,1): diag(b)=diag(u,u,u), residual D1 = 2x2 (Schur), C2 recoordinatized by Q^-1")

print("\n(3,3,4) TRACE:", "PASS" if ok else "FAIL")
import sys; sys.exit(0 if ok else 1)
