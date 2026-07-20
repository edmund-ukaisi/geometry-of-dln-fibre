# Confirm the value-lane TENSION is real: interior-only alpha (a VALID det-1 chart) leaves prod able
# to VANISH on the box (residualCore hits 0), so the cross MUST be cleared -- but clearing is a
# projection (fvw_chart: det 0). Targeted witness, exact rational.
import sympy as sp, sys
BATT = "/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/expeditions/2026-07-17-aoyagi-engine/threads/24-alpha-cover/battery"
sys.path.insert(0, BATT)
from rg_shape import init_params, layer_mat, spine, beta_blowup, alpha_interior
def prod_all(P,M):
    Pr=layer_mat(P,M,0)
    for s in range(1,len(M)-1): Pr=Pr*layer_mat(P,M,s)
    return Pr
M=[2,2,2]; P=init_params(M)
for (S,c) in spine(M):
    P,_=alpha_interior(P,M,S,c); P,_=beta_blowup(P,M,S,c)
Pr=prod_all(P,M)
syms=sorted(Pr.free_symbols,key=str)
frob=sp.expand(sum(Pr[i,j]**2 for i in range(2) for j in range(2)))
# search small rationals in [-1,1] for a NONtrivial zero of frob (divisor corners a0_00,a1_00 != 0)
import itertools
grid=[sp.Rational(k,2) for k in range(-2,3)]
found=None
for vals in itertools.product(grid,repeat=len(syms)):
    sub=dict(zip(syms,vals))
    if sub[sp.Symbol('a0_00',real=True)]!=0 and sub[sp.Symbol('a1_00',real=True)]!=0:
        if sp.expand(frob.subs(sub))==0:
            found=dict(zip([str(s) for s in syms],vals)); break
print("interior-only (2,2,2) frobSq(prod) vanishes at a box point with corners!=0 (residualCore->0)?",
      "YES" if found else "NO", "witness:", found)
