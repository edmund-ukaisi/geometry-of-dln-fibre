import sympy as sp
from sympy import Rational as Q
from adv_dln import nReg, jacobian_rank_at_deepest, product, build_chain_symbols

print("="*72)
print("ATTACK H — does the variety cap genuinely bind? prefix/suffix rank >> r, small output dims")
print("="*72)
# Want a config where naive {rows in rowspace} contribution would exceed nReg but the rank<=r variety caps it.
# (2,5,2) r=2: M=(0,3,0). BOTH ends are bottlenecks (H0=H2=2=r). interior width 5. nReg=2*(2+2-2)=4.
#   ambient = 2*5 + 5*2 = 20. The product is 2x2, rank<=2 (full possible). The rank-<=2 variety in R^{2x2}
#   is ALL of R^{2x2} (dim 4) since 2x2 max rank 2. So tangent = 4 = nReg. rank(J) should be 4.
H=(2,5,2); r=2
def show(label,H,r,base):
    rk,nv,J,mats=jacobian_rank_at_deepest(H,base); nr=nReg(H,r)
    P=product(mats).subs({s:0 for row in mats for s in row.free_symbols});
    flag="" if rk==nr else "  <<<<< MISMATCH"
    print(f"{label}: H={H} r={r} nReg={nr} ambient={nv} rank(J)={rk} prodrank={sp.Matrix(P).rank()} match:{rk==nr}{flag}")
    return rk,nr
C1=sp.Matrix([[1,0,0,0,0],[0,1,0,0,0]]); C2=sp.Matrix([[1,0],[0,1],[0,0],[0,0],[0,0]])
show("[H1] (2,5,2) r=2 both ends bottleneck, wide interior", H, r, [C1,C2])
# (2,5,3) r=2: M=(0,3,1). H0=2=r bottleneck (end). interior 5. output 2x3. nReg=2*(2+3-2)=6. ambient=10+15=25
#   rank-<=2 variety in R^{2x3}: max rank is 2, so ALL of R^{2x3} dim 6 = nReg. cap = ambient-output-free.
H=(2,5,3); r=2
C1=sp.Matrix([[1,0,0,0,0],[0,1,0,0,0]]); C2=sp.Matrix([[1,0,0],[0,1,0],[0,0,0],[0,0,0],[0,0,0]])
show("[H2] (2,5,3) r=2 H0 bottleneck, wide interior, output 2x3", H, r, [C1,C2])
# A case where rank<=r is a PROPER subvariety so the cap is nontrivial: (4,2,4) already tested (rank<=2 in 4x4
#   is dim 12 < 16). Confirmed nReg=12. Good.
# Push: (3,2,5) r=2: rank<=2 in 3x5 = dim 2(3+5-2)=12 < 15. nReg=12. ambient=6+10=16.
H=(3,2,5); r=2
C1=sp.Matrix([[1,0],[0,1],[0,0]]); C2=sp.Matrix([[1,0,0,0,0],[0,1,0,0,0]])
show("[H3] (3,2,5) r=2 interior bottleneck, asymmetric output 3x5", H, r, [C1,C2])
print()

print("="*72)
print("ATTACK I — GENUINE FLATNESS of the flat complement (loss EXACTLY 0 along it, not just Hessian-deg)")
print("   + higher-order check: is the loss along the kernel of J truly constant, or does a quartic survive?")
print("="*72)
# Take (3,1,3) r=1. ambient 6, rank(J)=5, flat dim 1. The flat dir is the gauge. Check loss restricted to
# the FULL kernel of the Hessian = exactly 0 to all orders. We expand the loss and check it vanishes on ker.
H=(3,1,3); r=1
base=[sp.Matrix([[1],[0],[0]]), sp.Matrix([[1,0,0]])]
mats, allv = build_chain_symbols(H, base)
P=product(mats); B=sp.zeros(3,3); B[0,0]=1
F=sp.expand(sum((P[i,j]-B[i,j])**2 for i in range(3) for j in range(3)))
Hm=sp.hessian(F,allv).subs({v:0 for v in allv})
# kernel of Hessian
ker = Hm.nullspace()
print(f"  (3,1,3): Hessian rank {Hm.rank()}, kernel dim {len(ker)}")
for idx,kv in enumerate(ker):
    t=sp.Symbol('t',real=True)
    subs={allv[i]: t*kv[i] for i in range(len(allv))}
    Frestr=sp.expand(F.subs(subs))
    print(f"   loss along kernel vec {idx} (param t): {Frestr}  -> {'FLAT (=0)' if Frestr==0 else 'NOT FLAT'}")
print()
# Critical higher-order subtlety: the kernel of the QUADRATIC Hessian might be flat to 2nd order but the
# loss could have a surviving QUARTIC making rlct LARGER (not smaller) -> would mean rlct could exceed nReg/2?
# Actually a surviving higher-order term on a 'flat' Hessian direction makes the loss POSITIVE there ->
# the direction is NOT free -> rlct could be DIFFERENT. Check (2,2) r=2 (no flat) and a case with flat.
# (3,1,3): the single kernel dir flat to all orders (above). Now check a 2-interior chain.
H=(3,1,1,3); r=1
base=[sp.Matrix([[1],[0],[0]]), sp.Matrix([[1]]), sp.Matrix([[1,0,0]])]
mats, allv = build_chain_symbols(H, base)
P=product(mats); B=sp.zeros(3,3); B[0,0]=1
F=sp.expand(sum((P[i,j]-B[i,j])**2 for i in range(3) for j in range(3)))
Hm=sp.hessian(F,allv).subs({v:0 for v in allv})
ker=Hm.nullspace()
print(f"  (3,1,1,3): Hessian rank {Hm.rank()}, kernel dim {len(ker)} (claim flat=2 gauge dirs)")
allflat=True
for idx,kv in enumerate(ker):
    t=sp.Symbol('t',real=True)
    subs={allv[i]: t*kv[i] for i in range(len(allv))}
    Frestr=sp.expand(F.subs(subs))
    flat = (Frestr==0)
    allflat = allflat and flat
    print(f"   loss along kernel vec {idx}: {Frestr} -> {'FLAT' if flat else 'NOT FLAT (quartic survives!)'}")
# Also test a GENERIC kernel combination (sum of basis vectors) — flatness must hold on the whole subspace,
# not just basis directions (cross terms!).
t=sp.Symbol('t',real=True)
combo = {allv[i]: t*sum(kv[i] for kv in ker) for i in range(len(allv))}
Fc=sp.expand(F.subs(combo))
print(f"   loss along SUM of kernel basis (cross-terms test): {Fc} -> {'FLAT' if Fc==0 else 'NOT FLAT'}")
