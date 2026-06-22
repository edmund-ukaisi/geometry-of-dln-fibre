# Verify Codex's two sharpenings independently.
import sympy as sp, numpy as np

# SHARPENING 1: (1,1,1) f=x^2 y^2 (the product of two 1x1 chains is x*y, squared). Blow up origin.
x,y,u,v=sp.symbols('x y u v')
f=(x*y)**2
fb=f.subs({x:u, y:u*v})  # blow up origin: x=u, y=u v
print(f"(1,1,1): f=x²y², blow up origin (x=u,y=uv): f∘φ = {sp.expand(fb)}  => u-order={sp.Poly(fb,u).monoms()[-1][0] if False else min(m[0] for m in sp.Poly(fb,u).monoms())} => k_E=2")
# Jacobian of (x,y)->(u,uv): det = u (standard). ratio = (h+1)/(2k) = (1+1)/(2*2)=2/4=1/2. = minAdm/2.
# minAdm(1,1,1): adm t_1 in {0,1}, t_L=0. Mval(0)= (1-0)(1-0)=1; so minAdm=1, rlct=1/2. ✓
print("  Jac det=u (h=1), k=2 => ratio=2/4=1/2 = minAdm(1,1,1)/2=1/2. k_E=2 but formula HOLDS.")
print("  => CONFIRMED: k_E=2 CAN occur (blowing up origin = intersection of x-axis & y-axis divisors).")
print()

# SHARPENING 2: (1,2,1) missed stratum. C1=(x1,x2) 1x2, C2=(y1,y2)^T 2x1. f=(x1 y1 + x2 y2)^2.
x1,x2,y1,y2=sp.symbols('x1 x2 y1 y2')
f2=(x1*y1+x2*y2)**2
# The admissible stratum t_1=1,t_2=0: C1 full rank (rank 1, since 1x2 nonzero), C1 C2=0. Mval=1.
# Codex: C1=(1,0), C2=(0,1)^T => C1C2 = 0, C1 rank 1 (full). A first-factor-rank-defect-only recursion
# would NOT blow up here (C1 is full rank!), missing this stratum. Verify the point:
import numpy as np
C1=np.array([[1.,0.]]); C2=np.array([[0.],[1.]])
print(f"(1,2,1): C1=(1,0) rank={np.linalg.matrix_rank(C1)} (FULL for 1x2), C1·C2={(C1@C2).ravel()} (=0!)")
print("  => admissible stratum t=(1,0), Mval=1, rlct=1/2. The DROP comes from C2 (later factor), NOT C1.")
print("  => a first-factor-rank-defect-ONLY recursion MISSES this; needs FULL-RANK PASS-THROUGH charts.")
print()
# Does my pernode model capture it? My recursion_branches chose t_j freely incl t_1=1 (C1 full rank),
# then t_2=0 (drop at C2). So the BRANCH SET includes it -- but ONLY because I let the node descend on
# a full-rank first factor (pass-through). Codex's point: the IMPLEMENTATION must actually DO that
# (descend on full-rank C1 via the Schur identity-block pass-through), not skip it as "no blow-up needed".
print("My pernode_atlas model HAD this branch (t_1=1 full-rank pass-through). Codex sharpens: the")
print("IMPLEMENTATION must include the full-rank pass-through Schur chart, else it misses t=(1,0).")
