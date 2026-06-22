import sympy as sp
# Reconcile: on the g172 counterexample gauge (X_s=0, i.e. (0,0) block exactly I), does ∏S_s = R = loss-core?
# vs the general symbolic case where ∏S_s ≠ R|{E=0}. Which is the RIGHT core object?
#
# The g172 ground truth (explicit ε): C1=[[1,0],[-ε²,ε]], C2=[[1,ε],[ε,0]], C3=[[1,-ε²],[0,ε]].
# There X1=X2=X3=0 (the (0,0) entries are exactly 1). ∏C=blockdiag[1,-ε⁴], so E=0 EXACTLY (P00=1,P01=P10=0).
# loss = ε⁸ = ‖R‖² = ‖∏S_s‖². Both matched. KEY: there E=0 held EXACTLY (not just to leading order).
#
# In the symbolic L=2 {E=0}-solve, I solved B,U,Z to make E=0 but kept A,Y,V,T,S,... general. The issue:
# is "∏S_s" using the RAW per-layer blocks, or the blocks AFTER the gauge slice that sets X=0?
print("THE QUESTION: which per-layer Schur? raw-block S_s, or post-gauge-slice S_s (X normalized)?")
print()
# g172 used: S_s = T_s - Z_s (I+X_s)^{-1} Y_s with the blocks AS GIVEN (X_s the (0,0)-deviation).
# In the ε-example X_s=0 so S_s = T_s - Z_s Y_s. Let me redo the symbolic with X explicit and see when ∏S_s=R.
A,Y,Z,T = sp.symbols('A Y Z T'); B,U,V,S = sp.symbols('B U V S')
C1 = sp.Matrix([[A, Y],[Z, T]]); C2 = sp.Matrix([[B, U],[V, S]])
P = sp.expand(C1*C2); P00,P01,P10,P11=P[0,0],P[0,1],P[1,0],P[1,1]
R = sp.simplify(P11 - P10*P00**(-1)*P01)
S1 = T - Z*A**(-1)*Y; S2 = S - V*B**(-1)*U
# Claim to test: R = S1 * (inter-layer unit) * S2. Solve for the unit g: R = S1 g S2 => g = R/(S1 S2).
g = sp.simplify(R/(S1*S2))
print("inter-layer unit g = R/(S1 S2) =", g)
print("  at the deepest w0 (A=B=1, Y=Z=U=V=0): g =", sp.simplify(g.subs({A:1,B:1,Y:0,Z:0,U:0,V:0})), "(unit? should be 1)")
print()
# So R = S1 · g · S2 with g a unit at w0 (g157's inter-layer unit). ‖R‖² vs ‖S1 S2‖²: differ by ‖g‖² (a unit).
# For RLCT (germ at w0), ‖R‖² and ‖S1 S2‖² differ by a UNIT factor g² => SAME rlct? Only if g is bounded
# unit (peelable). Check g near w0:
print("Is g a bounded unit near w0 (so ‖R‖²≍‖∏S_s‖², same rlct)? g at w0 =", 
      sp.simplify(g.subs({A:1,B:1,Y:0,Z:0,U:0,V:0})))
# Evaluate g on a small generic perturbation to see if bounded away from 0/inf:
import random
vals=[]
for _ in range(5):
    sub={A:1+0.01*random.uniform(-1,1),B:1+0.01*random.uniform(-1,1),Y:0.01*random.uniform(-1,1),
         Z:0.01*random.uniform(-1,1),U:0.01*random.uniform(-1,1),V:0.01*random.uniform(-1,1)}
    vals.append(float(g.subs(sub)))
print("  g on 5 small perturbations:", [round(v,4) for v in vals], "(near 1 ⟹ bounded unit ⟹ ‖R‖²≍‖∏S_s‖²)")
