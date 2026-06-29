import sympy as sp
print("="*78)
print("THE LOAD-BEARING CHECK: is F = D_E|reg invertible, where D_E = D(E)(0)∘D(coreAbsorb.symm)(0)?")
print("  (coreAbsorb.symm is a core-shear: reg fixed, core shifted by shift(reg,spec). Does the")
print("   reg→core mixing in D(coreAbsorb.symm) corrupt the reg-block F?)")
print("="*78)
print()
# coreAbsorb.symm: q=(r,c,s) ↦ (r, c - shift(r,s), s).  Its derivative at 0:
#   D(coreAbsorb.symm)(0) = [[I_r, 0, 0],[ -∂shift/∂r, I_c, -∂shift/∂s],[0,0,I_s]].
# D(E)(0) = [DE_reg, DE_core, DE_spec]  (E reads all three; atom: DE_core=0).
# D_E = D(E)(0) ∘ D(coreAbsorb.symm)(0).  The REG-block of D_E (the reg→reg part):
#   (D_E)|reg = DE_reg·I_r + DE_core·(-∂shift/∂r) + DE_spec·0 = DE_reg - DE_core·(∂shift/∂r).
# ATOM: DE_core = 0  =>  (D_E)|reg = DE_reg.   The core-shear mixing reg→core is KILLED by the atom!
print("D_E|reg = DE_reg - DE_core·(∂shift/∂r).  ATOM (DE_core=0) => D_E|reg = DE_reg.")
print("  => the core-shear's reg→core mixing is ANNIHILATED by the atom.  D_E|reg = DE_reg = PIN-1 F.")
print("  => F invertible  <=>  DE_reg = ∂(deepestEFull)/∂(reg-slot)(0) invertible  =  PIN-1.")
print()
# So the BARE π̃ reduces EXACTLY to PIN-1 invertibility of dE(0)|reg.  Verify PIN-1 holds:
# deepestEFull reg-slice deriv at 0.  reg = (X_first=u, Y_last=v, Z_first=w).  reads {11,12,21}.
u,v,w,p,q,x,T0,T1 = sp.symbols('u v w p q x T0 T1', real=True)
A0=sp.Matrix([[1+u, p],[w, T0]]); A1=sp.Matrix([[1+x, v],[q, T1]])
P=sp.expand(A0*A1); R=[P[0,0]-1, P[0,1], P[1,0]]   # deepestEFull reads
reg=[u,v,w]
# D_E|reg = Jacobian of R wrt reg, at 0 (all coords 0):
J = sp.Matrix([[sp.diff(Ri, rj).subs({k:0 for k in [u,v,w,p,q,x,T0,T1]}) for rj in reg] for Ri in R])
print("PIN-1 check: D(deepestEFull)/∂reg(0), reg=(u=X_first,v=Y_last,w=Z_first):")
sp.pprint(J)
print("  det / rank:", "rank =", J.rank(), " (3x3, need rank 3 for invertible)")
print("  Is it invertible?", J.rank()==3, " det =", J.det() if J.shape[0]==J.shape[1] else "n/a")
