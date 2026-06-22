import sympy as sp
def nReg(H, r): return r*(H[0] + H[-1] - r)

# DEEPER CASE: interior M_s=0 in a longer chain, non-degenerate neighbors. 
# (3,2,1,2,3) r=1? No — want M_s=0 at an INTERIOR layer = some H_s = r with the chain longer.
# Take H=(2,1,2) r=1: M=(1,0,1), middle M_1=0 (H_1=1=r). nReg = 1*(2+2-1)=3. Chain C1:2x1, C2:1x2.
print("="*64); print("CASE (2,1,2) r=1: H=(2,1,2), M=(1,0,1) [interior M_1=0], nReg =", nReg((2,1,2),1)); print("="*64)
u=sp.symbols('u0:2',real=True); v=sp.symbols('v0:2',real=True)
C1=sp.Matrix([[1+u[0]],[u[1]]]); C2=sp.Matrix([[1+v[0], v[1]]])  # 2x1, 1x2
P=sp.expand(C1*C2); B=sp.zeros(2,2); B[0,0]=1
F=sp.expand(sum((P-B)[i,j]**2 for i in range(2) for j in range(2)))
allv=list(u)+list(v)
Hm=sp.hessian(F,allv).subs({x:0 for x in allv}); rk=Hm.rank()
print(f"  Hessian rank = {rk}, nReg = {nReg((2,1,2),1)}, match {rk==nReg((2,1,2),1)}; flat = {len(allv)-rk}")
print(f"  rlctAt = nReg/2 = {sp.Rational(nReg((2,1,2),1),2)}")
print()

# CASE with a degenerate END + r=2: H=(2,2) r=2 ⟹ M=(0,0), nReg=2*(2+2-2)=4. Single matrix C:2x2, B rank2.
print("="*64); print("CASE (2,2) r=2: H=(2,2), M=(0,0), nReg =", nReg((2,2),2)); print("="*64)
a=sp.symbols('a0:4',real=True); C=sp.Matrix([[1+a[0],a[1]],[a[2],1+a[3]]]); B=sp.eye(2)
F2=sp.expand(sum((C-B)[i,j]**2 for i in range(2) for j in range(2)))
Hm2=sp.hessian(F2,list(a)).subs({x:0 for x in a}); rk2=Hm2.rank()
print(f"  Hessian rank = {rk2}, nReg = {nReg((2,2),2)}, match {rk2==nReg((2,2),2)}; flat = {len(a)-rk2}")
print(f"  rlctAt = nReg/2 = {sp.Rational(nReg((2,2),2),2)}")
print()

# FLAT-DIRECTION STRUCTURE: verify the flat complement is GENUINELY flat (loss constant along it),
# not just Hessian-degenerate. (3,1,3) r=1: the 1 flat direction = the GL_1 gauge (C1→λC1, C2→C2/λ).
print("="*64); print("FLAT-DIRECTION CHECK: (3,1,3) r=1, the gauge direction is genuinely flat (not just Hessian-deg)"); print("="*64)
u=sp.symbols('u0:3',real=True); v=sp.symbols('v0:3',real=True); lam=sp.symbols('lam',real=True)
C1=sp.Matrix([[1+u[0]],[u[1]],[u[2]]]); C2=sp.Matrix([[1+v[0],v[1],v[2]]])
P=sp.expand(C1*C2); B=sp.zeros(3,3); B[0,0]=1
F=sp.expand(sum((P-B)[i,j]**2 for i in range(3) for j in range(3)))
# gauge orbit at deepest: C1 → (1+t)·C1_0, C2 → C2_0/(1+t) — product invariant ⟹ loss CONSTANT.
# C1_0=(1,0,0)^T, C2_0=(1,0,0). gauge: C1=(1+t,0,0)^T, C2=(1/(1+t),0,0). product = e0 e0^T = B always.
F_gauge = F.subs({u[0]:lam, u[1]:0, u[2]:0, v[0]: 1/(1+lam)-1, v[1]:0, v[2]:0})
print(f"  loss along gauge orbit C1=(1+t)e0, C2=e0/(1+t): F = {sp.simplify(F_gauge)} (=0 ⟹ genuinely FLAT ✓)")
print(f"  ⟹ the flat complement is the GL_r gauge orbit (dim r² = 1 here) + the vanished-core (M_s=0 ⟹ 0 core dirs).")
print(f"     loss CONSTANT (=0, the fibre) along it — Morse-Bott (flat valley), not just Hessian-degenerate.")
print()
print("FLAT COMPLEMENT DIM (general): total ambient = Σ H_s H_{s+1}; nReg = r(H_0+H_L−r) nondeg; the rest")
print("= flat = the fibre tangent (gauge GL_r per interior + the vanished-core M_s=0 directions). At a")
print("degenerate boundary the fibre is SMOOTH (the core is empty), so the loss = pure rank-nReg Morse-Bott.")
