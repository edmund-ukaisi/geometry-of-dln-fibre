import sympy as sp
def nReg(H,r): return r*(H[0]+H[-1]-r)
# INDEPENDENTLY verify the adversarial seat's two breaks of my g203, before revising.
# BREAK 1: g203's flat = r²(L−1) is WRONG; flat = ambient − nReg, depends on interior widths.
# Witness (4,2,3,2,4) r=2: M=(2,0,1,0,2). ambient=ΣH_sH_{s+1}, nReg=r(H_0+H_L−r), flat=ambient−nReg vs r²(L−1).
print("BREAK 1: flat dim = ambient−nReg vs my g203 r²(L−1) — check the seat's witnesses:")
for H,r in [((4,2,3,2,4),2),((5,3,2,4),3),((3,1,2,1,3),1),((2,5,2),2),((4,3,1,3,4),3)]:
    L=len(H)-1; ambient=sum(H[s]*H[s+1] for s in range(L)); nr=nReg(H,r); flat=ambient-nr; g203form=r*r*(L-1)
    M=tuple(h-r for h in H); degen=any(m==0 for m in M)
    print(f"  H={H} r={r}: M={M} {'[DEGEN]' if degen else '[not degen]'}, ambient={ambient}, nReg={nr}, flat=ambient−nReg={flat}, my-g203 r²(L−1)={g203form}, GAP={flat-g203form}")
print()
print("⟹ flat = ambient−nReg ≠ r²(L−1) when an interior width > r (carries fibre dirs beyond gauge).")
print("  My g203 configs ALL had interior width = r (bottleneck) — the exact regime where they coincide.")
print("  CONFOUND I missed: unrepresentative validation set. The seat tested non-bottleneck interiors. ERROR CONFIRMED.")
print()
# BREAK 2: the loss is t⁴ along the straight Hessian-nullspace dir, NOT 0 (only the CURVED gauge orbit is 0).
print("BREAK 2: (2,1,2) r=1, loss along the straight nullspace dir [−1,0,1,0] (my g202 claimed flat≡0):")
u=sp.symbols('u0:2',real=True); v=sp.symbols('v0:2',real=True); t=sp.symbols('t',real=True)
C1=sp.Matrix([[1+u[0]],[u[1]]]); C2=sp.Matrix([[1+v[0],v[1]]]); P=sp.expand(C1*C2)
B=sp.zeros(2,2); B[0,0]=1; F=sp.expand(sum((P-B)[i,j]**2 for i in range(2) for j in range(2)))
# Hessian nullspace at deepest (u=v=0): vars (u0,u1,v0,v1). The straight dir the seat names: [−1,0,1,0]
# = (u0=−t, u1=0, v0=t, v1=0).
F_straight = sp.expand(F.subs({u[0]:-t, u[1]:0, v[0]:t, v[1]:0}))
print(f"  loss along straight [−1,0,1,0]·t: F = {F_straight}  (= t⁴? {sp.simplify(F_straight - t**4)==0 or 'see expr'})")
# the CURVED gauge orbit: C1=(1+t)e0... for (2,1,2): C1=(1+t,0)^T, C2=(1/(1+t),0). product=e0e0^T=B.
F_curved = sp.expand(F.subs({u[0]:t, u[1]:0, v[0]:1/(1+t)-1, v[1]:0}))
print(f"  loss along CURVED gauge orbit: F = {sp.simplify(F_curved)}  (=0 ⟹ only the curved orbit is flat)")
print()
print("⟹ My g202 'genuinely flat / loss≡0 along the flat complement' was WRONG for the LINEAR nullspace —")
print("  t⁴ along the straight dir (re-enters the cone). Only the CURVED gauge orbit is exactly flat. The")
print("  value nReg/2 survives via the SMOOTH-FIBRE-TRANSVERSAL argument (rank dΦ=nReg, fibre-adapted coords),")
print("  NOT linear flatness. ERROR CONFIRMED. (Build MUST use adapted coords, not raw nullspace — t⁴ bites.)")
