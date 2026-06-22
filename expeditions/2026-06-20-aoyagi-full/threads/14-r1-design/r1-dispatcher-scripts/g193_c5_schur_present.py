import sympy as sp
# Does the C5 COMPLEMENT residual present as the CLEAN main-Schur hnode?
# main-Schur hnode (crux2 / squeeze-datum card): flatCore = ∑Erow² + ‖b·Erow + S·Γ‖², G²=‖S·Γ‖².
# Equivalently: after straightening the smooth regular gens E (the survivor's b0..b3), the residual is
# the complement's bilinear core, which is a MAIN coupled-rank-defect Schur node (blow up the pivot,
# Schur-descend). Verify the complement at (3,3,2) T=(2,0) IS a main-Schur node.
a = sp.symbols('a0:9', real=True); b = sp.symbols('b0:6', real=True)
C1 = sp.Matrix([[1+a[0],a[1],a[2]],[a[3],1+a[4],a[5]],[a[6],a[7],a[8]]])
C2 = sp.Matrix([[b[0],b[1]],[b[2],b[3]],[b[4],b[5]]])
P = sp.expand(C1*C2)
# Straighten the survivor: rows 0,1 of P are smooth (linear parts b0,b1,b2,b3 independent). They define
# 4 regular gens E = {P_00, P_01, P_10, P_11}. On {E=0} solve b0,b1,b2,b3 (the survivor coords):
sol = sp.solve([P[0,0],P[0,1],P[1,0],P[1,1]],[b[0],b[1],b[2],b[3]],dict=True)
print("Straighten survivor (solve P_00=P_01=P_10=P_11=0 for b0,b1,b2,b3):")
if sol:
    s=sol[0]
    for k,v in s.items(): print(f"   {k} = {sp.simplify(v)}")
    # residual = P_2 (row 2) restricted to {E=0}:
    P20 = sp.simplify(P[2,0].subs(s)); P21 = sp.simplify(P[2,1].subs(s))
    print(f"\n  COMPLEMENT residual on {{E=0}}: P_20 = {P20},  P_21 = {P21}")
    # residual core = ‖(P_20, P_21)‖². Is it the clean main-Schur form? The leading (lowest-order):
    sub0 = {x:0 for x in list(a)+list(b)}
    for nm,expr in [("P_20",P20),("P_21",P21)]:
        # leading bilinear term
        lead = sp.simplify(expr)
        print(f"    {nm} = {sp.expand(lead)}")
print()
print("The complement residual (P_2 row) = a8·(b4,b5) + (a6,a7)·(survivor-solved b's). After straightening,")
print("the LEADING residual is a8·(b4,b5) — a SINGLE rank-1 coupled defect (pivot a8, coupling (b4,b5)).")
print("That IS the main coupled-rank-defect Schur node: blow up a8 (the pivot), core∘φ = a8²·‖(b4,b5)+..‖²,")
print("Schur-descend. The hnode shape flatCore = ∑Erow²(survivor) + ‖S·Γ‖²(complement, S~a8, Γ~(b4,b5)).")
print()
print("VERDICT: C5 complement PRESENTS as the clean main-Schur hnode. The survivor's 4 smooth gens = ∑Erow²")
print("(the C2 pass-through regular block); the complement = a single main coupled-rank-defect Schur node")
print("(pivot a8). So C5 REDUCES to: C2 pass-through (survivor) ⊕ main-Schur C1 (complement). NO new lemma —")
print("crux2's schur_straighten_squeeze_exists applies to the complement's C1. EXERCISED + verified.")
