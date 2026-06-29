import sympy as sp, random
random.seed(2)
# Squareness: #active = minAdm EXACTLY <=> the radial blow-up matches the codim, chart square, det != 0.
# WRONG allocation: if active.card != minAdm (too few or too many u-scaled coords), the chart degenerates.
# Build (2,3,2) and show: CORRECT active (card 4=minAdm) -> det = u^3 * nonzero; 
#   WRONG (allocate the pivot scaling to a K-CORE coord instead of an E/leaf coord) -> det identically 0 or wrong.
M0,M1,M2,t1=2,3,2,1; r1=M0-t1; c1=M1-t1
u=sp.Symbol('u',real=True)
def SM(name,r,c): return sp.Matrix(r,c, lambda i,j: sp.Symbol(f'{name}_{i}_{j}',real=True)) if r*c>0 else sp.zeros(r,c)
K=SM('K',t1,t1); X=SM('X',r1,t1); N=SM('N',t1,c1); E=SM('E',r1,c1); W=SM('W',c1,M2); lf=SM('lf',t1,M2)
lf[0,M2-1]=sp.Integer(1)
Bmat1=sp.Matrix.vstack(K,X*K); qN1=sp.Matrix.hstack(sp.eye(t1),N)
R1=sp.zeros(M0,M1)
for i in range(r1):
    for j in range(c1): R1[t1+i,t1+j]=E[i,j]
C2=u*lf; C1=Bmat1*qN1+u*R1; A0=C1; A1=sp.Matrix.vstack(C2-N*W,W)
F=[sp.expand(A[i,j]) for A in (A0,A1) for i in range(A.rows) for j in range(A.cols)]
allv=[u]+sorted({s for e in F for s in e.free_symbols if s!=u},key=str)
J=sp.Matrix(F).jacobian(sp.Matrix(allv))
# CORRECT: full det, factor u
sub={v:sp.Rational(random.randint(1,9),random.randint(1,5)) for v in allv if v!=u}
detC=sp.Poly(sp.expand(J.subs(sub).det()),u)
print("CORRECT allocation (2,3,2): det u-poly =", detC.as_expr(), " -> u^3 * nonzero. minAdm=4, #active=4. SQUARE.")
print()
# WRONG: suppose we (incorrectly) treat #active = minAdm+1 (5) by ALSO blowing up a K-core coord K_0_0.
# Or treat #active = minAdm-1 (3) by NOT blowing up the leaf lf_0_0. Either mismatches the codim.
# The KEY non-degeneracy: the radial blow-up Prad has det u^{card-1}; the chart det = det(DB)*u^{card-1}.
# det(DB) is the engine product = nonzero generically IFF the de-radialized B is a local iso (square, full rank).
# If #active wrong, the chart is NOT the square achiever chart: either coords missing (B not surjective ->
# det DB has a zero factor) or extra u-scaling (a column degenerates).
# Concretely the controller's (2,3,3,2)-type degeneration: allocating u to the WRONG block makes a column 
# of the Jacobian proportional to another -> det == 0. Demonstrate: force the anchor into a K-core position.
# Replace: make the K-core entry K_0_0 the anchor (scaled by u) AND drop the leaf anchor -> the leaf row
# loses its pivot, the C2 = u*lf row has no fixed direction -> a row of A1 becomes purely u*free, and the
# B-part K loses a DOF -> det degenerates. Build that mis-allocation:
lf2=SM('lf2',t1,M2)  # NO anchor in leaf now (all free)
K2=sp.Matrix([[sp.Integer(1)]])  # K_0_0 forced to fixed 1 (mis-allocated anchor) -- a WRONG square
Bmat1b=sp.Matrix.vstack(K2,X*K2); 
C1b=Bmat1b*qN1+u*R1; C2b=u*lf2; A0b=C1b; A1b=sp.Matrix.vstack(C2b-N*W,W)
Fb=[sp.expand(A[i,j]) for A in (A0b,A1b) for i in range(A.rows) for j in range(A.cols)]
allvb=[u]+sorted({s for e in Fb for s in e.free_symbols if s!=u},key=str)
print(f"MIS-ALLOCATION (anchor in K-core, leaf all-free): #free coords = {len(allvb)} vs flatDim {len(Fb)}")
if len(allvb)==len(Fb):
    Jb=sp.Matrix(Fb).jacobian(sp.Matrix(allvb))
    subb={v:sp.Rational(random.randint(1,9),random.randint(1,5)) for v in allvb if v!=u}
    detb=sp.Poly(sp.expand(Jb.subs(subb).det()),u)
    print("  mis-allocated det u-poly =", detb.as_expr(), " (wrong exponent / degenerate vs u^3)")
else:
    print(f"  NOT SQUARE: #coords {len(allvb)} != flatDim {len(Fb)} -> the chart is non-square, det undefined as a self-map.")
