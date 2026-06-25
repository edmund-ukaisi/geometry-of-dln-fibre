import sympy as sp
# DIRECT deepest-point chart reaching the origin. The achiever stratum for (3,3,4) t=(1,0): rank(A)=1.
# A rank-1 + the product structure. The cleanest reaching-origin chart with det = u0^7:
# Let the pivot u0 scale the binding directions. Construct A, C so that:
#   - at u0=0 with all coords 0: A=0, C=0 (ORIGIN reached). 
#   - det Dphi = +-u0^7.
#   - F = u0^2 U.
# The construction: A = u0-scaled rank-1-ish, C with top row u0-scaled. Try (the resolution chart):
#   A[0,0] = u0,                      (pivot itself in A)
#   A[0,1] = u0*p1, A[0,2] = u0*p2,   (top row = u0*(1,p1,p2), rank-1 direction)
#   A[1,0] = q1, A[2,0] = q2,         (col-0, free)
#   A[1,1]=u0*r11,A[1,2]=u0*r12,A[2,1]=u0*r21,A[2,2]=u0*r22,  (E-block = u0*R, blown up)
#   C[0,0]=v0, C[0,1]=v1, C[0,2]=v2, C[0,3]=v3   (top row of C, free -- the y)
#   C[1,:],C[2,:] = S free (8)
# Count u0-scaled: A[0,0],A[0,1],A[0,2],A[1,1],A[1,2],A[2,1],A[2,2] = 7 coords + ... need 8 for u0^7? No,
# det = u0^(#blownup -1)? For a pivot blow-up of k coords, the pivot is 1 of them, det = pivot^(k-1).
# If 8 coords carry a u0 factor with u0 itself = A[0,0], then det ~ u0^7. Let me just build & compute.
u0 = sp.Symbol('u0', real=True)
p1,p2 = sp.symbols('p1 p2', real=True)
q1,q2 = sp.symbols('q1 q2', real=True)
r11,r12,r21,r22 = sp.symbols('r11 r12 r21 r22', real=True)
v0,v1,v2,v3 = sp.symbols('v0 v1 v2 v3', real=True)
S = sp.Matrix(2,4, lambda i,j: sp.Symbol(f'S{i}{j}', real=True))
A = sp.Matrix([[u0, u0*p1, u0*p2],[q1, u0*r11, u0*r12],[q2, u0*r21, u0*r22]])
C = sp.Matrix([[v0,v1,v2,v3],[S[0,0],S[0,1],S[0,2],S[0,3]],[S[1,0],S[1,1],S[1,2],S[1,3]]])
AC = A*C
F = sp.expand(sum(AC[i,j]**2 for i in range(3) for j in range(4)))
# Is F = u0^2 * (u0-free)? Check the lowest u0-degree.
Fpoly = sp.Poly(F, u0)
print("F as poly in u0: degrees present =", sorted(set(m[0] for m in Fpoly.monoms())))
# The q1,q2 (col-0 of A rows 2,3, NOT scaled) times v (C top row, not scaled) give AC[1,0]=q1*v0+u0*...,
# AC[2,0]=q2*v0+... -> these are O(1), so F has O(1) terms (q1 v0)^2 -> F NOT u0^2 U. 
# So q1,q2 free + v free breaks it. Need the bottom-left product q*v to be O(u0): either q=u0*qh or v=u0*vh.
print("  (q1,q2 free, v free -> AC[1,0]=q1 v0 + ... = O(1) -> F has O(1) terms -> NOT u0^2 U)")
print()
# Make v = u0*vh (C top row scaled):
vh0,vh1,vh2,vh3 = sp.symbols('vh0 vh1 vh2 vh3', real=True)
C2 = sp.Matrix([[u0*vh0,u0*vh1,u0*vh2,u0*vh3],[S[0,0],S[0,1],S[0,2],S[0,3]],[S[1,0],S[1,1],S[1,2],S[1,3]]])
AC2 = A*C2
F2 = sp.expand(sum(AC2[i,j]**2 for i in range(3) for j in range(4)))
F2poly = sp.Poly(F2,u0)
degs2 = sorted(set(m[0] for m in F2poly.monoms()))
print("With C top row = u0*vh: F degrees in u0 =", degs2)
# AC2[1,0] = q1*u0*vh0 + u0*r11*S00 + u0*r12*S10 = u0*(...) -> O(u0). AC2[0,0]=u0*u0*vh0+... = O(u0^2)?
# AC2[0,j] = u0*(u0 vh_j) + u0 p . S_col = u0^2 vh + u0 (p.Scol). The u0(p.Scol) is O(u0) -> AC2[0,j]=O(u0).
# So all AC2 entries O(u0) -> F2 = O(u0^2). Is the leading u0^2 coeff u0-free? min degree:
print("  min u0-degree of F2 =", min(degs2), "(want 2)")
if min(degs2)==2:
    U2 = sp.expand(F2/u0**2)
    print("  F2 = u0^2 * U2, U2 u0-free:", not U2.has(u0))
# Jacobian: flat coords vs chart coords (u0,p1,p2,q1,q2,r11,r12,r21,r22,vh0..3,S(8)) = 21
chart=[u0,p1,p2,q1,q2,r11,r12,r21,r22,vh0,vh1,vh2,vh3]+[S[i,j] for i in range(2) for j in range(4)]
flat=[A[0,0],A[0,1],A[0,2],A[1,0],A[1,1],A[1,2],A[2,0],A[2,1],A[2,2]]+[C2[0,j] for j in range(4)]+[C2[1,j] for j in range(4)]+[C2[2,j] for j in range(4)]
print("  #chart =", len(chart), " #flat =", len(flat))
J=sp.Matrix(flat).jacobian(chart); dJ=sp.simplify(J.det())
print("  det Dphi =", dJ, "; |det|=u0^? :", sp.simplify(dJ-u0**7)==0 or sp.simplify(dJ+u0**7)==0)
print("  phi(0)=origin:", all(sp.simplify(f.subs({s:0 for s in chart}))==0 for f in flat))
