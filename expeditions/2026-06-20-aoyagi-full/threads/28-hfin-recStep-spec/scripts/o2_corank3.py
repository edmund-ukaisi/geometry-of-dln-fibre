import sympy as sp

# ============================================================
# O2 adjudication, corank-3, r=3, j=1 (M11 = R[0,0] scalar pivot, dominant).
# The recursion's Schur core: Sc = M22 - M21 * M11^{-1} * M12, an (r-j)x(r-j)=2x2 matrix.
# Question: as R ranges over the M11-dominant chart, is the MAP R -> Sc a submersion
# onto a full 2x2 box with bounded-below density INDEPENDENT of spectators?
# AND: does the recursion actually NEED this (pushforward), or does it factorise differently?
# ============================================================

# R is 3x3, entries r_ij, |r_ij|<=1, pivot R[0,0]=1 dominant.
r = sp.symbols('r00 r01 r02 r10 r11 r12 r20 r21 r22', real=True)
R = sp.Matrix(3,3, r)
# Fix pivot normalization R[0,0]=1 (on chart, the angular matrix has pivot entry =1).
R = R.subs(r[0], 1)

# Block split j=1: M11 = R[0,0]=1 (1x1), M12 = R[0,1:] (1x2), M21 = R[1:,0] (2x1), M22 = R[1:,1:] (2x2)
M11 = R[0:1,0:1]
M12 = R[0:1,1:3]
M21 = R[1:3,0:1]
M22 = R[1:3,1:3]

Sc = M22 - M21 * M11.inv() * M12
Sc = sp.simplify(Sc)
print("=== Sc (2x2 Schur complement), j=1, M11=R00=1 ===")
sp.pprint(Sc)

# The 'spectator' / shear entries: M21 (=r10,r20) and M12 (=r01,r02) and M11.
# The remaining free entries after fixing M11=1 are: r01,r02 (M12), r10,r20 (M21), r11,r12,r21,r22 (M22).
# So R-chart has 8 free coords (r01,r02,r10,r11,r12,r20,r21,r22).
# Sc is 2x2 = 4 coords: Sc_ab = M22_ab - M21_a * M12_b  (since M11=1).
print()
print("Sc entries as functions of the 8 free R-coords:")
for a in range(2):
    for b in range(2):
        print(f"  Sc[{a},{b}] =", sp.expand(Sc[a,b]))

# ---- KEY: is the map (8 free R-coords) -> (4 Sc-coords) a submersion with the
#      OTHER 4 coords (M12, M21 = the spectators) as fibre coordinates? ----
# Treat the change of variables: (r01,r02,r10,r20 ; r11,r12,r21,r22)
#   -> (r01,r02,r10,r20 ; Sc00,Sc01,Sc10,Sc11).
# i.e. keep the spectators (M12,M21) as themselves, map M22 -> Sc.
# Since Sc_ab = r_{(a+1)(b+1)} - M21_a*M12_b, the map M22 -> Sc at FIXED spectators
# is just a TRANSLATION: Sc = M22 - (rank-1 spectator matrix). Jacobian = identity!
spectators = [r[1], r[2], r[3], r[6]]   # r01, r02, r10, r20
M22coords  = [r[4], r[5], r[7], r[8]]   # r11, r12, r21, r22
Sccoords   = [Sc[0,0], Sc[0,1], Sc[1,0], Sc[1,1]]
J = sp.Matrix(4,4, lambda i,j: sp.diff(Sccoords[i], M22coords[j]))
print()
print("=== Jacobian d(Sc)/d(M22) at fixed spectators (M12,M21 held) ===")
sp.pprint(J)
print("det =", sp.simplify(J.det()))
