import sympy as sp

# CONSTRUCT the genuine chart explicitly and verify det = u0^7, all 21 coords live, F o phi = u0^2 U.
# 
# 21 chart coords u0..u20. Roles:
#   u0   = PIVOT (blow-up). The exceptional/binding axis. Jacobian u0^7.
#   u1   = a   = A[0,0]  (spectator, will live in [1/2,1] for the achiever box; here just FREE)
#   u2   = b0  = the shear param 1 (FREE spectator -- this is what the OLD chart dropped!)
#   u3   = b1  = the shear param 2 (FREE spectator -- dropped by OLD chart!)
#   u4   = c0  = A[1,0]  (spectator)
#   u5   = c1  = A[2,0]  (spectator)
#   u6..u9   = Delta (the 2x2 residual D-block), BLOWN UP: E-block entries = u0 * Delta + shear-correction
#   u10..u12 = tau (the T-row direction), BLOWN UP: T-row = u0*(1,tau)
#   u13..u20 = S (2x4), spectator (8 coords)
#
# The flat output (A 3x3, C 3x4). The chart realizes A C = [[a u0 (1,tau)],[c u0(1,tau) + u0 Delta S]]
# AND reads b. The trick: the SHEAR is applied to FLAT C so the b*S cancels. Define flat:
#   C[0,:] = u0*(1,tau) - a^{-1} b S   (the INVERSE shear: y = T - a^{-1} b S, T=u0(1,tau))
#   C[1:3,:] = S
#   A[0,0]=a=u1, A[0,1:3]=b=(u2,u3), A[1:3,0]=c=(u4,u5), A[1:3,1:3]=E = u0*Delta + c a^{-1} b
# Then A C = ... let me just compute symbolically and verify F = u0^2 U.
u0,a,b0,b1,c0,c1 = sp.symbols('u0 a b0 b1 c0 c1', real=True)
D00,D01,D10,D11 = sp.symbols('D00 D01 D10 D11', real=True)   # Delta
t1,t2,t3 = sp.symbols('t1 t2 t3', real=True)                  # tau
S = sp.Matrix(2,4, lambda i,j: sp.Symbol(f'S{i}{j}', real=True))

b = sp.Matrix([[b0, b1]])      # 1x2
c = sp.Matrix([[c0],[c1]])     # 2x1
Delta = sp.Matrix([[D00,D01],[D10,D11]])
tau_row = sp.Matrix([[1, t1, t2, t3]])   # 1x4
T = u0 * tau_row                          # 1x4  (the blown-up top)

# flat A:
ainv = 1/a
E = u0*Delta + c*ainv*b      # 2x2  (E = D + c a^{-1} b, so D = E - c a^{-1} b = u0 Delta)
A = sp.Matrix(sp.BlockMatrix([[sp.Matrix([[a]]), b],[c, E]]))   # 3x3
# flat C:
y = T - ainv*b*S             # 1x4  (y = T - a^{-1} b S, so T = y + a^{-1} b S)
C = sp.Matrix(sp.BlockMatrix([[y],[S]]))                        # 3x4
AC = sp.simplify(A*C)
# Claim AC = [[a T],[c T + u0 Delta S]]:
claim = sp.Matrix(sp.BlockMatrix([[a*T],[c*T + u0*Delta*S]]))
print("A C = [[a T],[c T + u0 Delta S]] (shear cancels b):", sp.simplify(AC - claim) == sp.zeros(3,4))
F = sum(AC[i,j]**2 for i in range(3) for j in range(4))
U = sp.expand(F/u0**2)
print("F = u0^2 * U, U u0-free:", sp.simplify(F - u0**2*U)==0, "; U has u0:", U.has(u0))
print()
# This chart READS b0,b1 (=u2,u3) in y and E. But is it a DIFFEO with det = u0^7? The map is
# (u0,a,b,c,Delta,tau,S) -> flat(A,C). The flat coords are 9 (A) + 12 (C) = 21. The 21 chart coords map
# to 21 flat coords. Compute the Jacobian determinant.
# Flat coord vector (21): A[0,0],A[0,1],A[0,2],A[1,0],A[1,1],A[1,2],A[2,0],A[2,1],A[2,2],
#                          C[0,0..3], C[1,0..3], C[2,0..3].
flat = [A[0,0],A[0,1],A[0,2],A[1,0],A[1,1],A[1,2],A[2,0],A[2,1],A[2,2]] + \
       [C[0,j] for j in range(4)] + [C[1,j] for j in range(4)] + [C[2,j] for j in range(4)]
chart_coords = [u0,a,b0,b1,c0,c1,D00,D01,D10,D11,t1,t2,t3] + [S[0,j] for j in range(4)] + [S[1,j] for j in range(4)]
print("num flat coords:", len(flat), " num chart coords:", len(chart_coords))
J = sp.Matrix(flat).jacobian(chart_coords)
detJ = sp.simplify(J.det())
print("det Dphi =", detJ)
print("det == u0^7 (up to sign):", sp.simplify(detJ - u0**7)==0 or sp.simplify(detJ + u0**7)==0)
