import sympy as sp
# M=(2,2,1), L=2, minAdm=2. N = M0*M1 + M1*M2 = 2*2 + 2*1 = 6.
# F = ||A0 * A1||^2, A0:2x2, A1:2x1. Product P = A0*A1 : 2x1. F = P[0]^2 + P[1]^2.
# Aoyagi: peel (2,2)->t, then leaf (t,1)=t*1. minAdm = min_t [(2-t)^2 + t*1]:
for t in range(3): print(f"  t={t}: (2-t)^2 + t = {(2-t)**2+t}")
# min at t=2: 0+2=2; or t=1: 1+1=2. minAdm=2.
# The achiever center: codim 2. The chart resolves it via a pivot blow-up of m=2 normal coords (1 pivot + 1 active free)
# PLUS layer-ops for spectators. Let me build a CORRECT option-(C) chart by hand and verify rate=u^2, det=|u|^{m-1}=|u|^1.
#
# Construction (mirroring 4422 spine + a Schur layer). Take the deepest factor A1 (2x1) as the rank-deficiency
# carrier. The achiever center {A0*A1=0} with the t=... pattern. Simplest: make P = A0*A1 = u * H (one u), det = u^{m-1}.
#
# Let me just exhibit the cleanest m=2 chart that is full-rank R^6->R^6 with det=|u|^1 and rate u^2.
# Flat coords u0..u5. Pivot p=0. Active set for radial = {0, j} for ONE free active j (m=2 => 1 pivot + 1 active).
# But we also need the loss to vanish to order u^2. The deepest factor carries the u.
#
# Take A1 = [[u0],[u0*u1]]  (the 2x1 deepest factor: entry 0 = u0 (fixed-1 scaled), entry 1 = u0*u1 (active))
#   -> this is pivotBlowupOn {0,1} 0 on the A1-slot coords. det of this 2-coord block = u0^{2-1}=u0^1.
# A0 = [[u2,u3],[u4,u5]] free (4 spectator coords, identity in flat map).
# P = A0*A1 = [[u2*u0 + u3*u0*u1],[u4*u0 + u5*u0*u1]] = u0*[[u2+u3*u1],[u4+u5*u1]] = u0 * H.  rate F = u0^2 * ||H||^2. GOOD.
u0,u1,u2,u3,u4,u5 = sp.symbols('u0 u1 u2 u3 u4 u5')
A1 = sp.Matrix([[u0],[u0*u1]])
A0 = sp.Matrix([[u2,u3],[u4,u5]])
P = A0*A1
print("P =", P)
Pf = sp.simplify(P/u0)
print("P/u0 =", Pf, " (u0-free?)", all(u0 not in e.free_symbols for e in Pf))
F = (P[0]**2 + P[1]**2)
Ff = sp.simplify(F/u0**2)
print("F/u0^2 =", sp.expand(Ff), " => rate = u0^2 * U, U=", sp.expand(Ff))
# Now the flat map: inputs (u0..u5) -> outputs = entries of A0 (4) and A1 (2) = [u2,u3,u4,u5, u0, u0*u1]
out = [u2,u3,u4,u5, u0, u0*u1]
ins=[u0,u1,u2,u3,u4,u5]
J = sp.Matrix([[sp.diff(o,v) for v in ins] for o in out])
print("det Dphi =", sp.factor(J.det()), " (expect ± u0^{m-1} = u0^1)")
print("minAdm(2,2,1)=2, m-1=1. PIVOT exponent =", sp.degree(sp.Poly(J.det(), u0)))
