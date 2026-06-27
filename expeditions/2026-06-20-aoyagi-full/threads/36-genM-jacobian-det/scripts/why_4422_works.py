import sympy as sp
# (4,4,2,2): the blow-up is pivotBlowupOn {0,1,2,3} 0:
#   coord 0 (pivot u0) -> u0 ; coords 1,2,3 -> u0*u1, u0*u2, u0*u3 ; coords 4..27 -> identity (spectators).
# Then pack into A2 = [[u0, u0*u1],[u0*u2, u0*u3]], A0,A1 = spectators directly.
# The OUTPUT = A0,A1,A2 entries. A2's 4 entries are (u0, u0*u1, u0*u2, u0*u3). The other 24 outputs are
# the spectator coords directly. So the map R^28->R^28 is:
#   y0=u0, y1=u0*u1, y2=u0*u2, y3=u0*u3, y4..27 = u4..27.
# This is FULL RANK off u0=0: Jacobian is block [pivotBlowup 4x4 arrow] (det u0^3) + identity (24x24).
u0,u1,u2,u3 = sp.symbols('u0 u1 u2 u3')
out=[u0, u0*u1, u0*u2, u0*u3]
ins=[u0,u1,u2,u3]
J=sp.Matrix([[sp.diff(o,v) for v in ins] for o in out])
print("4422 active-block det =", sp.factor(J.det()), " = u0^3 (minAdm=4, m-1=3)")
# KEY: the pivot u0 maps to OUTPUT y0=u0 (a FIXED residual entry =1 scaled: A2(0,0)=u0*1).
# Every active coord (u1,u2,u3) is RECOVERABLE: u_i = y_i/y0. The map is injective off u0=0. det=u0^3.
#
# CONTRAST (2,2,2)-structured: there is NO fixed-1 entry. A0=C1 has entries (k1,k1n1,k1x1, e1*u+k1n1x1).
# The image is NOT all of R^8 -- it is the achiever variety (rank-deficient prod). The 8 inputs include
# 2 dead + the map collapses. det=0.
#
# The FIX must make the chart a genuine R^N -> R^N blow-up: pivot u as a DISTINCT slot scaling a FIXED
# residual entry =1 (like A2(0,0)=u0*1 in 4422), with (m-1) active free coords scaled by u, and the
# remaining N-m coords as identity spectators. THEN det = u^{m-1}, rate = u^2 (the prod carries one u).
print("CONCLUSION: 4422 works because pivot scales a FIXED 1-entry (A2(0,0)=u0); det=u0^3. The structured")
print("decoder has NO fixed-1 slot and over-parametrizes -> det=0. CONFIRMS the wall (worse: det=0 not u^m).")
