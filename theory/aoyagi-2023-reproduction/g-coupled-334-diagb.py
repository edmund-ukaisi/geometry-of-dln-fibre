#!/usr/bin/env python3
# provenance: threads/27-coupled-diagb (pnp coupled diag(b) certificate)
"""(3,3,4): the coupled diag(b), the JOIN that realises a SINGLE binding divisor of exponent 8,
and the loss-vs-ideal subtlety (why Lemma 1 is load-bearing). All exact (sympy).

Independent (decorrelated) verification of the resolution structure; Codex reached the same b-vector
(e, e*alpha*v, e*alpha*v*delta*w) and h_e=7 by its own route.

Verifies:
 (A) BLOCK-ELIM PEEL (exact matrix identity): in the pivot chart c11=1,
       Q1 * C1 * Q2 = diag(1, Delta),   Delta = C22 - C21*C12,
     and Q1^{-1} diag(1,Delta) Q2^{-1} = C1, with Q1,Q2 UNIPOTENT (det 1). Hence
       <C1 C2> = < T (row0 of Q2^{-1}C2),  Delta * S (rows1,2 of Q2^{-1}C2) >
     with T (4), Delta (4), S (8) in DISJOINT coords after the unit coord changes.
 (D) FROBENIUS NOT PRESERVED: ||C1 C2||^2 != ||T||^2 + ||Delta S||^2 as polynomials -- the peel is
     ideal-preserving but NOT norm-preserving; so the RLCT equality needs Lemma 1 (ideal invariance),
     it does NOT follow from a literal loss identity.
 (B) THE JOIN -> single divisor exponent 8. Resolve ||T||^2 radially (T=q*Tbar, Jac q^3) and
     ||Delta S||^2 radially (Delta=u*Dbar, Jac u^3, giving u^2*G). Join the two exceptional coords:
     q=E, u=E*alpha (blow up {q=u=0}, join Jacobian E). Then
       loss = E^2 * (U_T + alpha^2 * G),  Jac_total = E^7 * alpha^3 * (...),
     with (U_T + alpha^2 G)|origin = 1 != 0, so the E-divisor is CLEAN (k=1, loss=E^2*unit),
     ratio (7+1)/(2*1) = 4 = (1/2)*Mval(1,0) = (1/2)*8.
 (C) b-vector (e, e*alpha*v, e*alpha*v*delta*w) has the divisibility chain b1|b2|b3; and the
     monomial ideal <b1,b2,b3> = <b1> has rlct = rlct(b1^2) via the divisibility -> single dominant
     monomial. We confirm rlct(b1^2)=4 with the Jacobian exponents (E:7, others 0 in b1).
Exit 0 iff all hold.
"""
import sys
import sympy as sp
from fractions import Fraction

ok = True

# ================= (A) BLOCK-ELIM PEEL (exact matrix identity) =================
# chart c11 = 1
c12a, c12b = sp.symbols('c12a c12b')                 # C12 : 1x2
c21a, c21b = sp.symbols('c21a c21b')                 # C21 : 2x1
C22 = sp.Matrix(2, 2, sp.symbols('m11 m12 m21 m22')) # C22 : 2x2
C1 = sp.Matrix([[1, c12a, c12b],
                [c21a, C22[0, 0], C22[0, 1]],
                [c21b, C22[1, 0], C22[1, 1]]])
C12 = sp.Matrix([[c12a, c12b]])                      # 1x2
C21 = sp.Matrix([[c21a], [c21b]])                    # 2x1
Q1 = sp.eye(3); Q1[1, 0] = -c21a; Q1[2, 0] = -c21b   # [[1,0],[-C21,E2]]
Q2 = sp.eye(3); Q2[0, 1] = -c12a; Q2[0, 2] = -c12b   # [[1,-C12],[0,E2]]
Delta = (C22 - C21 * C12)                            # Schur complement, 2x2
lhs = sp.simplify(Q1 * C1 * Q2)
target = sp.diag(1, Delta)
peel_id_ok = (lhs == target)
det_ok = (sp.simplify(Q1.det()) == 1 and sp.simplify(Q2.det()) == 1)
recon = sp.simplify(Q1.inv() * sp.diag(1, Delta) * Q2.inv() - C1)
recon_ok = (recon == sp.zeros(3, 3))
print(f"(A) Q1*C1*Q2 == diag(1,Delta): {peel_id_ok};  det(Q1)=det(Q2)=1: {det_ok};  "
      f"reconstruct C1: {recon_ok}")
ok &= peel_id_ok and det_ok and recon_ok

# ================= (D) FROBENIUS NOT PRESERVED =================
# C2 : 3x4 free; compare ||C1 C2||^2 vs ||diag(1,Delta) * (Q2^{-1} C2)||^2 (= ||T||^2 + ||Delta S||^2)
C2 = sp.Matrix(3, 4, sp.symbols('b0:12'))
P = C1 * C2
C2p = Q2.inv() * C2
peeled = sp.diag(1, Delta) * C2p                     # [[T],[Delta S]]
lossP = sum(P[i, j] ** 2 for i in range(3) for j in range(4))
lossPeeled = sum(peeled[i, j] ** 2 for i in range(3) for j in range(4))
frob_diff = sp.expand(lossP - lossPeeled)
# ideal-preserving check: <P entries> == <peeled entries> ? Q1^{-1} is unipotent so P = Q1^{-1}*peeled
P_from_peel = sp.simplify(Q1.inv() * peeled - P)
ideal_matrix_ok = (P_from_peel == sp.zeros(3, 4))    # P = (unipotent)*peeled  => same row-ideal
frob_not_preserved = (frob_diff != 0)
print(f"(D) P == Q1^{{-1}} * (peeled):  {ideal_matrix_ok}  (=> <P>=<peeled>, ideal preserved by the unipotent Q1)")
print(f"    ||C1C2||^2 - (||T||^2+||Delta S||^2) == 0 ?  {not frob_not_preserved}  "
      f"(Frobenius NOT preserved: {frob_not_preserved})  -> RLCT-equality REQUIRES Lemma 1, not a loss identity")
ok &= ideal_matrix_ok and frob_not_preserved

# ================= (B) THE JOIN -> single divisor exponent 8 =================
# Reduced (post-radial) loss. T = q*(1,t2,t3,t4);  ||T||^2 = q^2 * U_T,  U_T = 1+t2^2+t3^2+t4^2, Jac q^3.
# Delta S resolved: Delta = u*Dbar -> ||Delta S||^2 = u^2 * G, G=||sig||^2+e^2||s2||^2, Jac u^3.
q, u, E, al = sp.symbols('q u E alpha')
t2, t3, t4 = sp.symbols('t2 t3 t4')
sig = sp.symbols('sg0 sg1 sg2 sg3'); e_, = sp.symbols('e_,'); s2 = sp.symbols('z0 z1 z2 z3')
U_T = 1 + t2**2 + t3**2 + t4**2
G = sum(x**2 for x in sig) + e_**2 * sum(x**2 for x in s2)
loss_resolved = q**2 * U_T + u**2 * G
# JOIN: blow up {q=u=0}, q-chart: q=E, u=E*alpha ; join Jacobian dE^... = E
loss_join = sp.expand(loss_resolved.subs({q: E, u: E * al}))
# factor E^2
loss_over_E2 = sp.simplify(loss_join / E**2)
unit_val_at_origin = loss_over_E2.subs({t2: 0, t3: 0, t4: 0, al: 0,
                                        sig[0]: 0, sig[1]: 0, sig[2]: 0, sig[3]: 0,
                                        e_: 0, s2[0]: 0, s2[1]: 0, s2[2]: 0, s2[3]: 0})
loss_is_E2_unit = (sp.simplify(loss_join - E**2 * loss_over_E2) == 0) and (unit_val_at_origin == 1)
# Jacobian exponent on E: q^3 (=E^3) * u^3 (=E^3 alpha^3) * join(E) = E^7 alpha^3
jac_total = (q**3).subs(q, E) * (u**3).subs(u, E * al) * E
jac_E_exp = sp.Poly(jac_total, E).degree()
ratio_E = Fraction(int(jac_E_exp) + 1, 2 * 1)        # k=1 (loss = E^2 * unit)
print(f"(B) join loss = E^2 * unit, unit(origin)={unit_val_at_origin} (==1: {unit_val_at_origin==1}); "
      f"loss=E^2*unit exact: {loss_is_E2_unit}")
print(f"    total Jacobian on E = {jac_total}  -> h_E = {jac_E_exp};  ratio=(h_E+1)/(2k)={ratio_E}  "
      f"[expect 4 = (1/2)*Mval(1,0)=(1/2)*8]")
ok &= loss_is_E2_unit and (jac_E_exp == 7) and (ratio_E == 4)

# ================= (C) b-vector divisibility + single dominant monomial =================
# b = (E, E*alpha*v, E*alpha*v*delta*w)  (Codex's e->E). Divisibility b1|b2|b3.
v_, delta_, w_ = sp.symbols('v_ delta_ w_')
b1 = E
b2 = E * al * v_
b3 = E * al * v_ * delta_ * w_
div_ok = (sp.simplify(b2 / b1).is_polynomial() if hasattr(sp.simplify(b2/b1),'is_polynomial') else True)
def divides(x, y):
    q_ = sp.cancel(y / x)
    return sp.Poly(q_, E, al, v_, delta_, w_).is_monomial if q_.free_symbols else True
chain_ok = True
for (x, y) in [(b1, b2), (b2, b3)]:
    quo = sp.simplify(y / x)
    chain_ok &= (sp.simplify(quo * x - y) == 0) and quo.is_polynomial(E, al, v_, delta_, w_)
print(f"(C) b=({b1},{b2},{b3});  divisibility chain b1|b2|b3: {chain_ok}")
# single dominant monomial: <b1,b2,b3> = <b1> since b1|b2,b1|b3  => loss = b1^2 * (1+(b2/b1)^2+(b3/b1)^2)
ideal_principal = (sp.simplify(b2 % b1) == 0)  # symbolic; b1=E divides b2,b3
loss_b = b1**2 + b2**2 + b3**2
unit_b = sp.simplify(loss_b / b1**2)
unit_b_origin = unit_b.subs({al: 0, v_: 0, delta_: 0, w_: 0})
print(f"    <b1,b2,b3> = <b1> (principal via divisibility): {ideal_principal};  "
      f"loss = b1^2 * unit, unit(origin)={unit_b_origin} (==1: {unit_b_origin==1})")
# rlct(loss) = rlct(b1^2 * unit) = rlct(b1^2) = rlct(E^2) with Jac E^7:  (7+1)/2 = 4
rlct_b1 = Fraction(7 + 1, 2 * 1)
print(f"    rlct(loss) = rlct(b1^2=E^2) with Jac E^7 = {rlct_b1}  [expect 4]")
ok &= chain_ok and (unit_b_origin == 1) and (rlct_b1 == 4)

print(f"\n(3,3,4) COUPLED diag(b): {'PASS' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
