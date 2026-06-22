"""
Attack (ii)/(iii) crux: the per-node SQUEEZE c1*Phi <= F <= c2*Phi needs c1>0. If c1 could be 0 (F
vanishes faster than Phi on some divisor), the squeeze breaks and F undershoots. I verify on the
(2,2,2) post-step1 residual that F and Phi have the SAME zero set AND the ratio F/Phi is bounded in
[c1,c2] with c1>0 near the deepest point (so ord_divisor(F) = ord_divisor(Phi), k_E = k(Phi) = 1).

After step1 (A = x*Ahat, pivot a00=1), residual core G1 = ||Ahat B||^2 (an x-free 2x2 chain norm).
Ahat = [[1, p],[q, r]] (p=ah01,q=ah10,r=ah11 small). The deepest point of G1 is B=0 (Ahat invertible
near pivot). So G1 = ||Ahat B||^2 with Ahat invertible => G1 = B^T (Ahat^T Ahat) B summed = a POSITIVE
DEFINITE quadratic form in the entries of B (since Ahat^T Ahat is SPD near the pivot). So G1 is itself
a smooth nondegenerate block in B -- rlct 4/2 = 2. The SQUEEZE: G1 = ||Ahat B||^2 vs Phi = ||B||^2.
Since Ahat invertible, sigma_min(Ahat)^2 ||B||^2 <= ||Ahat B||^2 <= sigma_max(Ahat)^2 ||B||^2, with
sigma_min(Ahat) > 0 near pivot (Ahat -> I). So c1 = sigma_min^2 > 0, c2 = sigma_max^2. The squeeze
HOLDS with c1>0. Verify sigma_min(Ahat)>0 at the pivot point (Ahat=I):
"""
import sympy as sp
p,q,r = sp.symbols('p q r', real=True)
Ahat = sp.Matrix([[1,p],[q,r]])
G = (Ahat.T*Ahat)
print("Ahat^T Ahat =")
sp.pprint(G)
# eigenvalues at pivot point p=q=0, r=1 (Ahat=I):
G0 = G.subs({p:0,q:0,r:1})
ev = G0.eigenvals()
print("at Ahat=I: eigenvalues of Ahat^T Ahat =", ev, " => sigma_min^2 = 1 > 0 => c1=1>0. SQUEEZE HOLDS.")
# Generic small Ahat: det(Ahat) = r - p*q, near (p,q,r)=(0,0,1) det ~ 1 != 0 => invertible => c1>0.
print("det(Ahat) =", sp.expand(Ahat.det()), " -> at pivot (0,0,1) = 1 != 0 => Ahat invertible => c1>0 nearby.")
print()
print("KEY: the squeeze lower constant c1 = sigma_min(Ahat)^2 > 0 BECAUSE the blow-up made the pivot a")
print("UNIT (Ahat invertible). This is WHY the blow-up runs FIRST: at the bare origin A=0, Ahat is")
print("degenerate and c1=0; the blow-up restores invertibility => c1>0 => squeeze valid => k_E=1.")
print()
# The two-sided squeeze with c1,c2>0 forces ord(F)=ord(Phi) on every divisor:
print("Two-sided squeeze c1*Phi <= F <= c2*Phi, c1,c2>0  =>  along ANY curve gamma(t)->0:")
print("  c1*Phi(gamma) <= F(gamma) <= c2*Phi(gamma)  =>  ord_t F = ord_t Phi (same leading order).")
print("  => k_E(F) = k_E(Phi) on every exceptional divisor. Phi is the smooth-block normal form (k=1).")
print("  So the squeeze TRANSFERS k=1 from Phi to F. NO higher-multiplicity undershoot, PROVIDED c1>0,")
print("  which the unit-pivot (post-blow-up) guarantees.")
