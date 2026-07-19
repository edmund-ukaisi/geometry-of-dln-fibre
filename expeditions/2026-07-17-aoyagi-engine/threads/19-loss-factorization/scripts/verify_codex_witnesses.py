#!/usr/bin/env python3
"""
Re-verify (exactly) the two INDEPENDENT witnesses Codex produced (decorrelated;
hypothesis was withheld). pnp discipline: re-verify a consult's witnesses.

(W1) Pure-pivot chart fails ALREADY at L=2 (no incidence shear): with
     C1=α[[1,a],[b,ρ]], C2=[[ρξ,ρη],[r,s]], the loss at ρ=0 is α²a²(r²+s²) ≠ 0 —
     so the claimed α²ρ² factor is FALSE (ρ² not a factor). Witness α=a=r=½.

(W2) The scalar re-use example: x=u·r, r=u·s ⟹ x=u²·s; extracting only u² from
     x² leaves u²s², vanishing on u=0. (A divisor at product-power 2, not 1, in a
     naive pure-pivot re-use — precisely why the terminal divisor must be
     enumerated ONCE in divCoord and its accumulation put in divExp.)

(W3) The determinantal residual zero on the unit ratio box:
     [[1,1],[0,0]]·[[1,0],[-1,0]] = 0 with all ratios in [-1,1] — a constant-base
     lower bound fails on the full pivot box (kill-c) without normalization.
"""
import sympy as sp

# ---- (W1) pure-pivot L=2 ----
a,b,rho,xi,eta,r,s,alpha = sp.symbols('a b rho xi eta r s alpha', real=True)
C1 = alpha*sp.Matrix([[1,a],[b,rho]])
C2 = sp.Matrix([[rho*xi, rho*eta],[r,s]])
F = sp.expand(sum((C1*C2)[i,j]**2 for i in range(2) for j in range(2)))
Frho0 = sp.expand(F.subs({rho:0}))
print("=== (W1) pure-pivot L=2, loss at ρ=0 ===")
print("F|_{ρ=0} =", sp.factor(Frho0))
val = Frho0.subs({alpha:sp.Rational(1,2), a:sp.Rational(1,2), r:sp.Rational(1,2),
                  b:0, xi:0, eta:0, s:0})
print("at α=a=r=½ (rest 0):", val, " (nonzero => ρ² is NOT a factor; pure-pivot LeafPullback FALSE at L=2)")
print("   matches Codex F=α²a²(r²+s²):", sp.simplify(Frho0 - alpha**2*a**2*(r**2+s**2))==0)

# ---- (W2) scalar re-use x=u r, r=u s ----
u,ss = sp.symbols('u ss', real=True)
x = u*(u*ss)   # x = u*r, r = u*s
print("\n=== (W2) scalar re-use: x = u·r, r = u·s ===")
print("x =", sp.expand(x), " => x² =", sp.expand(x**2))
print("x²/u² =", sp.expand(x**2/u**2), " (still carries u² => vanishes on u=0 with s≠0)")
print("   => a divisor re-used by NAIVE pure pivots reaches product-power 2.")
print("   The construction AVOIDS this by enumerating the terminal divisor ONCE (divCoord)")
print("   and routing the accumulation to divExp (Jacobian) — the b_1-squarefree structure.")

# ---- (W3) determinantal residual zero on the ratio box ----
Md = sp.Matrix([[1,1],[0,0]])*sp.Matrix([[1,0],[-1,0]])
print("\n=== (W3) determinantal zero on unit ratio box ===")
print("[[1,1],[0,0]]·[[1,0],[-1,0]] =", Md.tolist(), " (=0 with all ratios in [-1,1])")
print("   => pure-pivot residual is NOT bounded below on the closed pivot box (kill-c).")
print("\nAll three Codex witnesses re-verified exactly. Convergent with the battery")
print("(l3_recursion / l3_leak_and_rb): normalization is load-bearing; pure-β leaks.")
