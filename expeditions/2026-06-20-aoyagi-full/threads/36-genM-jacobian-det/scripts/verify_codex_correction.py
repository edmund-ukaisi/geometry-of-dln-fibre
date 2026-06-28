"""
Verify Codex's correction: from P = U V (U: m0 x 1, V: 1 x m1):
  P i j = U[i,0] * V[0,j].
  col 0 of P: c0 i = U[i,0]*V[0,0].
  WANT: P i j = mu_j * c0 i = mu_j * U[i,0] * V[0,0].
  Since P i j = U[i,0]*V[0,j], need mu_j*V[0,0] = V[0,j], i.e. mu_j = V[0,j]/V[0,0]. NEEDS V[0,0]!=0.
  ||c0||^2 = V[0,0]^2 * sum_i U[i,0]^2. So ||c0||^2 != 0  <=>  V[0,0]!=0 AND U!=0.
  => the off-pole hypothesis ||c0||^2 != 0 gives BOTH V[0,0]!=0 (needed for mu) AND the Gram invertibility.
Confirm with the counterexample P=[0,1]: U=[1] (1x1), V=[0,1]. col0=0, ||c0||^2=0 -> off-pole FAILS,
  so the bridge correctly EXCLUDES it. Good.
Also verify: in our chart, is V[0,0] (= the running product's first entry) generically nonzero, AND
  is it EXACTLY the quantity ||c0||^2 controls? i.e. {||c0||^2=0} = {V[0,0]=0} cup {U=0}.
"""
import sympy as sp
# symbolic m0=2, V = [v0, v1, v2], U=[u0;u1]
u0,u1,v0,v1,v2=sp.symbols('u0 u1 v0 v1 v2')
U=sp.Matrix([[u0],[u1]]); V=sp.Matrix([[v0,v1,v2]])
P=U*V
c0=[P[0,0],P[1,0]]
print("P=",P.tolist())
print("c0=col0=",c0)
# mu_j = V[0,j]/V[0,0]
mu=[sp.cancel(V[0,j]/v0) for j in range(3)]
print("mu=",mu)
for j in range(3):
    for i in range(2):
        lhs=P[i,j]; rhs=sp.cancel(mu[j]*c0[i])
        print(f"  P[{i},{j}]={lhs}  mu_j*c0_i={rhs}  eq={sp.simplify(lhs-rhs)==0}")
nrm=sp.expand(c0[0]**2+c0[1]**2)
print("||c0||^2 =", nrm, " = v0^2*(u0^2+u1^2):", sp.simplify(nrm-v0**2*(u0**2+u1**2))==0)
# Counterexample P=[0,1]: U=[1], V=[0,1]
print("\nCounterexample P=[0 1]: c0=0, ||c0||^2=0 -> off-pole hypothesis FAILS, bridge excludes it. Correct.")
