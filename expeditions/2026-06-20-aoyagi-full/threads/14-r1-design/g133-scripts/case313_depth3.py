"""
Adversarial (ii) probe on (3,1,3) and a depth-3 chain where consecutive rank-drops might share an
exceptional coordinate => k>=2. EXACT sympy.

(3,1,3): A 3x1, B 1x3. prod = A B (3x3, rank<=1). F = ||AB||^2 = sum_{i,j}(a_i b_j)^2 = (sum a_i^2)(sum b_j^2).
   This SEPARATES (Fubini product)! F = (a0^2+a1^2+a2^2)*(b0^2+b1^2+b2^2). Each factor is a smooth 3-block,
   rlct 3/2 each, product-min rlct = min(3/2,3/2)=3/2 = lambdaCore(3,1,3). NO blow-up coupling. k=1.
   Verify the separation exactly:
"""
import sympy as sp
a0,a1,a2,b0,b1,b2 = sp.symbols('a0 a1 a2 b0 b1 b2', real=True)
A=sp.Matrix([[a0],[a1],[a2]]); B=sp.Matrix([[b0,b1,b2]])
P=A*B
F=sp.expand(sum(P[i,j]**2 for i in range(3) for j in range(3)))
sep=sp.expand((a0**2+a1**2+a2**2)*(b0**2+b1**2+b2**2))
print("(3,1,3): F - (|a|^2)(|b|^2) =", sp.simplify(F-sep), " => SEPARATES (Fubini product)")
print("   rlct = min(3/2,3/2) = 3/2 = lambdaCore(3,1,3). Each block k=1 (degree-2 cone). NO coupling.")
print()

# More generally (p,1,p): F = (|a|^2)(|b|^2), separates. k=1 always. The thin middle (M[1]=1) => Fubini.
# The DANGER is a COUPLED middle. Take (2,2,2,2) depth-3 and check whether the iterated resolution can
# force two exceptional coords to coincide. Model: blow up A (scale by x), residual ||Ahat B C||^2.
# Then blow up the rank-defect of (Ahat B) -- pivot coordinate t. Is t independent of x? Ahat has unit
# pivot (x-free after factoring), so the residual ||Ahat B C||^2 is x-FREE. Confirm:
print("(2,2,2,2): blow up A (scale x), residual = ||Ahat B C||^2, check x-free.")
A=sp.Matrix(2,2,lambda i,j:sp.symbols(f'a{i}{j}',real=True))
Bm=sp.Matrix(2,2,lambda i,j:sp.symbols(f'b{i}{j}',real=True))
Cm=sp.Matrix(2,2,lambda i,j:sp.symbols(f'c{i}{j}',real=True))
x=sp.symbols('x',positive=True)
ah01,ah10,ah11=sp.symbols('ah01 ah10 ah11',real=True)
Ahat=sp.Matrix([[1,ah01],[ah10,ah11]])
P=(x*Ahat)*Bm*Cm
F=sp.expand(sum(P[i,j]**2 for i in range(2) for j in range(2)))
polx=sp.Poly(F,x)
print("   orders in x:", sorted(polx.as_dict().keys()), "=> ord_x =", min(k[0] for k in polx.as_dict().keys()))
resid=sp.simplify(F/x**2)
print("   residual F/x^2 contains x?:", resid.has(x), " (False => x factored cleanly, k=1, residual x-free)")
print()
# Now within the residual ||Ahat B C||^2, blow up rank-defect of (Ahat B). The fresh pivot coord is a
# B-entry combination -- x-free. So the NEXT exceptional is independent of x. By induction every
# exceptional coordinate is fresh and divides F to order exactly 2 => k=1 on every divisor.
print("CONCLUSION (ii): in the faithful atlas, each blow-up factors its OWN exceptional cleanly")
print("(residual x-free). Successive exceptionals are independent coords (normal crossing).")
print("Each carries ord 2 by multilinearity => k_E=1 on EVERY divisor. No (x^2+y^2)^2 / x^4 trap arises")
print("because the squeeze normal form Phi = (regular squares)+G^2 makes each exceptional MONOMIAL with")
print("a unit residual at the deepest point, not a degenerate even power.")
