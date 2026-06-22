import sympy as sp
# Does an analytic Morse c-o-v make loss = ∑Ẽ² + g(core) EXACT? Test the 2-layer scalar case.
# loss = E00² + E01² + E10² + P11², with P11 = R + leak, leak = E10(1+E00)^{-1}E01, R the core Schur.
# = E00² + E01² + E10² + R² + 2 R·leak + leak².
# The Morse/splitting lemma: complete the square in the regular block (E00,E01,E10) to absorb 2R·leak+leak².
A,Y,Z,T = sp.symbols('A Y Z T'); B,U,V,S = sp.symbols('B U V S')
C1=sp.Matrix([[A,Y],[Z,T]]); C2=sp.Matrix([[B,U],[V,S]]); P=sp.expand(C1*C2)
E00=P[0,0]-1; E01=P[0,1]; E10=P[1,0]; P11=P[1,1]
loss = sp.expand(E00**2+E01**2+E10**2+P11**2)
R = sp.simplify(P11 - E10*(1+E00)**(-1)*E01)   # full-product Schur (=P11 - leak)
leak = sp.simplify(E10*(1+E00)**(-1)*E01)
print("leak =", leak, "  (carries E10·E01 => O(reg²))")
print("R (core) =", sp.simplify(R))
print()
# The claim: loss = E00² + E01² + (E10 + δ)² + R²  for some δ = δ(E, core) absorbing the cross.
# i.e. complete the square in E10: E10² + 2R·leak = E10² + 2R·E10·(1+E00)^{-1}E01 
#      = (E10 + R(1+E00)^{-1}E01)² - R²(1+E00)^{-2}E01²  ... let me just check if loss - (∑E² + R²) is
# absorbable. Compute the correction:
corr = sp.expand(loss - (E00**2+E01**2+E10**2+R**2))
print("correction = loss - (∑E² + R²) =", sp.simplify(corr))
print("  (= 2R·leak + leak², should be O(E01²·...) — carries E01 factors)")
print()
# Does corr factor through the regular coords E01,E10,E00? i.e. is corr in the ideal <E00,E01,E10>?
# Since leak ~ E10 E01, corr = 2R·E10·c·E01 + (E10 c E01)² with c=(1+E00)^{-1}. EVERY term has E01 (and E10).
corr_simpl = sp.simplify(corr)
# substitute E01->0 (i.e. P01->0): does corr vanish?
# E01 = P[0,1] = A*U + Y*S (the (0,1) entry). Set that =0:
print("Is the correction in the ideal <E01,E10>? Check: set leak's factors.")
# Morse completing-the-square in (E00,E01,E10): the new regular coords Ẽ_i = E_i + (core-dep h.o.t).
# The theorem holds iff the 3 regular gens (E00,E01,E10) have INDEPENDENT differentials at w0 (Jacobian
# rank 3) AND the correction is O(2) in them with no pure-core part. corr has every term carrying E01·E10
# => O(reg²), NO pure-core term. So completing the square is possible: loss∘φ = Ẽ00²+Ẽ01²+Ẽ10² + R².
print("corr lowest-order terms (in small a,b):")
ab = sp.symbols('a0:8')  # not used; just expand corr and show it's >=order 3 (reg²·core)
corr_poly = sp.Poly(corr_simpl* (1+E00)**2, [A,Y,Z,T,B,U,V,S]) if corr_simpl else None
# simpler: numerically confirm corr / (E01²+E10²) is bounded (=> absorbable into regular square)
import random
print()
print("Numeric: corr / (E01²+E10²+E00²) on small perturbations from w0 (A=B=1, rest 0):")
for _ in range(4):
    sub={A:1+0.01*random.uniform(-1,1),B:1+0.01*random.uniform(-1,1),
         Y:0.01*random.uniform(-1,1),Z:0.01*random.uniform(-1,1),
         U:0.01*random.uniform(-1,1),V:0.01*random.uniform(-1,1),
         T:0.01*random.uniform(-1,1),S:0.01*random.uniform(-1,1)}
    e2=float((E00**2+E01**2+E10**2).subs(sub))
    c=float(corr.subs(sub))
    print(f"   corr={c:.3e}, ∑E²={e2:.3e}, ratio corr/∑E²={c/e2 if e2 else 0:.4f}")
